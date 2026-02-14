# Copyright © 2025 Falvien Jaquerod, Clément Pit-Claudel
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

from pathlib import Path
from typing import Any, ClassVar, Iterable, Optional

import dataclasses
import re

from .core import Document, UTF8Document, Fragment, Goal, Hypothesis, Message, Positioned, Sentence, Text, must
from .lsp import JSON, LSPClient, LSPClientInitializeRequest, LSPClientNotification, LSPClientRequest, LSPDiagnostic, LSPDriver, LSPFile, LSPServerException, LSPServerNotification, LSPServerNotifications
from .coq import CoqIdents

class Notifications(LSPServerNotifications):
    PROOF_VIEW = "prover/proofView"
    BLOCK_ON_ERROR = "prover/blockOnError"

@dataclasses.dataclass
class StepForwardNotification(LSPClientNotification):
    METHOD = "prover/stepForward"
    fpath: Path
    uri: str

    def __post_init__(self):
        self.blocked_on_error = False
        self.proof_view: Optional[JSON] = None
        self.diagnostics: list[LSPDiagnostic] = [] # Could be handled by a wrapper class

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 } }

    def process_notification(self, message: LSPServerNotification):
        super().process_notification(message)
        if message.method == Notifications.PROOF_VIEW:
            self.proof_view = message.params
        elif message.method == Notifications.BLOCK_ON_ERROR:
            self.blocked_on_error = True
        elif message.method == Notifications.PUBLISH_DIAGNOSTICS:
            uri = message.params["uri"]
            fpath = str(self.fpath) if uri == self.uri else uri
            self.diagnostics.extend(LSPDiagnostic.of_json(fpath, d) for d in message.params["diagnostics"])

    @property
    def done(self) -> bool:
        return self.proof_view is not None

@dataclasses.dataclass
class URIRequest(LSPClientRequest):
    uri: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri } }

class DocumentProofsRequest(URIRequest):
    METHOD = "prover/documentProofs"

class DocumentStateRequest(URIRequest):
    METHOD = "prover/documentState"

@dataclasses.dataclass
class ExponentialBackoff:
    delay = 0.05
    delay_multiplier = 2

    def ready(self) -> bool:
        raise NotImplementedError

    def wait(self):
        import time
        while not self.ready():
            time.sleep(self.delay)
            self.delay *= self.delay_multiplier

@dataclasses.dataclass
class VsRocqReadyMonitor(ExponentialBackoff):
    """Wait until the document is parsed.

    We need this to get answers to StepForward queries; waiting on
    `DocumentState` doesn't work because it succeeds with empty contents if the
    document isn't parsed yet.
    """
    PARSING_NOT_FINISHED: ClassVar[int] = -32802

    client: "VsRocqClient"
    uri: str

    def ready(self):
        try:
            DocumentProofsRequest(self.client, self.uri).send()
        except LSPServerException as e:
            if e.code == self.PARSING_NOT_FINISHED:
                return False
            raise e
        return True

PP = str | list["PP"]

class VsRocqOutput:
    @staticmethod
    def string_of_pp_string(pp: PP) -> str:
        """Convert a Coq pretty-printed string to a regular string."""
        # FIXME get VsRocq to return structured output

        if not isinstance(pp, list) or len(pp) == 0:
            return str(pp) if pp else ""

        hd = pp[0]
        if hd == "Ppcmd_empty":
            return ""
        if hd == "Ppcmd_string":
            return str(pp[1]) if len(pp) > 1 else ""
        if hd == "Ppcmd_glue":
            if len(pp) > 1 and isinstance(pp[1], list):
                return "".join(VsRocqOutput.string_of_pp_string(sub_pp) for sub_pp in pp[1])
            return ""
        if hd == "Ppcmd_box":
            return VsRocqOutput.string_of_pp_string(pp[2]) if len(pp) > 2 else ""
        if hd == "Ppcmd_tag":
            return VsRocqOutput.string_of_pp_string(pp[2]) if len(pp) > 2 else ""
        if hd == "Ppcmd_print_break":
            return " " * pp[1] if len(pp) > 1 and isinstance(pp[1], int) else ""
        if hd == "Ppcmd_force_newline":
            return "\n"
        if hd == "Ppcmd_comment":
            if len(pp) > 1 and isinstance(pp[1], list):
                return " ".join(str(p) for p in pp[1])
            return ""
        else:
            return str(pp)

    @staticmethod
    def parse_message(mv: list[Any]) -> Message | None:
        level: int = mv[0] # LATER: Include message level in message
        pp: str = VsRocqOutput.string_of_pp_string(mv[1])
        return Message(pp) # TODO: Filter info-level messages

    @staticmethod
    def parse_hyp(hv):
        # FIXME don't use string processing: parse the structure instead
        # FIXME := from let will be parsed as hyp body
        full_str = VsRocqOutput.string_of_pp_string(hv)
        colon_count = full_str.count(':')
        if colon_count == 0:
            return Hypothesis(names=[full_str.strip()], body=None, type="")
        elif colon_count == 1:
            name_part, type_part = full_str.split(':', 1)
            return Hypothesis(names=[name_part.strip()], body=None, type=type_part.strip())
        else:
            first_colon_index = full_str.find(':')
            last_colon_index = full_str.rfind(':')
            name_part = full_str[:first_colon_index]
            type_part = full_str[last_colon_index + 1:]
            body_part = full_str[first_colon_index + 1:last_colon_index]
            return Hypothesis(names=[name_part.strip()], body=body_part.strip(), type=type_part.strip())

    @staticmethod
    def parse_goal(gv: JSON):
        name = gv.get("id", None)
        conclusion = VsRocqOutput.string_of_pp_string(gv["goal"])
        hypotheses = [VsRocqOutput.parse_hyp(hv) for hv in gv["hypotheses"]]
        return Goal(name if isinstance(name, str) else None, conclusion, hypotheses)

    @staticmethod
    def parseproof_view(pv: JSON):
        messages = [m for mv in pv.get("messages", []) if (m := VsRocqOutput.parse_message(mv))]
        goals = [VsRocqOutput.parse_goal(gv) for gv in (pv.get("proof") or {}).get("goals", [])]
        return messages, goals

class VsRocqClient(LSPClient):
    LANGUAGE_ID = "coq"

    INITIALIZATION_OPTIONS: JSON = {
        "goals": {
            "ppmode": "String", # Don't return Pp boxes
            "messages": { "full": True }, # Include errors and warnings with proof views
        },
        "proof": {
            "mode": 0, # Step manually
            "block": False, # Continue past the first error
        },
        "completion": { "enable": False },
        "diagnostics": { "full": False } # Dual of messages.full (skip info diagnostics)
    }

    def _init(self) -> LSPClientInitializeRequest:
        req = super()._init()
        req.params["initializationOptions"] = self.INITIALIZATION_OPTIONS
        return req

class VsRocqFile(LSPFile[VsRocqClient]):
    def _compute_ranges(self):
        req = DocumentStateRequest(self.client, self.uri)
        document: str = must(req.send().result)["document"]
        sep = document.find("Document using sentences_by_end map")
        assert sep >= 0, "Unexpected VsRocq documentState format"
        PATTERN = re.compile(r"\[\d+\].*?[(](?P<beg>\d+) -> (?P<end>\d+)[)]")
        for m in PATTERN.finditer(document[:sep].replace("\n", " ")):
            yield int(m.group("beg")), int(m.group("end"))

    def process(self) -> Iterable[Positioned[Fragment]]:
        VsRocqReadyMonitor(self.client, self.uri).wait()

        blocked_on_error: bool = False
        diagnostics: dict[LSPDiagnostic, None] = {}

        for (beg, end) in self._compute_ranges():
            contents: str = self.doc[beg:end]
            if blocked_on_error:
                yield Positioned(beg, end, Text(contents))
                continue
            pv = StepForwardNotification(self.client, self.fpath, self.uri).send()
            messages, goals = VsRocqOutput.parseproof_view(must(pv.proof_view))
            yield Positioned(beg, end, Sentence(contents, messages, goals))
            diagnostics |= dict.fromkeys(pv.diagnostics)
            blocked_on_error |= pv.blocked_on_error

        # LATER: Adjust line numbers for code blocks embedded in literate documents.
        for diag in diagnostics:
            if diag.severity >= 3:
                continue
            diag.notify(self.doc, self.client)

class VsRocq(LSPDriver[VsRocqClient]):
    BIN = "vsrocqtop"
    NAME = "VsRocq"
    VERSION_ARGS = ("--version",)

    ID = "vsrocq"
    LANGUAGE = "coq"
    AUTOSELECT = True

    CLIENT = VsRocqClient

    @staticmethod
    def _normalize_fpath(p: Path) -> Path:
        return CoqIdents.toppath_of_fpath(p)

    def _encode(self, chunks: Iterable[str]) -> Document:
        # FIXME: VsRocq sends prover/documentState info using utf-8 offsets but
        # uses codepoints (instead of utf-16?) in diagnostic line/char pairs.
        return UTF8Document(chunks, "\n")

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        """Find sentences in the document using VsRocq."""
        return VsRocqFile(self, document).process()
