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
from typing import ClassVar, Dict, Iterable, Optional

import dataclasses
import re

from .core import EncodedDocument, Fragment, Goal, Hypothesis, Message, Observer, Position, Positioned, Range, Sentence, Text, must
from .lspFinal import JSON, LSPClient, LSPClientNotification, LSPClientRequest, LSPDiagnostic, LSPDriver, LSPServerException, LSPServerMessage, LSPServerNotification, LSPServerNotifications
from .transforms import coalesce_text

class Notifications(LSPServerNotifications):
    PROOF_VIEW = "vscoq/proofView"
    BLOCK_ON_ERROR = "vscoq/blockOnError"

@dataclasses.dataclass
class StepForwardNotification(LSPClientNotification):
    METHOD = "vscoq/stepForward"
    fpath: Path
    uri: str

    def __post_init__(self):
        self.blocked_on_error = False
        self.proof_view: Optional[JSON] = None
        self.diagnostics: list[LSPDiagnostic] = [] # Could be handled by a wrapper class

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 } }

    def process_message(self, message: LSPServerMessage) -> None:
        super().process_message(message)
        if not isinstance(message, LSPServerNotification):
            return
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
    METHOD = "vscoq/documentProofs"

class DocumentStateRequest(URIRequest):
    METHOD = "vscoq/documentState"

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
class VsCoqReadyMonitor(ExponentialBackoff):
    """Wait until the document is parsed.

    We need this to get answers to StepForward queries; waiting on
    `DocumentState` doesn't work because it succeeds with empty contents if the
    document isn't parsed yet.
    """
    PARSING_NOT_FINISHED: ClassVar[int] = -32802

    client: "VsCoqClient"
    uri: str

    def ready(self):
        try:
            DocumentProofsRequest(self.client, self.uri).send()
        except LSPServerException as e:
            if e.code == self.PARSING_NOT_FINISHED:
                return False
            raise e
        return True

class VsCoqOutput:
    @staticmethod
    def string_of_pp_string(pp):
        """Convert a Coq pretty-printed string to a regular string."""
        # FIXME get VsCoq to return structured output

        if not isinstance(pp, list) or len(pp) == 0:
            return str(pp) if pp else ""

        match pp[0]:
            case "Ppcmd_empty":
                return ""
            case "Ppcmd_string":
                return pp[1] if len(pp) > 1 else ""
            case "Ppcmd_glue":
                if len(pp) > 1 and isinstance(pp[1], list):
                    return "".join(VsCoqOutput.string_of_pp_string(sub_pp) for sub_pp in pp[1])
                return ""
            case "Ppcmd_box":
                return VsCoqOutput.string_of_pp_string(pp[2]) if len(pp) > 2 else ""
            case "Ppcmd_tag":
                return VsCoqOutput.string_of_pp_string(pp[2]) if len(pp) > 2 else ""
            case "Ppcmd_print_break":
                return " " * pp[1] if len(pp) > 1 and isinstance(pp[1], int) else ""
            case "Ppcmd_force_newline":
                return "\n"
            case "Ppcmd_comment":
                if len(pp) > 1 and isinstance(pp[1], list):
                    return " ".join(pp[1])
                return ""
            case _:
                return str(pp)

    @staticmethod
    def parse_message(mv: list[JSON]):
        return Message(VsCoqOutput.string_of_pp_string(mv[1]))

    @staticmethod
    def parse_hyp(hv):
         # FIXME don't use string processing: parse the structure instead
        full_str = VsCoqOutput.string_of_pp_string(hv)
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
        conclusion = VsCoqOutput.string_of_pp_string(gv["goal"])
        hypotheses = [VsCoqOutput.parse_hyp(hv) for hv in gv["hypotheses"]]
        return Goal(name, conclusion, hypotheses)

    @staticmethod
    def parseproof_view(pv: JSON):
        messages = [VsCoqOutput.parse_message(mv) for mv in pv.get("messages", [])]
        goals = [VsCoqOutput.parse_goal(gv) for gv in (pv.get("proof") or {}).get("goals", [])]
        return messages, goals

class VsCoqFile:
    def __init__(self, driver: "VsCoq", doc: EncodedDocument):
        self.client = must(driver.client)
        self.observer = driver.observer
        self.fpath, self.uri = driver.fpath, driver.uri
        self.doc = doc

    def _compute_ranges(self):
        req = DocumentStateRequest(self.client, self.uri)
        document = must(req.send().result)["document"]
        first_section = document.split("Document using sentences_by_end map")[0]
        PATTERN = re.compile(r"\[\d+\].*?[(](?P<beg>\d+) -> (?P<end>\d+)[)]")
        for m in PATTERN.finditer(first_section):
            yield int(m.group("beg")), int(m.group("end"))

    def process(self) -> Iterable[Positioned]:
        self.client.open(self.uri, self.doc.str)
        VsCoqReadyMonitor(self.client, self.uri).wait()

        blocked_on_error: bool = False
        diagnostics: dict[LSPDiagnostic, None] = {}

        for (beg, end) in self._compute_ranges():
            contents: str = self.doc[beg:end]
            if blocked_on_error:
                yield Positioned(beg, end, Text(contents))
                continue
            pv = StepForwardNotification(self.client, self.fpath, self.uri).send()
            messages, goals = VsCoqOutput.parseproof_view(must(pv.proof_view))
            yield Positioned(beg, end, Sentence(contents, messages, goals))
            diagnostics |= dict.fromkeys(pv.diagnostics)
            blocked_on_error |= pv.blocked_on_error

        # LATER: Adjust line numbers for code blocks embedded in literate documents.
        for diag in diagnostics:
            if diag.severity >= 3:
                continue
            beg, end = self.doc.range2offsets(diag.range)
            context = self._format_error_context(beg, end)
            diag.notify(self.observer, context)

    def _format_error_context(self, beg, end) -> str:
        context = self._highlight_context(beg, end)
        return ("\nThe offending range is delimited by >>>…<<< below:\n" +
                "\n".join(f"  > {line}" for line in context.splitlines()))

    def _highlight_context(self, beg: int, end: int) -> str:
        """Highlight error location with >>> <<< markers."""
        prefix, substring, suffix = self.doc[:beg], self.doc[beg:end], self.doc[end:]
        prefix = "\n".join(prefix.splitlines()[-3:])
        suffix = "\n".join(suffix.splitlines()[:3])
        return f"{prefix}>>>{substring}<<<{suffix}"

class VsCoqClient(LSPClient):
    LANGUAGE_ID = "coq"

class VsCoq(LSPDriver[VsCoqClient]):
    ID = "vscoq"
    BIN = "vscoqtop"
    NAME = "VsCoq"

    VERSION_ARGS = ("--version",)

    CLIENT = VsCoqClient

    def _find_sentences(self, document: EncodedDocument) -> Iterable[Positioned]:
        """Find sentences in the document using VsCoq."""
        vdoc = VsCoqFile(self, document)
        sentences = vdoc.process()
        return sentences

    def partition(self, document: EncodedDocument):
        """Partition document into fragments."""
        return document.intersperse_text_fragments(self._find_sentences(document))

    def annotate(self, chunks: Iterable[str]) -> list[list[Fragment]]:
        """Annotate chunks of Coq code."""
        document = EncodedDocument(chunks, "\n", encoding="utf-8")

        with self as api:
            try:
                fragments = api.partition(document)
                return list(document.recover_chunks(coalesce_text(fragments)))
            except LSPServerException as e:
                api.observer.notify(None, str(e), Position(api.fpath, 0, 1).as_range(), level=3)
                return [[Text(c)] for c in chunks]

def annotate(chunks: Iterable[str], sertop_args=(), fpath="-", binpath=None) -> list[list[Fragment]]:
    """Annotate multiple chunks of Coq code.

    >>> annotate(["Check 1."])
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    return VsCoq(args=sertop_args, fpath=fpath, binpath=binpath).annotate(chunks)
