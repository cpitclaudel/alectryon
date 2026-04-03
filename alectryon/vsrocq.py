# Copyright © 2025 Flavien Jaquerod, Clément Pit-Claudel
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

from __future__ import annotations

from pathlib import Path
from typing import Any, ClassVar, Iterable, Optional, Union

import dataclasses
import re

from .core import Document, DriverInfo, JSON, Range, TextDocument, Fragment, \
    Goal, Hypothesis, Message, Positioned, Sentence, must
from .lsp import LSPClient, LSPClientInitializeRequest, LSPClientNotification, \
    LSPClientRequest, LSPDiagnostic, LSPDriver, LSPFile, LSPServerException, \
    LSPServerNotification, LSPServerNotifications
from .coq import CoqIdents

class Notifications(LSPServerNotifications):
    PROOF_VIEW = "prover/proofView"
    BLOCK_ON_ERROR = "prover/blockOnError"
    DEBUG_MESSAGE = "prover/debugMessage"

@dataclasses.dataclass
class StepForwardNotification(LSPClientNotification):
    METHOD = "prover/stepForward"
    fpath: Path
    uri: str

    def __post_init__(self):
        self.debug_messages: list[list[Any]] = []
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
            # FIXME: Should be included by the server as a regular message
            self.proof_view.setdefault("pp_messages", []).extend(self.debug_messages)
        elif message.method == Notifications.DEBUG_MESSAGE:
            self.debug_messages.append([5, message.params["message"]])
        elif message.method == Notifications.BLOCK_ON_ERROR:
            self.blocked_on_error = True
        elif message.method == Notifications.PUBLISH_DIAGNOSTICS:
            uri = message.params["uri"]
            fpath = str(self.fpath) if uri == self.uri else uri
            self.diagnostics.extend(LSPDiagnostic.of_json(fpath, d)
                                    for d in message.params["diagnostics"])

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
    max_delay = 30

    def ready(self) -> bool:
        raise NotImplementedError

    def wait(self):
        import time
        while not self.ready():
            time.sleep(self.delay)
            self.delay = min(self.delay * self.delay_multiplier, self.max_delay)

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
            raise
        return True

PP = Union[str, list["PP"]]

# https://github.com/rocq-prover/vsrocq/issues/1201
MESSAGE_FILTER = re.compile(
    r"is ((co)?recursively )?(declared|defined)|" +
    r"Interactive Module (Type )?[^ ]+ started|" +
    r"not a (coercion|keyword)|" +
    r"will only be used by eauto"
)

class VsRocqOutput:
    @staticmethod
    def parse_message(mv: list[Any]) -> Message | None:
         # LATER: Include message level in message and do filtering by level, as
         # a transform.  Needs a fix for rocq-prover/vsrocq#1201.
        _level, pp = mv
        return Message(pp) if not MESSAGE_FILTER.search(pp) else None

    @staticmethod
    def parse_hyp(hv):
        return Hypothesis(names=hv["ids"], body=hv["body"], type=hv["_type"])

    @staticmethod
    def parse_goal(gv: JSON):
        return Goal(gv.get("name"), gv["goal"],
                    [VsRocqOutput.parse_hyp(hv) for hv in gv["hypotheses"]])

    @staticmethod
    def parse_proof_view(pv: JSON):
        pp_proof = pv["pp_proof"]
        messages = [m for mv in pv["pp_messages"] if (m := VsRocqOutput.parse_message(mv))]
        goals = [VsRocqOutput.parse_goal(gv) for gv in pp_proof["goals"]] if pp_proof else []
        return messages, goals

class VsRocqClient(LSPClient):
    LANGUAGE_ID = "coq"

    # The server freezes on missing settings, so start with default options…
    INITIALIZATION_OPTIONS: JSON = {
        # "path": "",
        # "args": [],
        "memory": {"limit": 4},
        "goals": {
            "auto": "true",
            # "display": "List",
            "ppmode": "Pp",
            "messages": {"full": True},
            # "maxDepth": 17,
        },
        "proof": {
            "mode": 0,
            "pointInterpretationMode": 0,
            # "cursor": {"sticky": True},
            "delegation": "None",
            "workers": 1,
            "block": True,
            # "display-buttons": True,
        },
        "completion": {"enable": False, "unificationLimit": 100, "algorithm": 1},
        "diagnostics": {"full": False},
    }
    # … and add our own config:
    INITIALIZATION_OPTIONS["goals"]["ppmode"] = "String" # Don't return Pp boxes
    INITIALIZATION_OPTIONS["goals"]["messages"]["full"] = True # Include errors and warnings with proof views
    INITIALIZATION_OPTIONS["proof"]["mode"] = 0 # Step manually
    INITIALIZATION_OPTIONS["proof"]["block"] = False # Continue past the first error
    INITIALIZATION_OPTIONS["completion"]["enable"] = False
    INITIALIZATION_OPTIONS["diagnostics"]["full"] = False # Skip info diagnostics

    def _init(self) -> LSPClientInitializeRequest:
        req = super()._init()
        req.params["initializationOptions"] = self.INITIALIZATION_OPTIONS
        return req

class VsRocqFile(LSPFile[VsRocqClient]):
    def _compute_ranges(self):
        """Compute the utf-8 start and end positions of each sentence.

        Since all other offsets in VSRocq are in codepoints, we use this method
        only to count sentences, and we discard the sentence boundaries.
        """
        req = DocumentStateRequest(self.client, self.uri)
        document: str = must(req.send().result)["document"]
        sep = document.find("Document using sentences_by_end map")
        assert sep >= 0, "Unexpected VsRocq documentState format"
        PATTERN = re.compile(r"\[\d+\].*?[(](?P<beg>\d+) -> (?P<end>\d+)[)]")
        for m in PATTERN.finditer(document[:sep].replace("\n", " ")):
            yield int(m.group("beg")), int(m.group("end"))

    def process(self) -> Iterable[Positioned[Fragment]]:
        VsRocqReadyMonitor(self.client, self.uri).wait()

        diagnostics: set[LSPDiagnostic] = set()

        for _ in self._compute_ranges(): # Counting ranges is valuable, but the offsets are unusable
            pv = StepForwardNotification(self.client, self.fpath, self.uri).send()
            messages, goals = VsRocqOutput.parse_proof_view(must(pv.proof_view))
            beg, end = self.doc.range2offsets(Range.of_lsp(self.fpath, must(pv.proof_view)["range"]))
            sentence = Sentence(self.doc[beg:end], messages, goals)
            yield Positioned(beg, end, sentence)

            # Print severe diagnostics eagerly
            for diag in pv.diagnostics:
                # LATER: Adjust line numbers for code blocks embedded in literate documents.
                if diag not in diagnostics:
                    diagnostics.add(diag)
                    if diag.severity < 3:
                        diag.notify(self.doc, self.client)

            if pv.blocked_on_error:
                break

class VsRocq(LSPDriver[VsRocqClient]):
    BIN = "vsrocqtop"
    NAME = "VsRocq"
    VERSION_ARGS = ("-print-version",)

    ID = "vsrocq"
    LANGUAGE = "coq"
    AUTOSELECT = True

    CLIENT = VsRocqClient

    def version_info(self) -> DriverInfo:
        lsp, cli  = super().version_info(), super(LSPDriver, self).version_info()
        return lsp._replace(version=f"{cli.version} / {lsp.version}")

    @classmethod
    def _normalize_fpath(cls, p: Path) -> Path:
        return CoqIdents.toppath_of_fpath(p)

    def _encode(self, chunks: Iterable[str]) -> Document:
        # VsRocq sends prover/documentState info using utf-8 offsets, but uses
        # codepoints in diagnostic line/char pairs.
        # https://github.com/rocq-prover/vsrocq/issues/1199
        return TextDocument(chunks, "\n")

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        """Find sentences in the document using VsRocq."""
        return VsRocqFile(self, document).process()


def annotate(chunks: list[str], vsrocq_args=(), fpath="-", binpath=None) \
    -> list[list[Fragment]]:
    r"""Annotate multiple `chunks` of Rocq code.

    >>> annotate(["Check 1."])
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    return VsRocq(args=vsrocq_args, fpath=fpath, binpath=binpath).annotate(chunks)
