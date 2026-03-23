# Copyright © 2025 Mathis Bouverot, Clément Pit-Claudel
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
from typing import Iterable

import dataclasses

from .core import Document, Fragment, Goal, Hypothesis, Message, Position, Positioned, \
    Range, Sentence, must
from .lsp import LSPDocument, LSPClient, LSPClientRequest, LSPDriver, LSPFile
from .coq import CoqIdents

@dataclasses.dataclass
class CoqGetDocumentRequest(LSPClientRequest):
    METHOD = "coq/getDocument"
    uri: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 } }

@dataclasses.dataclass
class ProofGoalsRequest(LSPClientRequest):
    METHOD = "proof/goals"
    uri: str
    pos: Position

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 },
                 "position": self.pos.to_lsp() }

class CoqLSPOutput:
    @staticmethod
    def _decode_hyp(hyp):
        return Hypothesis(hyp["names"], hyp["def"], hyp["ty"])

    @staticmethod
    def _decode_hyps(hyps):
        return [CoqLSPOutput._decode_hyp(h) for h in hyps]

    @staticmethod
    def _decode_goal_name(name):
        if not name:
            return None
        if isinstance(name, list) and name[0] == "Id": # PPX encoding of Id.t
            return name[1]
        return str(name)

    @staticmethod
    def _decode_goal(goal):
        return Goal(CoqLSPOutput._decode_goal_name(goal["info"]["name"]), goal["ty"],
                    CoqLSPOutput._decode_hyps(goal["hyps"]))

    @staticmethod
    def decode_goals(goals):
        return [CoqLSPOutput._decode_goal(g) for g in goals]

    LEVEL_INFO = 4

    @staticmethod
    def _decode_message(msg) -> Message | None:
        # LATER: Attach level to message and filter later using a transform
        return Message(msg["text"]) if msg.get("level", 0) < CoqLSPOutput.LEVEL_INFO else None

    @staticmethod
    def decode_messages(msgs):
        return [dec for m in msgs if (dec := CoqLSPOutput._decode_message(m))]

class CoqLSPClient(LSPClient):
    LANGUAGE_ID = "coq"

class CoqLSPFile(LSPFile[CoqLSPClient]):
    def _get_ranges(self) -> Iterable[Range]:
        """Segment the document into sentence ranges."""
        json = must(CoqGetDocumentRequest(self.client, self.uri).send().result)
        for span in json["spans"]:
            # According to Emilio we shouldn't trust the "offset" field of positions
            # returned by coq-lsp.
            r = Range.of_lsp(self.fpath, span["range"])
            if r.beg != r.end: # Coq-lsp adds an empty sentence at the end.
                yield r

    def _get_sentence(self, rng: Range) -> Positioned[Sentence]:
        info = must(ProofGoalsRequest(self.client, self.uri, rng.beg).send().result)
        messages = CoqLSPOutput.decode_messages(info["messages"])
        goals = CoqLSPOutput.decode_goals(g["goals"]) if (g := info.get("goals")) else []
        beg, end = self.doc.range2offsets(rng)
        return Positioned(beg, end, Sentence(self.doc[beg:end], messages, goals))

    def process(self) -> Iterable[Positioned[Fragment]]:
        return [self._get_sentence(r) for r in self._get_ranges()]

class CoqLSP(LSPDriver[CoqLSPClient]):
    BIN = "coq-lsp"
    NAME = "Coq LSP"
    VERSION_ARGS = ("--version",)

    ID = "coqlsp"
    LANGUAGE = "coq"
    AUTOSELECT = True

    CLIENT = CoqLSPClient

    @staticmethod
    def _normalize_fpath(p: Path) -> Path:
        return CoqIdents.toppath_of_fpath(p)

    def _encode(self, chunks: Iterable[str]) -> Document:
        return LSPDocument(chunks, "\n")

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        return CoqLSPFile(self, document).process()
