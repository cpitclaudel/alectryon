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

from typing import Iterable

import dataclasses

from .core import Document, Fragment, Goal, Hypothesis, Message, Position, Positioned, Sentence, must
from .lsp import LSPDocument, LSPClient, LSPClientRequest, LSPDriver

class Requests:
    GOALS = "proof/goals"

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
    def _decode_goal(goal):
        return Goal(goal["info"]["name"], goal["ty"],
                    CoqLSPOutput._decode_hyps(goal["hyps"]))

    @staticmethod
    def decode_goals(goals):
        return [CoqLSPOutput._decode_goal(g) for g in goals]

    @staticmethod
    def _decode_message(msg):
        # Messages can be either a string or an object which contains a string.
        return Message(msg if isinstance(msg, str) else msg["text"])

    @staticmethod
    def decode_messages(msgs):
        return [CoqLSPOutput._decode_message(m) for m in msgs]

class CoqLSPFile:
    def __init__(self, driver: "CoqLSP", doc: Document):
        self.client = must(driver.client)
        self.observer = driver.observer
        self.fpath, self.uri = driver.fpath, driver.uri
        self.doc = doc

    def _get_ranges(self):
        """Segment the document into a list of ranges (beginning/end) for each sentence."""
        json = must(CoqGetDocumentRequest(self.client, self.uri).send().result)
        return [(span["range"]["start"], span["range"]["end"]) for span in json["spans"]]

    def _get_sentence(self, js_beg, js_end) -> Positioned[Sentence]:
        # According to Emilio we shouldn't trust the "offset" field of positions
        # returned by coq-lsp.
        beg, end = Position.of_lsp(self.fpath, js_beg), Position.of_lsp(self.fpath, js_end)
        beg_ofs, end_ofs = self.doc.pos2offset(beg), self.doc.pos2offset(end)
        info = must(ProofGoalsRequest(self.client, self.uri, beg).send().result)
        messages = CoqLSPOutput.decode_messages(info["messages"])
        goals = CoqLSPOutput.decode_goals(g["goals"]) if (g := info.get("goals")) else []
        return Positioned(beg_ofs, end_ofs, Sentence(self.doc[beg_ofs:end_ofs], messages, goals))

    def _get_sentences(self) -> Iterable[Positioned[Sentence]]:
        for (beg, end) in self._get_ranges():
            sentence = self._get_sentence(beg, end)
            if sentence.e.contents: # Coq-lsp adds an empty sentence at the end.
                yield sentence

    def process(self) -> Iterable[Positioned[Fragment]]:
        self.client.open(self.uri, self.doc.str)
        return self._get_sentences()

class CoqLSPClient(LSPClient):
    LANGUAGE_ID = "coq"

class CoqLSP(LSPDriver[CoqLSPClient]):
    ID = "coq-lsp"
    BIN = "coq-lsp"
    NAME = "Coq LSP"

    VERSION_ARGS = ("--version",)

    CLIENT = CoqLSPClient

    def _encode(self, chunks: Iterable[str]) -> Document:
        return LSPDocument(chunks, "\n")

    def _find_sentences(self, document: Document) -> Iterable[Positioned[Fragment]]:
        return CoqLSPFile(self, document).process()
