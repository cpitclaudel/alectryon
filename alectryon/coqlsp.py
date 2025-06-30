from typing import Any, Dict, Iterator, Iterable, List, Tuple, Union

import .core
from .lspFinal import LSPClient, LSPRequest
from .core import REPLDriver, debug, Hypothesis, Goal, \
    Sentence, Text, Fragment, Message, Document, Positioned

class CoqLSPClient(LSPClient):
    CLIENT_NAME = "Alectryon"
    LANGUAGE_ID = "coq"

    @staticmethod 
    def _decode_hyp(hyp):
        return Hypothesis(hyp["names"], hyp["def"], hyp["ty"])

    @staticmethod
    def _decode_hyps(hyps):
        return [CoqLSPClient._decode_hyp(h) for h in hyps]

    @staticmethod
    def _decode_goal(goal):
        return Goal(goal["info"]["name"], goal["ty"], 
            CoqLSPClient._decode_hyps(goal["hyps"]))

    @staticmethod
    def _decode_goals(goals):
        return [CoqLSPClient._decode_goal(g) for g in goals]

    @staticmethod
    def _decode_message(msg):
        """ Messages can be either a string or an object which contains a string. """ 
        if isinstance(msg, str):
            return Message(msg)
        else:
            return Message(msg["text"])

    @staticmethod
    def _decode_messages(msgs):
        return [CoqLSPClient._decode_message(m) for m in msgs]

    def _get_ranges(self):
        """ Segment the document into a list of ranges (beginning/end) for each sentence. """
        request = LSPRequest(
            self.get_next_request_id(),
            "coq/getDocument",
            {"textDocument": {"uri": self.uri, "version": 0}})
        self.send_and_process(request)
        return [(span["range"]["start"], span["range"]["end"]) for span in request.result["spans"]]

    def _get_sentence(self, text, position):
        """ Get the sentence at a given position. 
        The position should be in the range [sentence_start, sentence_end[
        i.e. start included and end excluded. 
        """
        request = LSPRequest(
            self.get_next_request_id(), 
            "proof/goals", 
            {"textDocument": {"uri": self.uri, "version": 0},
             "position": position })
        self.send_and_process(request)
        messages = CoqLSPClient._decode_messages(request.result["messages"])
        if "goals" in request.result:
            goals = CoqLSPClient._decode_goals(request.result["goals"]["goals"])
        else:
            goals = []
        return Sentence(text, messages, goals)

    def process(self, uri: str, document: Document) -> List[Fragment]:
        self.uri = uri
        # Initialize.
        self.initialize()
        self.open_document(self.uri, document.contents)
        # Segment the document.
        ranges = self._get_ranges()
        # Get a sentence for each segment.
        sentences = []
        for (start, end) in ranges:
            # According to Emilio we shouldn't trust the "offset" field of positions
            # returned by coq-lsp.
            start_ofs = document.pos2offset(start["line"] + 1, start["character"])
            end_ofs = document.pos2offset(end["line"] + 1, end["character"])
            text = document.contents[start_ofs : end_ofs]
            s = self._get_sentence(text, start)
            # Coq-lsp adds an empty sentence at the end.
            # We simply remove empty sentences.
            if s.contents:
                sentences.append(Positioned(start_ofs, end_ofs, s))
        # Intersperse the sentences in the original document.
        return document.intersperse_text_fragments(sentences)
 
class CoqLSP(REPLDriver):
    BIN = "coq-lsp"
    NAME = "Coq LSP Server"

    CLI_ARGS = ()
    REPL_ARGS = ()
    VERSION_ARGS = ("--version",)

    ID = "coq_lsp"
    LSP_LANGUAGE_ID = LANGUAGE = "coq"

    def annotate(self, chunks: Iterable[str]) -> List[List[Positioned]]:
        with self as api:
            assert api.repl
            document = Document(chunks, "\n")
            client = CoqLSPClient(api.repl)
            return client.process(self.fpath.absolute().as_uri(), document)
            
#if __name__ == '__main__':
#    with open("test.v", "r") as file:
#        contents = file.read()
#        sentences = CoqLSP(fpath="foo.v").annotate([contents])
#        for s in sentences:
#            print(s)