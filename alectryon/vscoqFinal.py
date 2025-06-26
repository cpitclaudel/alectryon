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

import dataclasses
from typing import Callable, ClassVar, Dict, Generic, Iterable, List, Any, Optional, TypeVar

from alectryon.lsp import LSPException, LSPResponse

from .core import EncodedDocument, Fragment, Position, Positioned, Sentence, Text
from .lspFinal import JSON, LSPClient, LSPClientNotification, LSPClientRequest, LSPDriver, LSPServerException, LSPServerMessage, LSPServerNotification, LSPServerNotifications, LSPServerRequest
from .transforms import coalesce_text, extract_goals_and_messages_from_proof_views

class Notifications(LSPServerNotifications):
    PROOF_VIEW = "vscoq/proofView"
    UPDATE_HIGHLIGHTS = "vscoq/updateHighlights"
    BLOCK_ON_ERROR = "vscoq/blockOnError"

class StepForwardQuery(LSPClientNotification):
    METHOD = "vscoq/stepForward"

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 } }

    def __init__(self, client: LSPClient, uri: str):
        super().__init__(client)
        self.uri = uri
        self.proof_view = None
        self.current_position = None
        self.error_detected = False
        self.diagnostics = []

    def process_message(self, message: LSPServerMessage) -> None:
        super().process_message(message)
        if not isinstance(message, LSPServerNotification):
            return
        if message.method == Notifications.UPDATE_HIGHLIGHTS:
            if pr := message.params["processedRange"]:
                self.current_position = pr[-1]
        elif message.method == Notifications.PROOF_VIEW:
            self.proof_view = { # FIXME: class
                "position": self.current_position,
                "proof_view": message.params
            }
        elif message.method == Notifications.BLOCK_ON_ERROR:
            self.error_detected = True
        elif message.method == Notifications.PUBLISH_DIAGNOSTICS:
            self.diagnostics.extend(message.params["diagnostics"])

    @property
    def done(self) -> bool:
        return bool(self.current_position and self.proof_view) or self.error_detected

class VsCoqFileProcessor:
    """Handles state and processing logic of a single VsCoq file"""
    proof_views: List[Dict[str, Any]] = []
    error_diagnostics: List[Dict[str, Any]] = []
    current_position: Optional[Dict[str, Any]] = None
    end_position: Dict[str, int]
    end_of_file_reached: bool = False
    error_detected: bool = False
    sentence_ranges: List[Dict[str, Any]] = []

    def is_end_of_file(self) -> bool:
        if not self.current_position or not self.end_position:
            return False

        return (self.current_position["end"]["line"] == self.end_position["line"] and
                self.current_position["end"]["character"] == self.end_position["character"])

    def update_position(self, position: Dict[str, int]) -> None:
        self.current_position = position
        if self.is_end_of_file():
            self.end_of_file_reached = True

    def add_proof_view(self, proof_view: Dict[str, Any]) -> None:
        if not self.end_of_file_reached:
            self.proof_views.append(proof_view)

    def add_diagnostics(self, diagnostics: List[Dict[str, Any]]) -> None:
        for diag in diagnostics:
            if diag.get("severity", 0) == 1:
                self.error_diagnostics.append(diag)

    def should_continue_processing(self) -> bool:
        return not self.end_of_file_reached and not self.error_detected

    def process_step_result(self, step_result: StepForwardQuery) -> None:
        if step_result.current_position:
            self.update_position(step_result.current_position)

        if step_result.diagnostics:
            self.add_diagnostics(step_result.diagnostics)

        if step_result.proof_view:
            self.add_proof_view(step_result.proof_view)
            if step_result.current_position:
                self.update_position(step_result.current_position)

        if step_result.error_detected:
            self.error_detected = True

    def process_document_state(self, ds: "DocumentStateRequest") -> None:
        assert ds.result
        document_text = ds.result["document"]
        self.sentence_ranges = self.parse_document_state(document_text)

    def parse_document_state(self, document_state: str) -> List[dict]:
        import re

        sentences = []

        first_section = document_state.split("Document using sentences_by_end map")[0]

        pattern = r'\[(\d+)\].*?\((\d+) -> (\d+)\)'

        for match in re.finditer(pattern, first_section):
            sentence_id = int(match.group(1))
            start_offset = int(match.group(2))
            end_offset = int(match.group(3))

            sentences.append({
                "id": sentence_id,
                "start": start_offset,
                "end": end_offset,
                "match_text": match.group(0)
            })

        # Remove the last sentence (alectryon_end_of_file)
        if sentences:
            last_sentence = sentences[-1]
            if("alectryon_end_of_file" in last_sentence["match_text"]):
                sentences.pop()

        return sentences

    def get_results(self) -> Dict[str, Any]:
        return {
            "proof_views": self.proof_views,
            "errors": self.error_diagnostics,
            "sentence_ranges": self.sentence_ranges
        }

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

class VsCoqClient(LSPClient):
    LANGUAGE_ID = "coq"

    def step_forward(self, uri: str, context: VsCoqFileProcessor) -> None:
        context.process_step_result(StepForwardQuery(self, uri).send())

    def calculate_file_end(self, contents: str) -> Dict[str, int]:
        lines = contents.split("\n")
        return {"line": len(lines) - 1, "character": len(lines[-1])}

    def get_state_info(self, uri: str, context: VsCoqFileProcessor) -> None:
        context.process_document_state(DocumentStateRequest(self, uri).send())

    def process_file(self, uri: str, contents: str) -> Dict[str, Any]:
        modified_contents = contents + "Create HintDb alectryon_end_of_file."

        context = VsCoqFileProcessor()
        context.end_position = self.calculate_file_end(modified_contents)

        self.open(uri, modified_contents)
        VsCoqReadyMonitor(self, uri).wait()

        self.get_state_info(uri, context)

        while context.should_continue_processing():
            self.step_forward(uri, context)

        result = context.get_results()

        return result

class VsCoq(LSPDriver[VsCoqClient]):
    ID = "vscoq"
    BIN = "vscoqtop"
    NAME = "VSCoq"

    VERSION_ARGS = ("--version",)

    CLIENT = VsCoqClient

    def _report_errors(self, result, contents) -> None:
        """Report errors from processing results"""
        if result["errors"]:
            error = result["errors"][0]
            error_range = error["range"]
            line = error_range["start"]["line"] + 1
            char = error_range["start"]["character"] + 1
            error_msg = f"Error at line {line}, column {char}: {error['message']}"
            error_msg = self._format_error(error, contents)
            self.observer.notify(None, error_msg, Position(self.fpath, line, char).as_range(), level=3)

    def _find_sentences(self, document: EncodedDocument):
        """Find sentences in the document using VSCoq"""
        str_contents = document.contents.decode(document.encoding)
        assert self.client
        try:
            result = self.client.process_file(self.uri, str_contents)
            self._report_errors(result, str_contents)

            sentence_ranges = result.get('sentence_ranges', [])
            proof_view_data = extract_goals_and_messages_from_proof_views(result.get('proof_views', []))

            min_length = min(len(sentence_ranges), len(proof_view_data))

            for i in range(min_length):
                sentence_range = sentence_ranges[i]
                start_offset = sentence_range["start"]
                end_offset = sentence_range["end"]

                content = document.contents[start_offset:end_offset].decode(document.encoding)

                pv_data = proof_view_data[i]
                sentence = Sentence(contents=content.strip(), goals=pv_data['goals'], messages=pv_data['messages'])

                yield Positioned(start_offset, end_offset, sentence)

        except LSPServerException as e:
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1).as_range(), level=3)

    def partition(self, document: EncodedDocument):
        """Partition document into fragments"""
        return document.intersperse_text_fragments(self._find_sentences(document))

    def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
        """Annotate chunks of Coq code"""
        document = EncodedDocument(chunks, "\n", encoding="utf-8")

        with self as api:
            try:
                fragments = api.partition(document)
                return list(document.recover_chunks(coalesce_text(fragments)))
            except LSPServerException as e:
                api.observer.notify(None, str(e), Position(api.fpath, 0, 1).as_range(), level=3)
                return [[Text(c)] for c in chunks]

    def _format_error(self, diagnostic: Dict, contents: str) -> str:
        """Format error message like SerAPI with context highlighting"""
        message = diagnostic.get("message", "Unknown error")

        QUOTE = '  > '
        ERR_FMT = "Coq raised an exception:\n{}"
        err = ERR_FMT.format(self.indent(message, QUOTE))

        if "range" in diagnostic:
            range_info = diagnostic["range"]
            start = range_info["start"]
            end = range_info["end"]

            try:
                highlighted = self.highlight_substring(
                    contents,
                    start["line"], start["character"],
                    end["line"], end["character"]
                )
                err += "\nThe offending chunk is delimited by >>>…<<< below:\n"
                err += "\n".join(f"{QUOTE}{line}" for line in highlighted.splitlines())
            except (IndexError, KeyError):
                err += f"\nError at line {start['line'] + 1}, column {start['character'] + 1}"

        err += "\nResults past this point may be unreliable."
        return err

    @staticmethod
    def highlight_substring(contents: str, start_line: int, start_char: int, end_line: int, end_char: int) -> str:
        """Highlight error location with >>> <<< markers like SerAPI"""
        lines = contents.splitlines()

        context_start = max(0, start_line - 3)
        context_end = min(len(lines), end_line + 4)

        context_lines = []
        for i in range(context_start, context_end):
            if i < len(lines):
                line = lines[i]
                if i == start_line and start_line == end_line:
                    highlighted = line[:start_char] + ">>>" + line[start_char:end_char] + "<<<" + line[end_char:]
                    context_lines.append(highlighted)
                elif start_line <= i <= end_line:
                    context_lines.append(f">>>{line}<<<")
                else:
                    context_lines.append(line)

        return "\n".join(context_lines)

    @staticmethod
    def indent(text: str, prefix: str) -> str:
        """Indent each line of text with prefix"""
        return "\n".join(prefix + line for line in text.splitlines())

def annotate(chunks: Iterable[str], sertop_args=(), fpath="-", binpath=None) -> List[List[Fragment]]:
    """Annotate multiple chunks of Coq code.

    >>> annotate(["Check 1."])
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    return VsCoq(args=sertop_args, fpath=fpath, binpath=binpath).annotate(chunks)
