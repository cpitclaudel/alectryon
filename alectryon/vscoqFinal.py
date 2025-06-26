# vscoq.py - VSCoq Driver using Ultra-Simple LSP Architecture
# Copyright © 2025
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

from enum import Enum
from pathlib import Path
import time
from typing import Dict, Iterable, List, Any, Optional, cast
from subprocess import Popen

from .core import EncodedDocument, Fragment, Position, Positioned, REPLDriver, Sentence, Text
from .lspFinal import LSPClient, LSPRequest, LSPNotification, LSPException, LSPResponse, LSPNotifications, LSPErrorCodes
from .transforms import coalesce_text, extract_goals_and_messages_from_proof_views

# VSCoq-specific LSP methods
class Notifications:
    STEP_FORWARD = "vscoq/stepForward"
    PROOF_VIEW = "vscoq/proofView"
    UPDATE_HIGHLIGHTS = "vscoq/updateHighlights"
    BLOCK_ON_ERROR = "vscoq/blockOnError"

class Requests:
    DOCUMENT_PROOFS = "vscoq/documentProofs"
    ABOUT = "vscoq/about"
    DOCUMENT_STATE = "vscoq/documentState"

################################################################################################################################
#                                         STEPFORWARDQUERY CLASS DEFINITION                                                    #
################################################################################################################################

class StepForwardQuery(LSPNotification):
    def __init__(self, uri: str):
        super().__init__(Notifications.STEP_FORWARD, {
            "textDocument": {"uri": uri, "version": 0}
        })
        self.uri = uri
        self.proof_view = None
        self.current_position = None
        self.error_detected = False
        self.diagnostics = []

    def handle_notification(self, notification: 'LSPNotification') -> None:
        super().handle_notification(notification)
        method = notification.method

        if method == Notifications.UPDATE_HIGHLIGHTS:
            if "processedRange" in notification.params and notification.params["processedRange"]:
                self.current_position = notification.params["processedRange"][-1]

        elif method == Notifications.PROOF_VIEW:
            self.proof_view = {
                "position": self.current_position,
                "proof_view": notification.params
            }

        elif method == Notifications.BLOCK_ON_ERROR:
            self.error_detected = True

        elif method == LSPNotifications.PUBLISH_DIAGNOSTICS:
            if "diagnostics" in notification.params and notification.params["diagnostics"]:
                self.diagnostics.extend(notification.params["diagnostics"])

    @property
    def is_done(self) -> bool:
        return self.proof_view is not None or self.error_detected

################################################################################################################################
#                                        VSCOQFILEPROCESSOR CLASS DEFINITION                                                   #
################################################################################################################################

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

    def process_document_state(self, document_state_data: dict) -> None:
        document_text = document_state_data["document"]
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


################################################################################################################################
#                                            VSCOQCLIENT CLASS DEFINITION                                                      #
################################################################################################################################

class VsCoqClient(LSPClient):
    """VSCoq client using the simplified architecture"""
    def __init__(self, repl: Popen):
        super().__init__(repl)

    CAPABILITIES = {
        "workspace": {
            "configuration": False,
        },
        "textDocument": {
            "semanticTokens": {
                "requests": {"range": False, "full": True},
                "tokenTypes": list(LSPClient.TOKEN_TYPES),
                "tokenModifiers": list(LSPClient.TOKEN_MODIFIERS),
                "formats": ["relative"],
                "overlappingTokenSupport": False,
                "multilineTokenSupport": True,
                "serverCancelSupport": False,
                "augmentsSyntaxTokens": False,
            }
        }
    }

    def step_forward(self, uri: str, context: VsCoqFileProcessor) -> None:
        query = StepForwardQuery(uri)
        result = self.send_and_process(query)
        step_result = cast(StepForwardQuery, result)
        context.process_step_result(step_result)

    def calculate_file_end(self, contents: str) -> Dict[str, int]:
        lines = contents.split("\n")
        return {"line": len(lines) - 1, "character": len(lines[-1])}

    def wait_for_parsing_complete(self, uri: str) -> None:
        delay = self.INITIAL_PARSING_DELAY
        while True:
            try:
                request = LSPRequest(self.get_next_request_id(), Requests.DOCUMENT_PROOFS, {"textDocument": {"uri":uri}})
                self.send_and_process(request)
                break
            except LSPException as e:
                if e.code == LSPErrorCodes.PARSING_NOT_FINISHED:
                    time.sleep(delay)
                    delay *= self.PARSING_DELAY_MULTIPLIER
                else:
                    raise e

    def get_state_info(self, uri: str, context: VsCoqFileProcessor) -> None:
        query = LSPRequest(self.get_next_request_id(), Requests.DOCUMENT_STATE, {"textDocument": {"uri":uri}})
        result = self.send_and_process(query)
        state_result = cast(LSPResponse, result)
        context.process_document_state(state_result.result)

    def process_file(self, uri: str, contents: str) -> Dict[str, Any]:
        modified_contents = contents + "Create HintDb alectryon_end_of_file."

        context = VsCoqFileProcessor()
        context.end_position = self.calculate_file_end(modified_contents)

        try:
            if self.initialize():
                self.send_initialized()
                self.open_document(uri, modified_contents)
                self.wait_for_parsing_complete(uri)

            self.get_state_info(uri, context)

            while context.should_continue_processing():
                self.step_forward(uri, context)

            self.shutdown()
            self.exit()

            result = context.get_results()

            return result
        except LSPException as e:
            raise e

################################################################################################################################
#                                                  VSCOQ CLASS DEFINITION                                                      #
################################################################################################################################

class VsCoq(REPLDriver):
    """Alectryon driver for VsCoq using ultra-simple LSP architecture"""
    BIN = "vscoqtop"
    NAME = "VSCoq"

    CLI_ARGS = ()
    REPL_ARGS = ()
    VERSION_ARGS = ("--version",)

    ID = "vscoq"
    LSP_LANGUAGE_ID = LANGUAGE = "coq"
    LSP_CLIENT_NAME = "Alectryon"

    def __init__(self, args=(), fpath="-", binpath=None):
        super().__init__(args, fpath, binpath)
        self._client = None

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

        if not self._client and self.repl:
            self._client = VsCoqClient(self.repl)

        if self.fpath and str(self.fpath) != "-":
            uri = Path(self.fpath).absolute().as_uri()
        else:
            uri = f"file:///virtual/alectryon_temp.v"

        try:
            result = self._client.process_file(uri, str_contents)
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

        except Exception as e:
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
            except Exception as e:
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
                err += f"\nThe offending chunk is delimited by >>>…<<< below:\n"
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
