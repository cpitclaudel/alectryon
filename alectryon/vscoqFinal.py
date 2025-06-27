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

from typing import ClassVar, Dict, Iterable, Any, Optional

import dataclasses
import re

from .core import EncodedDocument, Fragment, Goal, Hypothesis, Message, Position, Positioned, Sentence, Text
from .lspFinal import JSON, LSPClient, LSPClientNotification, LSPClientQuery, LSPClientRequest, LSPDriver, LSPServerException, LSPServerMessage, LSPServerNotification, LSPServerNotifications
from .transforms import coalesce_text

class Notifications(LSPServerNotifications):
    PROOF_VIEW = "vscoq/proofView"
    BLOCK_ON_ERROR = "vscoq/blockOnError"

@dataclasses.dataclass
class StepForwardNotification(LSPClientNotification):
    METHOD = "vscoq/stepForward"
    uri: str

    def __post_init__(self):
        self.proof_view: Optional[JSON] = None
        self.blocked_on_error: bool = False
        self.diagnostics: list[JSON] = []

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
            self.diagnostics.extend(message.params["diagnostics"])

    @property
    def done(self) -> bool:
        return self.proof_view is not None or self.blocked_on_error


@dataclasses.dataclass
class URIRequest(LSPClientRequest):
    uri: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri } }

class DocumentProofsRequest(URIRequest):
    METHOD = "vscoq/documentProofs"

@dataclasses.dataclass
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
    def parse_proof_view(pv: JSON):
        messages = [VsCoqOutput.parse_message(mv) for mv in pv.get("messages", [])]
        goals = [VsCoqOutput.parse_goal(gv) for gv in (pv.get("proof") or {}).get("goals", [])]
        return messages, goals

class VsCoqDocument:
    def __init__(self, client: "VsCoqClient", uri: str, contents: str):
        self.client = client
        self.uri, self.contents = uri, contents
        self.blocked_on_error: bool = False
        self.error_diagnostics: list[Dict[str, Any]] = []

    def _compute_ranges(self):
        document = DocumentStateRequest(self.client, self.uri).send().result["document"]
        first_section = document.split("Document using sentences_by_end map")[0]
        PATTERN = re.compile(r"\[\d+\].*?[(](?P<beg>\d+) -> (?P<end>\d+)[)]")
        for m in PATTERN.finditer(first_section):
            yield int(m.group("beg")), int(m.group("end"))

    def _step_forward(self):
        sf = StepForwardNotification(self.client, self.uri).send()
        self.blocked_on_error |= sf.blocked_on_error
        self.error_diagnostics.extend(d for d in sf.diagnostics if d.get("severity") == 1)
        return sf.proof_view

    def process(self) -> Iterable[Positioned]:
        self.client.open(self.uri, self.contents)
        VsCoqReadyMonitor(self.client, self.uri).wait()

        for (beg, end) in self._compute_ranges():
            if not (pv := self._step_forward()):
                break
            contents = self.contents[beg:end]
            messages, goals = VsCoqOutput.parse_proof_view(pv)
            yield Positioned(beg, end, Sentence(contents, messages, goals))

class VsCoqClient(LSPClient):
    LANGUAGE_ID = "coq"

class VsCoq(LSPDriver[VsCoqClient]):
    ID = "vscoq"
    BIN = "vscoqtop"
    NAME = "VsCoq"

    VERSION_ARGS = ("--version",)

    CLIENT = VsCoqClient

    def _report_errors(self, doc: VsCoqDocument) -> None:
        """Report errors from processing results"""
        if doc.error_diagnostics:
            error = doc.error_diagnostics[0]
            error_range = error["range"]
            line = error_range["start"]["line"] + 1
            char = error_range["start"]["character"] + 1
            error_msg = f"Error at line {line}, column {char}: {error['message']}"
            error_msg = self._format_error(error, doc.contents)
            self.observer.notify(None, error_msg, Position(self.fpath, line, char).as_range(), level=3)

    def _find_sentences(self, document: EncodedDocument):
        """Find sentences in the document using VsCoq."""
        contents = document.contents.decode(document.encoding) # FIXME why decode?
        vdoc = VsCoqDocument(self.client, self.uri, contents)
        sentences = vdoc.process()
        self._report_errors(vdoc)
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

def annotate(chunks: Iterable[str], sertop_args=(), fpath="-", binpath=None) -> list[list[Fragment]]:
    """Annotate multiple chunks of Coq code.

    >>> annotate(["Check 1."])
    [[Sentence(contents='Check 1.', messages=[Message(contents='1\n     : nat')], goals=[])]]
    """
    return VsCoq(args=sertop_args, fpath=fpath, binpath=binpath).annotate(chunks)
