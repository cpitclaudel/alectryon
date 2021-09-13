# Copyright © 2019 Clément Pit-Claudel
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

import json
import re
import tempfile
from collections import deque
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Tuple

from .core import TextREPLDriver, Positioned, Document, Hypothesis, Goal, Message, Sentence,\
    Text, cwd, Position

AstNode = Any
AstData = List[Dict[str, AstNode]]
Pos = Tuple[int, int]

class ProtocolError(ValueError):
    pass

class Lean3(TextREPLDriver):
    BIN = "lean"
    NAME = "Lean3"

    # TODO: Threading
    REPL_ARGS = ("--server", "--threads=0", "-M 4096", "-T 100000") # Same defaults as vscode
    CLI_ARGS = ("--ast", "-M 4096", "-T 100000")

    ID = "lean3_repl"
    LANGUAGE = "lean3"

    TACTIC_CONTAINERS = ["begin", "{", "by"]
    TACTIC_NODES = ["tactic", "<|>", ";"]
    DONT_RECURSE_IN = TACTIC_NODES

    def __init__(self, args=(), fpath="-", binpath=None):
        super().__init__(args=args, fpath=fpath, binpath=binpath)
        self.ast: AstData = []
        self.seq_num = -1

    def _wait(self):
        messages = []
        while True:
            js = json.loads(self._read())
            kind = js["response"]
            if kind in ("ok", "error"):
                assert js["seq_num"] == self.seq_num
            if kind == "ok":
                return js, messages
            if kind == "error":
                raise ProtocolError(js["message"])
            if kind == "current_tasks":
                pass
            elif kind == "all_messages":
                messages = js["msgs"]
            else:
                raise ProtocolError("Unexpected response {!r}".format(js))

    def _query(self, command, **kwargs):
        self.seq_num += 1
        query = {"seq_num": self.seq_num, "command": command,
                 "file_name": self.fpath.name, **kwargs}
        self._write(json.dumps(query, indent=None), "\n")
        return self._wait()

    def _get_descendants(self, idx: int, parent: int) -> Iterable[Tuple[int, int]]:
        node = self.ast[idx]
        if node:
            yield idx, parent
            if node["kind"] in self.TACTIC_CONTAINERS:
                parent = idx
            if node["kind"] not in self.DONT_RECURSE_IN:
                for cidx in node.get("children", ()):
                    yield from self._get_descendants(cidx, parent)

    KIND_ENDER = {"begin": "end", "{": "}", "by": ""}

    def _find_root(self):
        for idx, n in enumerate(self.ast):
            if n and n["kind"] == "file":
                return idx
        return None

    def _find_sentence_ranges(self) -> Iterable[Tuple[Pos, Pos, int]]:
        """Get the ranges covering individual sentences of a Lean3 file.

        Each value in the resulting stream is a 4-element: the start and end of
        the sentence, the index of its node, and the index of its parent.
        """
        for idx, parent in set(self._get_descendants(self._find_root(), 0)):
            node = self.ast[idx]
            if not node or "start" not in node or "end" not in node:
                continue
            kind = node["kind"]
            start, end = tuple(node["start"]), tuple(node["end"])
            if kind in self.TACTIC_NODES:
                yield start, end, idx, parent
            elif kind in self.TACTIC_CONTAINERS:
                # Yield a span corresponding to the opening delimiter
                yield start, (start[0], start[1] + len(kind)), idx, parent

    def _get_state_at(self, pos: Pos):
        # LATER: Render using Lean widgets
        info, _ = self._query("info", line=pos[0], column=pos[1])
        record = info.get("record", {})
        return record.get("state")

    DEBUG = False

    def _collect_sentences_and_states(self, doc: Document) -> Iterable[Tuple[Pos, Any]]:
        last_end: Pos = (0, 0)
        last_idx: Optional[int] = None
        last_parent: Optional[int] = None
        last_span: Optional[Pos] = None

        if self.DEBUG:
            print("=" * 72)
            for idx, node in enumerate(self.ast):
                print(idx, node)
                if node and "start" in node and "end" in node:
                    print(doc[doc.pos2offset(*node["start"]):
                              doc.pos2offset(*node["end"])])
                print()

        for start, end, idx, parent in sorted(self._find_sentence_ranges()):
            if end <= last_end: # Skip overlapping ranges
                print("Skip")
                continue
            if last_span:
                last_state = self._get_state_at(start) if parent in (last_idx, last_parent) else None
                yield (last_span, last_state)
            last_span = (doc.pos2offset(*start), doc.pos2offset(*end)) if start != end else None
            last_end, last_idx, last_parent = end, idx, parent
        if last_span:
            yield (last_span, None)

    # FIXME: this does not handle hypotheses with a body
    HYP_RE = re.compile(r"(?P<names>.*?)\s*:\s*(?P<type>(?:.*|\n )+)(?:,\n|\Z)")

    def _parse_hyps(self, hyps):
        for m in self.HYP_RE.finditer(hyps.strip()):
            names = m.group("names").split()
            typ = m.group("type").replace("\n  ", "\n")
            yield Hypothesis(names, None, typ)

    CCL_SEP_RE = re.compile("(?P<hyps>.*?)^⊢(?P<ccl>.*)", re.DOTALL | re.MULTILINE)

    def _parse_goals(self, state):
        if not state or state == "no goals":
            return
        goals = state.split("\n\n")
        if len(goals) > 1:
            goals[0] = goals[0][goals[0].find('\n'):]  # Strip "`n` goals"
        for goal in goals:
            m = self.CCL_SEP_RE.match(goal)  # note : this does not deal with, e.g. `conv` goals
            yield Goal(None, m.group("ccl").replace("\n  ", "\n").strip(),
                       list(self._parse_hyps(m.group("hyps"))))

    def _find_sentences(self, doc: Document):
        for (beg, end), st in self._collect_sentences_and_states(doc):
            sentence = Sentence(doc[beg:end], [], list(self._parse_goals(st)))
            yield Positioned(beg, end, sentence)

    def partition(self, doc: Document):
        return Document.intersperse_text_fragments(doc.contents, self._find_sentences(doc))

    @staticmethod
    def _collect_message_span(msg, doc):
        return (doc.pos2offset(msg["pos_line"], msg["pos_col"]),
                doc.pos2offset(msg["end_pos_line"], msg["end_pos_col"]),
                msg)

    @staticmethod
    def _collect_message_spans(messages, doc):
        # FIXME this drops some errors (try ````#xyz 1````) (no end_pos)
        return sorted(Lean3._collect_message_span(m, doc) for m in messages
                      if "end_pos_line" in m and "end_pos_col" in m)

    def _add_messages(self, segments, messages, doc):
        segments = deque(Document.with_boundaries(segments))
        messages = deque(self._collect_message_spans(messages, doc))

        if not segments:
            return

        fr_beg, fr_end, fr = segments.popleft()

        while messages:
            beg, end, msg = messages[0]
            assert fr_beg <= beg <= end
            if beg < fr_end: # Message overlaps current fragment
                end = min(end, fr_end) # Truncate to current fragment
                if isinstance(fr, Text): # Split current fragment if it's text
                    if fr_beg < beg:
                        # print(f"prefix: {(fr_beg, beg, Text(fr.contents[:beg - fr_beg]))=}")
                        yield Text(fr.contents[:beg - fr_beg])
                        fr_beg, fr = beg, fr._replace(contents=fr.contents[beg - fr_beg:])
                    if end < fr_end:
                        # print(f"suffix: {(end, fr_end, Text(fr.contents[end - fr_beg:]))=}")
                        segments.appendleft(Positioned(end, fr_end, Text(fr.contents[end-fr_beg:])))
                        fr_end, fr = end, fr._replace(contents=fr.contents[:end - fr_beg])
                    fr = Sentence(contents=fr.contents, messages=[], goals=[])
                fr.messages.append(Message(msg["text"])) # Don't truncate existing sentences
                messages.popleft()
            else: # msg starts past fr; move to next fragment
                yield fr
                fr_beg, fr_end, fr = segments.popleft()

        yield fr
        for _, _, fr in segments:
            yield fr

    def _annotate(self, document: Document):
        _, messages = self._query("sync", content=document.contents)
        fragments = self._add_messages(self.partition(document), messages, document)
        return list(document.recover_chunks(fragments))

    def annotate(self, chunks):
        """Annotate multiple ``chunks`` of Lean 3 code.

        >>> lean3 = Lean3()
        >>> lean3.annotate(["#eval 1 + 1", "#check nat"])
        [[Sentence(contents='#eval 1 + 1',
                   messages=[Message(contents='2')], goals=[])],
         [Sentence(contents='#check nat',
                   messages=[Message(contents='ℕ : Type')], goals=[])]]
        """
        document = Document(chunks, "\n")
        with cwd(self.fpath.parent.resolve()):
            # We use this instead of the ``NamedTemporaryFile`` API
            # because it works with Windows file locking.
            (fdescriptor, tmpname) = tempfile.mkstemp(suffix=".lean")
            try:
                tmpname = Path(tmpname).resolve()
                with open(fdescriptor, "w", encoding="utf-8") as tmp:
                    tmp.write(document.contents)
                self.run_cli([str(tmpname)])
                self.ast = json.loads(tmpname.with_suffix(".ast.json").read_text("utf8"))["ast"]
            finally:
                tmpname.unlink(missing_ok=True)
                tmpname.with_suffix(".ast.json").unlink(missing_ok=True)
        with self as api:
            return api._annotate(document)
