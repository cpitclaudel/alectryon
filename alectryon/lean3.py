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
import subprocess
from collections import deque
from pathlib import Path
from typing import Dict, List, Any, Tuple, Set, Iterable

from .core import TextREPLDriver, Positioned, Document, Hypothesis, Goal, Message, Sentence,\
    Text, cwd, Position, Range

AstNode = Any
AstData = List[Dict[str, AstNode]]

class ProtocolError(ValueError):
    pass

class Lean3(TextREPLDriver):
    BIN = "lean"
    NAME = "Lean3"

    # todo: threading
    REPL_ARGS = ("--server", "--threads=0", "-M 4096", "-T 100000")  # use the same defaults as vscode

    ID = "lean3_repl"
    LANGUAGE = "lean3"

    TACTIC_CONTAINERS = ["begin", "{"]
    TACTIC_NODES = ["tactic", "<|>", ";"]
    DONT_RECURSE_IN = ["by"] + TACTIC_NODES

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

    def _get_children(self, node: AstNode) -> Set[int]:
        if node and "children" in node and node["kind"] not in self.DONT_RECURSE_IN:
            yield from node["children"]
            for idx in node["children"]:
                yield from self._get_children(self.ast[idx])

    KIND_ENDER = {'begin': 'end', '{': '}'}

    def _get_key_locs(self) -> Iterable[Range]:
        """
        Gets the "key locations" in a Lean3 file. Will return their location; if they're a tactic container,
        it splits these between begin and end.
        """
        indices = set(idx for n in self.ast for idx in self._get_children(n))
        for idx in indices:
            node = self.ast[idx]
            if not node:
                continue
            if node["kind"] in self.TACTIC_NODES:
                yield Position(self.fpath, node["start"][0], node["start"][1]),\
                      Position(self.fpath, node["end"][0], node["end"][1])
            elif node["kind"] in self.TACTIC_CONTAINERS:
                yield Position(self.fpath, node["start"][0], node["start"][1]),\
                      Position(self.fpath, node["start"][0], node["start"][1] + len(node["kind"]))

                # the reported end position is where the "d" of the "end" is, for example.
                assert 0 <= node["end"][1] - len(self.KIND_ENDER[node["kind"]])

                yield Position(self.fpath, node["end"][0], node["end"][1] - len(self.KIND_ENDER[node["kind"]])),\
                      Position(self.fpath, node["end"][0], node["end"][1])

    def _get_state_at(self, pos: Position):
        # future improvement: use widget stuff. may be inviable.
        info, _ = self._query("info", line=pos.line, column=pos.col)
        record = info.get("record", {})
        return record.get("state")

    def _find_sentence_ranges(self, doc: Document) -> Tuple[int, int, Any]:
        prev = Position(self.fpath, 0, 0)
        to_yield = None
        for (start, end) in sorted(self._get_key_locs()):
            if end <= prev:
                continue
            prev = end
            if to_yield:
                yield (*to_yield, self._get_state_at(start))
            to_yield = (doc.pos2offset(start), doc.pos2offset(end))
        if to_yield:
            yield (*to_yield, "")

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
        for beg, end, st in self._find_sentence_ranges(doc):
            sentence = Sentence(doc[beg:end], [], list(self._parse_goals(st)))
            yield Positioned(beg, end, sentence)

    def partition(self, doc: Document):
        return Document.intersperse_text_fragments(doc.contents, self._find_sentences(doc))

    @staticmethod
    def _collect_message_span(msg, doc):
        return (doc.pos2offset(Position(self.fpath, msg["pos_line"], msg["pos_col"])),
                doc.pos2offset(Position(self.fpath, msg["end_pos_line"], msg["end_pos_col"])),
                msg)

    @staticmethod
    def _collect_message_spans(messages, doc):
        # FIXME this drops some errors (try ``#compute 1``) (not a real command, but there's no "end of error")
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
            if beg < fr_end:  # Message overlaps current fragment
                end = min(end, fr_end)  # Truncate to current fragment
                if isinstance(fr, Text):  # Split current fragment if it's text
                    if fr_beg < beg:
                        # print(f"prefix: {(fr_beg, beg, Text(fr.contents[:beg - fr_beg]))=}")
                        yield Text(fr.contents[:beg - fr_beg])
                        fr_beg, fr = beg, fr._replace(contents=fr.contents[beg - fr_beg:])
                    if end < fr_end:
                        before, after = fr.contents[:end - fr_beg], fr.contents[end - fr_beg:]
                        segments.appendleft(Positioned(end, fr_end, Text(after)))
                        fr_end, fr = end, fr._replace(contents=before)
                    fr = Sentence(contents=fr.contents, messages=[], goals=[])
                fr.messages.append(Message(msg["text"]))  # Don't truncate existing sentences
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
            # todo: error checking around AST loading, and if AST is empty at runtime
            # We use this instead of the `NamedTemporaryFile` API because it works with Windows file locking
            (fdescriptor, tmpname) = tempfile.mkstemp(suffix=".lean")
            tmpname = Path(tmpname).resolve()
            try:
                with open(fdescriptor, "w") as tmp:
                    tmp.write(document.contents)
                # FIXME: Use CLI_ARGS + self.run_cli
                args = ["lean", "--make", "--ast", *(x for x in self.REPL_ARGS + self.user_args if x != "--server"), str(tmpname)]
                subprocess.check_call(args)
                self.ast = json.loads(tmpname.with_suffix(".ast.json").read_text("utf8"))["ast"]
            finally:
                tmpname.unlink(missing_ok=True)
                tmpname.with_suffix(".ast.json").unlink(missing_ok=True)
                tmpname.with_suffix(".olean").unlink(missing_ok=True)
        with self as api:
            return api._annotate(document)
