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

import bisect
import json
import re
from collections import namedtuple

from .core import TextREPLProver, Hypothesis, Goal, Message, Sentence, Text, debug

class ProtocolError(ValueError):
    pass

ApiMessages = namedtuple("ApiMessages", "messages")

class Lean3(TextREPLProver):
    REPL_BIN = "lean"
    REPL_NAME = "Lean3"

    # We need --threads=0 because I didn't find a way to join() on all pending queries
    DEFAULT_ARGS = ("--server", "--threads=0")

    def __init__(self, binpath=None, args=()):
        super().__init__(binpath, args)
        self.fname = "-"
        self.seq_num = -1
        self.doc = ""

    def prover_not_found(self):
        raise ValueError("Not found: {}".format(self.binpath))

    def kill(self):
        super().kill()
        self.doc = ""

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
        query = { "seq_num": self.seq_num, "command": command, **kwargs }
        self._write(json.dumps(query, indent=None), "\n")
        return self._wait()

    # FIXME
    # def _last_pos(self, doc):
    #     line = doc.count('\n')
    #     last_nl = doc.rfind('\n')
    #     return (line, len(doc) - last_nl)

    # def _partition(doc, messages):

    @staticmethod
    def _find_bols(doc):
        pos, bols = 0, [0]
        while True:
            pos = doc.find('\n', pos) + 1
            if pos == 0:
                return bols
            bols.append(pos)

    @staticmethod
    def _offset2pos(offset, bol_offsets):
        zline = bisect.bisect_right(bol_offsets, offset)
        bol = bol_offsets[zline - 1]
        return zline, offset - bol

    @staticmethod
    def _pos2offset(line, col, bol_offsets):
        return bol_offsets[line - 1] + col

    MARKERS_RE = re.compile(r"(?:\b(?:begin|end)\b)|,")

    @classmethod
    def _find_markers(cls, doc):
        for m in cls.MARKERS_RE.finditer(doc):
            yield m.group(), m.span()

    # FIXME: handle nested begins
    # FIXME: handle errors?
    def _find_sentence_ranges(self, doc):
        bol_offsets = self._find_bols(doc)
        tac_beg = None
        for (marker, (marker_beg, marker_end)) in self._find_markers(doc):
            if tac_beg is not None and marker_beg < tac_beg:
                # print(f"skipping over {doc[marker_beg - 10:marker_end]} as {marker_beg} < {tac_beg}")
                continue # Skip over markers in comments
            line, column = self._offset2pos(marker_end, bol_offsets)

            info, _ = self._query("info", file_name=self.fname, line=line, column=column)
            record = info.get("record", {})
            widget, state = record.get("widget"), record.get("state")

            if widget is not None:
                widget_beg = self._pos2offset(widget["line"], widget["column"], bol_offsets)
            else:
                assert marker == "end", "Unexpected marker '{}' without widget: {}".format(marker, info)
                widget_beg = None

            # print(f"[→] {marker=}, {marker_beg=}, {tac_beg=}")
            if marker == "begin":
                if tac_beg is not None:
                    continue # FIXME needs a stack of begin/end
                yield (marker_beg, marker_end, state)
            elif marker == ",":
                assert tac_beg is not None
                if widget_beg <= marker_end:
                    continue # Skip over commas within a term
                yield (tac_beg, marker_end, state)
            elif marker == "end":
                pass
            else:
                assert False
            tac_beg = widget_beg

    HYP_RE = re.compile("(?P<names>.*?) : (?P<type>(?:.*|\n )+)\n")
    def _parse_hyps(self, hyps):
        for m in self.HYP_RE.finditer(hyps):
            yield Hypothesis(m.group("names").split(), None, m.group("type").replace("\n  ", "\n"))

    def _parse_goals(self, state):
        if state == "no goals":
            return
        goals = state.split("\n\n")
        if len(goals) > 1:
            goals[0] = goals[0][goals[0].find('\n'):] # Strip "`n` goals"
        for goal in goals:
            print(goal)
            hyps, ccl = goal.split("\n⊢", 1)
            yield Goal(None, ccl.replace("\n  ", "\n").strip(), list(self._parse_hyps(hyps)))

    def _segment(self, doc):
        pos = 0
        for (beg, end, st) in self._find_sentence_ranges(doc):
            if beg > pos:
                yield pos, beg, Text(doc[pos:beg])
            yield beg, end, Sentence(doc[beg:end], [], list(self._parse_goals(st)))
            pos = end
        if pos < len(doc):
            yield pos, len(doc), Text(doc[pos:len(doc)])

    @staticmethod
    def _iter_offsets(strs):
        end = 0
        for s in strs:
            beg, end = end, end + len(s)
            yield (beg, end, s)

    def _rebuild_chunks(self, inputs, fragments):
        if not inputs:
            return []
        chunks = [[]]
        inputs, fragments = iter(self._iter_offsets(inputs)), iter(fragments)
        in_beg, in_end, _in = next(inputs)
        beg, end, fragment = next(fragments)
        while fragment is not None:
            assert in_beg <= beg <= end
            print(f"input: [{in_beg, in_end}[	output: [{beg, end}[	{fragment=}")
            if end <= in_end: # fragment ⊂ input
                print(f"[{in_beg, in_end}[ ⊃ [{beg, end}[")
                chunks[-1].append(fragment)
                beg, end, fragment = next(fragments, (None, None, None))
            else: # fragment goes past end of input
                if beg < in_end: # input and fragment do overlap; truncate fragment
                    print(f"[{in_beg, in_end}[ ∩ [{beg, end}[")
                    chunks[-1].append(Text(fragment.contents[:in_end - beg]))
                    fragment = fragment._replace(contents=fragment.contents[in_end - beg:])
                    beg = in_end
                chunks.append([])
                in_beg, in_end, _in = next(inputs)
        return chunks

    def _annotate(self, chunks):
        doc = "".join(chunks)
        _, messages = self._query("sync", file_name=self.fname, content=doc)
        return self._rebuild_chunks(chunks, list(self._segment(doc)))

    @classmethod
    def annotate(cls, chunks, *args, **kwargs):
        with cls(*args, **kwargs) as api:
            return api._annotate(chunks)
