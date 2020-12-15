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
from collections import namedtuple, UserString

from .core import TextREPLProver, Hypothesis, Goal, Message, Sentence, Text, debug

class ProtocolError(ValueError):
    pass

ApiMessages = namedtuple("ApiMessages", "messages")

class Document(UserString):
    def __init__(self, doc):
        super().__init__(doc)
        self.bol_offsets = self._find_bols(self)

    @staticmethod
    def _find_bols(doc):
        pos, bols = 0, [0]
        while True:
            pos = doc.find('\n', pos) + 1
            if pos == 0:
                return bols
            bols.append(pos)

    def __getitem__(self, index):
        return super().__getitem__(index).data

    def offset2pos(self, offset):
        zline = bisect.bisect_right(self.bol_offsets, offset)
        bol = self.bol_offsets[zline - 1]
        return zline, offset - bol

    def pos2offset(self, line, col):
        return self.bol_offsets[line - 1] + col

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

    MARKERS_RE = re.compile(r"(?:\b(?:begin|end)\b)|,")

    @classmethod
    def _find_markers(cls, doc):
        for m in cls.MARKERS_RE.finditer(doc.data):
            yield m.group(), m.span()

    # FIXME: handle nested begins
    # FIXME: handle errors?
    def _find_sentence_ranges(self, doc):
        tac_beg = None
        for (marker, (marker_beg, marker_end)) in self._find_markers(doc):
            if tac_beg is not None and marker_beg < tac_beg:
                # print(f"skipping over {doc[marker_beg - 10:marker_end]} as {marker_beg} < {tac_beg}")
                continue # Skip over markers in comments
            line, column = doc.offset2pos(marker_end)

            info, _ = self._query("info", file_name=self.fname, line=line, column=column)
            record = info.get("record", {})
            widget, state = record.get("widget"), record.get("state")

            if widget is not None:
                widget_beg = doc.pos2offset(widget["line"], widget["column"])
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

    HYP_RE = re.compile(r"(?P<names>.*?)\s*:\s*(?P<type>(?:.*|\n )+)(?:,\n|\Z)")
    def _parse_hyps(self, hyps):
        for m in self.HYP_RE.finditer(hyps.strip()):
            names = m.group("names").split()
            typ = m.group("type").replace("\n  ", "\n")
            yield Hypothesis(names, None, typ)

    CCL_SEP_RE = re.compile("(?P<hyps>.*?)^⊢(?P<ccl>.*)", re.DOTALL | re.MULTILINE)
    def _parse_goals(self, state):
        if state == "no goals":
            return
        goals = state.split("\n\n")
        if len(goals) > 1:
            goals[0] = goals[0][goals[0].find('\n'):] # Strip "`n` goals"
        for goal in goals:
            m = self.CCL_SEP_RE.match(goal)
            yield Goal(None, m.group("ccl").replace("\n  ", "\n").strip(),
                   list(self._parse_hyps(m.group("hyps"))))

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
    def _collect_message_spans(messages, doc):
        return sorted((doc.pos2offset(m["pos_line"], m["pos_col"]),
                  doc.pos2offset(m["end_pos_line"], m["end_pos_col"]),
                  m) for m in messages)

    def _add_messages(self, segments, messages, doc):
        segments = list(segments)
        segments.reverse() # Use as a stack
        messages = iter(self._collect_message_spans(messages, doc))

        if not segments:
            return

        beg, end, msg = next(messages, (None, None, None)) # pylint: disable=stop-iteration-return
        fr_beg, fr_end, fr = segments.pop()

        while msg is not None:
            assert fr_beg <= beg <= end
            if beg < fr_end: # Message overlaps current fragment
                end = min(end, fr_end) # Truncate to current fragment
                if isinstance(fr, Text): # Split current fragment if it's text
                    if fr_beg < beg:
                        # print(f"prefix: {(fr_beg, beg, Text(fr.contents[:beg - fr_beg]))=}")
                        yield (fr_beg, beg, Text(fr.contents[:beg - fr_beg]))
                        fr_beg, fr = beg, fr._replace(contents=fr.contents[beg - fr_beg:])
                    if end < fr_end:
                        # print(f"suffix: {(end, fr_end, Text(fr.contents[end - fr_beg:]))=}")
                        segments.append((end, fr_end, Text(fr.contents[end - fr_beg:])))
                        fr_end, fr = end, fr._replace(contents=fr.contents[:end - fr_beg])
                    fr = Sentence(contents=fr.contents, messages=[], goals=[])
                fr.messages.append(Message(msg["text"])) # Don't truncate existing sentences
                beg, end, msg = next(messages, (None, None, None))
            else: # msg starts past fr; move to next fragment
                yield fr_beg, fr_end, fr
                fr_beg, fr_end, fr = segments.pop()
        yield fr_beg, fr_end, fr
        yield from reversed(segments)

    @staticmethod
    def _iter_offsets(strs, padding=0):
        end = 0
        for s in strs:
            beg, end = end, end + len(s) + padding
            yield (beg, end, s)

    CHUNK_PADDING = "\n"

    def _rebuild_chunks(self, inputs, segments):
        if not inputs:
            return []
        chunks = [[]]

        segments = iter(segments)
        inputs = iter(self._iter_offsets(inputs, padding=len(self.CHUNK_PADDING)))

        beg, end, fragment = next(segments)
        in_beg, in_end, _in = next(inputs)

        while fragment is not None:
            assert in_beg <= beg <= end
            # print(f"input: [{in_beg, in_end}[	output: [{beg, end}[	{fragment=}")
            if end <= in_end: # fragment ⊂ input
                # print(f"[{in_beg, in_end}[ ⊃ [{beg, end}[")
                chunks[-1].append(fragment)
                beg, end, fragment = next(segments, (None, None, None))
            else: # fragment goes past end of input
                if beg < in_end: # input and fragment do overlap; truncate fragment
                    # print(f"[{in_beg, in_end}[ ∩ [{beg, end}[")
                    chunks[-1].append(Text(fragment.contents[:in_end - beg]))
                    fragment = fragment._replace(contents=fragment.contents[in_end - beg:])
                    beg = in_end
                chunks.append([])
                in_beg, in_end, _in = next(inputs)

        for chunk in chunks:
            if chunk:
                last = chunk[-1]
                assert last.contents.endswith(self.CHUNK_PADDING)
                chunk[-1] = last._replace(contents=last.contents[:-1])
        return chunks

    def _annotate(self, chunks):
        doc = Document("".join(c + self.CHUNK_PADDING for c in chunks))
        _, messages = self._query("sync", file_name=self.fname, content=doc.data)
        segments = self._add_messages(self._segment(doc), messages, doc)
        return self._rebuild_chunks(chunks, segments)

    @classmethod
    def annotate(cls, chunks, *args, **kwargs):
        with cls(*args, **kwargs) as api:
            return api._annotate(chunks)
