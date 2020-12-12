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
from collections import deque

from .core import TextREPLDriver, Positioned, Document, \
    Hypothesis, Goal, Message, Sentence, Text, debug

class ProtocolError(ValueError):
    pass

class Lean3(TextREPLDriver):
    BIN = "lean"
    NAME = "Lean3"

    # We need --threads=0 because I didn't find a way to join() on all pending queries
    REPL_ARGS = ("--server", "--threads=0")

    ID = "lean3_repl"
    LANGUAGE = "lean3"

    def __init__(self, args=(), fpath="-", binpath=None):
        super().__init__(args=args, fpath=fpath, binpath=binpath)
        self.seq_num = -1

    @classmethod
    def driver_not_found(cls, binpath):
        raise ValueError("Not found: {}".format(binpath))

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
        query = { "seq_num": self.seq_num, "command": command,
                  "file_name": self.fpath.name, **kwargs }
        self._write(json.dumps(query, indent=None), "\n")
        response = self._wait()
        debug(response, '<< ')
        return response

    MARKERS_RE = re.compile(r"(?:\b(?:begin|end)\b)|,")

    @classmethod
    def _find_markers(cls, doc):
        for m in cls.MARKERS_RE.finditer(doc):
            yield m.group(), m.span()

    BOL = re.compile("^", re.MULTILINE)

    # FIXME: handle nested begins
    # FIXME: handle errors?
    def _find_sentence_ranges(self, doc: Document):
        tac_beg = None
        for (marker, (marker_beg, marker_end)) in self._find_markers(doc.contents):
            if tac_beg is not None and marker_beg < tac_beg:
                # print(f"skipping over {doc[marker_beg - 10:marker_end]} "
                #       f"as {marker_beg} < {tac_beg}")
                continue # Skip over markers in comments

            # Read goal right past end of ``begin``/``end``, but on commas
            # (commas can be directly followed by text).
            goal_pos = marker_beg if marker == "," else marker_end
            line, column = doc.offset2pos(goal_pos)

            info, _ = self._query("info", line=line, column=column)
            record = info.get("record", {})
            widget, state = record.get("widget"), record.get("state")
            widget_beg = widget and doc.pos2offset(widget["line"], widget["column"])

            # print(f"[→] {marker=}, {marker_beg=}, {tac_beg=}")
            if marker == "begin":
                if tac_beg is not None:
                    continue # FIXME needs a stack of begin/end
                yield (marker_beg, marker_end, state)
            elif marker == ",":
                if widget_beg is None or tac_beg is None or widget_beg <= marker_end:
                    continue # Skip over commas within terms
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

    def _find_sentences(self, doc: Document):
        for beg, end, st in self._find_sentence_ranges(doc):
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
        # FIXME this drops some errors (try ``#compute 1``)
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

    def _annotate(self, chunks):
        document = Document(chunks, "\n")
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
        with self as api:
            return api._annotate(chunks)
