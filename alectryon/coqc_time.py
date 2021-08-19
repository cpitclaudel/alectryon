# Copyright © 2021 Clément Pit-Claudel
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

from typing import Union

import tempfile
import re
from collections import deque, namedtuple
from pathlib import Path

from .core import CLIDriver, Sentence, Text
from .serapi import CoqIdents

Positioned = namedtuple("Positioned", "item beg end")

class Separator(str):
    pass

class CoqcTime(CLIDriver):
    BIN = "coqc"
    NAME = "Coq+coqc-time"
    DEFAULT_ARGS = ("-time", "-color", "no", "-quiet", "-q")

    ID = "coqc_time"
    LANGUAGE = "coq"

    @classmethod
    def driver_not_found(cls, binpath):
        raise ValueError("`coqc` binary not found (bin={}).".format(binpath))

    COQ_TIME_RE = re.compile(r"^Chars (?P<beg>[0-9]+) - (?P<end>[0-9]+) ",
                             re.MULTILINE)

    def coqc_time(self, doc_bytes):
        topfile = CoqIdents.topfile_of_fpath(self.fpath)
        with tempfile.TemporaryDirectory(prefix="alectryon_coq-time") as wd:
            source = Path(wd) / topfile
            source.write_bytes(doc_bytes)
            with self.start(additional_args=[str(source)]) as coqc:
                stdout, stderr = (s.decode("utf-8") for s in coqc.communicate())
                if coqc.returncode != 0:
                    MSG = "coqc exited with code {}:\n{}"
                    raise ValueError(MSG.format(coqc.returncode, stderr))
        for m in self.COQ_TIME_RE.finditer(stdout):
            yield int(m.group("beg")), int(m.group("end"))

    def partition_sentences(self, document):
        bs = document.encode("utf-8")
        prev_end = 0
        for beg, end in self.coqc_time(bs):
            if prev_end < beg:
                yield Text(bs[prev_end:beg].decode("utf-8"))
            yield Sentence(bs[beg:end].decode("utf-8"), messages=[], goals=[])
            prev_end = end
        if prev_end < len(bs):
            yield Text(bs[prev_end:len(bs)].decode("utf-8"))

    @staticmethod
    def with_boundaries(items: Union[Sentence, Text, str]):
        beg = 0
        for item in items:
            s = getattr(item, "contents", item)
            end = beg + len(s)
            yield Positioned(item, beg, end)
            beg = end

    @staticmethod
    def split_fragment(fr, cutoff):
        before = fr.contents[:cutoff]
        after = fr.contents[cutoff:]
        if isinstance(fr, Text):
            fr0 = Text(before)
        else:
            assert isinstance(fr, Sentence)
            fr0 = Sentence(before, messages=[], goals=[])
        return fr0, fr._replace(contents=after)

    CHUNK_SEPARATOR = Separator("\n")

    @classmethod
    def recover_chunks(cls, chunks, fragments):
        fragments = deque(cls.with_boundaries(fragments))
        for chunk in iter(cls.with_boundaries(chunks)):
            chunk_fragments = []
            if fragments:
                assert fragments[0].beg >= chunk.beg
            while fragments and fragments[0].end <= chunk.end:
                chunk_fragments.append(fragments.popleft().item)
            if fragments and fragments[0].beg < chunk.end and fragments[0].end > chunk.end:
                cutoff = chunk.end - fragments[0].end
                before, after = cls.split_fragment(fragments[0].item, cutoff)
                fragments[0] = fragments[0]._replace(item=after, beg=chunk.end)
                chunk_fragments.append(before)
            assert chunk.item == "".join(c.contents for c in chunk_fragments)
            if not isinstance(chunk.item, Separator):
                yield chunk_fragments
        assert not fragments, fragments

    @staticmethod
    def intersperse(items, separator):
        interspersed = [separator] * (2 * len(items) - 1)
        interspersed[::2] = items
        return interspersed

    def annotate(self, chunks):
        with_separator = self.intersperse(chunks, self.CHUNK_SEPARATOR)
        document = "".join(with_separator)
        return list(self.recover_chunks(with_separator, self.partition_sentences(document)))

def annotate(chunks, args=(), fpath="-", binpath=None):
    r"""Use ``coqc -time`` to fragment multiple chunks of Coq code.

    >>> annotate(["Check 1. (* c *) ", "Print nat."])
    [[Sentence(contents='Check 1.', messages=[], goals=[]),
      Text(contents=' (* c *) ')],
     [Sentence(contents='Print nat.', messages=[], goals=[])]]
    >>> annotate(["Check (* c *)", "1."])
    [[Sentence(contents='Check (* c *)', messages=[], goals=[])],
     [Sentence(contents='1.', messages=[], goals=[])]]
    """
    return CoqcTime(args=args, fpath=fpath, binpath=binpath).annotate(chunks)
