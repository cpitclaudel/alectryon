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

import tempfile
import re
from pathlib import Path

from .core import CLIDriver, Document, Positioned, Position, Sentence, Text, indent
from .serapi import CoqIdents

class UTF8Adapter:
    def __init__(self, s):
        self.data = s.encode("utf-8")
    def __getitem__(self, index):
        return self.data.__getitem__(index).decode("utf-8")
    def __len__(self):
        return len(self.data)

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

    def _find_sentences(self, doc_bytes):
        topfile = CoqIdents.topfile_of_fpath(self.fpath)
        with tempfile.TemporaryDirectory(prefix="alectryon_coqc-time") as wd:
            source = Path(wd) / topfile
            source.write_bytes(doc_bytes)
            with self.start(additional_args=[str(source)]) as coqc:
                stdout, stderr = (s.decode("utf-8") for s in coqc.communicate())
                if coqc.returncode != 0:
                    MSG = "coqc exited with code {}:\n{}"
                    raise ValueError(MSG.format(coqc.returncode, indent(stderr, "   ")))
        for m in self.COQ_TIME_RE.finditer(stdout):
            beg, end = int(m.group("beg")), int(m.group("end"))
            contents = doc_bytes[beg:end].decode("utf-8")
            yield Positioned(beg, end, Sentence(contents, [], []))

    def partition(self, contents):
        bs = UTF8Adapter(contents)
        return Document.intersperse_text_fragments(bs, self._find_sentences(bs.data))

    CHUNK_SEPARATOR = "\n"

    def annotate(self, chunks):
        document = Document(chunks, self.CHUNK_SEPARATOR)
        try:
            fragments = self.partition(document.contents)
            return list(document.recover_chunks(fragments))
        except ValueError as e:
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1), level=3)
            return [[Text(c)] for c in chunks]

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
