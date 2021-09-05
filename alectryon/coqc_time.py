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

from .core import CLIDriver, EncodedDocument, Positioned, Position, Sentence, Text, indent
from .serapi import CoqIdents

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

    def _find_sentences(self, document):
        topfile = CoqIdents.topfile_of_fpath(self.fpath)
        with tempfile.TemporaryDirectory(prefix="alectryon_coqc-time") as wd:
            source = Path(wd) / topfile
            source.write_bytes(document.contents)
            with self.start(additional_args=[str(source)]) as coqc:
                stdout, stderr = (s.decode("utf-8") for s in coqc.communicate())
                if coqc.returncode != 0:
                    MSG = "coqc exited with code {}:\n{}"
                    raise ValueError(MSG.format(coqc.returncode, indent(stderr, "   ")))
        for m in self.COQ_TIME_RE.finditer(stdout):
            beg, end = int(m.group("beg")), int(m.group("end"))
            yield Positioned(beg, end, Sentence(document[beg:end], [], []))

    def partition(self, document):
        return EncodedDocument.intersperse_text_fragments(
            document, self._find_sentences(document))

    def annotate(self, chunks):
        r"""Use ``coqc -time`` to fragment multiple chunks of Coq code.

        >>> CoqcTime().annotate(["Check 1. (* … *) ", "Print nat."])
        [[Sentence(contents='Check 1.', messages=[], goals=[]),
          Text(contents=' (* … *) ')],
         [Sentence(contents='Print nat.', messages=[], goals=[])]]
        >>> CoqcTime().annotate(["Check (* … *)", "1."])
        [[Sentence(contents='Check (* … *)', messages=[], goals=[])],
         [Sentence(contents='1.', messages=[], goals=[])]]
        """
        document = EncodedDocument(chunks, "\n", encoding="utf-8")
        try:
            fragments = self.partition(document)
            return list(document.recover_chunks(fragments))
        except ValueError as e:
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1), level=3)
            return [[Text(c)] for c in chunks]
