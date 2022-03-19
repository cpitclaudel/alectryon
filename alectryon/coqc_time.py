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

from typing import Iterable, List

import tempfile
import re
from pathlib import Path

from .core import CLIDriver, EncodedDocument, Positioned, Position, Sentence, Text, Fragment
from .serapi import CoqIdents

class CoqcTime(CLIDriver):
    BIN = "coqc"
    NAME = "Coq+coqc-time"
    CLI_ARGS = ("-time", "-color", "no", "-quiet", "-q")

    ID = "coqc_time"
    LANGUAGE = "coq"

    COQ_TIME_RE = re.compile(r"^Chars (?P<beg>[0-9]+) - (?P<end>[0-9]+) ",
                             re.MULTILINE)

    def _find_sentences(self, document: EncodedDocument):
        with tempfile.TemporaryDirectory(prefix="alectryon_coqc-time") as wd:
            source = Path(wd) / CoqIdents.topfile_of_fpath(self.fpath)
            source.write_bytes(document.contents)
            stdout = self.run_cli(more_args=[str(source)])
        for m in self.COQ_TIME_RE.finditer(stdout):
            beg, end = int(m.group("beg")), int(m.group("end"))
            yield Positioned(beg, end, Sentence(document[beg:end], [], []))

    def partition(self, document: EncodedDocument):
        return document.intersperse_text_fragments(self._find_sentences(document))

    def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
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
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1).as_range(), level=3)
            return [[Text(c)] for c in chunks]
