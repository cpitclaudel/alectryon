# Copyright © 2022 Clément Pit-Claudel
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
from typing import Any, Dict, Iterator, List, NamedTuple, Optional, Tuple

class Token(NamedTuple):
    start: int
    end: int
    typ: str
    mods: Tuple[str, ...]

    def value(self, s: str) -> str:
        # Avoid overrides by calling ``__getitem__`` directly
        return str.__getitem__(s, slice(self.start, self.end, None))

    def reposition(self, startpos: int, endpos: int) -> "Token":
        return self._replace(  # pylint: disable=no-member
            start=max(self.start, startpos) - startpos,
            end=min(self.end, endpos) - startpos)

class Tokens(NamedTuple):
    toks: List[Token]
    start: int
    end: int
    startpos: int
    endpos: int

    @staticmethod
    def bisect_right(a, x, lo, hi, key):
        # From bisect.py, modified for `key`
        while lo < hi:
            mid = (lo+hi)//2
            if x < key(a[mid]): hi = mid
            else: lo = mid+1
        return lo

    def filter(self, startpos: int, endpos: int) -> "Tokens":
        startpos, endpos = self.startpos + startpos, self.startpos + endpos
        start = self.bisect_right(self.toks, startpos, self.start, self.end, key=lambda t: t.end)
        end = bisect.bisect_left(self.toks, (endpos,), self.start, self.end)
        return Tokens(self.toks, start, end, startpos, endpos)

    def __iter__(self) -> Iterator[Token]:
        for idx in range(self.start, self.end):
            yield self.toks[idx].reposition(self.startpos, self.endpos)

    def iter_contiguous(self, typ: str, mods: Tuple[str, ...]) -> Iterator[Token]:
        pos = 0
        for tok in self:
            if tok.start > pos:
                yield Token(pos, tok.start, typ, mods)
            yield tok
            pos = tok.end
        if pos < self.endpos:
            yield Token(pos, self.endpos, typ, mods)

class TokenizedStr(str):
    def __new__(cls, s, *_args):
        return super().__new__(cls, s)

    def __init__(self, _s, tokens: Tokens=None, type_map: Dict[str, Any]=None):
        assert tokens and type_map
        super().__init__()
        self.tokens = tokens
        self.type_map = type_map

    @staticmethod
    def _wrapidx(idx: Optional[int], dflt: int, mod: int):
        idx = dflt if idx is None else idx
        return idx if idx >= 0 else idx + mod

    def __getitem__(self, index: slice):
        assert index.step is None
        s = super().__getitem__(index)
        start = self._wrapidx(index.start, 0, len(self))
        stop = self._wrapidx(index.stop, len(self), len(self))
        return TokenizedStr(s, self.tokens.filter(start, stop), self.type_map)
