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
from typing import Any, Dict, Iterable, Iterator, List, NamedTuple, Optional, Tuple, Union

class Range(NamedTuple):
    start: int
    end: int

    @property
    def slice(self):
        return slice(self.start, self.end, None)

class Token(NamedTuple):
    rng: Range
    typ: str
    mods: Tuple[str, ...]

    def value(self, s: str) -> str:
        # Avoid overrides by calling ``__getitem__`` directly
        return str.__getitem__(s, self.rng.slice)

    def reposition(self, startpos: int, endpos: int) -> "Token":
        return self._replace(  # pylint: disable=no-member
            rng=Range(start=max(self.rng.start, startpos) - startpos,
                      end=min(self.rng.end, endpos) - startpos))

class Tokens(NamedTuple):
    toks: List[Token]
    view: slice
    rng: Range

    @staticmethod
    def bisect_right(a, x, lo, hi, key):
        # From bisect.py, modified for `key`
        while lo < hi:
            mid = (lo+hi)//2
            if x < key(a[mid]): hi = mid
            else: lo = mid+1
        return lo

    def filter(self, startpos: int, endpos: int) -> "Tokens":
        startpos, endpos = self.rng.start + startpos, self.rng.start + endpos
        start = self.bisect_right(self.toks, startpos, self.view.start, self.view.stop,
                                  key=lambda t: t.rng.end)
        end = bisect.bisect_left(self.toks, ((endpos,),), self.view.start, self.view.stop)
        return Tokens(self.toks, slice(start, end, None), Range(startpos, endpos))

    def __iter__(self) -> Iterator[Token]:
        for idx in range(self.view.start, self.view.stop):
            yield self.toks[idx].reposition(self.rng.start, self.rng.end)

    def iter_contiguous(self, typ: str, mods: Tuple[str, ...]) -> Iterator[Token]:
        pos = 0
        it: Iterable[Token] = self # type: ignore # LATER (≥ 3.10): Inherit
        for tok in it:
            if tok.rng.start > pos:
                yield Token(Range(pos, tok.rng.start), typ, mods)
            yield tok
            pos = tok.rng.end
        if pos < self.rng.end:
            yield Token(Range(pos, self.rng.end), typ, mods)

class TokenizedStr(str):
    def __new__(cls, s, *_args):
        return super().__new__(cls, s)

    def __init__(self, _s, tokens: Optional[Tokens]=None,
                 type_map: Optional[Dict[Tuple[str, ...], Any]]=None):
        assert tokens and type_map
        super().__init__()
        self.tokens = tokens
        self.type_map = type_map

    @staticmethod
    def _wrapidx(idx: Optional[int], dflt: int, mod: int):
        idx = dflt if idx is None else idx
        return idx if idx >= 0 else idx + mod

    def __getitem__(self, index: Union[int, slice]): # type: ignore # 3.6
        s = super().__getitem__(index)
        if index is int:
            return s
        assert isinstance(index, slice)
        assert index.step is None
        start = self._wrapidx(index.start, 0, len(self))
        stop = self._wrapidx(index.stop, len(self), len(self))
        return TokenizedStr(s, self.tokens.filter(start, stop), self.type_map)
