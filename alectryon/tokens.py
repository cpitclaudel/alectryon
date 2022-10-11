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
import warnings
from typing import Any, Dict, Iterable, Iterator, List, NamedTuple, Optional, Tuple, Union

class Range(NamedTuple):
    start: int
    end: int

    @property
    def slice(self):
        return slice(self.start, self.end, None)

class Token(NamedTuple):
    rng: Range
    typ: Tuple[str, ...]

    def value(self, s: str) -> str:
        # Avoid overrides by calling ``__getitem__`` directly
        return str.__getitem__(s, self.rng.slice)

    def reposition(self, startpos: int, endpos: int) -> "Token":
        return self._replace(  # pylint: disable=no-member
            rng=Range(start=max(self.rng.start, startpos) - startpos,
                      end=min(self.rng.end, endpos) - startpos))

    def resolve(self, type_map: Dict[Tuple[str, ...], str]) -> Optional[str]:
        tokstr = type_map.get(self.typ) or type_map.get((self.typ[0],))
        if tokstr is None:
            MSG = "!! Unexpected pre-tokenized token type {!r} with modifiers {!r}\n"
            warnings.warn(MSG.format(self.typ[0], self.typ[1:]))
        return tokstr

class Tokens(NamedTuple):
    toks: List[Token]
    view: slice # Slice of `toks`
    rng: Range # Since of the original string

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

    def iter_contiguous(self) -> Iterator[Token]:
        pos = 0
        it: Iterable[Token] = self # type: ignore # LATER (≥ 3.10): Inherit
        for tok in it:
            if tok.rng.start > pos:
                yield Token(Range(pos, tok.rng.start), ())
            yield tok
            pos = tok.rng.end
        if pos < self.rng.end:
            yield Token(Range(pos, self.rng.end), ())

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

    CACHE_TYPE_MAP_KEY = "type_map"
    CACHE_TYPES_KEY = "types"

    def js_encode(self, target: Dict[str, Any],
                  persistent: Dict[str, Any], ephemeral: Dict[str, Any]):
        # All strings in the cache must have the same ``type_map``; check that
        assert ephemeral.setdefault(self.CACHE_TYPE_MAP_KEY, self.type_map) == self.type_map

        # Build a table to retrieve indices quickly
        revmap: Optional[Dict[Tuple[str, ...], int]] = \
            ephemeral.get(self.CACHE_TYPES_KEY)
        if revmap is None:
            types = persistent[self.CACHE_TYPES_KEY] = \
                [(), *((typ,) for typ in self.type_map.values())]
            revmap = ephemeral[self.CACHE_TYPES_KEY] = \
                {typ: idx for (idx, typ) in enumerate(types)}

        # Serialize the tokens
        toks: List[int]
        target["str"] = str(self)
        target["toks"] = toks = []
        for tok in self.tokens:
            assert isinstance(tok, Token)
            rng, typ = tok.rng, tok.resolve(self.type_map)
            ttyp: Tuple[str, ...] = (typ,) if typ else ()
            toks.extend((rng.start, rng.end, revmap[ttyp]))

    @classmethod
    def js_decode(cls, source: Dict[str, Any],
                  persistent: Dict[str, Any], ephemeral: Dict[str, Any]):
        types: List[Tuple[str, ...]] = persistent[cls.CACHE_TYPES_KEY]
        type_map: Optional[Dict[Tuple[str, ...], Any]] = \
            ephemeral.get(cls.CACHE_TYPE_MAP_KEY)

        # Rebuild a dummy type map
        if type_map is None:
            types[:] = [tuple(typ) for typ in types]
            type_map = ephemeral[cls.CACHE_TYPES_KEY] = \
                {tuple(typ): (typ[0] if typ else None) for typ in types}

        # Reconstruct tokens
        toks, enc = [], source["toks"]
        for i in range(0, len(enc), 3):
            start, end, typidx = enc[i], enc[i+1], enc[i+2]
            toks.append(Token(Range(start, end), types[typidx]))

        s = source["str"]
        tokens = Tokens(toks, slice(0, len(toks)), Range(0, len(s)))
        return TokenizedStr(s, tokens, type_map)
