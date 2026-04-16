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

from typing import Any, ClassVar, Dict, Iterable, Iterator, List, NamedTuple, Optional, Tuple, Union

from dataclasses import dataclass, field
import warnings

from .core import Document, JSON, must
from .lsp import LSPClient, LSPClientInitializeRequest, LSPClientRequest, LSPDriver, LSPServerConfig

Bounds = "slice[int, int, None]" # LATER: : TypeAlias

LSPTokenMap = dict[tuple[str, ...], str]

class Token(NamedTuple):
    rng: Bounds
    typ: Tuple[str, ...]

    def value(self, s: str) -> str:
        # Avoid overrides by calling ``__getitem__`` directly
        return str.__getitem__(s, self.rng)

    def reposition(self, startpos: int, endpos: int) -> "Token":
        return self._replace(  # pylint: disable=no-member
            rng=slice(max(self.rng.start, startpos) - startpos,
                      min(self.rng.stop, endpos) - startpos))

    def resolve(self, type_map: LSPTokenMap) -> Optional[str]:
        """Resolve token type to a Pygments token string."""
        if not self.typ:
            return None
        tokstr = type_map.get(self.typ) or type_map.get((self.typ[0],))
        if tokstr is None:
            MSG = "!! Unexpected pre-tokenized token type {!r} with modifiers {!r}\n"
            warnings.warn(MSG.format(self.typ[0], self.typ[1:]))
        return tokstr

@dataclass
class Tokens:
    toks: list[Token]
    view: slice # Slice of `toks`
    rng: Bounds # Slice of the original string

    @staticmethod
    def _bisect(a, x, lo, hi, key, right):
        r"""Bisect `a` with a `key` function.

        Equivalent to ``bisect_{right,left}(list(map(key, a)), x, lo, hi)``:

        >>> from bisect import bisect_left, bisect_right
        >>> key = lambda v: (v * 31 + 7) % 43
        >>> a = sorted(range(0, 100), key=key)
        >>> mapped = [key(v) for v in a]
        >>> for x in range(100):
        ...   for right in (True, False):
        ...     ref = bisect_right(mapped, x) if right else bisect_left(mapped, x)
        ...     assert ref == Tokens._bisect(a, x, 0, len(a), key, right)
        """
        while lo < hi:
            mid = (lo + hi) // 2
            k = key(a[mid])
            if k <= x and (right or k != x):
                lo = mid+1
            else:
                hi = mid
        return lo

    def filter(self, startpos: int, endpos: int) -> "Tokens":
        startpos, endpos = self.rng.start + startpos, self.rng.start + endpos
        start = self._bisect(self.toks, startpos, self.view.start, self.view.stop,
                             key=lambda t: t.rng.stop, right=True)
        end = self._bisect(self.toks, endpos, self.view.start, self.view.stop,
                           key=lambda t: t.rng.start, right=False)
        return Tokens(self.toks, slice(start, end, None), slice(startpos, endpos))

    def __iter__(self) -> Iterator[Token]:
        for idx in range(self.view.start, self.view.stop):
            yield self.toks[idx].reposition(self.rng.start, self.rng.stop)

    def iter_contiguous(self) -> Iterator[Token]:
        """Yield contiguous tokens covering the full ``self.rng``.

        >>> s = "** kwd: xy"
        >>> toks = [Token(slice(3, 6), ('kw',)), Token(slice(8, 10), ('v',))]
        >>> filtered = Tokens(toks, slice(0, 2), slice(2, 10))
        >>> [(t.rng.start, t.rng.stop) for t in filtered.iter_contiguous()]
        [(0, 1), (1, 4), (4, 6), (6, 8)]
        """
        pos = 0
        it: Iterable[Token] = self # type: ignore # LATER (≥ 3.10): Inherit
        for tok in it:
            if tok.rng.start > pos:
                yield Token(slice(pos, tok.rng.start), ())
            yield tok
            pos = tok.rng.stop
        repos_stop = self.rng.stop - self.rng.start
        if pos < repos_stop:
            yield Token(slice(pos, repos_stop), ())

    @staticmethod
    def remove_overlapping(tokens: Iterable[Token]) -> list[Token]:
        """Remove overlapping token from a list of `tokens`.

        Later tokens are preferred over earlier ones, so if two overlapping
        tokens are found the first one is discarded.
        """
        filtered: list[Token] = []
        tokens = sorted(tokens, key=lambda t: (t.rng.start, t.rng.stop))
        for tok in tokens:
            while filtered and tok.rng.start < filtered[-1].rng.stop:
                _ = filtered.pop()
            filtered.append(tok)
        return filtered

class TokenizedStr(str):
    r"""A string annotated with LSP semantic tokens.

    >>> toks = [Token(slice(0, 4), ("keyword",)), Token(slice(5, 11), ("variable",))]
    >>> ts = TokenizedStr("abcd 012345", Tokens(toks, slice(0, 2), slice(0, 11)), {("keyword",): "kw"})
    >>> str(ts) == "abcd 012345"
    True

    >>> sub = ts[3:9]
    >>> str(sub)
    'd 0123'
    >>> [(t.rng.start, t.rng.stop, t.typ) for t in sub.tokens]
    [(0, 1, ('keyword',)), (2, 6, ('variable',))]
    """
    def __new__(cls, s, *_args):
        return super().__new__(cls, s)

    def __init__(self, _s, tokens: Optional[Tokens]=None,
                 type_map: Optional[Dict[Tuple[str, ...], Any]]=None):
        assert tokens and type_map
        super().__init__()
        self.tokens = tokens
        self.type_map: LSPTokenMap = type_map

    @staticmethod
    def _clampidx(idx: Optional[int], dflt: int, mod: int):
        idx = dflt if idx is None else idx
        return idx if idx >= 0 else max(0, idx + mod)

    def __getitem__(self, index: Union[int, slice]): # type: ignore # 3.6
        s = super().__getitem__(index)
        if isinstance(index, int):
            return s
        assert isinstance(index, slice)
        assert index.step is None
        start = self._clampidx(index.start, 0, len(self))
        stop = self._clampidx(index.stop, len(self), len(self))
        return TokenizedStr(s, self.tokens.filter(start, stop), self.type_map)

    CACHE_TYPE_MAP_KEY = "type_map"
    CACHE_TYPES_KEY = "types"

    def js_encode(self, _serializer, target: Dict[str, Any],
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
            toks.extend((rng.start, rng.stop, revmap[ttyp]))

    @classmethod
    def js_decode(cls, _serializer, source: Dict[str, Any],
                  persistent: Dict[str, Any], ephemeral: Dict[str, Any]):
        types: List[Tuple[str, ...]] = persistent[cls.CACHE_TYPES_KEY]
        type_map: Optional[Dict[Tuple[str, ...], Any]] = \
            ephemeral.get(cls.CACHE_TYPE_MAP_KEY)

        # Rebuild a dummy type map
        if type_map is None:
            types[:] = [tuple(typ) for typ in types]
            type_map = ephemeral[cls.CACHE_TYPE_MAP_KEY] = \
                {tuple(typ): (typ[0] if typ else None) for typ in types}

        # Reconstruct tokens
        toks, enc = [], source["toks"]
        for i in range(0, len(enc), 3):
            start, end, typidx = enc[i], enc[i+1], enc[i+2]
            toks.append(Token(slice(start, end), types[typidx]))

        s = source["str"]
        tokens = Tokens(toks, slice(0, len(toks)), slice(0, len(s)))
        return TokenizedStr(s, tokens, type_map)

@dataclass
class LSPTokenLegend:
    types: list[str]
    modifiers: list[str]
    _modifiers_cache: dict[int, tuple[str, ...]] = field(init=False, default_factory=lambda: {})

    @staticmethod
    def of_json(js: JSON) -> "LSPTokenLegend":
        return LSPTokenLegend(js["tokenTypes"], js["tokenModifiers"])

    @staticmethod
    def of_config(config: LSPServerConfig) -> "LSPTokenLegend":
        js = config.capabilities.get("semanticTokensProvider", {})["legend"]
        return LSPTokenLegend.of_json(js)

    def resolve_modifiers(self, bitset: int) -> tuple[str, ...]:
        if (mods := self._modifiers_cache.get(bitset)) is None:
            bits = enumerate(bin(bitset)[:1:-1], 0)
            self._modifiers_cache[bitset] = mods = \
                tuple(sorted(self.modifiers[i] for i, c in bits if c == '1'))
        return mods

    def resolve_one(self, doc: Document, l: int, c: int, length: int,
                    itype: int, imods: int) -> Token:
        typ = self.types[itype]
        mods = self.resolve_modifiers(imods)
        start = doc.lc2offset(l, c)
        return Token(slice(start, start + length), (typ, *mods))

    def resolve(self, doc: Document, tokens: Iterable[int]) -> Iterator[Token]:
        l, c = 1, 0
        # pylint: disable=unsubscriptable-object
        groups: zip[tuple[int, ...]] = zip(*([iter(tokens)] * 5)) # type: ignore
        for dl, dc, length, itype, imods in groups:
            l, c = l + dl, (dc if dl != 0 else c + dc)
            yield self.resolve_one(doc, l, c, length, itype, imods)

@dataclass
class LSPClientSemanticTokensRequest(LSPClientRequest):
    METHOD = "textDocument/semanticTokens/full"

    uri: str

    @property
    def params(self):
        return { "textDocument": { "uri": self.uri, "version": 0 } }

class LSPClientSemanticTokensMixin(LSPClient):
    TOKEN_MAP: ClassVar[LSPTokenMap] = {
        ("namespace",): "Name.Namespace",
        ("type",): "Keyword.Type",
        ("class",): "Name.Class",
        ("enum",): "Name.Class",
        ("interface",): "Name.Class",
        ("struct",): "Name.Class",
        ("typeParameter",): "Name.Entity",
        ("parameter",): "Name.Variable",
        ("variable",): "Name.Variable",
        ("property",): "Name.Variable.Instance",
        ("enumMember",): "Name.Constant",
        ("event",): "Name.Class",
        ("function",): "Name.Function",
        ("method",): "Name.Function",
        ("macro",): "Name.Function",
        ("keyword",): "Keyword",
        ("modifier",): "Keyword",
        ("comment",): "Comment",
        ("string",): "String",
        ("number",): "Number",
        ("regexp",): "String.Regex",
        ("operator",): "Operator"
    }

    TOKEN_MODIFIERS: ClassVar[set[str]] = {
        'declaration', 'definition', 'readonly', 'static', 'deprecated',
        'abstract', 'async', 'modification', 'documentation', 'defaultLibrary'
    }

    def __init__(self, driver: "LSPDriver[Any]"):
        super().__init__(driver)
        self.legend: LSPTokenLegend = LSPTokenLegend.of_config(self.config)

    def _init(self) -> LSPClientInitializeRequest:
        req = super()._init()
        modifiers = self.TOKEN_MODIFIERS | {m for t in self.TOKEN_MAP for m in t[1:]}
        req.params["capabilities"]["textDocument"]["semanticTokens"] = {
            "requests": {"range": False, "full": True},
            "tokenTypes": [t[0] for t in self.TOKEN_MAP],
            "tokenModifiers": list(modifiers),
            "formats": ['relative'],
            "overlappingTokenSupport": False,
            "multilineTokenSupport": True,
            "serverCancelSupport": False,
            "augmentsSyntaxTokens": False,
        }
        return req

    def get_tokens(self, doc: Document):
        req = LSPClientSemanticTokensRequest(self, self.driver.uri)
        data: list[int] = must(req.send().result)["data"]
        tokens = self.legend.resolve(doc, data)
        filtered = Tokens.remove_overlapping(tokens)
        return Tokens(filtered, slice(0, len(filtered)), slice(0, len(doc)))
