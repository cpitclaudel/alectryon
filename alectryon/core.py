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

from __future__ import annotations

from typing import Any, ClassVar, DefaultDict, Dict, Generic, Iterable, IO, List, \
    NamedTuple, NoReturn, Optional, overload, Tuple, TypeVar, Union

from collections import UserDict, deque, namedtuple, defaultdict
from contextlib import contextmanager
from dataclasses import dataclass, replace
from functools import cached_property
from importlib import import_module
from pathlib import Path
from shlex import quote
from shutil import which
from subprocess import PIPE, CompletedProcess
import os
import re
import subprocess
import sys
import textwrap

_Path = Union[str, os.PathLike]
_FILE = Union[None, int, IO[Any]]
JSON = Dict[str, Any]

DEBUG = False
TRACEBACK = False

class UnexpectedError(ValueError):
    pass

def indent(text, prefix):
    if prefix.isspace():
        return textwrap.indent(text, prefix)
    text = re.sub("^(?!$)", prefix, text, flags=re.MULTILINE)
    return re.sub("^$", prefix.rstrip(), text, flags=re.MULTILINE)

INDENTATION_RE = re.compile(r"^ *(?=[^\s])")

def measure_indentation(line):
    m = INDENTATION_RE.match(line)
    return m.end() - m.start() if m else None

def measure_min_indentation(lines):
    indents = (measure_indentation(ln) for ln in lines)
    return min((i for i in indents if i is not None), default=0)

def dedent(lines, amount):
    indentation = min(amount, measure_min_indentation(lines))
    contents = "\n".join(ln[indentation:] for ln in lines)
    return indentation, contents

def debug(v, prefix):
    if DEBUG:
        if isinstance(v, (bytes, bytearray)):
            v = v.decode("utf-8", errors="replace")
        v = str(v).rstrip().replace("\r\n", "\n")
        print(indent(v, prefix), flush=True)

class DriverInfo(namedtuple("DriverInfo", "name version")):
    def fmt(self, include_version_info=True):
        return "{} v{}".format(self.name, self.version) if include_version_info else self.name

Hypothesis = namedtuple("Hypothesis", "names body type")
Goal = namedtuple("Goal", "name conclusion hypotheses")
Message = namedtuple("Message", "contents")
Sentence = namedtuple("Sentence", "contents messages goals")
Text = namedtuple("Text", "contents")
Fragment = Union[Text, Sentence]

class Enriched():
    def __new__(cls, *args, **kwargs):
        if len(args) < len(getattr(super(), "_fields", ())):
            # Don't repeat fields given by position (it breaks pickle & deepcopy)
            kwargs = {"props": {}, **kwargs}
        return super().__new__(cls, *args, **kwargs)
    @property
    def ids(self):
        return getattr(self, "props", {}).setdefault("ids", [])
    @property
    def markers(self):
        return getattr(self, "props", {}).setdefault("markers", [])

def _enrich(nt) -> type[Enriched]:
    # LATER: Use dataclass + multiple inheritance; change `ids` and `markers` to
    # mutable `id` and `marker` fields.
    name = "Rich" + nt.__name__
    fields = nt._fields + ("props",)
    # Using ``type`` this way ensures compatibility with pickling
    return type(name, (Enriched, namedtuple(name, fields)),
                {"__slots__": ()})

Goals = namedtuple("Goals", "goals")
Messages = namedtuple("Messages", "messages")

class Names(list):
    pass
RichHypothesis = _enrich(Hypothesis)
RichGoal = _enrich(Goal)
RichMessage = _enrich(Message)
RichCode = _enrich(namedtuple("Code", "contents"))
RichSentence = _enrich(namedtuple("Sentence", "input outputs annots prefixes suffixes"))
RichFragment = Union[Text, RichSentence]

def b16(i):
    return hex(i)[len("0x"):]

class Gensym():
    # Having a global table of counters ensures that creating multiple Gensym
    # instances in the same session doesn't cause collisions.
    GENSYM_COUNTERS: Dict[str, DefaultDict[str, int]] = {}

    def __init__(self, stem):
        self.stem = stem
        self.counters = self.GENSYM_COUNTERS.setdefault(stem, defaultdict(lambda: -1))

    def __call__(self, prefix):
        self.counters[prefix] += 1
        return self.stem + prefix + b16(self.counters[prefix])

T = TypeVar("T")
def must(x: Optional[T]) -> T:
    assert x is not None
    return x

@contextmanager
def nullctx():
    yield

@contextmanager
def cwd_mgr(wd: _Path):
    old_cwd = os.getcwd()
    os.chdir(wd)
    try:
        yield
    finally:
        os.chdir(old_cwd)

class Backend:
    def __init__(self, highlighter):
        self.highlighter = highlighter

    def gen_fragment(self, fr): raise NotImplementedError()
    def gen_hyp(self, hyp): raise NotImplementedError()
    def gen_goal(self, goal): raise NotImplementedError()
    def gen_message(self, message): raise NotImplementedError()
    def highlight(self, s): raise NotImplementedError()
    def gen_names(self, names): raise NotImplementedError()
    def gen_code(self, code): raise NotImplementedError()
    def gen_txt(self, s): raise NotImplementedError()

    def highlight_enriched(self, obj):
        lang = obj.props.get("lang")
        with self.highlighter.override(lang=lang) if lang else nullctx():
            return self.highlight(obj.contents)

    def _gen_any(self, obj):
        if isinstance(obj, (Text, RichSentence)):
            self.gen_fragment(obj)
        elif isinstance(obj, RichHypothesis):
            self.gen_hyp(obj)
        elif isinstance(obj, RichGoal):
            self.gen_goal(obj)
        elif isinstance(obj, RichMessage):
            self.gen_message(obj)
        elif isinstance(obj, RichCode):
            self.gen_code(obj)
        elif isinstance(obj, Names):
            self.gen_names(obj)
        elif isinstance(obj, str):
            self.gen_txt(obj)
        else:
            raise TypeError("Unexpected object type: {}".format(type(obj)))

    def gen_fragments(self, fragments, ids=(), classes=()):
        raise NotImplementedError

    def gen(self, annotated):
        for fragments in annotated:
            yield self.gen_fragments(fragments) if fragments is not None else None

class Asset(str):
    def __new__(cls, fname, gen=None):
        return super().__new__(cls, fname)

    def __init__(self, _fname, gen=lambda _: ""):
        super().__init__()
        self.gen = gen

class Position(NamedTuple):
    fpath: _Path
    line: int # 1-based
    col: Optional[int] # 0-based

    @staticmethod
    def default(fpath):
        """Return a position at the beginning of the current buffer."""
        return Position(fpath, 1, None)

    def as_range(self):
        return Range(self, None)

    def as_header(self, wrap: bool=False) -> str:
        """Format this position as a string, without the path.

        >>> l = Position("input.rst", 3, None)
        >>> l.as_header(True), l.as_header(False)
        ('3', '3')
        >>> lc = Position("input.v", 10, 0)
        >>> lc.as_header(False), lc.as_header(True)
        ('10:0', '(10:0)')
        """
        header = f"{self.line}:{self.col}" if self.col is not None else f"{self.line}"
        return f"({header})" if self.col is not None and wrap else header

    @classmethod
    def of_lsp(cls, fpath: _Path, js: dict[str, Any]):
        return Position(fpath, js["line"] + 1, js["character"])

    def to_lsp(self):
        return { "line": self.line - 1, "character": self.col or 0 }

    def __add__(self, other):
        """Advance `self` by `other`.

        >>> Position("f", 5, 10) + Position("f", 1, 3)
        Position(fpath='f', line=5, col=13)
        >>> Position("f", 5, 10) + Position("f", 2, 3)
        Position(fpath='f', line=6, col=3)
        """
        line = self.line + other.line - 1
        col = ((self.col or 0) if other.line == 1 else 0) + (other.col or 0)
        return Position(self.fpath, line, col)

    def __sub__(self, other):
        """Rewind `self` by `other`.

        >>> Position("f", 5, 13) - Position("f", 1, 3)
        Position(fpath='f', line=5, col=10)
        >>> Position("f", 5, 10) - Position("f", 1, 3)
        Position(fpath='f', line=5, col=7)
        """
        line = self.line - other.line + 1
        col = (self.col or 0) - ((other.col or 0) if other.line == 1 else 0)
        return Position(self.fpath, line, col)

class Range(NamedTuple):
    beg: Position
    end: Position | None

    @staticmethod
    def default(fpath):
        """Return an empty range at the beginning of the current buffer."""
        return Position.default(fpath).as_range()

    def as_header(self):
        """Format `self` as a string.
        >>> Range(Position("", 1, None), None).as_header()
        '<unknown>:1:'
        >>> Range(Position("f", 5, None), None).as_header()
        'f:5:'
        >>> Range(Position("f", 5, 0), None).as_header()
        'f:5:0:'
        >>> Range(Position("f", 5, 3), Position("f", 5, None)).as_header()
        'f:5:3:'
        >>> Range(Position("f", 5, 3), Position("f", 5, 3)).as_header()
        'f:5:3:'
        >>> Range(Position("f", 5, 3), Position("f", 5, 4)).as_header()
        'f:5:3-4:'
        >>> Range(Position("f", 5, 3), Position("f", 6, None)).as_header()
        'f:(5:3)-6:'
        >>> Range(Position("f", 5, 3), Position("f", 6, 4)).as_header()
        'f:(5:3)-(6:4):'
        """
        beg, end = self.beg, self.end or self.beg
        assert beg.fpath == end.fpath
        if end.line != beg.line and end.line is not None:
            pos = f"{beg.as_header(True)}-{end.as_header(True)}"
        elif end.line == beg.line and end.col != beg.col and beg.col is not None and end.col is not None:
            pos = f"{beg.line}:{beg.col}-{end.col}"
        else:
            pos = beg.as_header(False)
        return f"{beg.fpath or '<unknown>'}:{pos}:"

    @classmethod
    def of_lsp(cls, fpath: _Path, js: dict[str, Any]):
        return cls(Position.of_lsp(fpath, js["start"]),
                   Position.of_lsp(fpath, js["end"]))

    def as_docutils(self):
        beg = {"line": self.beg.line, "column": self.beg.col}
        end = {"end_line": self.end.line, "end_column": self.end.col} if self.end else {}
        return {"source": self.beg.fpath, **beg, **end}

    @classmethod
    def of_docutils(cls, msg: dict[str, Any]):
        src = msg["source"]
        l, c = msg.get("line", 1), msg.get("column")
        endl, endc = msg.get("end_line"), msg.get("end_column")
        beg, end = Position(src, l, c), endl and Position(src, endl, endc)
        return Range(beg, end) if beg else None

class PosStr(str):
    def __new__(cls, s, *_args):
        return super().__new__(cls, s)

    # pylint: disable=redefined-outer-name
    def __init__(self, _s, pos: Position, indent: int):
        super().__init__()
        self.pos, self.indent = pos, indent

    @staticmethod
    def remap(s: str, base: Position, pos: Position):
        """Express `pos` in coordinate space of `s`, relative to `base`.

        `base` indicates the coordinates of `s` starts in the document that
        `pos` is taken from.  If `s` is a ``PosStr``; recompute `pos` relative
        to the real coordinates of `s` instead of `base`.  Otherwise, return
        `pos` unchanged.
        """
        if not isinstance(s, PosStr):
            return pos
        abs = s.pos + (pos - base)
        return Position(pos.fpath, abs.line, s.indent + (abs.col or 0))

class View(bytes):
    def __getitem__(self, key):
        return memoryview(self).__getitem__(key)

    def __init__(self, s):
        super().__init__()
        self.s = s

TPositioned = TypeVar("TPositioned", covariant=True)
@dataclass(frozen=True)
class Positioned(Generic[TPositioned]):
    beg: int
    end: int
    e: TPositioned # type: ignore (covariance OK since frozen)

    def astuple(self):
        return self.beg, self.end, self.e

TItem = TypeVar("TItem", bound=Union[Sentence, Text, str])

class Document:
    """A base class to handle conversions to and from a list of chunks.

    This is useful to recover chunk boundaries for provers that concatenate all
    chunks before processing them.
    """
    def __init__(self, chunks, chunk_separator):
        self.chunks = list(chunks)
        self.with_separator = [c + chunk_separator for c in self.chunks]
        self.str: str = chunk_separator[0:0].join(self.with_separator)
        self.separator = chunk_separator

    @classmethod
    def _len(cls, s: str) -> int:
        raise NotImplementedError

    @classmethod
    def _slice(cls, s: str, index: slice) -> str:
        raise NotImplementedError

    def __getitem__(self, index) -> str:
        raise NotImplementedError

    def __len__(self) -> int:
        raise NotImplementedError

    def _find_bols(self) -> Iterable[int]:
        raise NotImplementedError

    def _find_eol(self, start: int) -> int:
        raise NotImplementedError

    def _decode_column(self, pos: Position) -> Position:
        """Translate the ``column`` part of `pos` to a character offset."""
        raise NotImplementedError

    def recover_chunks(self, fragments):
        grouped = self._recover_chunks(self.with_separator, fragments)
        return self.strip_separators(grouped, self.separator)

    @cached_property
    def bol_offsets(self) -> list[int]:
        return list(self._find_bols())

    @cached_property
    def chunk_offsets(self) -> list[int]:
        return [p.beg for p in self.with_boundaries(self.with_separator)]

    def offset2lc(self, offset) -> Tuple[int, int]:
        r"""Convert a character offset to a (line, column) pair.

        >>> d = TextDocument(["abc\n", "def"], "\n")
        >>> all(d.lc2offset(*d.offset2lc(o)) == o for o in range(len(d)))
        True
        """
        import bisect
        line = bisect.bisect_right(self.bol_offsets, offset)
        bol = self.bol_offsets[line - 1]
        return line, offset - bol

    def lc2offset(self, line: int, col: int) -> int:
        assert line >= 1
        return self.bol_offsets[line - 1] + col

    @overload
    def offset2pos(self, fpath: _Path, offset: int) -> Position: ...
    @overload
    def offset2pos(self, fpath: _Path, offset: None) -> None: ...

    def offset2pos(self, fpath: _Path, offset: int | None) -> Position | None:
        return Position(fpath, *self.offset2lc(offset)) if offset is not None else None

    def pos2offset(self, pos: Position) -> int:
        return self.lc2offset(pos.line, pos.col or 0)

    def offsets2range(self, fpath: _Path, beg: int, end: int | None) -> Range:
        return Range(self.offset2pos(fpath, beg), self.offset2pos(fpath, end))

    def range2offsets(self, range: Range) -> Tuple[int, int]:
        beg = self.pos2offset(range.beg)
        end = self.pos2offset(range.end) if range.end else self._find_eol(beg)
        return beg, end

    def remap_pos(self, pos: Position) -> Position:
        """Translate `pos` from document to source-file space."""
        import bisect
        idx = bisect.bisect_right(self.chunk_offsets, self.pos2offset(pos)) - 1
        base = self.offset2pos(pos.fpath, self.chunk_offsets[idx])
        return PosStr.remap(self.chunks[idx],
                       self._decode_column(base),
                       self._decode_column(pos))

    def remap_range(self, range: Range) -> Range:
        """Translate `range` from document to source-file space."""
        return Range(self.remap_pos(range.beg), range.end and self.remap_pos(range.end))

    def format_error_context(self, beg: int, end: int) -> str:
        """Format a >>>…<<< context snippet for the encoded range [beg, end)."""
        prefix, substring, suffix = self[:beg], self[beg:end], self[end:]
        prefix = "\n".join(prefix.splitlines()[-3:])
        suffix = "\n".join(suffix.splitlines()[:3])
        context = f"{prefix}>>>{substring}<<<{suffix}"
        return ("\nThe offending range is delimited by >>>…<<< below:\n" +
                "\n".join(f"  > {line}" for line in context.splitlines()))

    def intersperse_text_fragments(self, pfragments: Iterable[Positioned[Fragment]]) -> Iterable[Fragment]:
        """Split document into fragments.

        For ranges covered by `pfragments`, return the corresponding element.
        For the rest, create fresh ``Text`` objects.
        """
        pos = 0
        for st in pfragments:
            if pos < st.beg:
                yield Text(self[pos:st.beg])
            yield st.e
            pos = st.end
        if pos < len(self):
            yield Text(self[pos:])

    @classmethod
    def with_boundaries(cls, items: Iterable[TItem]) -> Iterable[Positioned[TItem]]:
        end = 0
        for item in items:
            beg, end = end, end + cls._len(item if isinstance(item, str) else item.contents)
            yield Positioned(beg, end, item)

    @classmethod
    def split_fragment(cls, fr: Fragment, cutoff: int):
        """Split `fr` at position `cutoff`.

        >>> TextDocument.split_fragment(Text("abcxyz"), 3)
        (Text(contents='abc'), Text(contents='xyz'))
        >>> TextDocument.split_fragment(Sentence("abcxyz", [Message("out")], []), 3)
        (Sentence(contents='abc', messages=[], goals=[]),
         Sentence(contents='xyz', messages=[Message(contents='out')], goals=[]))
        """
        before = cls._slice(fr.contents, slice(0, cutoff))
        after = cls._slice(fr.contents, slice(cutoff, None))
        fr0: Fragment
        if isinstance(fr, Text):
            fr0 = Text(before)
        else:
            fr0 = Sentence(before, messages=[], goals=[])
        return fr0, fr._replace(contents=after)

    @classmethod
    def split_fragments(cls, fragments, cutoffs):
        """Split `fragments` at positions `cutoffs`.

        >>> list(TextDocument.split_fragments([Text("abcdwxyz")], [0, 2, 4, 5, 7]))
        [Text(contents='ab'), Text(contents='cd'),
         Text(contents='w'), Text(contents='xy'), Text(contents='z')]
        >>> list(TextDocument.split_fragments([Text("abcd"), Text("wxyz")], [0, 2, 4, 5, 7]))
        [Text(contents='ab'), Text(contents='cd'),
         Text(contents='w'), Text(contents='xy'), Text(contents='z')]
        """
        fragments = deque(cls.with_boundaries(fragments))
        for cutoff in cutoffs:
            while fragments and fragments[0].end <= cutoff:
                yield fragments.popleft().e
            if fragments and fragments[0].beg < cutoff < fragments[0].end:
                before, after = cls.split_fragment(fragments[0].e, cutoff - fragments[0].beg)
                fragments[0] = replace(fragments[0], beg=cutoff, e=after)
                yield before
        for fr in fragments:
            yield fr.e

    @classmethod
    def _recover_chunks(cls, chunks: Iterable[str],
                        fragments: Iterable[Union[Sentence, Text]]):
        frs = deque(cls.with_boundaries(fragments))
        for chunk in cls.with_boundaries(chunks):
            chunk_frs = []
            if frs:
                assert frs[0].beg >= chunk.beg
            while frs and frs[0].end <= chunk.end:
                chunk_frs.append(frs.popleft().e)
            if frs and frs[0].beg < chunk.end < frs[0].end:
                cutoff = chunk.end - frs[0].beg
                before, after = cls.split_fragment(frs[0].e, cutoff)
                frs[0] = replace(frs[0], beg=chunk.end, e=after)
                chunk_frs.append(before)
            assert chunk.e == chunk.e[0:0].join(c.contents for c in chunk_frs)
            yield chunk_frs
        assert not frs

    @classmethod
    def strip_separators(cls, grouped, separator):
        r"""Remove separator at end of each fragment in `grouped`.
        >>> list(TextDocument.strip_separators([[Text("!"), Text("(* … *)\n")]], "\n"))
        [[Text(contents='!'), Text(contents='(* … *)')]]
        >>> list(TextDocument.strip_separators([[Text("A"), Text("\n")]], "\n"))
        [[Text(contents='A')]]
        >>> list(TextDocument.strip_separators([[Text("\n")]], "\n"))
        [[]]
        """
        for fragments in grouped:
            if fragments:
                assert fragments[-1].contents.endswith(separator)
                contents = fragments[-1].contents[:-len(separator)]
                fragments[-1] = fragments[-1]._replace(contents=contents)
                if isinstance(fragments[-1], Text) and not contents:
                    fragments.pop()
            yield fragments

class TextDocument(Document):
    @classmethod
    def _len(cls, s: str) -> int:
        return len(s)

    @classmethod
    def _slice(cls, s: str, index: slice) -> str:
        return s[index]

    def __getitem__(self, index) -> str:
        return self.str.__getitem__(index)

    def __len__(self) -> int:
        return len(self.str)

    _BOL = re.compile("^", re.MULTILINE)
    def _find_bols(self) -> Iterable[int]:
        return (m.start() for m in self._BOL.finditer(self.str))

    _EOL = re.compile("$", re.MULTILINE)
    def _find_eol(self, start: int) -> int:
        return must(self._EOL.search(self.str, pos=start)).start()

    def _decode_column(self, pos: Position):
        return pos

class EncodedDocument(Document):
    """Variant of ``Document`` in which positions are byte offsets, not char offsets."""
    ENCODING: ClassVar[str]

    def __init__(self, chunks, chunk_separator):
        super().__init__(chunks, chunk_separator)
        self.bytes = self.str.encode(self.ENCODING)

    @classmethod
    def _len(cls, s: str) -> int:
        return len(s.encode(cls.ENCODING))

    @classmethod
    def _slice(cls, s: str, index: slice) -> str:
        return s.encode(cls.ENCODING)[index].decode(cls.ENCODING)

    def __getitem__(self, index):
        return self.bytes.__getitem__(index).decode(self.ENCODING)

    def __len__(self) -> int:
        return len(self.bytes)

    _BOL = re.compile(b"^", re.MULTILINE)
    def _find_bols(self) -> Iterable[int]:
        return (m.start() for m in self._BOL.finditer(self.bytes))

    _EOL = re.compile(b"$", re.MULTILINE)
    def _find_eol(self, start: int) -> int:
        return must(self._EOL.search(self.bytes, pos=start)).start()

    def _decode_column(self, pos: Position) -> Position:
        """Translate the ``column`` part of `pos` to a character offset."""
        assert pos.col is not None
        line_start = self.bol_offsets[pos.line - 1]
        text_col = len(self[line_start:line_start + pos.col])
        return pos._replace(col=text_col)

class UTF8Document(EncodedDocument):
    ENCODING = "utf-8"

class Notification(NamedTuple):
    obj: Any
    message: str
    location: Optional[Range]
    level: int

    def as_text(self):
        header = self.location.as_header() if self.location else "!!"
        message = re.sub("\n(?!$)", "\n   ", self.message.rstrip(), flags=re.MULTILINE)
        LEVELS = {0: "DEBUG", 1: "INFO", 2: "WARNING", 3: "ERROR", 4: "SEVERE"}
        return f"{header} ({LEVELS.get(self.level, '??')}/{self.level}) {message}"

    def as_docutils(self):
        dc = self.location.as_docutils() if self.location else {}
        return {"level": self.level, "message": self.message, **dc}

    @classmethod
    def of_docutils(cls, message, level, n):
        return cls(None, message, Range.of_docutils(n), level)

class Observer:
    def __init__(self):
        self.exit_code = 0

    def _notify(self, n: Notification):
        raise NotImplementedError()

    def notify(self, obj: Any, message: str, location: Optional[Range], level: int):
        self.exit_code = max(self.exit_code, level)
        self._notify(Notification(obj, message, location, level))

class StderrObserver(Observer):
    def _notify(self, n: Notification):
        sys.stderr.write(n.as_text())
        sys.stderr.write("\n")

PrettyPrinted = namedtuple("PrettyPrinted", "sid pp")

class Driver():
    ID: ClassVar[str]
    LANGUAGE: ClassVar[str | None]

    def __init__(self, args: Tuple[str, ...]=(), fpath: _Path="-"):
        assert fpath != ''
        self.observer: Observer = StderrObserver()
        self.fpath: Path = Path(fpath)
        self.user_args: Tuple[str, ...] = args

    @classmethod
    def autoselect(cls) -> bool:
        """Check whether this driver may be auto-selected and can be used."""
        return False

    @property
    def metadata(self):
        return {"args": self.user_args}

    def version_info(self) -> DriverInfo:
        raise NotImplementedError()

    def annotate(self, chunks: list[str]) -> List[List[Fragment]]:
        """Annotate multiple `chunks` of code.

        All fragments are executed in the same (fresh) prover instance.  The
        return value is a list with as many elements as in `chunks`, but each
        element is a list of fragments: either ``Text`` instances (whitespace
        and comments) or ``Sentence`` instances (code).
        """
        raise NotImplementedError()

class CLIDriver(Driver): # pylint: disable=abstract-method
    BIN: ClassVar[str]
    NAME: ClassVar[str]
    AUTOSELECT: ClassVar[bool]

    CLI_ARGS: ClassVar[Tuple[_Path, ...]] = ()
    VERSION_ARGS: ClassVar[Tuple[_Path, ...]] = ("--version",)

    CLI_ENCODING: ClassVar[str | None] = "utf-8"

    def __init__(self, args=(), fpath="-", binpath: str | None=None):
        super().__init__(args, fpath)
        self.binpath = binpath

    @classmethod
    def autoselect(cls) -> bool:
        return cls.AUTOSELECT and (which(cls.BIN) is not None)

    def version_info(self) -> DriverInfo:
        bs = subprocess.check_output([*self.resolve_driver(), *self.VERSION_ARGS])
        return DriverInfo(self.NAME, bs.decode('ascii', 'ignore').strip())

    @classmethod
    def driver_not_found(cls, binpath) -> NoReturn:
        """Raise an error to indicate that ``binpath`` cannot be found."""
        raise ValueError("{} binary not found (bin={!r}).".format(cls.NAME, binpath))

    @classmethod
    def _which(cls, path: str) -> str:
        if (resolved := which(path)) is None:
            cls.driver_not_found(path)
        return resolved

    def resolve_driver(self) -> list[_Path]:
        return [self._which(self.binpath or self.BIN)]

    @staticmethod
    def _debug_start(cmd):
        debug(" ".join(quote(str(s)) for s in cmd), '# ')

    @classmethod
    def _proc_out(cls, p: CompletedProcess) -> str:
        return str(p.stderr)

    def run_cli(self, cwd=None, more_args=(), input=None, capture_output=True):
        driver = self.resolve_driver()
        cmd: list[_Path] = [*driver, *self.CLI_ARGS, *self.user_args, *more_args]
        self._debug_start(cmd)
        p = subprocess.run(cmd, cwd=cwd, input=input,
                           stderr=subprocess.PIPE,
                           stdout=subprocess.PIPE if capture_output else None,
                           check=False, **({"encoding": self.CLI_ENCODING} if self.CLI_ENCODING else {}))
        if p.returncode != 0:
            MSG = "Driver {} ({}) exited with code {}:\n{}"
            raise ValueError(MSG.format(self.NAME, driver, p.returncode, self._proc_out(p)))
        return p.stdout

class PopenDriver(CLIDriver): # pylint: disable=abstract-method
    REPL_ARGS: ClassVar[Tuple[str, ...]] = ()
    REPL_ENCODING: str | None = None

    def __init__(self, args=(), fpath="-", binpath=None):
        super().__init__(args, fpath, binpath)
        self.repl = None
        self.instance_args: Tuple[str, ...] = ()

    def __enter__(self):
        assert not self.repl
        self.reset()
        return self

    def __exit__(self, *_exn):
        self.kill()
        return False

    def kill(self):
        """Terminate this prover instance."""
        if not self.repl:
            return
        assert self.repl.stdin and self.repl.stdout
        self.repl.kill()
        try:
            self.repl.stdin.close()
            self.repl.stdout.close()
        except OSError:
            pass
        finally:
            self.repl.wait()
            self.repl = None

    def _start(self, stdin: _FILE=PIPE, stderr: _FILE=PIPE, stdout: _FILE=PIPE, more_args=()):
        cmd = [*self.resolve_driver(),
               *self.REPL_ARGS, *self.user_args, *self.instance_args, *more_args]
        self._debug_start(cmd)
        return subprocess.Popen(cmd, stdin=stdin, stderr=stderr, stdout=stdout, encoding=self.REPL_ENCODING)

    def reset(self):
        """Start or restart this prover instance."""
        self.kill()
        self.repl = self._start(stderr=None)

class REPLDriver(PopenDriver): # pylint: disable=abstract-method
    def _read(self):
        assert self.repl and self.repl.stdout
        response = self.repl.stdout.readline()
        debug(response, '<< ')
        return response

    def _write(self, s, end):
        assert self.repl and self.repl.stdin
        debug(s, '>> ')
        self.repl.stdin.write(s + end)  # type: ignore
        self.repl.stdin.flush()

DRIVERS_BY_LANGUAGE = {
    "coq": {
        "vsrocq": (".vsrocq", "VsRocq"),
        "sertop": (".serapi", "SerAPI"),
        "coqlsp": (".coqlsp", "CoqLSP"),
        "sertop_noexec": (".serapi", "SerAPI_noexec"),
        "coqc_time": (".coqc_time", "CoqcTime"),
        "noop": (".noop", "NoOp")
    },
    "dafny": {
        "dafny_lsp": (".dafny", "DafnyLSP"),
        "noop": (".noop", "NoOp")
    },
    "lean3": {
        "lean3_repl": (".lean3", "Lean3"),
        "noop": (".noop", "NoOp")
    },
    "lean4": {
        "leanInk": (".lean4", "Lean4"),
        "noop": (".noop", "NoOp")
    },
}
"""A map from language identifiers to dictionaries of drivers.

Keys in the driver dictionary are driver names; values are pairs of module names
and class names.  In other words, each driver is a class within a module.
"""

class DriverDict(UserDict[str, str]): # UserDict needed for proper ``copy`` behavior
    """Subclass of ``dict`` for loading Alectryon drivers on demand."""
    def __missing__(self, lang: str):
        """Find the first available driver in ``DRIVERS_BY_LANGUAGE``.
        If none can be found, return the first driver."""
        all_drivers = DRIVERS_BY_LANGUAGE[lang]
        for driver in all_drivers:
            debug(f"autoselect: Trying to select {driver} for {lang}", prefix="# ")
            if resolve_driver(lang, driver).autoselect():
                self[lang] = driver
                return driver
        return next(iter(all_drivers)) # Return first if none is available (for better error messages)

ALL_MARKUPS = {"md", "rst"}
ALL_LANGUAGES = DRIVERS_BY_LANGUAGE.keys()
ALL_DRIVERS = {d for ds in DRIVERS_BY_LANGUAGE.values() for d in ds}
DEFAULT_DRIVERS = DriverDict()

EXTENSIONS_BY_LANGUAGE = {
    "coq": (".v",),
    "dafny": (".dfy",),
    "lean3": (".lean3", ".lean"),
    "lean4": (".lean",),
}
"""A map from language identifiers to file extensions.

Later entries take precedence over previous ones.
"""
assert EXTENSIONS_BY_LANGUAGE.keys() == ALL_LANGUAGES

EXTENSIONS_BY_MARKUP = {
    "md": (".md", ".myst",),
    "rst": (".rst",),
}
"""A map from markup language identifiers to file extensions."""
assert EXTENSIONS_BY_MARKUP.keys() == ALL_MARKUPS

DEFAULT_MARKUP = "rst"
"""The default markup, assumed when the suffix of a file name doesn't allow us to guess."""

def resolve_driver(input_language: str, driver_name: str) -> type[Driver]:
    if input_language not in DRIVERS_BY_LANGUAGE:
        raise ValueError("Unknown language: {}".format(input_language))
    known_drivers = DRIVERS_BY_LANGUAGE[input_language]
    if driver_name not in known_drivers:
        MSG = "Unknown driver for language {}: {}"
        raise ValueError(MSG.format(input_language, driver_name))
    mod, cls = known_drivers[driver_name]
    return getattr(import_module(mod, __package__), cls)

@dataclass
class DriverConfig:
    lang: str
    drivers: dict[str, str]
    driver_args: dict[str, tuple[str, ...]]
    used: bool = False

    def init_driver(self, fpath: _Path) -> Driver:
        self.used = True
        name = self.drivers[self.lang]
        args = self.driver_args.get(name, ())
        driver_cls = resolve_driver(self.lang, name)
        assert driver_cls.LANGUAGE in (self.lang, None)
        assert name == driver_cls.ID
        return driver_cls(args, fpath=fpath)
