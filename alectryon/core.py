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

from typing import Any, ClassVar, DefaultDict, Dict, Generic, Iterable, IO, List, \
    NamedTuple, NoReturn, Optional, Tuple, TypeVar, Union

from collections import deque, namedtuple, defaultdict
from contextlib import contextmanager
from importlib import import_module
from pathlib import Path
from shlex import quote
from shutil import which
from subprocess import PIPE
import os
import re
import subprocess
import sys
import textwrap

_FILE = Union[None, int, IO[Any]]

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
    if isinstance(v, (bytes, bytearray)):
        v = v.decode("utf-8", errors="replace")
    if DEBUG:
        print(indent(str(v).rstrip(), prefix), flush=True)

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

def _enrich(nt):
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
def cwd(wd: Union[str, os.PathLike]):
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
    def __new__(cls, fname, _gen=None):
        return super().__new__(cls, fname)

    def __init__(self, _fname, gen=lambda _: ""):
        super().__init__()
        self.gen = gen

class Position(NamedTuple):
    fpath: Union[str, Path]
    line: int # 1-based
    col: int # 0-based

    def as_range(self):
        return Range(self, None)

    @classmethod
    def of_lsp(cls, fpath: Union[str, Path], js: dict[str, Any]):
        return Position(fpath, js["line"] + 1, js["character"])

    def to_lsp(self):
        return { "line": self.line - 1, "character": self.col }

class Range(NamedTuple):
    beg: Position
    end: Optional[Position]

    def as_header(self):
        assert self.end is None or self.beg.fpath == self.end.fpath
        beg = "{}:{}".format(self.beg.line, self.beg.col)
        end = "{}:{}".format(self.end.line, self.end.col) if self.end else ""
        pos = ("({})-({})" if end else "{}:{}").format(beg, end)
        return "{}:{}:".format(self.beg.fpath or "<unknown>", pos)

    @classmethod
    def of_lsp(cls, fpath: Union[str, Path], js: dict[str, Any]):
        return cls(Position.of_lsp(fpath, js["start"]),
                   Position.of_lsp(fpath, js["end"]))

class PosStr(str):
    def __new__(cls, s, *_args):
        return super().__new__(cls, s)

    def __init__(self, _s, pos, col_offset):
        super().__init__()
        self.pos, self.col_offset = pos, col_offset

class View(bytes):
    def __getitem__(self, key):
        return memoryview(self).__getitem__(key)

    def __init__(self, s):
        super().__init__()
        self.s = s

class PosView(View):
    NL = b"\n"

    def __new__(cls, s):
        bs = s.encode("utf-8")
        # https://stackoverflow.com/questions/20221858/
        return super().__new__(cls, bs) if isinstance(s, PosStr) else View(bs)

    def __init__(self, s):
        super().__init__(s)
        self.pos, self.col_offset = s.pos, s.col_offset

    def __getitem__(self, key):
        return memoryview(self).__getitem__(key)

    def translate_offset(self, offset):
        r"""Translate a character-based `offset` into a (line, column) pair.
        Columns are 1-based.

        >>> text = "abc\ndef\nghi"
        >>> s = PosView(PosStr(text, Position("f", 3, 2), 5))
        >>> s.translate_offset(0)
        Position(fpath='f', line=3, col=2)
        >>> s.translate_offset(10) # col=3, + offset (5) = 8
        Position(fpath='f', line=5, col=8)
        """
        nl = self.rfind(self.NL, 0, offset)
        if nl == -1: # First line
            line, col = self.pos.line, self.pos.col + offset
        else:
            line = self.pos.line + self.count(self.NL, 0, offset)
            prefix = bytes(self[nl+1:offset]).decode("utf-8", 'ignore')
            col = 1 + self.col_offset + len(prefix)
        return Position(self.pos.fpath, line, col)

    def translate_span(self, beg, end):
        return Range(self.translate_offset(beg),
                     self.translate_offset(end))

TPositioned = TypeVar("TPositioned", covariant=True)
class Positioned(NamedTuple, Generic[TPositioned]):
    beg: int
    end: int
    e: TPositioned

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
        self._bol_offsets = None

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

    def recover_chunks(self, fragments):
        grouped = self._recover_chunks(self.with_separator, fragments)
        return self.strip_separators(grouped, self.separator)

    @property
    def bol_offsets(self):
        if self._bol_offsets is None:
            self._bol_offsets = list(self._find_bols())
        return self._bol_offsets

    def offset2lc(self, offset) -> Tuple[int, int]:
        import bisect
        line = bisect.bisect_right(self.bol_offsets, offset)
        bol = self.bol_offsets[line - 1]
        return line, offset - bol

    def lc2offset(self, line: int, col: int) -> int:
        assert line >= 1
        return self.bol_offsets[line - 1] + col

    def offset2pos(self, fpath: Union[str, Path], offset: int) -> Position:
        return Position(fpath, *self.offset2lc(offset))

    def pos2offset(self, pos: Position) -> int:
        return self.lc2offset(pos.line, pos.col)

    def offsets2range(self, fpath: Union[str, Path], beg: int, end: int) -> Range:
        return Range(self.offset2pos(fpath, beg), self.offset2pos(fpath, end))

    def range2offsets(self, range: Range) -> Tuple[int, int]:
        beg = self.pos2offset(range.beg)
        end = self.pos2offset(range.end) if range.end else self._find_eol(beg)
        return beg, end

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

    TItem = TypeVar("TItem", bound=Union[Sentence, Text, str])
    @classmethod
    def with_boundaries(cls, items: Iterable[TItem]) -> Iterable[Positioned[TItem]]:
        end = 0
        for item in items:
            beg, end = end, end + cls._len(item if isinstance(item, str) else item.contents)
            yield Positioned(beg, end, item)

    @classmethod
    def split_fragment(cls, fr: Fragment, cutoff):
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
                fragments[0] = fragments[0]._replace(beg=cutoff, e=after)
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
                frs[0] = frs[0]._replace(beg=chunk.end, e=after)
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
        matches = self._BOL.finditer(self.str)
        return (m.start() for m in matches)

    _EOL = re.compile("$", re.MULTILINE)
    def _find_eol(self, start: int) -> int:
        return must(self._EOL.search(self.str, pos=start)).start()

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
        matches = self._BOL.finditer(self.bytes)
        matches = list(matches)
        return (m.start() for m in matches)

    _EOL = re.compile(b"$", re.MULTILINE)
    def _find_eol(self, start: int) -> int:
        return must(self._EOL.search(self.bytes, pos=start)).start()

class UTF8Document(EncodedDocument):
    ENCODING = "utf-8"

class Notification(NamedTuple):
    obj: Any
    message: str
    location: Optional[Range]
    level: int

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
        header = n.location.as_header() if n.location else "!!"
        message = n.message.rstrip().replace("\n", "\n   ")
        level_name = {1: "INFO", 2: "WARNING", 3: "ERROR"}.get(n.level, "??")
        sys.stderr.write("{} ({}/{}) {}\n".format(header, level_name, n.level, message))

PrettyPrinted = namedtuple("PrettyPrinted", "sid pp")

class Driver():
    ID: ClassVar[str]

    def __init__(self, args: Tuple[str, ...]=(), fpath: str="-"):
        self.observer: Observer = StderrObserver()
        self.fpath = Path(fpath)
        self.user_args = args

    @property
    def metadata(self):
        return {"args": self.user_args}

    def version_info(self) -> DriverInfo:
        raise NotImplementedError()

    def annotate(self, chunks: Iterable[str]) -> List[List[Fragment]]:
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

    CLI_ARGS: Tuple[str, ...] = ()
    VERSION_ARGS: Tuple[str, ...] = ("--version",)

    CLI_ENCODING = "utf-8"

    def __init__(self, args=(), fpath="-", binpath=None):
        super().__init__(args, fpath)
        self.binpath: str = binpath or self.BIN

    def version_info(self) -> DriverInfo:
        bs = subprocess.check_output([self.resolve_driver(), *self.VERSION_ARGS])
        return DriverInfo(self.NAME, bs.decode('ascii', 'ignore').strip())

    @classmethod
    def driver_not_found(cls, binpath) -> NoReturn:
        """Raise an error to indicate that ``binpath`` cannot be found."""
        raise ValueError("{} binary not found (bin={!r}).".format(cls.NAME, binpath))

    def resolve_driver(self) -> str:
        path: Optional[str] = which(self.binpath)
        if path is None:
            self.driver_not_found(self.binpath)
        return path

    @staticmethod
    def _debug_start(cmd):
        debug(" ".join(quote(s) for s in cmd), '# ')

    @classmethod
    def _proc_out(cls, p):
        return p.stderr

    def run_cli(self, working_directory=None, capture_output=True, more_args=()):
        cmd = [self.resolve_driver(),
               *self.CLI_ARGS, *self.user_args, *more_args]
        self._debug_start(cmd)
        p = subprocess.run(cmd, cwd=working_directory,
                           stderr=subprocess.PIPE,
                           stdout=subprocess.PIPE if capture_output else None,
                           check=False, encoding=self.CLI_ENCODING)
        if p.returncode != 0:
            MSG = "Driver {} ({}) exited with code {}:\n{}"
            raise ValueError(MSG.format(self.NAME, self.binpath, p.returncode,
                                        indent(self._proc_out(p), "   ")))
        return p.stdout

class PopenDriver(CLIDriver): # pylint: disable=abstract-method
    REPL_ARGS: Tuple[str, ...] = ()
    REPL_ENCODING = None

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
        if self.repl:
            self.repl.kill()
            try:
                assert self.repl and self.repl.stdin and self.repl.stdout
                self.repl.stdin.close()
                self.repl.stdout.close()
            finally:
                self.repl.wait()

    def _start(self, stdin: _FILE=PIPE, stderr: _FILE=PIPE, stdout: _FILE=PIPE, more_args=()):
        cmd = [self.resolve_driver(),
               *self.REPL_ARGS, *self.user_args, *self.instance_args, *more_args]
        self._debug_start(cmd)
        return subprocess.Popen(cmd, stdin=stdin, stderr=stderr, stdout=stdout, encoding=self.REPL_ENCODING)

    def reset(self):
        """Start or restart this prover instance."""
        self.kill()
        self.repl = self._start(stderr=None)

class REPLDriver(PopenDriver):
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
        "sertop": (".serapi", "SerAPI"),
        "sertop_noexec": (".serapi", "SerAPI_noexec"),
        "coqc_time": (".coqc_time", "CoqcTime"),
        "coq_lsp": (".coqlsp", "CoqLSP"),
        "vsrocq": (".vsrocq", "VsRocq"),
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

ALL_MARKUPS = {"md", "rst"}
ALL_LANGUAGES = DRIVERS_BY_LANGUAGE.keys()
ALL_DRIVERS = {d for ds in DRIVERS_BY_LANGUAGE.values() for d in ds}
DEFAULT_DRIVERS = {lang: next(iter(drivers)) for lang, drivers in DRIVERS_BY_LANGUAGE.items()}

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
    "md": (".md",),
    "rst": (".rst",),
}
"""A map from markup language identifiers to file extensions."""
assert EXTENSIONS_BY_MARKUP.keys() == ALL_MARKUPS

DEFAULT_MARKUP = "rst"
"""The default markup, assumed when the extension of a file doesn't allow us to guess."""

def resolve_driver(input_language, driver_name):
    if input_language not in DRIVERS_BY_LANGUAGE:
        raise ValueError("Unknown language: {}".format(input_language))
    known_drivers = DRIVERS_BY_LANGUAGE[input_language]
    if driver_name not in known_drivers:
        MSG = "Unknown driver for language {}: {}"
        raise ValueError(MSG.format(input_language, driver_name))
    mod, cls = known_drivers[driver_name]
    return getattr(import_module(mod, __package__), cls)

class DriverConfig:
    def __init__(self, lang, language_drivers, driver_args_by_name):
        self.lang = lang
        self.name = language_drivers.get(lang)
        self.args = driver_args_by_name.get(self.name, ())
        self.used = False

    def init_driver(self, fpath):
        self.used = True
        driver_cls = resolve_driver(self.lang, self.name)
        assert self.lang == driver_cls.LANGUAGE
        assert self.name == driver_cls.ID
        return driver_cls(self.args, fpath=fpath)
