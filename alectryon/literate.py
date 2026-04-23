#!/usr/bin/env python3

from typing import Callable, Deque, Dict, Iterable, Iterator, List, Match, \
    MutableSequence, Optional, Pattern, Tuple, Type, Union, \
    NamedTuple, Sequence, cast

import re
from enum import Enum
from itertools import groupby
from collections import namedtuple, deque

## Utilities
## =========

class StringView:
    r"""A view of a string slice."""
    def __init__(self, s: str, beg=0, end=None):
        """Create a view of s[beg:end]."""
        assert isinstance(s, str)
        end = end if end is not None else len(s)
        self.s, self.beg, self.end = s, beg, end
        assert self.beg <= self.end <= len(s)

    def __len__(self):
        return self.end - self.beg

    def __bool__(self):
        return len(self) > 0

    def __getitem__(self, idx) -> "StringView":
        """Slice from this view.

        >>> sv = StringView("abcdefghijkl", 3, 10)
        >>> str(sv[:2]), str(sv[4:])
        ('de', 'hij')
        >>> str(sv[-2:]), str(sv[-100:])
        ('ij', 'defghij')
        """
        if isinstance(idx, slice):
            start = idx.start or 0
            beg = max(self.beg, self.end + start) if start < 0 else min(self.beg + start, self.end)
            if idx.stop is None:
                end = self.end
            elif idx.stop < 0:
                end = max(self.beg, self.end + idx.stop)
            else:
                end = min(self.end, self.beg + idx.stop)
            return StringView(self.s, beg, end)
        assert 0 <= idx < len(self)
        idx = min(self.beg + idx, self.end)
        return StringView(self.s, idx, idx + 1)

    def __add__(self, other) -> "StringView":
        if self.s is not other.s:
            raise ValueError("Cannot concatenate {!r} and {!r}".format(self, other))
        if self.end != other.beg:
            raise ValueError("Cannot concatenate [{}:{}] and [{}:{}]".format(
                self.beg, self.end, other.beg, other.end))
        return StringView(self.s, self.beg, other.end)

    def __contains__(self, other):
        return self.s.find(other, self.beg, self.end) >= 0

    def __str__(self) -> str:
        return self.s[self.beg:self.end]

    def __iter__(self):
        """Iterate over this view's characters.

        >>> list(StringView("01234", 1, 3))
        ['1', '2']
        """
        for idx in range(self.beg, self.end):
            yield self.s[idx]

    def __repr__(self):
        return repr(str(self))

    def split(self, sep: str, nsplits=None, keepsep=False) -> List["StringView"]:
        r"""Split this view on `sep`.

        >>> sv = StringView("a\nbc\ndef\ng\nhi", 2, 12)
        >>> [str(p) for p in sv.split("\n", keepsep=True)]
        ['bc\n', 'def\n', 'g\n', 'h']
        """
        assert sep, "Empty separator"
        beg = self.beg
        chunks: List[StringView] = []
        while beg <= self.end:
            end = self.s.find(sep, beg, self.end)
            if end < 0 or nsplits and len(chunks) == nsplits:
                end = sep_end = self.end
            else:
                sep_end = end + len(sep)
            chunks.append(StringView(self.s, beg, sep_end if keepsep else end))
            beg = end + len(sep)
        return chunks

    def match(self, regexp: Pattern[str]) -> Optional[re.Match]:
        return regexp.match(self.s, self.beg, self.end)

    def search(self, regexp: Pattern[str]) -> Optional[re.Match]:
        return regexp.search(self.s, self.beg, self.end)

    def trim(self, beg=None, end=None):
        v = self
        b = beg and v.match(beg)
        if b:
            v = v[len(b.group()):]
        e = end and v.search(end)
        if e:
            v = v[:-len(e.group())]
        return v

    SPACES = re.compile(r"\s*\Z")
    def isspace(self):
        return bool(self.match(StringView.SPACES))

class Line:
    def __init__(self, num: int, parts: List[StringView]):
        assert not parts or any(parts), \
            f"Line must not have all-empty parts: {parts!r}"
        self.num = num
        self.parts = parts

    def __repr__(self):
        return f"{type(self).__name__}({self.num}, {self.parts!r})"

    @classmethod
    def of_parts(cls, l: List[StringView]):
        return cls(-1, l)

    @classmethod
    def of_view(cls, v: StringView):
        return cls.of_parts([v])

    @classmethod
    def of_str(cls, s: str):
        return cls.of_view(StringView(s + "\n"))

    def __len__(self):
        """Compute the number of characters in `self`.
        >>> len(Line.of_parts([StringView("abc", 0, 1), StringView("123", 1, 3)]))
        3
        """
        return sum(len(p) for p in self.parts)

    def __bool__(self):
        return not self.isspace()

    def __str__(self):
        return "".join(str(p) for p in self.parts)

    def __iter__(self):
        """Iterate over this line's characters.

        >>> list(Line.of_parts([StringView("abc", 0, 1), StringView("123", 1, 3)]))
        ['a', '2', '3']
        """
        for part in self.parts:
            yield from part

    def __contains__(self, s):
        assert len(self.parts) <= 1 # Would need to concatenate ``.parts`` otherwise
        return any(s in p for p in self.parts)

    def isspace(self):
        return all(p.isspace() for p in self.parts)

    def dedent(self, n: int):
        for idx, p in enumerate(self.parts):
            if n < 0:
                break
            self.parts[idx] = p[n:]
            n -= len(p)
        return self

    def __radd__(self, other: str) -> "Line":
        if not isinstance(other, str):
            return NotImplemented
        s = StringView(other, 0, len(other))
        return self._replace_parts(parts = [s] + self.parts)

    def __iadd__(self, other: str) -> "Line":
        if not isinstance(other, str):
            return NotImplemented
        self.parts.append(StringView(other))
        return self

    def replace(self, src: str, dst: str) -> "Line":
        parts: List[StringView] = []
        for part in self.parts:
            for idx, p in enumerate(part.split(src)):
                if idx > 0:
                    parts.append(StringView(dst))
                parts.append(p)
        return self._replace_parts(parts=parts)

    @staticmethod
    def replacen(line: "Line", pairs) -> "Line":
        for src, dst in pairs:
            line = line.replace(src, dst) # type: ignore
        return line

    def match(self, regex: Pattern[str]) -> Optional[Match]:
        assert len(self.parts) == 1, f"Cannot call `match()` on {self!r}."
        return self.parts[0].match(regex)

    # _replace from NamedTuple doesn't work because of __len__ above
    def _replace_parts(self, parts: List[StringView]) -> "Line": # pylint: disable=arguments-differ
        # ``Line`` (not ``type(self)``), since we can't change the parts of an ``EmptyLine``.
        return Line(self.num, parts)

class EmptyLine(Line):
    """A subclass used to track empty lines added by Alectryon."""
    def __init__(self, num=-1):
        super().__init__(num, [StringView("\n")])

def strip_deque(lines: Deque[Line]) -> Deque[Line]:
    while lines and lines[0].isspace():
        lines.popleft()
    while lines and lines[-1].isspace():
        lines.pop()
    return lines

def _source_parts(lines: Iterable[Line], source: str):
    """Yield ``(line, part_index, part)`` from lines.

    Only yield parts that are views into `source`, skipping synthetic parts
    (e.g. comment delimiters).
    """
    for l in lines:
        for idx, p in enumerate(l.parts):
            if p.s is source:
                yield l, idx, p

def mark_point(lines: Iterable[Line], point: Optional[int], marker: Optional[str], source: str) -> List[Line]:
    lines = list(lines)
    if point is None:
        return lines
    assert marker
    last_line_with_parts = None
    for l, idx, p in _source_parts(lines, source):
        if p.end >= point:
            cutoff = max(0, min(point - p.beg, len(p)))
            l.parts[idx:idx+1] = [p[:cutoff], StringView(marker), p[cutoff:]]
            return lines
        last_line_with_parts = l
    if last_line_with_parts:
        last_line_with_parts += marker
    else: # All lines are empty and will be trimmed; append a new one
        lines.append(Line.of_str(marker))
    return lines

def remove_consecutive_empty_lines(lines: Iterable[Line]):
    """Remove consecutive ``EmptyLine`` objects from `lines`.

    The converters below use ``EmptyLine`` instances to ensure that blocks are
    property separated from each other.  Extraneous blank lines are not an issue
    for the reST parser, but when generating user-facing markup or code it looks
    better to remove them.
    """
    prev: Optional[Line] = None
    for line in strip_deque(deque(lines)):
        if isinstance(prev, EmptyLine) and isinstance(line, EmptyLine):
            continue
        yield line
        prev = line

def _str_nl(l: Line) -> str:
    r"""Normalize a line `l` to a string ending with ``\n``."""
    s = "" if l.isspace() else str(l)
    return s if "\n" in s else s + "\n"

def join_lines(lines: Iterable[Line]) -> str:
    return "".join(_str_nl(l) for l in remove_consecutive_empty_lines(lines))

# Code → Markup
# =============

# Partitioning
# ------------

Code = namedtuple("Code", "v")
Comment = namedtuple("Comment", "v")
Classified = Union[Code, Comment]

class Token(str, Enum):
    ESCAPE = "ESCAPE"
    LINE_COMMENT_OPEN = "LINE_COMMENT_OPEN"
    COMMENT_OPEN = "COMMENT_OPEN"
    COMMENT_CLOSE = "COMMENT_CLOSE"
    STRING_ESCAPE = "STRING_ESCAPE"
    STRING_DELIM = "STRING_DELIM"
    EOF = "EOF"
    EOL = "EOL"

class State(str, Enum):
    CODE = "CODE"
    STRING = "STRING"
    COMMENT = "COMMENT"
    LINE_COMMENT = "LINE_COMMENT"
    NESTED_COMMENT = "NESTED_COMMENT"

def regexp_opt(tokens, token_regexps):
    labeled = ("(?P<{}>{})".format(tok.name, token_regexps[tok]) for tok in tokens)
    return re.compile("|".join(labeled), re.DOTALL)

class ParsingError(ValueError):
    def __init__(self, document, state, expected, position, end):
        super().__init__()
        self.document = document
        self.state = state
        self.expected = expected
        self.position, self.end = position, end
        self.line, self.column = self.line_col_of_pos(position)
        self.end_line, self.end_column = self.line_col_of_pos(end)

    def line_col_of_pos(self, pos):
        assert pos >= 0
        # TODO use the binary search code from core
        # Lines are 1-based, columns are 0-based
        bol = self.document.rfind("\n", 0, pos) + 1 # 0 if not found
        line = 1 + self.document.count("\n", 0, pos)
        column = pos - bol
        return line, column

    @property
    def message(self):
        expected_str = " or ".join(t.name for t in self.expected)
        MSG = "Unterminated {} (looking for {})"
        return MSG.format(self.state.name.lower(), expected_str)

    def __str__(self):
        return "{}:{}: {}".format(self.line, self.column, self.message)

class Parser:
    def __init__(self, doc: str):
        self.doc = doc

    def partition(self) -> Iterable[Classified]:
        """Partition ``self.doc`` into runs of ``Code`` and ``Comment`` objects."""
        raise NotImplementedError

class BlockParser(Parser):
    TRANSITIONS: Dict[State, Tuple[Token, ...]] = {}
    TOKEN_REGEXPS: Dict[Token, str] = {}

    def __init__(self, doc: str):
        super().__init__(doc)
        self.pos = 0
        self.spans: List[Classified] = []
        self.stack: List[Tuple[int, int, State]] = [(0, 0, State.CODE)]

    def step(self, state: State, start: int, tok: Token, mstart: int):
        raise NotImplementedError()

    def partition(self) -> List[Classified]:
        """Partition ``self.doc`` into runs of ``Code`` and ``Comment`` objects."""
        scanners = {state: regexp_opt(tokens, self.TOKEN_REGEXPS)
                    for (state, tokens) in self.TRANSITIONS.items()}
        while True:
            start, token_end, state = self.stack[-1]
            m = scanners[state].search(self.doc, self.pos)
            if not m:
                expected = self.TRANSITIONS[state]
                raise ParsingError(self.doc, state, expected, start, token_end)
            tok, mstart, self.pos = Token(m.lastgroup), m.start(), m.end()
            if not self.step(state, start, tok, mstart):
                break
        return self.spans

class LineParser(Parser):
    LIT_HEADER_RE: Pattern[str]

    @classmethod
    def _classify(cls, lines: List[StringView]) -> Iterator[Classified]:
        for line in lines:
            yield Comment(line) if line.match(cls.LIT_HEADER_RE) else Code(line)

    def partition(self) -> Iterator[Classified]:
        last = None
        for line in self._classify(StringView(self.doc).split("\n", keepsep=True)):
            if type(last) is type(line):
                assert last
                last = last._replace(v = last.v + line.v)
            else:
                if last and last.v:
                    yield last
                last = line
        if last and last.v:
            yield last

def partition(lang: "LangDef", code: str) -> Iterable[Classified]:
    return list(lang.parser(code).partition())

# Language definitions
# --------------------

class LangDef:
    def __init__(self, name: str, parser: Type[Parser]):
        self.name = name
        self.parser = parser

    def is_literate_comment(self, block: StringView) -> bool:
        raise NotImplementedError

    def wrap_literate(self, lines: Sequence[Line]) -> Iterable[Line]:
        raise NotImplementedError

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        raise NotImplementedError

    def escape(self, line: Line) -> Line:  # FIXME depends on the markup
        raise NotImplementedError

    def unescape(self, line: Line) -> Line:
        raise NotImplementedError

class BlockLangDef(LangDef):
    def __init__(self, name: str, parser: Type[Parser],
                 lit_open: str, lit_close: str,
                 lit_open_re: str, lit_close_re: str,
                 escape_pairs: List[Tuple[str, str]]):
        super().__init__(name, parser)
        self.lit_open, self.lit_close = lit_open, lit_close
        self.lit_open_re, self.lit_close_re = re.compile(lit_open_re), re.compile(lit_close_re)
        self.escape_pairs = escape_pairs
        self.unescape_pairs = [(dst, src) for (src, dst) in self.escape_pairs]

    def is_literate_comment(self, block: StringView) -> bool:
        return bool(block.match(self.lit_open_re))

    def wrap_literate(self, lines: Sequence[Line]) -> Iterable[Line]:
        if lines:
            yield Line.of_str(self.lit_open)
            yield from lines
            yield Line.of_str(self.lit_close)
        else:
            yield Line.of_str(self.lit_open + self.lit_close)

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        return split_lines(block.trim(self.lit_open_re, self.lit_close_re))

    def escape(self, line: Line) -> Line:
        return Line.replacen(line, self.escape_pairs)

    def unescape(self, line: Line) -> Line:
        return Line.replacen(line, self.unescape_pairs)

class LineLangDef(LangDef):
    def __init__(self, name: str, parser: Type[Parser],
                 lit_header: str, lit_header_re: Pattern[str]):
        super().__init__(name, parser)
        self.lit_header = lit_header
        self.lit_header_re = lit_header_re

    def is_literate_comment(self, block: StringView) -> bool:
        return True

    def wrap_literate(self, lines: Sequence[Line]) -> Iterable[Line]:
        if lines:
            for line in lines:
                yield self.lit_header + (" " if not line.isspace() else "") + line
        else:
            yield Line.of_str(self.lit_header)

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        for l in split_lines(block):
            yield l.trim(self.lit_header_re, None)

    def escape(self, line: Line) -> Line:
        return line

    def unescape(self, line: Line) -> Line:
        return line

class CoqParser(BlockParser):
    TRANSITIONS = {
        State.CODE: (Token.COMMENT_OPEN,
                     Token.STRING_DELIM,
                     Token.EOF),
        State.STRING: (Token.STRING_ESCAPE,
                       Token.STRING_DELIM,),
        State.COMMENT: (Token.COMMENT_OPEN,
                        Token.COMMENT_CLOSE,
                        Token.STRING_DELIM),
        State.NESTED_COMMENT: (Token.COMMENT_OPEN,
                               Token.COMMENT_CLOSE,
                               Token.STRING_DELIM)
    }

    TOKEN_REGEXPS = {
        Token.COMMENT_OPEN: r"[(][*]+(?![)])",
        Token.COMMENT_CLOSE: r"[*]+[)]",
        Token.STRING_ESCAPE: r'""',
        Token.STRING_DELIM: r'"',
        Token.EOF: r"(?!.)",
    }

    def step(self, state: State, start: int, tok: Token, mstart: int):
        """Partition ``self.doc`` into runs of ``Code`` and ``Comment`` objects.

        Example:
        >>> CoqParser("Code (* comment *) code").partition()
        [Code(v='Code '), Comment(v='(* comment *)'), Code(v=' code')]


        Tricky cases:
        >>> CoqParser("").partition()
        [Code(v='')]
        >>> CoqParser("(**)(***)").partition()
        [Code(v=''), Comment(v='(**)'), Code(v=''), Comment(v='(***)'), Code(v='')]
        >>> CoqParser("(*c*)(*c*c*)").partition()
        [Code(v=''), Comment(v='(*c*)'), Code(v=''), Comment(v='(*c*c*)'), Code(v='')]
        >>> CoqParser('C "(*" C "(*""*)" C').partition()
        [Code(v='C "(*" C "(*""*)" C')]
        >>> CoqParser('C (** "*)" *)').partition()
        [Code(v='C '), Comment(v='(** "*)" *)'), Code(v='')]
        """
        doc, pos, stack, spans = self.doc, self.pos, self.stack, self.spans
        if state is State.CODE:
            if tok is Token.COMMENT_OPEN:
                stack.pop()
                stack.append((mstart, pos, State.COMMENT))
                spans.append(Code(StringView(doc, start, mstart)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            elif tok is Token.EOF:
                stack.pop()
                spans.append(Code(StringView(doc, start, pos)))
                return False
            else:
                assert False
        elif state is State.STRING:
            if tok is Token.STRING_ESCAPE:
                pass
            elif tok is Token.STRING_DELIM:
                stack.pop()
            else:
                assert False
        elif state is State.COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, pos, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
                stack.append((pos, pos, State.CODE))
                spans.append(Comment(StringView(doc, start, pos)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            else:
                assert False
        elif state is State.NESTED_COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, pos, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            else:
                assert False
        else:
            assert False
        return True

class LeanParser(BlockParser):
    # TODO: Add support for char (``'"'``) syntax
    # TODO: Technically doc comments don't support nesting
    TRANSITIONS = {
        State.CODE: (Token.LINE_COMMENT_OPEN,
                     Token.COMMENT_OPEN,
                     Token.STRING_DELIM,
                     Token.EOF),
        State.STRING: (Token.ESCAPE,
                       Token.STRING_ESCAPE,
                       Token.STRING_DELIM,),
        State.LINE_COMMENT: (Token.EOL,),
        State.COMMENT: (Token.COMMENT_OPEN,
                        Token.COMMENT_CLOSE),
        State.NESTED_COMMENT: (Token.COMMENT_OPEN,
                               Token.COMMENT_CLOSE)
    }

    TOKEN_REGEXPS = {
        Token.LINE_COMMENT_OPEN: r"--",
        Token.COMMENT_OPEN: r"[/][-]+(?![/])",
        Token.COMMENT_CLOSE: r"[-]+[/]",
        Token.ESCAPE: r'\\\\',
        Token.STRING_ESCAPE: r'\\"',
        Token.STRING_DELIM: r'"',
        Token.EOF: r"(?!.)",
        Token.EOL: r"\n|(?!.)",
    }

    def step(self, state: State, start: int, tok: Token, mstart: int):
        r"""Partition ``self.doc`` into runs of ``Code`` and ``Comment`` objects.

        Example:
        >>> LeanParser("Code /- comment -/ code").partition()
        [Code(v='Code '), Comment(v='/- comment -/'), Code(v=' code')]
        >>> LeanParser("Code -- comment\nCode").partition()
        [Code(v='Code '), Comment(v='-- comment\n'), Code(v='Code')]


        Tricky cases:
        >>> LeanParser("").partition()
        [Code(v='')]
        >>> LeanParser("/--//---/").partition()
        [Code(v=''), Comment(v='/--/'), Code(v=''), Comment(v='/---/'), Code(v='')]
        >>> LeanParser("/-c-//-c*c-/").partition()
        [Code(v=''), Comment(v='/-c-/'), Code(v=''), Comment(v='/-c*c-/'), Code(v='')]
        >>> LeanParser('C "/-" C "/-""-/" C').partition()
        [Code(v='C "/-" C "/-""-/" C')]
        """
        doc, pos, stack, spans = self.doc, self.pos, self.stack, self.spans
        if state is State.CODE:
            if tok is Token.COMMENT_OPEN:
                stack.pop()
                stack.append((mstart, pos, State.COMMENT))
                spans.append(Code(StringView(doc, start, mstart)))
            elif tok is Token.LINE_COMMENT_OPEN:
                stack.pop()
                stack.append((mstart, pos, State.LINE_COMMENT))
                spans.append(Code(StringView(doc, start, mstart)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            elif tok is Token.EOF:
                stack.pop()
                spans.append(Code(StringView(doc, start, pos)))
                return False
            else:
                assert False
        elif state is State.STRING:
            if tok in (Token.ESCAPE, Token.STRING_ESCAPE):
                pass
            elif tok is Token.STRING_DELIM:
                stack.pop()
            else:
                assert False
        elif state is State.LINE_COMMENT:
            if tok is Token.EOL:
                stack.pop()
                stack.append((pos, pos, State.CODE))
                spans.append(Comment(StringView(doc, start, pos)))
            else:
                assert False
        elif state is State.COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, pos, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
                stack.append((pos, pos, State.CODE))
                spans.append(Comment(StringView(doc, start, pos)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            else:
                assert False
        elif state is State.NESTED_COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, pos, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, pos, State.STRING))
            else:
                assert False
        else:
            assert False
        return True

class DafnyParser(LineParser):
    r"""Line-based parser for Dafny.

    >>> list(DafnyParser("/// A\nB").partition())
    [Comment(v='/// A\n'), Code(v='B')]
    >>> list(DafnyParser("/// A\n/// A\nB\nB\n/// A\n").partition())
    [Comment(v='/// A\n/// A\n'), Code(v='B\nB\n'), Comment(v='/// A\n')]
    """
    LIT_HEADER_RE = re.compile("^[ \t]*///[ ]?", re.MULTILINE)

def measure_indentation(line: Line) -> int:
    """Compute the position of the first non-space character in `line`.

    >>> measure_indentation(Line.of_str(""))
    0
    >>> measure_indentation(Line.of_str("  "))
    2
    >>> measure_indentation(Line.of_str("  a"))
    2
    >>> measure_indentation(Line.of_parts([
    ...     StringView("abcd", 1, 1),
    ...     StringView("a  d", 1, 3),
    ...     StringView("a  d", 2, 3),
    ... ]))
    3
    """
    for idx, c in enumerate(line):
        if c != " ":
            return idx
    return len(line)

# Conversion
# ----------

class LitBlock(NamedTuple):
    lines: Deque[Line]
    indent: int
class CodeBlock(NamedTuple):
    directive: Sequence[Line]
    lines: Deque[Line]
    footer: Sequence[Line]
    indent: int
Block = Union[LitBlock, CodeBlock]
"""Blocks are a halfway point between the code and markup views of a document.

Once abstracted from its original syntax (code or prose), a document is just a
sequence of blocks, with all redundant directives removed, the code dedented,
comment markers removed, and literate comments unescaped.  Blocks are
constructed from ``ParsedLitBlock`` and ``ParsedCodeBlock`` objects, which are
generated either from prose or from code.

"""

class ParsedLitBlock(NamedTuple):
    footer: MutableSequence[Line]
    lines: Deque[Line]
    directive: Sequence[Line]
    body_indent: int
    directive_indent: int

    @staticmethod
    def of_lines(footer: MutableSequence[Line], lines: Deque[Line],
                 directive: Sequence[Line], last_indent: int) -> "ParsedLitBlock":
        strip_deque(lines)
        if lines:
            last_indent = measure_indentation(lines[-1])
        directive_indent = measure_indentation(directive[0]) if directive else last_indent
        return ParsedLitBlock(footer, lines, directive, last_indent, directive_indent)

class ParsedCodeBlock(NamedTuple):
    lines: Deque[Line]
ParsedBlock = Union[ParsedLitBlock, ParsedCodeBlock]

class MarkupParseState(NamedTuple):
    span: Tuple[int, int]
    directive: StringView
    code: StringView
    footer: StringView

class MarkupDef:
    name: str
    header: str

    def __init__(self, lang: LangDef):
        self.lang = lang

    def scan_markup(self, txt: str) \
        -> Iterator[MarkupParseState]:
        raise NotImplementedError

    def parse_lit(self, lines: Deque[Line], last_indent: int) \
        -> ParsedLitBlock:
        raise NotImplementedError

    def has_redundant_directive(self, block: ParsedLitBlock):
        raise NotImplementedError

    def indent_code(self, block: CodeBlock) -> Iterable[Line]:
        raise NotImplementedError

    def dedent_code(self, block: CodeBlock) -> Iterable[Line]:
        raise NotImplementedError

    def code_as_markup(self, block: CodeBlock) -> Iterable[Line]:
        raise NotImplementedError

    def wrap_code(self, block: CodeBlock) -> Iterable[Classified]:
        raise NotImplementedError

class RegexMarkup(MarkupDef):
    CODE_INDENT: int
    header_re: Pattern[str]
    directive_re: Pattern[str]

    def scan_markup(self, txt: str) -> Iterator[MarkupParseState]:
        for m in self.directive_re.finditer(txt):
            directive = StringView(txt, *m.span('directive'))
            code = StringView(txt, *m.span('code'))
            footer = StringView(txt, *m.span('footer'))
            yield MarkupParseState(m.span(), directive, code, footer)

    def code_as_markup(self, block: CodeBlock) -> Iterable[Line]:
        raise NotImplementedError

    def indent_code(self, block: CodeBlock) -> Iterable[Line]:
        for line in block.lines:
            yield " " * (self.CODE_INDENT + block.indent) + line

    def dedent_code(self, block: CodeBlock) -> Iterable[Line]:
        for line in block.lines:
            yield line.dedent(self.CODE_INDENT + block.indent)

class IndentedMarkup(RegexMarkup):
    def parse_lit(self, lines: Deque[Line], last_indent: int) -> ParsedLitBlock:
        r"""Parse a literate block.

        >>> _, ls = split_lines_numbered(StringView('''\
        ... Text.
        ... .. coq:: unfold
        ...    :name: nm
        ... '''), 6)
        >>> scan = RST(COQ).parse_lit
        >>> scan(ls, 2) # doctest: +ELLIPSIS
        ParsedLitBlock(footer=[],
                       lines=...[Line(6, ['Text.\n'])]...,
                       directive=...[Line(7, ['.. coq:: unfold\n']),
                                     Line(8, ['   :name: nm\n'])]..., ...)
        >>> _, ls = split_lines_numbered(StringView('''\
        ... Text.
        ...    .. coq:: unfold
        ...    Text.
        ... '''), 6)
        >>> scan(ls, 2) # doctest: +ELLIPSIS
        ParsedLitBlock(footer=[],
                       lines=...[Line(6, ['Text.\n']),
                                 Line(7, ['   .. coq:: unfold\n']),
                                 Line(8, ['   Text.\n'])]...,
                       directive=...[]..., ...)
        >>> _, ls = split_lines_numbered(StringView('Text.\n   Text.'), 6)
        >>> scan(ls, 2) # doctest: +ELLIPSIS
        ParsedLitBlock(footer=[],
                       lines=...[Line(6, ['Text.\n']),
                                 Line(7, ['   Text.'])]...,
                       directive=...[]..., body_indent=3, ...)
        """
        strip_deque(lines)
        directive: Deque[Line] = deque()
        expected_indent = float("+inf")
        while lines:
            line = lines.pop()
            directive.appendleft(line)
            indent = measure_indentation(line)
            if line.match(self.header_re):
                if indent <= expected_indent:
                    return ParsedLitBlock.of_lines([], lines, directive, last_indent)
                break # pragma: no cover # coverage.py bug
            if not line.isspace():
                expected_indent = min(expected_indent, indent - self.CODE_INDENT)
                if expected_indent < 0:
                    break # No need to keep looping
        lines.extend(directive)
        return ParsedLitBlock.of_lines([], lines, [], last_indent)

    def wrap_code(self, block: CodeBlock) -> Iterable[Classified]:
        assert not block.footer
        if block.directive:
            yield Comment(EmptyLine())
            yield from (Comment(l) for l in block.directive)
        else:
            yield Code(EmptyLine())
        yield Code(EmptyLine())
        yield from (Code(l) for l in block.lines)

    def code_as_markup(self, block: CodeBlock) -> Iterable[Line]:
        block = block._replace(
            directive=block.directive or [Line.of_str(" " * block.indent + self.header)],
            lines=deque(self.indent_code(block)))
        for c in self.wrap_code(block):
            yield c.v

    def has_redundant_directive(self, block: ParsedLitBlock):
        return (
            len(block.directive) == 1 and
            str(block.directive[0]).strip() == self.header
            and block.directive_indent == block.body_indent
        )

class BracketedMarkup(RegexMarkup):
    CODE_INDENT: int = 0
    footer: str
    footer_re: Pattern[str]

    def parse_lit(self, lines: Deque[Line], last_indent: int) -> ParsedLitBlock:
        strip_deque(lines)

        directive: Deque[Line] = deque()
        footer = [lines.popleft()] if lines and lines[0].match(self.footer_re) else []

        saved = deque(lines)
        while lines:
            line = lines.pop()
            # Look for a header…
            if line.match(self.header_re):
                directive.appendleft(line)
                strip_deque(lines)
                break
            # … but stop if we find a footer first
            if line.match(self.footer_re):
                lines, directive = saved, deque()
                break
            directive.appendleft(line)
        else:
            lines, directive = directive, deque()

        # Block based: ignore last_indent
        indent = measure_indentation(directive[0]) if directive else 0
        return ParsedLitBlock(footer, lines, directive, 0, indent)

    def wrap_code(self, block: CodeBlock) -> Iterable[Classified]:
        assert bool(block.directive) == bool(block.footer)
        if block.directive:
            yield Comment(EmptyLine())
            yield from (Comment(l) for l in block.directive)
        else:
            yield Code(EmptyLine())
        yield from (Code(l) for l in block.lines)
        if block.footer:
            yield from (Comment(l) for l in block.footer)
            yield Comment(EmptyLine())
        else:
            yield Code(EmptyLine())

    def code_as_markup(self, block: CodeBlock) -> Iterable[Line]:
        block = block._replace(
            directive=block.directive or [Line.of_str(self.header)],
            footer=block.footer or [Line.of_str(self.footer)],
            lines=deque(self.indent_code(block)))
        for c in self.wrap_code(block):
            yield c.v

    def has_redundant_directive(self, block: ParsedLitBlock):
        return (
            len(block.directive) == 1 and
            str(block.directive[0]).strip() == self.header
            and block.directive_indent == 0 # Block based: ignore last_indent
        )

class RST(IndentedMarkup):
    name = "rst"
    CODE_INDENT = 3

    def __init__(self, lang: LangDef):
        super().__init__(lang)
        self.header = f".. {lang.name}::"
        self.header_re = re.compile(
            fr"(?P<indent>[ \t]*)([.][.] {lang.name}::.*)")
        self.directive_re = re.compile(fr"""
           (?P<directive>
            ^(?P<indent>[ ]*)[.][.][ ]{lang.name}::.*
             (?P<options>
              (?:\n
                (?P=indent)[ ][ ][ ] [ \t]*[^ \t].*$)*))
           (?P<code>
              (?:\n
                (?:[ \t]*\n)*
                (?P=indent)[ ][ ][ ] .*$)*
              \n?)
           (?P<footer>)
        """, re.VERBOSE | re.MULTILINE)

class MYST(BracketedMarkup):
    name = "md"

    def __init__(self, lang: LangDef):
        super().__init__(lang)
        self.header = f"```{{{lang.name}}}"
        self.footer = "```"
        self.footer_re = re.compile(
            "[ \t]*```[ \t]*$", re.MULTILINE)
        self.header_re = re.compile(
            fr"(?P<indent>[ \t]*)(```+{{{lang.name}}}.*)")
        self.directive_re = re.compile(fr"""
           (?P<directive>
            ^(?P<indent>[ ]*)
             (?P<ticks>```){{{lang.name}}}.*
             (?P<options>
              \n(?P=indent)---
              (?:\n(?P=indent).*$)*
              \n(?P=indent)---)?)
           (?P<code>
              (?:\n
                (?:[ \t]*\n)*
                (?P=indent).*$)*?) # Minimal match
         \n(?P<footer>(?P=indent)(?P=ticks)\n?)
        """, re.VERBOSE | re.MULTILINE)

class TYPST(MYST): # Same syntax as MyST
    name = "typst"

    def __init__(self, lang: LangDef):
        super().__init__(lang)
        # No --- option headers in Typst, so override the directive regexp
        self.directive_re = re.compile(fr"""
           (?P<directive>
              ^(?P<indent>[ ]*)
               (?P<ticks>```){{{lang.name}}}.*)
           (?P<code>
              (?:\n
                (?:[ \t]*\n)*
                (?P=indent).*$)*?) # Minimal match
           \n(?P<footer>(?P=indent)(?P=ticks)\n?)
        """, re.VERBOSE | re.MULTILINE)

def number_lines(lines: Iterable[StringView], start: int) -> Tuple[int, Deque[Line]]:
    """Number `lines`, starting from `start`."""
    d = deque(Line(num, [s]) for (num, s) in enumerate(lines, start=start))
    # ``split_lines`` drops the final blank line, so count `\n` instead
    return start + sum("\n" in l for l in d), d

def split_lines(text: StringView) -> List[StringView]:
    r"""Split `text` into lines, keeping trailing ``\n``s.

    >>> [str(p) for p in split_lines(StringView("a\nb\n\n"))]
    ['a\n', 'b\n', '\n']
    """
    parts = text.split("\n", keepsep=True)
    if parts and not parts[-1]:  # Drop empty chunk after trailing \n
        parts.pop()
    return parts

def split_lines_numbered(text: StringView, start: int) \
    -> Tuple[int, Deque[Line]]:
    return number_lines(split_lines(text), start) if text else (start, deque([]))

def parsed_blocks_of_partition(md: MarkupDef, spans: Iterable[Classified]) -> Iterable[ParsedBlock]:
    linum = 0
    last: Optional[ParsedLitBlock] = None
    for span in spans:
        if isinstance(span, Comment):
            linestrs = md.lang.unwrap_literate(span.v)
            linum, lines = number_lines(linestrs, linum)
            last = md.parse_lit(lines, last.directive_indent if last else 0)
            last = last._replace(lines=deque(map(md.lang.unescape, last.lines)))
            yield last
        else:
            linum, lines = split_lines_numbered(span.v, linum)
            yield ParsedCodeBlock(lines)

def blocks_of_parsed_blocks(md: MarkupDef, parsed: List[ParsedBlock]):
    for idx, span in enumerate(parsed):
        strip_deque(span.lines)
        if isinstance(span, ParsedLitBlock):
            if idx - 2 >= 0 and not cast(ParsedLitBlock, parsed[idx - 2]).directive:
                while span.footer: # A marker is a real footer only if it matches a directive.
                    span.lines.appendleft(span.footer.pop())
            yield LitBlock(span.lines, span.body_indent)
        else:
            redundant_directive, indent = False, 0
            directive: Sequence[Line] = []
            footer: Sequence[Line] = []
            if idx - 1 >= 0:
                prev = cast(ParsedLitBlock, parsed[idx - 1])
                redundant_directive = md.has_redundant_directive(prev)
                directive, indent = prev.directive, prev.directive_indent
            if idx + 1 < len(parsed):
                footer = cast(ParsedLitBlock, parsed[idx + 1]).footer
            if redundant_directive:
                directive = footer = []
            yield CodeBlock(directive, span.lines, footer, indent)

def gen_markup(md: MarkupDef, blocks: Iterable[Block]) -> Iterable[Line]:
    for b in blocks:
        if isinstance(b, LitBlock):
            yield from b.lines
        elif b.lines:
            yield from md.code_as_markup(b)
        yield EmptyLine()

def _partition_literate(code, spans, literate_matcher):
    """Fold non-literate ``Comment`` spans into ``Code`` ones.
    `literate_matcher` should return ``True`` for literate comments and
    ``False`` for regular ones.  `spans` should be the result of partitioning
    `code`."""
    code = StringView(code, 0, len(code))
    code_acc = code[0:0]
    for span in spans:
        if isinstance(span, Comment) and literate_matcher(span.v):
            if code_acc:
                yield Code(code_acc)
            code_acc = code[span.v.end:span.v.end]
            yield span
        else:
            code_acc += span.v
    if code_acc:
        yield Code(code_acc)

def _make_matcher(p: Pattern) -> Callable[[StringView], bool]:
    return lambda s: bool(s.match(p))

def partition_literate(lang: LangDef, code: str,
                       opener: Optional[Pattern]=None) -> Iterable[Classified]:
    matcher = _make_matcher(opener) if opener else lang.is_literate_comment
    return _partition_literate(code, partition(lang, code), matcher)

def _code2markup_lines(md: MarkupDef, code: str) -> Iterable[Line]:
    spans = partition_literate(md.lang, code)
    parsed = list(parsed_blocks_of_partition(md, spans))
    blocks = blocks_of_parsed_blocks(md, parsed)
    return gen_markup(md, blocks)

def code2markup_lines(md: MarkupDef, code: str) -> Iterable[Line]:
    return _code2markup_lines(md, _expand_indents(code)[0])

def code2markup(md: MarkupDef, code: str) -> str:
    """Translate a fragment of `code` in ``md.lang`` to markup `md`."""
    return join_lines(code2markup_lines(md, code))

def code2markup_marked(md: MarkupDef, code: str, point: Optional[int], marker: Optional[str]) -> str:
    code, point = _expand_indents(code, point)
    return join_lines(mark_point(_code2markup_lines(md, code), point, marker, code))

# Markup → Code
# =============

# Markup parsing
# --------------

# A previous version of this code used the docutils parsers directly.  This
# would be a better approach in theory, but in practice it doesn't work well,
# because the reST parser tends to throw errors and bail out when it encounters
# malformed text (maybe a configuration issue?).  Hence the approach below, but
# note that it detects *all* ‘.. coq::’ blocks, including quoted ones.

def markup_parse(md: MarkupDef, s: str) -> Iterator[ParsedBlock]:
    r"""Identify code blocks in text sources.

    >>> print(list(markup_parse(RST(COQ), '''\
    ... .. coq::
    ...
    ...      Goal True.
    ...        exact I. Qed.\
    ... ''')))
    [ParsedLitBlock(footer=[],
                    lines=deque([]),
                    directive=deque([Line(0, ['.. coq::'])]),
                    body_indent=0, directive_indent=0),
     ParsedCodeBlock(lines=deque([Line(0, ['\n']),
                                  Line(1, ['\n']),
                                  Line(2, ['     Goal True.\n']),
                                  Line(3, ['       exact I. Qed.'])]))]
    """
    beg, linum, last_indent = 0, 0, 0
    last_footer: MutableSequence[Line] = []
    for (start, end), directive_v, code_v, footer_v in md.scan_markup(s):
        markup_v = StringView(s, beg, start)
        linum, markup = split_lines_numbered(markup_v, linum)
        linum, directive = split_lines_numbered(directive_v, linum)
        linum, code = split_lines_numbered(code_v, linum)
        linum, footer = split_lines_numbered(footer_v, linum)
        lit = ParsedLitBlock.of_lines(last_footer, markup, directive, last_indent)
        yield lit
        yield ParsedCodeBlock(code)
        last_indent, last_footer, beg = lit.directive_indent, footer, end
    if beg < len(s) or last_footer:
        rst = StringView(s, beg, len(s))
        linum, markup = split_lines_numbered(rst, linum)
        yield ParsedLitBlock.of_lines(last_footer, markup, [], last_indent)

# Conversion
# ----------

def dedent_code(md: MarkupDef, blocks: Iterable[Block]) -> Iterable[Block]:
    for block in blocks:
        if isinstance(block, CodeBlock):
            block = block._replace(lines=deque(md.dedent_code(block)))
        yield block

def blocks_as_code(md: MarkupDef, blocks: Iterable[Block]) -> Iterable[Classified]:
    # Lines of literate comments come from literate blocks (prose) and from code
    # blocks (directives), so we first create a mixed stream and then wrap
    # consecutive groups.
    blocks = list(blocks)
    for idx, block in enumerate(blocks):
        if isinstance(block, LitBlock):
            if block.lines:
                for line in block.lines:
                    yield Comment(md.lang.escape(line))
            elif 0 < idx < len(blocks) - 1:
                yield Comment(EmptyLine())
        elif isinstance(block, CodeBlock):
            yield from md.wrap_code(block)

def gen_code(md: MarkupDef, blocks: Iterable[Block]) -> Iterable[Line]:
    classified = blocks_as_code(md, blocks)
    for typ, group in groupby(classified, key=type):
        # Stripping is crucial here, as it allows wrap_literate to special-case
        # empty blocks.
        lines = strip_deque(deque(cl.v for cl in group))
        if typ is Comment:
            yield from md.lang.wrap_literate(lines)
        elif typ is Code:
            yield from lines
        yield EmptyLine()

INDENT_RE = re.compile("^[ \t]+", re.MULTILINE)
def __expand_indents(txt: str, tabsize: int):
    return INDENT_RE.sub(lambda m: m.group().expandtabs(tabsize), txt)

def _expand_indents(txt: str, point: Optional[int]=None, tabsize: int=8):
    r"""Expand indentation tabs in `txt` and map `point` to its post-expansion offset.

    >>> _expand_indents("  \t abc\n\t \tdef", 4)
    ('         abc\n                def', 9)
    """
    expanded = __expand_indents(txt, tabsize)
    point = len(__expand_indents(txt[:point], tabsize)) if point is not None else None
    return expanded, point

def _markup2code_lines(md: MarkupDef, txt: str) -> Iterable[Line]:
    parsed = list(markup_parse(md, txt))
    blocks = blocks_of_parsed_blocks(md, parsed)
    blocks = dedent_code(md, blocks)
    return gen_code(md, blocks)

def markup2code_lines(md: MarkupDef, txt: str) -> Iterable[Line]:
    return _markup2code_lines(md, _expand_indents(txt)[0])

def markup2code(md: MarkupDef, txt: str) -> str:
    """Translate a fragment of a text document `txt` to code in ``md.lang``."""
    return join_lines(markup2code_lines(md, txt))

def markup2code_marked(md: MarkupDef, txt: str, point: Optional[int], marker: Optional[str]) -> str:
    txt, point = _expand_indents(txt, point)
    return join_lines(mark_point(_markup2code_lines(md, txt), point, marker, txt))

# Language definitions
# ====================

COQ = BlockLangDef(
    "coq",
    CoqParser,
    lit_open="(*|", lit_close="|*)",
    lit_open_re=r"[(][*][|][ \t]*", lit_close_re=r"[ \t]*[|]?[*][)]\Z",
    escape_pairs=[("(*", r"(\ *"), ("*)", r"*\ )")]
)

def docprint(s: str) -> None:
    """Replace blank lines with ``{BLANKLINE}``.

    This makes it possible to check for blank lines while asking doctest to
    ignore spaces.
    """
    print(re.sub("^$", "{BLANKLINE}", s, flags=re.MULTILINE))

def coq2rst(code):
    """Convert from Coq to reStructuredText.

    >>> docprint(coq2rst('''
    ... (*|
    ... Example:
    ... |*)
    ...
    ... Goal True.
    ...
    ... (*|
    ... Second example:
    ...
    ... .. coq::
    ...    :name:
    ...       snd
    ... |*)
    ...
    ... exact I. Qed.
    ... '''))
    Example:
    {BLANKLINE}
    .. coq::
    {BLANKLINE}
       Goal True.
    {BLANKLINE}
    Second example:
    {BLANKLINE}
    .. coq::
       :name:
          snd
    {BLANKLINE}
       exact I. Qed.
    {BLANKLINE}
    """
    return code2markup(RST(COQ), code)

def rst2coq(rst):
    """Convert from reStructuredText to Coq.

    >>> docprint(rst2coq('''
    ... Example:
    ...
    ... .. coq::
    ...
    ...    Goal True.
    ...
    ... Second example:
    ...
    ... .. coq::
    ...    :name:
    ...       snd
    ...
    ...    exact I. Qed.
    ... '''))
    (*|
    Example:
    |*)
    {BLANKLINE}
    Goal True.
    {BLANKLINE}
    (*|
    Second example:
    {BLANKLINE}
    .. coq::
       :name:
          snd
    |*)
    {BLANKLINE}
    exact I. Qed.
    {BLANKLINE}

    >>> docprint(rst2coq('''
    ... .. coq::
    ...
    ...    X.
    ...
    ... .. coq::
    ...
    ...    Y.
    ... '''))
    X.
    {BLANKLINE}
    (*||*)
    {BLANKLINE}
    Y.
    {BLANKLINE}
    """
    return markup2code(RST(COQ), rst)

def coq2typst(code):
    """Convert from Coq to Typst.

    >>> docprint(coq2typst('''
    ... (*|
    ... Example:
    ... |*)
    ...
    ... Goal True.
    ...
    ... (*|
    ... Second example:
    ... |*)
    ...
    ... exact I. Qed.
    ... '''))
    Example:
    {BLANKLINE}
    ```{coq}
    Goal True.
    ```
    {BLANKLINE}
    Second example:
    {BLANKLINE}
    ```{coq}
    exact I. Qed.
    ```
    {BLANKLINE}

    >>> docprint(coq2typst('''
    ... (*|
    ... Corner case:
    ...
    ... ```coq
    ... Goal True.
    ... ```
    ... |*)
    ...
    ... exact I. Qed.
    ... '''))
    Corner case:
    {BLANKLINE}
    ```coq
    Goal True.
    ```
    {BLANKLINE}
    ```{coq}
    exact I. Qed.
    ```
    {BLANKLINE}
    """
    return code2markup(TYPST(COQ), code)

def typst2coq(typ):
    """Convert from Typst to Coq.

    >>> docprint(typst2coq('''
    ... Example:
    ...
    ... ```{coq}
    ... Goal True.
    ... ```
    ...
    ... Second example:
    ...
    ... ```{coq}
    ... exact I. Qed.
    ... ```
    ... '''))
    (*|
    Example:
    |*)
    {BLANKLINE}
    Goal True.
    {BLANKLINE}
    (*|
    Second example:
    |*)
    {BLANKLINE}
    exact I. Qed.
    {BLANKLINE}

    >>> docprint(typst2coq('''
    ... ```coq
    ... Check 1 + 1.
    ... ```
    ...
    ... ```{coq}
    ... exact I. Qed.
    ... ```
    ... '''))
    (*|
    ```coq
    Check 1 + 1.
    ```
    |*)
    {BLANKLINE}
    exact I. Qed.
    {BLANKLINE}
    """
    return markup2code(TYPST(COQ), typ)

LEAN3 = BlockLangDef(
    "lean3",
    LeanParser,
    lit_open=r"/-|", lit_close=r"|-/",
    lit_open_re=r"[/][-][|][ \t]*", lit_close_re=r"[ \t]*[|]?[-][/]\Z",
    escape_pairs=[("/-", r"/\ -"), ("-/", r"-\ /")]
)

def lean32rst(code):
    """Convert from Lean3 to reStructuredText."""
    return code2markup(RST(LEAN3), code)

def lean32md(code):
    """Convert from Lean3 to MyST Markdown."""
    return code2markup(MYST(LEAN3), code)

def md2lean3(md):
    """Convert from MyST Markdown to Lean3."""
    return markup2code(MYST(LEAN3), md)

def rst2lean3(rst):
    """Convert from reStructuredText to Lean3.

    >>> docprint(rst2lean3('''
    ... Example:
    ...
    ... .. lean3::
    ...
    ...    def x :=
    ...
    ... Second example:
    ...
    ... .. lean3::
    ...    :name:
    ...       snd
    ...
    ...      1 + 1
    ... '''))
    /-|
    Example:
    |-/
    {BLANKLINE}
    def x :=
    {BLANKLINE}
    /-|
    Second example:
    {BLANKLINE}
    .. lean3::
       :name:
          snd
    |-/
    {BLANKLINE}
      1 + 1
    {BLANKLINE}
    """
    return markup2code(RST(LEAN3), rst)

LEAN4 = BlockLangDef(
    "lean4",
    parser=LEAN3.parser,
    lit_open=LEAN3.lit_open, lit_close=LEAN3.lit_close,
    lit_open_re=LEAN3.lit_open_re.pattern, lit_close_re=LEAN3.lit_close_re.pattern,
    escape_pairs=LEAN3.escape_pairs
)

def lean42rst(code: str):
    """Convert from Lean4 to reStructuredText."""
    return code2markup(RST(LEAN4), code)

def rst2lean4(rst: str):
    """Convert from reStructuredText to Lean4."""
    return markup2code(RST(LEAN4), rst)

def lean42md(code: str):
    """Convert from Lean4 to MyST Markdown."""
    return code2markup(MYST(LEAN4), code)

def md2lean4(md: str):
    """Convert from MyST Markdown to Lean4."""
    return markup2code(MYST(LEAN4), md)

DAFNY = LineLangDef(
    "dafny",
    DafnyParser,
    lit_header="///",
    lit_header_re=DafnyParser.LIT_HEADER_RE
)

def dafny2rst(code: str):
    """Convert from Dafny to reStructuredText.

    >>> docprint(dafny2rst('''
    ... /// Example:
    ... /// .. dafny::
    ...
    ... method m() { print "hi"; }
    ...
    ... /// Second example:
    ... ///
    ... /// .. dafny::
    ... ///    :name:
    ... ///       snd
    ...
    ... function f(): int { 1 }
    ...
    ... /// Third example:
    ...
    ... datatype T = T(t: int)
    ... '''))
    Example:
    {BLANKLINE}
    .. dafny::
    {BLANKLINE}
       method m() { print "hi"; }
    {BLANKLINE}
    Second example:
    {BLANKLINE}
    .. dafny::
       :name:
          snd
    {BLANKLINE}
       function f(): int { 1 }
    {BLANKLINE}
    Third example:
    {BLANKLINE}
    .. dafny::
    {BLANKLINE}
       datatype T = T(t: int)
    {BLANKLINE}
    """
    return code2markup(RST(DAFNY), code)

def rst2dafny(rst: str):
    """Convert from reStructuredText to Dafny.

    >>> docprint(rst2dafny('''
    ... Example:
    ...
    ... .. dafny::
    ...
    ...    method m() { print "hi"; }
    ...
    ... Second example:
    ...
    ... .. dafny::
    ...    :name:
    ...       snd
    ...
    ...    function f(): int { 1 }
    ...
    ... Third example:
    ...
    ... .. dafny::
    ...
    ...    datatype T = T(t: int)
    ... '''))
    /// Example:
    {BLANKLINE}
    method m() { print "hi"; }
    {BLANKLINE}
    /// Second example:
    ///
    /// .. dafny::
    ///    :name:
    ///       snd
    {BLANKLINE}
    function f(): int { 1 }
    {BLANKLINE}
    /// Third example:
    {BLANKLINE}
    datatype T = T(t: int)
    {BLANKLINE}
    """
    return markup2code(RST(DAFNY), rst)

def dafny2md(code):
    """Convert from Dafny to Markdown.

    >>> docprint(dafny2md('''
    ... /// Example:
    ...
    ... method m() { print "hi"; }
    ...
    ... /// - Second example:
    ... ///
    ... ///   ```{dafny}
    ... ///   ---
    ... ///   name: snd
    ... ///   ---
    ...
    ... function f(): int { 1 }
    ...
    ... ///   ```
    ... /// Third example:
    ...
    ... datatype T = T(t: int)
    ... '''))
    Example:
    {BLANKLINE}
    ```{dafny}
    method m() { print "hi"; }
    ```
    {BLANKLINE}
    - Second example:
    {BLANKLINE}
      ```{dafny}
      ---
      name: snd
      ---
      function f(): int { 1 }
      ```
    {BLANKLINE}
    Third example:
    {BLANKLINE}
    ```{dafny}
    datatype T = T(t: int)
    ```
    {BLANKLINE}
    """
    return code2markup(MYST(DAFNY), code)

def md2dafny(md: str):
    """Convert from Markdown to Dafny.
    >>> docprint(md2dafny('''
    ... Example:
    ...
    ... ```{dafny}
    ... method m() { print "hi"; }
    ... ```
    ...
    ... - Second example:
    ...
    ...   ```{dafny}
    ...   ---
    ...   name: snd
    ...   ---
    ...   function f(): int { 1 }
    ...   ```
    ...
    ... Third example:
    ...
    ... ```{dafny}
    ... datatype T = T(t: int)
    ... ```
    ... '''))
    /// Example:
    {BLANKLINE}
    method m() { print "hi"; }
    {BLANKLINE}
    /// - Second example:
    ///
    ///   ```{dafny}
    ///   ---
    ///   name: snd
    ///   ---
    {BLANKLINE}
    function f(): int { 1 }
    {BLANKLINE}
    ///   ```
    ///
    /// Third example:
    {BLANKLINE}
    datatype T = T(t: int)
    {BLANKLINE}
    """
    return markup2code(MYST(DAFNY), md)

LANGUAGES = {L.name: L for L in (COQ, DAFNY, LEAN3, LEAN4)}
MARKUPS = {M.name: M for M in (MYST, RST, TYPST)}

def get_language(lang: str) -> LangDef:
    if lang not in LANGUAGES:
        raise ValueError("Unsupported literate language: {}".format(lang))
    return LANGUAGES[lang]

def get_markup(markup: str, lang: str) -> MarkupDef:
    ldef = get_language(lang)
    if markup not in MARKUPS:
        raise ValueError("Unsupported markup format: {}".format(markup))
    return MARKUPS[markup](ldef)

# CLI
# ===

def diff(before: str, after: str) -> str:
    import difflib
    s0, s1 = before.splitlines(keepends=True), after.splitlines(keepends=True)
    return "".join(difflib.unified_diff(s0, s1))

def parse_arguments():
    import argparse
    from os import path

    DESCRIPTION = "Convert between reStructuredText and literate code."
    parser = argparse.ArgumentParser(description=DESCRIPTION)

    CHOICES = (*MARKUPS, *LANGUAGES)
    parser.add_argument("--from", choices=CHOICES, dest="src")
    parser.add_argument("--to", choices=CHOICES, required=True, dest="dst")
    parser.add_argument("--roundtrip", action="store_true", default=False)
    parser.add_argument("input", nargs="?", default="-")

    args = parser.parse_args()

    if args.src is None:
        if args.input == "-":
            parser.error("Flag --from is required when reading from standard input.")
        _, ext = path.splitext(args.input)
        args.src = {".v": "coq", ".lean3": "lean3", ".lean": "lean4",
                    ".dfy": "dafny", ".md": "md", ".rst": "rst"}.get(ext)
        if args.src is None:
            parser.error("Not sure how to translate {}: use --from.".format(args.input))
            assert False

    assert args.src
    if args.src in MARKUPS and args.dst in LANGUAGES:
        mdef = get_markup(args.src, args.dst)
        fw, bw = markup2code, code2markup
    elif args.src in LANGUAGES and args.dst in MARKUPS:
        mdef = get_markup(args.dst, args.src)
        fw, bw = code2markup, markup2code
    else:
        parser.error("Unsupported conversion: {} → {}".format(args.src, args.dst))
        assert False

    if args.roundtrip:
        args.fn = lambda s: diff(s, bw(mdef, fw(mdef, s)))
    else:
        args.fn = lambda s: fw(mdef, s)

    return args

def main():
    import sys

    args = parse_arguments()
    if args.input == "-":
        contents = sys.stdin.read()
    else:
        with open(args.input, encoding="utf-8") as fstream:
            contents = fstream.read()
    sys.stdout.write(args.fn(contents))

if __name__ == '__main__':
    main()
