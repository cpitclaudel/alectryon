#!/usr/bin/env python3

from typing import Any, Dict, Deque, Iterable, Iterator, List, Optional, Tuple, Type, TypeVar, Union

import re
from enum import Enum
from collections import namedtuple, deque

## Utilities
## =========

class StringView:
    def __init__(self, s, beg=0, end=None):
        end = end if end is not None else len(s)
        self.s, self.beg, self.end = s, beg, end
        assert self.beg <= len(s)
        assert self.beg <= self.end, (self.beg, self.end)

    def __len__(self):
        return self.end - self.beg

    def __bool__(self):
        return len(self) > 0

    def __getitem__(self, idx):
        if isinstance(idx, slice):
            beg = min(self.beg + (idx.start or 0), self.end)
            if idx.stop is None:
                end = self.end
            elif idx.stop < 0:
                end = self.end + idx.stop
            else:
                end = self.beg + idx.stop
            return StringView(self.s, beg, end)
        return self.s[self.beg + idx]

    def __add__(self, other):
        if self.s is not other.s:
            raise ValueError("Cannot concatenate {!r} and {!r}".format(self, other))
        if self.end != other.beg:
            raise ValueError("Cannot concatenate [{}:{}] and [{}:{}]".format(
                self.beg, self.end, other.beg, other.end))
        return StringView(self.s, self.beg, other.end)

    def __contains__(self, other):
        return self.s.find(other, self.beg, self.end) >= 0

    def __str__(self):
        return self.s[self.beg:self.end]

    def __repr__(self):
        return repr(str(self))

    def split(self, sep, nsplits=None, keepsep=False):
        beg, chunks = self.beg, []
        while beg <= self.end:
            end = self.s.find(sep, beg, self.end)
            if end < 0 or nsplits and len(chunks) == nsplits:
                end = sep_end = self.end
            else:
                sep_end = end + len(sep)
            chunks.append(StringView(self.s, beg, sep_end if keepsep else end))
            beg = end + len(sep)
        return chunks

    def match(self, regexp: re.Pattern) -> Optional[re.Match]:
        return regexp.match(self.s, self.beg, self.end)

    def search(self, regexp: re.Pattern) -> Optional[re.Match]:
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

    BLANKS = re.compile(r"\s*\Z")
    def isspace(self):
        return bool(self.match(StringView.BLANKS))

class Line(namedtuple("Line", "num parts")):
    def __len__(self):
        """Compute the number of characters in `self`.
        >>> len(Line(0, ("a", "bc", "def")))
        6
        """
        return sum(len(p) for p in self.parts)

    def __bool__(self):
        return len(self) > 0

    def __str__(self):
        s = "".join(str(p) for p in self.parts)
        return s if not s.isspace() else ""

    def isspace(self):
        return all(p.isspace() for p in self.parts)

    def dedent(self, n):
        for idx, p in enumerate(self.parts):
            if n < 0:
                break
            self.parts[idx] = p[n:]
            n -= len(p)
        return Line(self.num, self.parts)

    def __radd__(self, other: Any) -> "Line":
        if not isinstance(other, str):
            return NotImplemented
        return self._replace(parts = [other] + self.parts)

    def replace(self, src: str, dst: str) -> "Line":
        parts = []
        for part in self.parts:
            for idx, p in enumerate(part.split(src)):
                if idx > 0:
                    parts.append(dst)
                parts.append(p)
        return self._replace(parts=parts)

    @staticmethod
    def replacen(line: "T_LineOrStr", pairs) -> "T_LineOrStr":
        for src, dst in pairs:
            line = line.replace(src, dst) # type: ignore
        return line

    def match(self, regex):
        assert len(self.parts) == 1
        return self.parts[0].match(regex)

    # Overload needed because of __len__ above
    def _replace(self, **kwds) -> "Line": # pylint: disable=arguments-differ
        line = Line(*map(kwds.pop, self._fields, self))
        assert not kwds
        return line

def strip_block(lines, beg, end):
    while beg < len(lines) and lines[beg].isspace():
        beg += 1
    while end > beg and lines[end - 1].isspace():
        end -= 1
    return (beg, end)

def strip_deque(lines):
    beg, end = strip_block(lines, 0, len(lines))
    before, after = [], []
    for _ in range(end, len(lines)):
        after.append(lines.pop())
    for _ in range(beg):
        before.append(lines.popleft())
    after.reverse()
    return before, after

def sliding_window(seq, n):
    seq = iter(seq)
    window = deque(maxlen=n)
    for item in seq:
        if len(window) == n:
            yield tuple(window)
        window.append(item)
    while window:
        yield tuple(window) + (None,) * (n - len(window))
        window.popleft()

def mark_point(lines, point, marker):
    for l, nextl in sliding_window(lines, 2):
        last_line = nextl is None
        if point is not None:
            if isinstance(l, Line):
                parts = []
                for p in l.parts:
                    if point is not None and isinstance(p, StringView) and p.end >= point:
                        cutoff = max(0, min(point - p.beg, len(p)))
                        parts.extend((p[:cutoff], marker, p[cutoff:]))
                        point = None
                    else:
                        parts.append(p)
                l.parts[:] = parts
            if point is not None and last_line:
                l += marker
                point = None
        yield l
    if point is not None:
        yield marker # Reached if no lines

def join_lines(lines):
    return "\n".join(str(l) for l in lines)

# Code → reST
# ===========

# Partitioning
# ------------

Code = namedtuple("Code", "v")
Comment = namedtuple("Comment", "v")

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
        # FIXME use the binary search code from core
        # Lines and columns are 1-based
        bol = self.document.rfind("\n", 0, pos) + 1 # 0 if not found
        line = 1 + self.document.count("\n", 0, pos)
        column = 1 + pos - bol
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

    def partition(self) -> Iterable[Union[Code, Comment]]:
        """Partition `self.doc` into runs of ``Code`` and ``Comment`` objects."""
        raise NotImplementedError

class BlockParser(Parser):
    TRANSITIONS: Dict[State, Tuple[Token, ...]] = {}
    TOKEN_REGEXPS: Dict[Token, str] = {}

    def __init__(self, doc: str):
        super().__init__(doc)
        self.pos = 0
        self.spans: List[Union[Code, Comment]] = []
        self.stack: List[Tuple[int, int, State]] = [(0, 0, State.CODE)]

    def step(self, state: State, start: int, tok: Token, mstart: int):
        raise NotImplementedError()

    def partition(self) -> List[Union[Code, Comment]]:
        """Partition `self.doc` into runs of ``Code`` and ``Comment`` objects."""
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
    LIT_HEADER_RE: re.Pattern

    @classmethod
    def _classify(cls, lines: List[StringView]) -> Iterator[Union[Code, Comment]]:
        for line in lines:
            yield Comment(line) if line.match(cls.LIT_HEADER_RE) else Code(line)

    def partition(self):
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

def partition(lang, code):
    return list(lang.parser(code).partition())

# Language definitions
# --------------------

LineOrStr = Union[Line, str]
T_LineOrStr = TypeVar("T_LineOrStr", bound=LineOrStr)

class LangDef:
    def __init__(self, name: str, parser: Type[Parser]):
        self.name = name
        self.parser = parser
        self.header = ".. {}::".format(name)
        self.directive = re.compile(r"(?P<indent>[ \t]*)([.][.] {}::.*)".format(name))
        self.rst_block = re.compile(r"""
           (?P<directive>
            ^(?P<indent>[ ]*)
             [.][.][ ]{}::.*
             (?P<options>
              (?:\n
                (?P=indent)[ ][ ][ ] [ \t]*[^ \t].*$)*))
           (?P<body>
              (?:\n
                (?:[ \t]*\n)*
                (?P=indent)[ ][ ][ ] .*$)*)
        """.format(name), re.VERBOSE | re.MULTILINE)

    @property
    def lit_empty(self) -> str:
        raise NotImplementedError

    def is_literate_comment(self, block: StringView) -> bool:
        raise NotImplementedError

    def wrap_literate(self, lines: Iterable[LineOrStr]) -> Iterable[LineOrStr]:
        raise NotImplementedError

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        raise NotImplementedError

    def quote(self, line: T_LineOrStr) -> T_LineOrStr:
        raise NotImplementedError

    def unquote(self, line: T_LineOrStr) -> T_LineOrStr:
        raise NotImplementedError

class BlockLangDef(LangDef):
    def __init__(self, name: str, parser: Type[Parser],
                 lit_open: str, lit_close: str,
                 lit_open_re: str, lit_close_re: str,
                 quote_pairs: List[Tuple[str, str]]):
        super().__init__(name, parser)
        self.lit_open, self.lit_close = lit_open, lit_close
        self.lit_open_re, self.lit_close_re = re.compile(lit_open_re), re.compile(lit_close_re)
        self.quote_pairs = list(quote_pairs)
        self.unquote_pairs = [(dst, src) for (src, dst) in self.quote_pairs]

    @property
    def lit_empty(self) -> str:
        return self.lit_open + self.lit_close

    def is_literate_comment(self, block: StringView) -> bool:
        return bool(block.match(self.lit_open_re))

    def wrap_literate(self, lines: Iterable[LineOrStr]) -> Iterable[LineOrStr]:
        yield self.lit_open
        yield from lines
        yield self.lit_close

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        return split_lines(block.trim(self.lit_open_re, self.lit_close_re))

    def quote(self, line: T_LineOrStr) -> T_LineOrStr:
        return Line.replacen(line, self.quote_pairs)

    def unquote(self, line: T_LineOrStr) -> T_LineOrStr:
        return Line.replacen(line, self.unquote_pairs)

class LineLangDef(LangDef):
    def __init__(self, name: str, parser: Type[Parser],
                 lit_header: str, lit_header_re: re.Pattern[str]):
        super().__init__(name, parser)
        self.lit_header = lit_header
        self.lit_header_re = lit_header_re

    @property
    def lit_empty(self) -> str:
        return self.lit_header

    def is_literate_comment(self, block: StringView) -> bool:
        return True

    def wrap_literate(self, lines: Iterable[LineOrStr]) -> Iterable[LineOrStr]:
        for line in lines:
            yield self.lit_header + (" " if line else "") + line

    def unwrap_literate(self, block: StringView) -> Iterable[StringView]:
        for l in split_lines(block):
            yield l.trim(self.lit_header_re, None)

    def quote(self, line: T_LineOrStr) -> T_LineOrStr:
        return line

    def unquote(self, line: T_LineOrStr) -> T_LineOrStr:
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
        """Partition `doc` into runs of ``Code`` and ``Comment`` objects.

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
    # FIXME: Add support for char (``'"'``) syntax
    # FIXME: Technically doc comments don't support nesting
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
        r"""Partition `doc` into runs of ``Code`` and ``Comment`` objects.

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

# Conversion
# ----------

INDENT = re.compile(r"(?P<indent>[ ]*)")

Lit = namedtuple("Lit", "lines directive_lines indent")
CodeBlock = namedtuple("CodeBlock", "lines indent")

def _last_directive(lang: LangDef, lines: List[Line]):
    r"""Scan backwards across `lines` to find the beginning of the Coq directive.

    >>> _, ls = split_lines_numbered(StringView('''\
    ... Text.
    ... .. coq:: unfold
    ...    :name: nm
    ... '''), 6)
    >>> _last_directive(COQ, ls) # doctest: +ELLIPSIS
    (...[Line(num=6, parts=['Text.'])]...,
        <re.Match ...'.. coq:: unfold'>,
     ...[Line(num=7, parts=['.. coq:: unfold']),
         Line(num=8, parts=['   :name: nm']),
         Line(num=9, parts=[''])]...)

    >>> _, ls = split_lines_numbered(StringView('''\
    ... Text.
    ...    .. coq:: unfold
    ...    Text.
    ... '''), 6)
    >>> _last_directive(COQ, ls) # doctest: +ELLIPSIS
    (...[Line(num=6, parts=['Text.']),
         Line(num=7, parts=['   .. coq:: unfold']),
         Line(num=8, parts=['   Text.']),
         Line(num=9, parts=[''])]...)

    >>> _, ls = split_lines_numbered(StringView('Text.\n   Text.'), 6)
    >>> _last_directive(COQ, ls) # doctest: +ELLIPSIS
    (...[Line(num=6, parts=['Text.']),
         Line(num=7, parts=['   Text.'])]...)

    """
    directive: Deque[Line] = deque()
    expected_indent = float("+inf")
    while lines:
        line = lines.pop()
        directive.appendleft(line)
        indent = measure_indentation(line)
        m = line.match(lang.directive)
        if m:
            if indent <= expected_indent:
                return lines, m, directive
            break # pragma: no cover # coverage.py bug
        if not line.isspace():
            expected_indent = min(expected_indent, indent - 3)
            if expected_indent < 0:
                break # No need to keep looping
    lines.extend(directive)
    return lines, None, None

def lit(lang: LangDef, lines, indent):
    strip_deque(lines)
    lines, m, directive_lines = _last_directive(lang, lines)
    if directive_lines:
        assert m
        indent = m.group("indent")
        strip_deque(lines)
    else:
        if lines:
            indent = lines[-1].match(INDENT).group("indent")
        directive_lines = [indent + lang.header]
    return Lit(lines, directive_lines=directive_lines, indent=indent)

def number_lines(lines: Iterable[StringView], start: int) \
    -> Tuple[int, Deque[Line]]:
    d = deque(Line(num, [s]) for (num, s) in enumerate(lines, start=start))
    return start + len(d) - 1, d

def split_lines(text: StringView) -> Iterable[StringView]:
    return text.split("\n")

def split_lines_numbered(text: StringView, start: int) \
    -> Tuple[int, Deque[Line]]:
    return number_lines(split_lines(text), start)

def gen_rst(lang: LangDef, spans):
    linum, indent, prefix = 0, "", [lang.header]
    for span in spans:
        if isinstance(span, Comment):
            linestrs = lang.unwrap_literate(span.v)
            linum, lines = number_lines(linestrs, linum)
            litspan = lit(lang, lines, indent)
            indent, prefix = litspan.indent, litspan.directive_lines
            if litspan.lines:
                yield from (lang.unquote(l) for l in litspan.lines)
                yield ""
        else:
            linum, lines = split_lines_numbered(span.v, linum)
            strip_deque(lines)
            if lines:
                yield from prefix
                yield ""
                for line in lines:
                    yield indent + "   " + line
                yield ""

def _partition_literate(code, spans, literate_matcher):
    """Fold non-literate ``Comment`` spans into ``Code`` ones.
    ``literate_matcher`` should return ``True`` for literate comments and
    ``False`` for regular ones.  ``spans`` should be the result of partitioning
    ``code``."""
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

def partition_literate(lang: LangDef, code, opener=None):
    matcher = (lambda s: s.match(opener)) if opener else lang.is_literate_comment
    return _partition_literate(code, partition(lang, code), matcher)

def code2rst_lines(lang: LangDef, code):
    return gen_rst(lang, partition_literate(lang, code))

def code2rst(lang: LangDef, code):
    """Translate a fragment of `code` in `lang` to reST."""
    return join_lines(code2rst_lines(lang, code))

def mark_rst_lines(rst_lines, point, marker):
    return join_lines(mark_point(rst_lines, point, marker))

def code2rst_marked(lang: LangDef, code, point, marker):
    return mark_rst_lines(code2rst_lines(lang, code), point, marker)

# reStructuredText → Code
# =======================

# reST parsing
# ------------

# A previous version of this code used the docutils parsers directly.  This
# would be a better approach in theory, but in practice it doesn't work well,
# because the reST parser tends to throw errors and bail out when it encounters
# malformed text (maybe a configuration issue?).  Hence the approach below, but
# note that it detects *all* ‘.. coq::’ blocks, including quoted ones.

def rst_partition(lang: LangDef, s):
    """Identify ``.. lang::`` blocks in reST sources.

    >>> print(list(rst_partition(COQ, '''\\
    ... .. coq::
    ...
    ...      Goal True.
    ...        exact I. Qed.\\
    ... ''')))
    [Lit(lines=deque([Line(num=0, parts=[''])]),
         directive_lines=deque([Line(num=0, parts=['.. coq::'])]),
         indent=0),
     CodeBlock(lines=deque([Line(num=0, parts=['']),
                            Line(num=1, parts=['']),
                            Line(num=2, parts=['  Goal True.']),
                            Line(num=3, parts=['    exact I. Qed.'])]),
               indent=0)]
    """
    beg, linum = 0, 0
    for m in lang.rst_block.finditer(s):
        indent = len(m.group("indent"))
        rst = StringView(s, beg, m.start())
        directive = StringView(s, *m.span('directive'))
        body = StringView(s, *m.span('body'))

        linum, rst_lines = split_lines_numbered(rst, linum)
        linum, directive_lines = split_lines_numbered(directive, linum)
        linum, body_lines = split_lines_numbered(body, linum)

        # body_lines.popleft() # Discard initial blank

        yield Lit(rst_lines, directive_lines=directive_lines, indent=indent)
        yield CodeBlock(body_lines, indent=indent)
        beg = m.end()
    if beg < len(s):
        rst = StringView(s, beg, len(s))
        linum, lines = split_lines_numbered(rst, linum)
        yield Lit(lines, directive_lines=None, indent=None)

# Conversion
# ----------

INDENTATION_RE = re.compile(" *")
def measure_indentation(line: Line):
    m = line.match(INDENTATION_RE)
    return m.end() - m.start()

def redundant_directive(lang: LangDef, directive_lines, directive_indent, last_indent):
    return (
        directive_lines and
        len(directive_lines) == 1 and
        str(directive_lines[0]).strip() == lang.header
        and directive_indent == last_indent
    )

def concat_line_blocks(*blocks: List[Line]) -> Iterator[LineOrStr]:
    prev = None
    for b in blocks:
        if not b:
            continue
        if prev:
            yield ""
        yield from b
        prev = b

def trim_rst_block(lang: LangDef, block, last_indent, keep_empty):
    strip_deque(block.lines)
    last_indent = measure_indentation(block.lines[-1]) if block.lines else last_indent

    directive_lines = block.directive_lines
    keep_empty = keep_empty and directive_lines
    if redundant_directive(lang, directive_lines, block.indent, last_indent):
        directive_lines = []

    if not block.lines and not directive_lines:
        if keep_empty:
            yield lang.lit_empty
            yield ""
    else:
        lines = concat_line_blocks(block.lines, directive_lines)
        yield from lang.wrap_literate(lang.quote(l) for l in lines)
        yield ""

def trim_code_block(block):
    strip_deque(block.lines)
    for line in block.lines:
        yield line.dedent(block.indent + 3)
    if block.lines:
        yield ""

def gen_code(lang: LangDef, blocks):
    last_indent = 0
    for idx, block in enumerate(blocks):
        if isinstance(block, Lit):
            yield from trim_rst_block(lang, block, last_indent, idx > 0)
        elif isinstance(block, CodeBlock):
            yield from trim_code_block(block)
        last_indent = block.indent

def rst2code_lines(lang: LangDef, rst):
    return gen_code(lang, rst_partition(lang, rst))

def rst2code(lang: LangDef, rst):
    """Translate a fragment of a reST document `rst` to code in `lang`."""
    return join_lines(rst2code_lines(lang, rst))

def rst2code_marked(lang: LangDef, rst, point, marker):
    return join_lines(mark_point(rst2code_lines(lang, rst), point, marker))

# Language definitions
# ====================

COQ = BlockLangDef(
    "coq",
    CoqParser,
    lit_open="(*|", lit_close="|*)",
    lit_open_re=r"[(][*][|][ \t]*", lit_close_re=r"[ \t]*[|]?[*][)]\Z",
    quote_pairs=[("(*", r"(\ *"), ("*)", r"*\ )")]
)

def coq2rst(code):
    """Convert from Coq to reStructuredText.

    >>> print(coq2rst('''
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
    <BLANKLINE>
    .. coq::
    <BLANKLINE>
       Goal True.
    <BLANKLINE>
    Second example:
    <BLANKLINE>
    .. coq::
       :name:
          snd
    <BLANKLINE>
       exact I. Qed.
    <BLANKLINE>
    """
    return code2rst(COQ, code)

def rst2coq(rst):
    """Convert from reStructuredText to Coq.

    >>> print(rst2coq('''
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
    <BLANKLINE>
    Goal True.
    <BLANKLINE>
    (*|
    Second example:
    <BLANKLINE>
    .. coq::
       :name:
          snd
    |*)
    <BLANKLINE>
    exact I. Qed.
    <BLANKLINE>
    """
    return rst2code(COQ, rst)

LEAN3 = BlockLangDef(
    "lean3",
    LeanParser,
    lit_open=r"/-!", lit_close=r"-/",
    lit_open_re=r"[/][-][!][ \t]*", lit_close_re=r"[ \t]*[-][/]\Z",
    quote_pairs=[("/-", r"/\ -"), ("-/", r"-\ /")]
)

def lean32rst(code):
    """Convert from Lean3 to reStructuredText."""
    return code2rst(LEAN3, code)

def rst2lean3(rst):
    """Convert from reStructuredText to Lean3.

    >>> print(rst2lean3('''
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
    /-!
    Example:
    -/
    <BLANKLINE>
    def x :=
    <BLANKLINE>
    /-!
    Second example:
    <BLANKLINE>
    .. lean3::
       :name:
          snd
    -/
    <BLANKLINE>
      1 + 1
    <BLANKLINE>
    """
    return rst2code(LEAN3, rst)

LEAN4 = BlockLangDef(
    "lean4",
    LeanParser, # We can use the same parser as Lean 3, because the syntax for
                # comments has not changed between the versions.
    lit_open=r"/-!", lit_close=r"-/",
    lit_open_re=r"[/][-][!][ \t]*", lit_close_re=r"[ \t]*[-][/]\Z",
    quote_pairs=[("/-", r"/\ -"), ("-/", r"-\ /")]
)

def lean42rst(lean):
    """Convert from Lean4 to reStructuredText."""
    return code2rst(LEAN4, lean)

def rst2lean4(rst):
    """Convert from reStructuredText to Lean4."""
    return rst2code(LEAN4, rst)

DAFNY = LineLangDef(
    "dafny",
    DafnyParser,
    lit_header="///",
    lit_header_re=DafnyParser.LIT_HEADER_RE
)

def dafny2rst(code):
    """Convert from Dafny to reStructuredText.

    >>> print(dafny2rst('''
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
    <BLANKLINE>
    .. dafny::
    <BLANKLINE>
       method m() { print "hi"; }
    <BLANKLINE>
    Second example:
    <BLANKLINE>
    .. dafny::
       :name:
          snd
    <BLANKLINE>
       function f(): int { 1 }
    <BLANKLINE>
    Third example:
    <BLANKLINE>
    .. dafny::
    <BLANKLINE>
       datatype T = T(t: int)
    <BLANKLINE>
    """
    return code2rst(DAFNY, code)

def rst2dafny(rst):
    """Convert from reStructuredText to Dafny.

    >>> print(rst2dafny('''
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
    <BLANKLINE>
    method m() { print "hi"; }
    <BLANKLINE>
    /// Second example:
    ///
    /// .. dafny::
    ///    :name:
    ///       snd
    <BLANKLINE>
    function f(): int { 1 }
    <BLANKLINE>
    /// Third example:
    <BLANKLINE>
    datatype T = T(t: int)
    <BLANKLINE>
    """
    return rst2code(DAFNY, rst)

LANGUAGES = {
    "coq": COQ,
    "dafny": DAFNY,
    "lean3": LEAN3,
    "lean4": LEAN4
}

# CLI
# ===

CONVERTERS = (coq2rst, rst2coq,
              lean32rst, rst2lean3,
              lean42rst, rst2lean4,
              dafny2rst, rst2dafny)

def parse_arguments():
    import argparse
    from os import path

    DESCRIPTION = "Convert between reStructuredText and literate code."
    parser = argparse.ArgumentParser(description=DESCRIPTION)

    group = parser.add_mutually_exclusive_group()
    converters = {"--{}".format(fn.__name__): fn for fn in CONVERTERS}
    for opt, fn in converters.items():
        group.add_argument(opt, dest="fn", action="store_const",
                           const=fn, help=fn.__doc__.split("\n", 1)[0])
    parser.add_argument("input", nargs="?", default="-")

    args = parser.parse_args()
    available_converters = ", ".join(converters)

    if args.input == "-":
        if not args.fn:
            parser.error("Reading from standard input requires one of {}."
                         .format(available_converters))
    else:
        if not args.fn:
            _, ext = path.splitext(args.input)
            ext_fn = {".v": coq2rst, ".lean3": lean32rst, ".lean": lean42rst, ".dfy": dafny2rst}
            args.fn = ext_fn.get(ext)
        if not args.fn:
            parser.error("Not sure how to translate {}: use one of {}"
                         .format(args.input, available_converters))

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
