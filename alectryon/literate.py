#!/usr/bin/env python3

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

    def split(self, sep, nsplits=None):
        beg, chunks = self.beg, []
        while beg <= self.end:
            end = self.s.find(sep, beg, self.end)
            if end < 0 or nsplits and len(chunks) == nsplits:
                end = self.end
            chunks.append(StringView(self.s, beg, end))
            beg = end + len(sep)
        return chunks

    def match(self, regexp):
        return regexp.match(self.s, self.beg, self.end)

    def search(self, regexp):
        return regexp.search(self.s, self.beg, self.end)

    def trim(self, beg, end):
        v = self
        b = v.match(beg)
        if b:
            v = v[len(b.group()):]
        e = v.search(end)
        if e:
            v = v[:-len(e.group())]
        return v

    BLANKS = re.compile(r"\s+\Z")
    def isspace(self):
        return bool(self.match(StringView.BLANKS))

class Line(namedtuple("Line", "num parts")):
    def __len__(self):
        return sum(len(p) for p in self.parts)

    def __str__(self):
        s = "".join(str(p) for p in self.parts)
        return s if not s.isspace() else ""

    def __radd__(self, s):
        self.parts.append(s)

    def isspace(self):
        return all(p.isspace() for p in self.parts)

    def dedent(self, n):
        for idx, p in enumerate(self.parts):
            if n < 0:
                break
            self.parts[idx] = p[n:]
            n -= len(p)
        return Line(self.num, self.parts)

    def replace(self, src, dst):
        parts = []
        for part in self.parts:
            for idx, p in enumerate(part.split(src)):
                if idx > 0:
                    parts.append(dst)
                parts.append(p)
        self.parts[:] = parts
        return self

    def match(self, regex):
        assert len(self.parts) == 1
        return self.parts[0].match(regex)

QUOTE_PAIRS = [("(*", r"(\ *"), ("*)", r"*\ )")]
UNQUOTE_PAIRS = [(dst, src) for (src, dst) in QUOTE_PAIRS]

def replace(line, pairs):
    for src, dst in pairs:
        line = line.replace(src, dst)
    return line

def blank(line):
    return (not line) or line.isspace()

def strip_block(lines, beg, end):
    while beg < len(lines) and blank(lines[beg]):
        beg += 1
    while end > beg and blank(lines[end - 1]):
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

# Coq → reStructuredText
# ======================

# Coq parsing
# -----------

Code = namedtuple("Code", "v")
Comment = namedtuple("Comment", "v")

class Token(Enum):
    COMMENT_OPEN = "COMMENT_OPEN"
    COMMENT_CLOSE = "COMMENT_CLOSE"
    STRING_ESCAPE = "STRING_ESCAPE"
    STRING_DELIM = "STRING_DELIM"
    EOF = "EOF"

class State(Enum):
    CODE = "CODE"
    STRING = "STRING"
    COMMENT = "COMMENT"
    NESTED_COMMENT = "NESTED_COMMENT"

REGEXPS = {
    Token.COMMENT_OPEN: r"[(][*]+(?![)])",
    Token.COMMENT_CLOSE: r"[*]+[)]",
    Token.STRING_ESCAPE: r'""',
    Token.STRING_DELIM: r'"',
    Token.EOF: r"(?!.)",
}

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

def regexp_opt(tokens):
    labeled = ("(?P<{}>{})".format(tok.name, REGEXPS[tok]) for tok in tokens)
    return re.compile("|".join(labeled), re.DOTALL)

SCANNERS = {state: regexp_opt(tokens)
            for (state, tokens) in TRANSITIONS.items()}

class ParsingError(ValueError):
    def __init__(self, document, state, position, end):
        super().__init__()
        self.document = document
        self.state = state
        self.position, self.end = position, end
        self.line, self.column = self.line_col_of_pos(position)
        self.end_line, self.end_column = self.line_col_of_pos(end)

    def line_col_of_pos(self, pos):
        assert pos >= 0
        # Lines and columns are 1-based
        bol = self.document.rfind("\n", 0, pos) + 1 # 0 if not found
        line = 1 + self.document.count("\n", 0, pos)
        column = 1 + pos - bol
        return line, column

    @property
    def message(self):
        expected = " or ".join(t.name for t in TRANSITIONS[self.state])
        MSG = "Unterminated {} (looking for {})"
        return MSG.format(self.state.name.lower(), expected)

    def __str__(self):
        return "{}:{}: {}".format(self.line, self.column, self.message)

def coq_partition(doc):
    """Partition `doc` into runs of code and comments (both ``StringView``\\s).

    Example:
    >>> coq_partition("Code (* comment *) code")
    [Code(v='Code '), Comment(v='(* comment *)'), Code(v=' code')]


    Tricky cases:
    >>> coq_partition("")
    [Code(v='')]
    >>> coq_partition("(**)(***)")
    [Code(v=''), Comment(v='(**)'), Code(v=''), Comment(v='(***)'), Code(v='')]
    >>> coq_partition("(*c*)(*c*c*)")
    [Code(v=''), Comment(v='(*c*)'), Code(v=''), Comment(v='(*c*c*)'), Code(v='')]
    >>> coq_partition('C "(*" C "(*""*)" C')
    [Code(v='C "(*" C "(*""*)" C')]
    >>> coq_partition('C (** "*)" *)')
    [Code(v='C '), Comment(v='(** "*)" *)'), Code(v='')]
    """
    pos = 0
    spans = []
    stack = [(0, 0, State.CODE)]
    spans = []
    while True:
        start, token_end, state = stack[-1]
        m = SCANNERS[state].search(doc, pos)
        if not m:
            raise ParsingError(doc, state, start, token_end)
        tok = Token(m.lastgroup)
        mstart, mend, pos = m.start(), m.end(), m.end()
        if state is State.CODE:
            if tok is Token.COMMENT_OPEN:
                stack.pop()
                stack.append((mstart, mend, State.COMMENT))
                spans.append(Code(StringView(doc, start, mstart)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, mend, State.STRING))
            elif tok is Token.EOF:
                stack.pop()
                spans.append(Code(StringView(doc, start, pos)))
                break
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
                stack.append((mstart, mend, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
                stack.append((pos, pos, State.CODE))
                spans.append(Comment(StringView(doc, start, pos)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, mend, State.STRING))
            else:
                assert False
        elif state is State.NESTED_COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, mend, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, mend, State.STRING))
            else:
                assert False
        else:
            assert False

    return spans

# Conversion
# ----------

LIT_OPEN = re.compile(r"[(][*][|][ \t]*")
LIT_CLOSE = re.compile(r"[ \t]*[|]?[*][)]\Z")

COQDOC_OPEN = re.compile(r"[(][*][*]\s[ \t]*")
COQDOC_CLOSE = re.compile(r"[ \t]*[*]+[)]\Z")

DEFAULT_HEADER = ".. coq::"
DIRECTIVE = re.compile(r"([ \t]*)([.][.] coq::.*)?")

Lit = namedtuple("Lit", "lines directive indent")
CodeBlock = namedtuple("CodeBlock", "lines indent")

def lit(lines, indent):
    strip_deque(lines)
    m = lines and lines[-1].match(DIRECTIVE)
    indent, directive = m.groups() if m else (indent, None)
    if directive:
        directive = lines.pop()
        strip_deque(lines)
    else:
        directive = indent + DEFAULT_HEADER
    return Lit(lines, directive=directive, indent=indent)

def number_lines(span, start):
    lines = span.split("\n")
    d = deque(Line(num, [s]) for (num, s) in enumerate(lines, start=start))
    return start + len(lines) - 1, d

def gen_rst(spans):
    linum, indent, prefix = 0, "", DEFAULT_HEADER
    for span in spans:
        if isinstance(span, Comment):
            linum, lines = number_lines(span.v.trim(LIT_OPEN, LIT_CLOSE), linum)
            litspan = lit(lines, indent)
            indent, prefix = litspan.indent, litspan.directive
            if litspan.lines:
                yield from (replace(l, UNQUOTE_PAIRS) for l in litspan.lines)
                yield ""
        else:
            linum, lines = number_lines(span.v, linum)
            strip_deque(lines)
            for l in lines:
                l.parts.insert(0, indent + "   ")
            if lines:
                yield prefix
                yield ""
                yield from lines
                yield ""

def coq_partition_literate(code, opener=LIT_OPEN):
    spans = coq_partition(code)
    code = StringView(code, 0, len(code))
    code_acc = code[0:0]
    for span in spans:
        if isinstance(span, Comment) and span.v.match(opener):
            if code_acc:
                yield Code(code_acc)
            code_acc = code[span.v.end:span.v.end]
            yield span
        else:
            code_acc += span.v
    if code_acc:
        yield Code(code_acc)

def coq2rst_lines(coq):
    return gen_rst(coq_partition_literate(coq))

def coq2rst(coq):
    return join_lines(coq2rst_lines(coq))

def coq2rst_marked(coq, point, marker):
    return join_lines(mark_point(coq2rst_lines(coq), point, marker))

# reStructuredText → Coq
# ======================

# reST parsing
# ------------

# A previous version of this code used the docutils parsers directly.  This
# would be a better approach in theory, but in practice it doesn't work well,
# because the reST parser tends to throw errors and bail out when it encounters
# malformed text (maybe a configuration issue?).  Hence the approach below, but
# note that it detects *all* ‘.. coq::’ blocks, including quoted ones.

COQ_BLOCK = re.compile(r"""
^(?P<indent>[ \t]*)[.][.][ ]coq::.*
(?P<body>
 (?:\n
    (?:[ \t]*\n)*
    (?P=indent)[ ][ ][ ].*$)*)
""", re.VERBOSE | re.MULTILINE)

def rst_partition(s):
    beg, linum = 0, 0
    for m in COQ_BLOCK.finditer(s):
        indent = len(m.group("indent"))
        rst = StringView(s, beg, m.start())
        block = StringView(s, *m.span())

        linum, rst_lines = number_lines(rst, linum)
        linum, block_lines = number_lines(block, linum)
        directive = block_lines.popleft()

        yield Lit(rst_lines, directive=directive, indent=indent)
        yield CodeBlock(block_lines, indent=indent)
        beg = m.end()
    if beg < len(s):
        rst = StringView(s, beg, len(s))
        linum, lines = number_lines(rst, linum)
        yield Lit(lines, directive=None, indent=None)

# Conversion
# ----------

INDENTATION_RE = re.compile(" *")
def measure_indentation(line):
    m = line.match(INDENTATION_RE)
    return m.end() - m.start()

def trim_rst_block(block, last_indent, keep_empty):
    strip_deque(block.lines)
    directive_indent = block.indent # Stored here for convenience
    last_indent = measure_indentation(block.lines[-1]) if block.lines else last_indent

    directive = block.directive
    keep_empty = keep_empty and directive is not None
    if (directive
        and str(directive).strip() == DEFAULT_HEADER
        and directive_indent == last_indent):
        directive = None

    if not block.lines and not directive:
        if keep_empty:
            yield "(*||*)"
            yield ""
    else:
        yield "(*|"
        yield from (replace(l, QUOTE_PAIRS) for l in block.lines)
        if directive:
            if block.lines:
                yield ""
            yield directive
        yield "|*)"
        yield ""

def trim_coq_block(block):
    strip_deque(block.lines)
    for line in block.lines:
        yield line.dedent(block.indent + 3)
    if block.lines:
        yield ""

def gen_coq(blocks):
    last_indent = 0
    for idx, block in enumerate(blocks):
        if isinstance(block, Lit):
            yield from trim_rst_block(block, last_indent, idx > 0)
        elif isinstance(block, CodeBlock):
            yield from trim_coq_block(block)
        last_indent = block.indent

def rst2coq_lines(rst):
    return gen_coq(rst_partition(rst))

def rst2coq(rst):
    return join_lines(rst2coq_lines(rst))

def rst2coq_marked(rst, point, marker):
    return join_lines(mark_point(rst2coq_lines(rst), point, marker))

# CLI
# ===

def parse_arguments():
    import argparse
    from os import path

    DESCRIPTION = "Convert between reStructuredText and literate Coq."
    parser = argparse.ArgumentParser(description=DESCRIPTION)

    group = parser.add_mutually_exclusive_group()
    group.add_argument("--coq2rst", dest="fn",
                       action="store_const", const=coq2rst,
                       help="Convert from Coq to reStructuredText.")
    group.add_argument("--rst2coq", dest="fn",
                       action="store_const", const=rst2coq,
                       help="Convert from reStructuredText to Coq.")
    parser.add_argument("input", nargs="?", default="-")

    args = parser.parse_args()
    if args.input == "-":
        if not args.fn:
            parser.error("Reading from standard input requires one of --coq2rst, --rst2coq.")
    else:
        _, ext = path.splitext(args.input)
        args.fn = {".v": coq2rst, ".rst": rst2coq}.get(ext)
        if not args.fn:
            parser.error("Unexpected file extension: "
                         "expected '.rst' or '.v', got '{}'.".format(ext))

    return args

def main():
    import sys

    args = parse_arguments()
    if args.input == "-":
        contents = sys.stdin.read()
    else:
        with open(args.input) as fstream:
            contents = fstream.read()
    sys.stdout.write(args.fn(contents))

def run_doctest():
    import sys
    import doctest
    doctest.debug(sys.modules.get('__main__'), "__main__.partition", pm=True)

if __name__ == '__main__':
    main()
