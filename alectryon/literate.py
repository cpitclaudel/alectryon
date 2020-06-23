#!/usr/bin/env python3

import sys
import re
import textwrap
from enum import Enum
from itertools import islice
from collections import namedtuple, deque

## Utilities
## =========

Line = namedtuple("Line", "num s indent")

class StringView:
    def __init__(self, s, beg=0, end=None):
        end = end if end is not None else len(s)
        self.s, self.beg, self.end = s, beg, end

    def __len__(self):
        return self.end - self.beg

    def __getitem__(self, idx):
        if isinstance(idx, slice):
            beg = self.beg + (idx.start or 0)
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

    def __str__(self):
        return self.s[self.beg:self.end]

    def __repr__(self):
        return repr(str(self))

    def split(self, sep):
        beg, chunks = self.beg, []
        while True:
            end = self.s.find(sep, beg, self.end)
            if end < 0:
                break
            chunks.append(StringView(self.s, beg, end))
            beg = end + 1
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

def blank(line):
    if isinstance(line, Line):
        line = line.s
    return (not line) or line.isspace()

def strip_block(lines, beg, end):
    while beg < len(lines) and blank(lines[beg]):
        beg += 1
    while end > beg and blank(lines[end - 1]):
        end -= 1
    return (beg, end)

def strip_deque(lines):
    beg, end = strip_block(lines, 0, len(lines))
    for _ in range(end, len(lines)):
        lines.pop()
    for _ in range(beg):
        lines.popleft()
    return lines

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

SCANNERS = { state: regexp_opt(tokens)
             for (state, tokens) in TRANSITIONS.items() }

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
    stack = [(0, State.CODE)]
    spans = []
    while True:
        start, state = stack[-1]
        m = SCANNERS[state].search(doc, pos)
        if not m:
            MSG = "Parsing failed (looking for {} in state {} at position {})"
            raise ValueError(MSG.format(SCANNERS[state].pattern, state, pos))
        tok = Token(m.lastgroup)
        mstart, pos = m.start(), m.end()
        if state is State.CODE:
            if tok is Token.COMMENT_OPEN:
                stack.pop()
                stack.append((mstart, State.COMMENT))
                spans.append(Code(StringView(doc, start, mstart)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, State.STRING))
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
                stack.append((mstart, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
                stack.append((pos, State.CODE))
                spans.append(Comment(StringView(doc, start, pos)))
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, State.STRING))
            else:
                assert False
        elif state is State.NESTED_COMMENT:
            if tok is Token.COMMENT_OPEN:
                stack.append((mstart, State.NESTED_COMMENT))
            elif tok is Token.COMMENT_CLOSE:
                stack.pop()
            elif tok is Token.STRING_DELIM:
                stack.append((mstart, State.STRING))
            else:
                assert False
        else:
            assert False

    return spans

# Conversion
# ----------

LIT_OPEN = re.compile(r"[(][*][|][ \t]*")
LIT_CLOSE = re.compile(r"[ \t]*[|]?[*][)]\Z")

DEFAULT_HEADER = ".. coq::"
DIRECTIVE = re.compile(r"([ \t]*)([.][.] coq::.*)?")

Lit = namedtuple("Lit", "lines suffix indent")
CodeBlock = namedtuple("CodeBlock", "lines indent")

def lit(lines, indent):
    strip_deque(lines)
    m = lines and lines[-1].s.match(DIRECTIVE)
    indent, directive = m.groups() if m else (indent, None)
    if directive:
        directive = lines.pop()
        strip_deque(lines)
    else:
        directive = indent + DEFAULT_HEADER
    return Lit(lines, suffix=directive, indent=indent)

def number_lines(span, start, indent):
    lines = span.split("\n")
    d = deque(Line(num, s, indent) for (num, s) in enumerate(lines, start=start))
    return start + len(lines) - 1, d

def gen_rst(spans):
    linum, indent, prefix = 0, "", (DEFAULT_HEADER,)
    for span in spans:
        if isinstance(span, Comment):
            linum, lines = number_lines(span.v.trim(LIT_OPEN, LIT_CLOSE), linum, "")
            span = lit(lines, indent)
            indent, prefix = span.indent, ("", span.suffix)
            yield from span.lines
        else:

            linum, lines = number_lines(span.v, linum, indent + "   ")
            strip_deque(lines)
            if lines:
                yield from prefix
                yield ""
                yield from lines
                yield ""

def isolate_literate_comments(code, spans):
    code = StringView(code, 0, len(code))
    code_acc = code[0:0]
    for span in spans:
        if isinstance(span, Comment) and span.v.match(LIT_OPEN):
            if code_acc:
                yield Code(code_acc)
            code_acc = code[span.v.end:span.v.end]
            yield span
        else:
            code_acc += span.v
    if code_acc:
        yield Code(code_acc)

def coq2rst(code):
    ls = ((l.indent + str(l.s) if isinstance(l, Line) else l)
          for l in gen_rst(isolate_literate_comments(code, coq_partition(code))))
    return "\n".join(ls)

# reStructuredText → Coq
# ======================

import docutils.nodes
import docutils.parsers.rst
from docutils import nodes, parsers

# ReST parsing
# ------------

class coqnode(nodes.inline):
    pass

class CoqDirective(parsers.rst.Directive):
    optional_arguments = 1
    final_argument_whitespace = True
    has_content = True

    def rel_line(self, lineno):
        source, line = self.state_machine.get_source_and_line(lineno)
        return line if source == self.state_machine.document['source'] else None

    def run(self):
        line, content_line = self.rel_line(self.lineno), self.rel_line(self.content_offset)
        if line is None: # Skip ‘.. coq’ directives from included files
            return []
        assert content_line is not None
        end = content_line + len(self.content) + 1
        return [coqnode(span=(line - 1, end - 1))] # Use 0-indexed linums

parsers.rst.directives.register_directive("coq", CoqDirective)

def rst_partition(s):
    parser = parsers.rst.Parser()
    settings = docutils.frontend.OptionParser((parsers.rst.Parser,)).get_default_values()
    document = docutils.utils.new_document("<input>", settings)
    parser.parse(s, document)
    for node in document.traverse(coqnode):
        yield node['span']

# Conversion
# ----------

# FIXME either get rid of \t or disallow it
INDENTATION = re.compile("^[ \t]*")

def indentation(line):
    return INDENTATION.match(line).end()

def fmt_rst_block(lines, directive, beg, end, keep_empty):
    if beg == end and not directive:
        if keep_empty:
            yield "(*||*)"
    else:
        yield "(*|"
        yield from islice(lines, beg, end)
        if directive:
            yield ""
            yield directive
        yield "|*)"

def trim_rst_block(lines, directive, indent, lit_beg, lit_end):
    keep_empty = directive is not None
    lit_beg, lit_end = strip_block(lines, lit_beg, lit_end)

    directive_indent = indentation(directive) if directive else indent
    if directive and directive.strip() == DEFAULT_HEADER and directive_indent == indent:
        directive = None

    if directive:
        indent = directive_indent
    elif lit_beg < lit_end:
        indent = indentation(lines[lit_end - 1])

    return indent, "\n".join(fmt_rst_block(lines, directive, lit_beg, lit_end, keep_empty))

def strip_indent(line, indent):
    if not blank(line[:indent]):
        MSG = "Unexpected indentation: {!r} (expected at least {} spaces)"
        raise ValueError(MSG.format(line, indent))
    return line[indent:]

def trim_code_block(lines, indent, code_beg, code_end):
    code_beg, code_end = strip_block(lines, code_beg, code_end)
    return "\n".join(strip_indent(lines[linum], indent) for linum in range(code_beg, code_end))

def gen_coq(s):
    lines = s.splitlines()
    rst_beg, last_indent = 0, 0
    for (beg, end) in rst_partition(s):
        last_indent, rst = trim_rst_block(lines, lines[beg], last_indent, rst_beg, beg)
        yield rst
        yield trim_code_block(lines, last_indent + 3, beg + 1, end)
        rst_beg = end
    _, rst = trim_rst_block(lines, None, last_indent, rst_beg, len(lines))
    if rst:
        yield rst

def rst2coq(rst):
    return "\n\n".join(gen_coq(rst))

# CLI
# ===

# FIXME replace by cli.py
import argparse
import sys
from os import path

def parse_arguments():
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
    args = parse_arguments()
    if args.input == "-":
        contents = sys.stdin.read()
    else:
        with open(args.input) as fstream:
            contents = fstream.read()
    sys.stdout.write(args.fn(contents))

def doctest():
    import doctest
    doctest.debug(sys.modules.get('__main__'), "__main__.partition", pm=True)

if __name__ == '__main__':
    main()
