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

from typing import Dict, Optional

import re
import warnings
from collections import deque
from textwrap import indent
from contextlib import contextmanager
from functools import lru_cache

import pygments
import pygments.styles
import pygments.formatters
from pygments.token import Error, STANDARD_TYPES, Name, Operator, Text
from pygments.filter import Filter
from pygments.filters import TokenMergeFilter, NameHighlightFilter
from pygments.formatter import Formatter
from pygments.lexers import get_lexer_by_name # pylint: disable=no-name-in-module

from dominate.util import raw as dom_raw

from .pygments_lexer import CoqLexer, TokenizedStrLexer
from .pygments_style import AlectryonStyle

def resolve_token(kind):
    # FIXME: add support for Lean
    tokentype = CoqLexer.TOKEN_TYPES.get(kind) if isinstance(kind, str) else kind
    if not tokentype:
        raise ValueError("Unknown token kind: {}".format(kind))
    return tokentype

CUSTOM_LEXERS = {
    'CoqLexer': CoqLexer,
    'TokenizedStrLexer': TokenizedStrLexer,
}
CUSTOM_LEXER_ALIASES: Dict[str, str] = {
    "lean3": "lean",
    "lean4": "lean"
}
CUSTOM_LEXERS_BY_ALIAS = {
    alias: Lx for Lx in CUSTOM_LEXERS.values() for alias in Lx.aliases
}

@lru_cache(maxsize=None)
def get_lexer(lang):
    alias = CUSTOM_LEXER_ALIASES.get(lang, lang)
    # LATER: Upstream Coq lexer, remove this branch
    if alias in CUSTOM_LEXERS_BY_ALIAS:
        lexer = CUSTOM_LEXERS_BY_ALIAS[alias](ensurenl=False)
        # Custom lexers only, since some lexers report plenty of errors
        lexer.add_filter(WarnOnErrorTokenFilter())
    else:
        lexer = get_lexer_by_name(alias, ensurenl=False)
        lexer.add_filter(StripErrorsTokenFilter())
    lexer.add_filter(TokenMergeFilter())
    return lexer

def add_tokens(tokens, lang="coq"):
    """Register additional `tokens` to add custom syntax highlighting.

    `tokens` should be a dictionary, whose keys indicate a type of token and
    whose values are lists of strings to highlight with that token type.

    The return value is a list of Pygments filters.

    This is particularly useful to highlight custom tactics or symbols.  For
    example, if your code defines a Coq tactic ``map_eq`` to decide map equalities,
    and two tactics ``map_simplify`` and ``map_subst`` to simplify map
    expressions, you might write the following:

    >>> filters = add_tokens({
    ...     'tacn-solve': ['map_eq'],
    ...     'tacn': ['map_simplify', 'map_subst']
    ... })
    """
    filters = []
    for tokentype, names in tokens.items():
        tokentype = resolve_token(tokentype)
        filters.append(NameHighlightFilter(names=names, tokentype=tokentype))
    lexer = get_lexer(lang)
    for f in filters:
        lexer.add_filter(f)
    return filters

@contextmanager
def added_tokens(tokens, lang):
    """Temporarily register additional syntax-highlighting tokens.

    `tokens` should be as in ``add_tokens``.  This is intended to be used as a
    context manager.
    """
    added = add_tokens(tokens, lang)
    try:
        yield
    finally:
        lexer = get_lexer(lang)
        lexer.filters[:] = [f for f in lexer.filters if f not in added]

WHITESPACE_RE = re.compile(r"\A(\s*)(.*?)(\s*)\Z", re.DOTALL)

def _highlight(code, lexer, formatter):
    # See https://bitbucket.org/birkenfeld/pygments-main/issues/1522/ to
    # understand why we munge the STANDARD_TYPES dictionary
    with munged_dict(STANDARD_TYPES, {Name: '', Operator: ''}):
        # Pygments' HTML formatter adds an unconditional newline, so we pass it only
        # the code, and we restore the spaces after highlighting.
        beg, end = WHITESPACE_RE.match(code).span(2) # Preserve subclass of ``code``
        return code[:beg], pygments.highlight(code[beg:end], lexer, formatter).strip(), code[end:]

def validate_style(name):
    if isinstance(name, str):
        known_styles = sorted(pygments.styles.get_all_styles())
        if name not in known_styles:
            MSG = "Unknown Pygments style `{}`.  Expecting one of {}."
            raise ValueError(MSG.format(name, ", ".join(known_styles)))
    return name

def _get_style(name):
    # Pygments' style resolver will only work for "alectryon" if Alectryon
    # is installed via Pip, hence the special case here.
    if name in (None, AlectryonStyle.name):
        return AlectryonStyle
    return validate_style(name)

class HtmlFormatter(pygments.formatters.HtmlFormatter): # pylint: disable=no-member
    def get_linenos_style_defs(self):
        return [l for l in super().get_linenos_style_defs()
                if not l.startswith("pre {")]

class LatexFormatter(pygments.formatters.LatexFormatter): # pylint: disable=no-member
    COMMANDPREFIX: Optional[str] = None
    def __init__(self, **options):
        if self.COMMANDPREFIX:
            options.setdefault("commandprefix", self.COMMANDPREFIX)
        super().__init__(**options)

@lru_cache(maxsize=None)
def get_formatter(fmt, style=None) -> Formatter:
    style = _get_style(style)
    if fmt == "html":
        return HtmlFormatter(nobackground=True, nowrap=True, style=style)
    if fmt == "latex":
        return LatexFormatter(nobackground=True, nowrap=True, style=style)
    raise ValueError("Unknown format {}".format(fmt))

def get_stylesheet(fmt, style):
    return get_formatter(fmt, style).get_style_defs(('.highlight', '.code')) # type: ignore

def highlight_html(code, lang, style=None):
    """Highlight a string `code` in language `lang`.

    Return a raw HTML string.  This function is just a convenience wrapper
    around Pygments' machinery, using a custom style and, for Coq code, a custom
    lexer.

    The resulting code needs to be paired with a Pygments stylesheet, which can
    be generated by running the following commands for HTML and LaTeX output,
    respectively::

        pygmentize -S default -f html -a .highlight > pygments.css
        pygmentize -S default -f latex > pygments.sty

    You may replace ``default`` with any style known to Pygments (use
    ``pygmentize -L styles`` to see a list).

    If you use Alectryon's command line interface directly, you won't have to
    jump through that last hoop: it renders and writes out the HTML for you,
    with the appropriate CSS inlined or linked to.  It might be instructive to
    consult the implementation of ``alectryon.cli.dump_html_standalone`` to see
    how the CLI does it.

    >>> str(highlight_html("Program Fixpoint a.", lang="coq"))
    '<span class="kn">Program Fixpoint</span> <span class="nf">a</span>.'
    """
    return dom_raw("".join(_highlight(code, get_lexer(lang), get_formatter("html", style))))

PYGMENTS_LATEX_PREFIX = r"\begin{Verbatim}[commandchars=\\\{\}]" + "\n"
PYGMENTS_LATEX_SUFFIX = r"\end{Verbatim}"

def highlight_latex(code, lang,
                    prefix=PYGMENTS_LATEX_PREFIX,
                    suffix=PYGMENTS_LATEX_SUFFIX,
                    style=None):
    """Highlight a string `code` in language `lang`.

    Like ``highlight_html``, but return a plain LaTeX string.
    """
    before, tex, after = _highlight(code, get_lexer(lang), get_formatter("latex", style))
    if tex.startswith(r"\begin"):
        # LATER: Remove (Pygments 2.12.0+ / 231366c7 recognizes nowrap for LaTeX)
        assert tex.startswith(PYGMENTS_LATEX_PREFIX) and tex.endswith(PYGMENTS_LATEX_SUFFIX), tex
        tex = tex[len(PYGMENTS_LATEX_PREFIX):-len(PYGMENTS_LATEX_SUFFIX)]
    return prefix + before + tex + after + suffix

HIGHLIGHTERS = {"html": highlight_html, "latex": highlight_latex}

@contextmanager
def munged_dict(d, updates):
    saved = d.copy()
    d.update(updates)
    try:
        yield
    finally:
        d.update(saved)

class Highlighter: # LATER: dataclass
    def __init__(self, fmt, lang, style=None):
        self.kwargs = {"lang": lang, "style": style}
        self.highlighter = HIGHLIGHTERS[fmt]

    def __call__(self, code, **kwargs):
        return self.highlighter(code, **{**self.kwargs, **kwargs})

    @contextmanager
    def override(self, **kwargs):
        assert set(kwargs.keys()) <= {"lang", "style"}
        with munged_dict(self.kwargs, kwargs):
            yield

def make_highlighter(fmt, lang, style=None):
    return Highlighter(fmt, lang, style)

class WarnOnErrorTokenFilter(Filter):
    """Print a warning when the lexer generates an error token."""

    def filter(self, _lexer, stream):
        history = deque(maxlen=80)
        for typ, val in stream:
            history.extend(val)
            if typ is Error:
                ell = '...' if len(history) == history.maxlen else ''
                context = ell + ''.join(history).lstrip()
                MSG = ("!! Warning: Unexpected token during syntax-highlighting: {!r}\n"
                       "!! Alectryon's lexer isn't perfect: please send us an example.\n"
                       "!! Context:\n{}")
                warnings.warn(MSG.format(val, indent(context, ' ' * 8)))
            yield typ, val

class StripErrorsTokenFilter(Filter):
    """Change ``Error`` tokens to ``Text`` ones.

    >>> f = StripErrorsTokenFilter()
    >>> list(f.filter(None, [(Error, "err")]))
    [(Token.Text, 'err')]
    """

    def filter(self, _lexer, stream):
        for typ, val in stream:
            if typ is Error:
                typ = Text
            yield typ, val

def replace_builtin_lexers():
    """Patch pygments to replace its Coq Lexer and register aliases.

    https://stackoverflow.com/questions/40514205/ describes a way to register
    entry points dynamically, so we could use that to play nice with pygments
    architecture, but it wouldn't pick up our Lexer (it would stick with the
    built-in one).
    """ # FIXME replace the formatter too?
    from pygments.lexers import _lexer_cache
    from pygments.lexers._mapping import LEXERS

    for nm, Lx in CUSTOM_LEXERS.items():
        dflt = (None, Lx.name, tuple(Lx.aliases), tuple(Lx.filenames), tuple(Lx.mimetypes))
        meta = ("alectryon.pygments_lexer", *LEXERS.get(nm, dflt)[1:])
        LEXERS[nm] = meta
        _lexer_cache.pop(meta[1], None)

    for dst, src in CUSTOM_LEXER_ALIASES.items():
        for key, (mod, name, aliases, fnames, mimes) in LEXERS.items():
            if src.lower() in aliases:
                LEXERS[key] = (mod, name, aliases + (dst,), fnames, mimes)
                _lexer_cache.pop(name, None)
