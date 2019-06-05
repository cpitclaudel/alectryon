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

import re

import pygments
import pygments.lexers
from pygments.filters import TokenMergeFilter
from pygments.formatters import HtmlFormatter

from dominate import tags
from dominate.util import raw as dom_raw

from .pygments_lexer import CoqLexer
from .pygments_style import TangoSubtleStyle

LEXER = CoqLexer(ensurenl=False)  # pylint: disable=no-member
LEXER.add_filter(TokenMergeFilter())
FORMATTER = HtmlFormatter(nobackground=True, nowrap=True, style=TangoSubtleStyle)
WHITESPACE_RE = re.compile(r"^(\s*)((?:.*\S)?)(\s*)$", re.DOTALL)

def highlight(coqstr):
    # Pygments HTML formatter adds an unconditional newline, so we pass it only
    # the code, and we restore the spaces after highlighting.
    before, code, after = WHITESPACE_RE.match(coqstr).groups()
    highlighted = pygments.highlight(code, LEXER, FORMATTER).strip()
    return tags.span(before, dom_raw(highlighted), after, cls="highlight")
