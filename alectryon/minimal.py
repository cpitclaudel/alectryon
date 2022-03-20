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

"""Minimal shims to compile Alectryon docs without Alectryon.

If you start from reST files, this script is enough.  If you start from Coq
files, you also need literate.py to convert .v files to .rst.

Invoke with ``python3 -m alectryon.minimal --help``.
"""

# pylint: disable=dangerous-default-value

from typing import Dict, Any

from docutils import nodes
from docutils.parsers.rst import directives, roles, Directive # type: ignore
import docutils.parsers.rst.directives.body # type: ignore # pylint: disable=unused-import

## Directives

class ProverDirective(directives.body.CodeBlock):
    final_argument_whitespace = True
    option_spec: Dict[str, Any] = {}

    def run(self):
        self.arguments = [self.name] # Ignore arguments
        return super().run()

class NoOp(Directive):
    has_content = True
    def run(self):
        return []

class Id(Directive):
    has_content = True
    def run(self):
        return [nodes.literal("".join(self.content))]

ALL_LANGUAGES = ["coq", "dafny", "lean3", "lean4"]

# Treat .. coq:: as a regular code block and ignore .. alectryon-toggle::
DIRECTIVES = {**{lang: ProverDirective for lang in ALL_LANGUAGES},
              "alectryon-toggle": NoOp,
              "exercise": Id,
              "directive": NoOp,
              "massert": NoOp,
              "mquote": Id}

## Map :coq: to plain literals

def custom_code_role(lang):
    def _code_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
        options = {**options, "language": lang, "classes": "highlight"}
        return roles.code_role(role, rawtext, text, lineno, inliner, options, content)
    return _code_role

def no_op(role, rawtext, text, lineno, inliner, options={}, content=[]):
    return roles.generic_custom_role(
        role, rawtext, text, lineno, inliner, options, content)
no_op.options = { # type: ignore
    'url': directives.unchanged,
    'counter-style': directives.unchanged,
    'prefix': directives.unchanged,
    'kind': directives.unchanged,
    'language': directives.unchanged,
}

ROLES = {
    **{lang: custom_code_role(lang) for lang in ALL_LANGUAGES},
    "coqid": no_op,
    "alectryon-bubble": no_op,
    "mref": no_op,
    "mquote": no_op,
}

def docutils_setup():
    for name, directive in DIRECTIVES.items():
        directives.register_directive(name, directive)
    for name, role in ROLES.items():
        roles.register_canonical_role(name, role)

def cli():
    """Run a minimal Alectryon that skips special roles and directives.

    >>> from . import docutils as ref
    >>> sorted(set(d.name for d in ref.DIRECTIVES) ^ set(DIRECTIVES))
    []
    >>> sorted(set(r.name for r in ref.ROLES) - set(ROLES))
    []
    """

    import locale
    locale.setlocale(locale.LC_ALL, '')
    from docutils.core import publish_cmdline, default_description
    docutils_setup()
    DESCRIPTION = 'Convert reSt + Alectryon to HTML.' + default_description
    publish_cmdline(writer_name='html', description=(DESCRIPTION + default_description))

if __name__ == '__main__':
    cli()
