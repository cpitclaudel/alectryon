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

from docutils.parsers.rst import directives, roles, Directive
import docutils.parsers.rst.directives.body # pylint: disable=unused-import

## Directives

class CoqDirective(directives.body.CodeBlock):
    final_argument_whitespace = True
    option_spec = {}

    def run(self):
        self.arguments = ["coq"] # Ignore arguments
        return super().run()

class NoOp(Directive):
    def run(self):
        pass

# Treat .. coq:: as a regular code block and ignore .. alectryon-toggle::
DIRECTIVES = {"coq": CoqDirective,
              "alectryon-toggle": NoOp}

## Map :coq: to plain literals

def coq_code_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
    options = {**options.copy(), "language": "coq", "classes": "highlight"}
    return roles.code_role(role, rawtext, text, lineno, inliner, options, content)

def no_op(role, rawtext, text, lineno, inliner, options={}, content=[]):
    return roles.generic_custom_role(
        role, rawtext, text, lineno, inliner, options, content)
no_op.options = {'url': directives.unchanged}

ROLES = {"coqid": no_op,
         "coq": coq_code_role,
         "alectryon-bubble": no_op}

def docutils_setup():
    for name, directive in DIRECTIVES.items():
        directives.register_directive(name, directive)
    for name, role in ROLES.items():
        roles.register_canonical_role(name, role)

def cli():
    import locale
    locale.setlocale(locale.LC_ALL, '')
    from docutils.core import publish_cmdline, default_description
    docutils_setup()
    DESCRIPTION = 'Convert reSt + Alectryon to HTML.' + default_description
    publish_cmdline(writer_name='html', description=(DESCRIPTION + default_description))

if __name__ == '__main__':
    cli()
