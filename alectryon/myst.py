# Copyright © 2021 Clément Pit-Claudel
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

"""MyST support for Alectryon.

This file extends ``docutils.py`` to expose a convenient interface for
connecting with MyST.

This is mostly useful through Alectryon's command line.  For integration with
Sphinx, use the ``myst_parser`` and the ``alectryon.sphinx`` plugins.
"""

from typing import Type

import docutils.parsers

try:
    from myst_parser.docutils_ import Parser as MystParser # type: ignore

    # https://github.com/executablebooks/MyST-Parser/issues/347
    # https://github.com/executablebooks/MyST-Parser/pull/419
    class RealParser(MystParser):
        def get_transforms(self):
            from .docutils import ActivateMathJaxTransform
            return super().get_transforms() + [ActivateMathJaxTransform]

    Parser: Type[docutils.parsers.Parser] = RealParser

except ImportError as err:
    class FallbackParser(docutils.parsers.Parser):
        def parse(self, inputstring, document):
            document.append(document.reporter.severe(
                'Cannot parse Markdown input without Python package `myst_parser`.'))
    Parser = FallbackParser
