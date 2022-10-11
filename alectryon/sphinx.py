# Copyright © 2020 Clément Pit-Claudel
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

import os.path

from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from sphinx.application import Sphinx

from . import core, docutils
from .html import ASSETS as HTML_ASSETS
from .latex import ASSETS as LATEX_ASSETS
from .pygments import LatexFormatter

# Setup
# =====

# FIXME: Test

def register_source_suffixes(app: "Sphinx", lang: str, markup: str):
    for markup_ext in core.EXTENSIONS_BY_MARKUP[markup]:
        for lang_ext in core.EXTENSIONS_BY_LANGUAGE[lang]:
            suffix = "{}{}".format(markup_ext, lang_ext)
            app.add_source_suffix(suffix, lang, override=True)

def register_default_source_suffixes(app: "Sphinx"):
    for lang, lang_exts in core.EXTENSIONS_BY_LANGUAGE.items():
        for suffix in lang_exts:
            supported = "{}+{}".format(lang, core.DEFAULT_MARKUP)
            app.add_source_suffix(suffix, supported, override=True)

def register_code_parsers(app: "Sphinx"):
    for parser in docutils.CUSTOM_PARSERS.values():
        app.add_source_parser(parser)
        register_source_suffixes(app, parser.LANG, parser.MARKUP)
    register_default_source_suffixes(app)

def add_assets(app: "Sphinx"):
    app.config.html_static_path.append(HTML_ASSETS.PATH)

    for css in HTML_ASSETS.ALECTRYON_CSS:
        app.add_css_file(css) # Not PYGMENTS_CSS: Sphinx generates its own
    for js in HTML_ASSETS.ALECTRYON_JS:
        app.add_js_file(js)

    for sty in LATEX_ASSETS.ALECTRYON_STY: # Not PYGMENTS_STY: Sphinx generates its own
        app.config.latex_additional_files.append(os.path.join(LATEX_ASSETS.PATH, sty))
        app.add_latex_package(sty.replace(".sty", ""))

def setup(app: "Sphinx"):
    """Register Alectryon's directives, transforms, etc."""
    register_code_parsers(app)

    for role in docutils.ROLES:
        app.add_role(role.name, role)

    for directive in docutils.DIRECTIVES:
        app.add_directive(directive.name, directive)

    # All custom nodes are removed by transforms or events,
    # so no need for ``app.add_node(...)``

    if app.config.default_role is None:
        app.config.default_role = "coq" # type: ignore

    for (_doc, _flags, opts) in docutils.ALECTRYON_SETTINGS:
        if opts["dest"] not in ("pygments_style",): # Already in Sphinx
            app.add_config_value(opts["dest"], opts["default"], "env")

    # All custom transforms are run through pending nodes, so no need for
    # ``app.add_transform(...)`` — except for MyST and for post_transforms.

    # (This specific transformation is not strictly necessary in all cases, as
    # only MyST disables math processing at the level of the whole document; but
    # since there's an open Sphinx PR to do that in all cases, better do it
    # right away.)
    app.add_transform(docutils.ActivateMathJaxTransform)

    for transform in docutils.TRANSFORMS:
        if transform.is_post_transform:
            app.add_post_transform(transform)

    # Sphinx uses PYG instead of PY for pygments
    LatexFormatter.COMMANDPREFIX = 'PYG'

    app.connect('builder-inited', add_assets)

    return {'version': '0.1', "parallel_read_safe": True}
