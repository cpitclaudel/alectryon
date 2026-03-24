# Configuration file for the Sphinx documentation builder.
#
# For the full list of built-in configuration values, see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

import sys
from pathlib import Path
from importlib.util import find_spec
sys.path.insert(0, str(Path('../../').resolve())) # Add Alectryon to path

# -- Project information -----------------------------------------------------
# https://www.sphinx-doc.org/en/master/usage/configuration.html#project-information

project = 'alectryon-demo'
copyright = '2019-2026, Clément Pit-Claudel'
author = 'Clément Pit-Claudel'
today = " "

# -- Sphinx configuration ----------------------------------------------------

html_theme = 'alabaster'
html_static_path = ['_static']

pygments_style = "emacs"
latex_engine = "xelatex"
latex_elements = {
    'fontpkg': r'''
\setmainfont{Linux Libertine O}
\setsansfont{Linux Biolinum O}
\setmonofont[Scale=MatchLowercase,AutoFakeSlant=0.2]{Fira Code}
''',
}

myst_enable_extensions = ["dollarmath"]

# -- Alectryon configuration -------------------------------------------------

if find_spec("myst_parser"):
    # Import Alectryon and turn on Markdown and math support
    extensions = ["alectryon.sphinx", "myst_parser", "sphinx.ext.mathjax"]
else:
    # Skip Markdown files if ``myst_parser`` isn't available
    extensions = ["alectryon.sphinx", "sphinx.ext.mathjax"]
    print("/!\\ `myst_parser` not found, skipping MyST tests /!\\", file=sys.stderr)

import alectryon.docutils
alectryon.docutils.CACHE_DIRECTORY = "_build/alectryon/"

# Change the following lines to adjust the default Markup language or driver:

from alectryon import core
core.DEFAULT_MARKUP = core.DEFAULT_MARKUP # Change to "md" or "rst"
core.DEFAULT_DRIVERS["coq"] = core.DEFAULT_DRIVERS["coq"] # Change to "coqlsp" or "vsrocq"

# -- MathJax configuration ---------------------------------------------------
# This configuration is explained in recipes/mathjax.rst

from sphinx.ext import mathjax
mathjax.MATHJAX_URL = alectryon.docutils.HtmlTranslator.MATHJAX_URL # MathJax 3

# If you want to use MathJax to postprocess Alectryon's output (not just to
# include math in your pages), you need a special MathJax config.  You have
# three options:

# 1. Inline your config in every generated file.  In that case, replace
#    ``Path(…).read_text()`` below with the file's contents:

html_js_files = [(None, { "body": Path("_static/mathjax_config.js").read_text(),
                       "priority": 1000 } )]

# 2. Put your MathJax config in a separate file in ``_static/``:

html_js_files = ['mathjax_config.js']
mathjax_options = { "priority": 1000 }

# 3. Configure MathJax by hand in each source file.  In that case, include your
#    MathJax configuration in an inline ``<script>`` block in your document in
#    addition to the setting below.

mathjax_loading_method = "defer"
