# Configuration file for the Sphinx documentation builder.

# -- Path setup --------------------------------------------------------------

import os
import sys
sys.path.insert(0, os.path.abspath('../../'))

# -- Project information -----------------------------------------------------

project = 'alectryon-demo'
copyright = '2019-2021, Clément Pit-Claudel'
author = 'Clément Pit-Claudel'

# -- General configuration ---------------------------------------------------

extensions = ["alectryon.sphinx", "sphinx.ext.mathjax"]

try:
    import myst_parser
    extensions.append("myst_parser")
except ImportError:
    print("/!\\ `myst_parser` not found, skipping MyST tests /!\\", file=sys.stderr)

# -- Options for HTML output -------------------------------------------------

html_theme = 'alabaster'
html_static_path = ['_static']

# -- Alectryon configuration -------------------------------------------------

import alectryon.docutils
alectryon.docutils.CACHE_DIRECTORY = "_build/alectryon/"

# -- MathJax configuration ---------------------------------------------------

from sphinx.ext import mathjax
mathjax.MATHJAX_URL = alectryon.docutils.HtmlTranslator.MATHJAX_URL # MathJax 3

# This configuration is explained in README.rst
# Use either this (Sphinx ≥ 4.0 only):

html_js_files = ['mathjax_config.js']
mathjax_options = { "priority": 1000 }

# or this (but inline the configuration instead of open(…).read()):

html_js_files = [
    (None, {
        "body": open("_static/mathjax_config.js").read(),
        "priority": 0
    })
]

# or this:

html_js_files = [('mathjax_config.js', { "priority": 0 })]
