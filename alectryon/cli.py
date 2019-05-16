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

import argparse
import json
import os.path
import re

from dominate import tags, document

from . import core
from .core import CoqSentence, CoqGoal, CoqHypothesis, CoqText, annotate, GENERATOR, __version__
from .html import gen_html
from .pygments import FORMATTER

ARGDOC = ".\n".join([
    core.__doc__, "When run as a standalone application, take input as multiple "
    ".v or .json files, and create one .io.json file per input file."
])

COQ_SPLIT_RE = re.compile(r"(\n(?:[ \t]*\n)+)")

def read_input(fpath):
    _fdir, fname = os.path.split(fpath)
    _fn, fext = os.path.splitext(fname)
    if fext == '.v':
        with open(fpath) as src:
            return fname, COQ_SPLIT_RE.split(src.read())
    elif fext == '.json':
        with open(fpath) as src:
            return fname, json.load(src)
    else:
        msg = "Input files must have extension .v or .json ({})."
        raise argparse.ArgumentTypeError(msg.format(fname))

def parse_arguments():
    parser = argparse.ArgumentParser(description=ARGDOC)
    add = parser.add_argument

    INPUT_HELP = """Input file.  Can be either .v (plain Coq code) or \
.json (a list of Coq fragments)."""
    add("input", nargs="+", type=read_input, help=INPUT_HELP)

    WRITER_HELP = """Output type"""
    WRITER_CHOICES = ("json", "html", "webpage")
    add("--writer",
        default="webpage",
        choices=WRITER_CHOICES,
        help=WRITER_HELP)

    DEBUG_HELP = "Print communications with SerAPI."
    add("--debug", action="store_true", default=False, help=DEBUG_HELP)

    return parser.parse_args()

COQ_TYPES = (CoqSentence, CoqGoal, CoqHypothesis, CoqText)
COQ_TYPE_NAMES = {
    "CoqHypothesis": "hypothesis",
    "CoqGoal": "goal",
    "CoqSentence": "sentence",
    "HTMLSentence": "html_sentence",
    "CoqText": "text",
}

def prepare_json(obj):
    if isinstance(obj, list):
        return [prepare_json(x) for x in obj]
    if isinstance(obj, dict):
        return {k: prepare_json(v) for k, v in obj.items()}
    if isinstance(obj, COQ_TYPES):
        d = {k: prepare_json(v) for k, v in zip(obj._fields, obj)}
        nm = COQ_TYPE_NAMES[type(obj).__name__]
        return {"_type": nm, **d}
    return obj

def write_json(fname, annotated):
    with open("{}.io.json".format(fname), mode="w") as out:
        json.dump(prepare_json(annotated), out, indent=4)

def write_html(fname, annotated):
    ts = list(gen_html(annotated))
    with open("{}.snippets.html".format(fname), mode="w") as out:
        for t in ts:
            out.write(t.render(pretty=False))
            out.write('\n')

def write_webpage(fname, annotated):
    doc = document(title=fname)
    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))
    doc.head.add(tags.link(rel="stylesheet", href="alectryon.css"))

    FIRA_CODE_CDN = "https://unpkg.com/firacode/distr/fira_code.css"
    doc.head.add(tags.link(rel="stylesheet", href=FIRA_CODE_CDN))

    pygments_css = FORMATTER.get_style_defs('.highlight')
    doc.head.add(tags.style(pygments_css, type="text/css"))

    for t in gen_html(annotated):
        doc.body.add(t)

    with open("{}.html".format(fname), mode="w") as out:
        out.write(doc.render(pretty=False))

WRITERS = {'json': write_json, 'html': write_html, 'webpage': write_webpage}

def main():
    args = parse_arguments()
    core.DEBUG = args.debug

    for fname, chunks in args.input:
        annotated = annotate(chunks)
        WRITERS[args.writer](fname, annotated)
