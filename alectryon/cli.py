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
import inspect
import os.path
import sys

# pylint: disable=import-outside-toplevel

def load_json(contents):
    from json import loads
    return loads(contents)

def parse_coq_plain(contents):
    return [contents]

def coq_to_rst(coq, point, marker):
    from .literate import coq2rst_marked
    return coq2rst_marked(coq, point, marker)

def rst_to_coq(coq, point, marker):
    from .literate import rst2coq_marked
    return rst2coq_marked(coq, point, marker)

def annotate_chunks(chunks, serapi_args):
    from .core import annotate
    return annotate(chunks, serapi_args)

DOCUTILS_CSS = "https://cdn.rawgit.com/matthiaseisen/docutils-css/master/docutils_basic.css"
MATHJAX_URL = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.0/MathJax.js?config=TeX-AMS_HTML-full"

def gen_docutils_html(document):
    pass # FIXME

def _init_docutils_settings(components):
    from docutils.frontend import OptionParser
    return OptionParser(components=components).get_default_values()

def _lint_docutils(source, parser, document):
    from io import StringIO
    from .docutils import JsErrorPrinter
    document.reporter.stream = False # Disable textual reporting
    observer = JsErrorPrinter(StringIO(), document.settings)
    document.reporter.attach_observer(observer)
    parser.parse(source, document)
    return observer.stream.getvalue()

def _parse_docutils(source, parser, document):
    parser.parse(source, document)
    document.transformer.apply_transforms()
    return document

def _prepare_docutils_parser(fpath, Parser, Reader):
    from docutils.utils import new_document
    from .docutils import register
    register()
    parser = Parser()
    reader = Reader(parser)
    settings = _init_docutils_settings((Parser, Reader))
    document = new_document(fpath, settings)
    document.transformer.populate_from_components((parser, reader))
    return parser, document

def _prepare_coq_rst_parser(fpath):
    from .docutils import CoqReSTParser, StandaloneCoqReSTReader
    return _prepare_docutils_parser(fpath, CoqReSTParser, StandaloneCoqReSTReader)

def _prepare_rst_parser(fpath):
    from docutils.parsers.rst import Parser
    from docutils.readers.standalone import Reader
    return _prepare_docutils_parser(fpath, Parser, Reader)

def parse_coq_rst(coq, fpath):
    return _parse_docutils(coq, *_prepare_coq_rst_parser(fpath))

def lint_coq_rst(coq, fpath):
    return _lint_docutils(coq, *_prepare_coq_rst_parser(fpath))

def parse_rst(rst, fpath):
    return _parse_docutils(rst, *_prepare_rst_parser(fpath))

def lint_rst(rst, fpath):
    return _lint_docutils(rst, *_prepare_rst_parser(fpath))

def gen_html_snippets(annotated):
    from .html import HtmlWriter
    from .pygments import highlight
    return HtmlWriter(highlight).gen_html(annotated)

def copy_assets(state, no_assets, output_directory):
    from .html import copy_assets as cp
    if not no_assets:
        cp(output_directory)
    return state

def dump_html_standalone(snippets, fname):
    from dominate import tags, document
    from .core import SerAPI
    from .html import gen_header, GENERATOR, CSS_ASSETS, JS_ASSETS
    from .pygments import FORMATTER

    doc = document(title=fname)
    doc.set_attribute("class", "alectryon-standalone")

    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))
    for css in CSS_ASSETS:
        doc.head.add(tags.link(rel="stylesheet", href=css))
    for js in JS_ASSETS:
        doc.head.add(tags.script(src=js))

    FIRA_CODE_CDN = "https://unpkg.com/firacode/distr/fira_code.css"
    doc.head.add(tags.link(rel="stylesheet", href=FIRA_CODE_CDN))

    pygments_css = FORMATTER.get_style_defs('.highlight')
    doc.head.add(tags.style(pygments_css, type="text/css"))

    root = doc.body.add(tags.article(cls="alectryon-windowed alectryon-root"))
    root.add(gen_header(SerAPI.version_info()))
    for snippet in snippets:
        root.add(snippet)

    return doc.render(pretty=False)

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
    type_name = COQ_TYPE_NAMES.get(type(obj).__name__)
    if type_name:
        d = {k: prepare_json(v) for k, v in zip(obj._fields, obj)}
        return {"_type": type_name, **d}
    return obj

def dump_json(js):
    from json import dumps
    return dumps(js, indent=4)

def dump_html_snippets(snippets):
    from io import StringIO
    io = StringIO()
    for snippet in snippets:
        io.write(snippet.render(pretty=False))
        io.write('\n')
    return io.getvalue()

def write_file(ext):
    return lambda contents: (contents, ext)

PIPELINES = {
    'json': {
        'json': (load_json, annotate_chunks,
                 prepare_json, dump_json, write_file(".io.json")),
        'snippets-html': (load_json, annotate_chunks, gen_html_snippets,
                          dump_html_snippets, write_file(".snippets.html"))
    },
    'coq': {
        'webpage': (parse_coq_plain, annotate_chunks, gen_html_snippets,
                    dump_html_standalone, copy_assets, write_file(".v.html")),
        'snippets-html': (parse_coq_plain, annotate_chunks, gen_html_snippets,
                          dump_html_snippets, write_file(".snippets.html")),
        'lint': (lint_coq_rst, write_file(".lint")),
        'rst': (rst_to_coq, write_file(".v.rst"))
    },
    'coq+rst': {
        'webpage': (parse_coq_rst, gen_docutils_html, write_file(".html")),
        'lint': (lint_coq_rst, write_file(".lint")),
        'rst': (coq_to_rst, write_file(".v.rst"))
    },
    'rst': {
        'webpage': (parse_rst, gen_docutils_html, write_file(".html")),
        'lint': (lint_rst, write_file(".lint")),
        'coq': (rst_to_coq, write_file(".v")),
        'coq+rst': (rst_to_coq, write_file(".v"))
    }
}

MODES_BY_EXTENSION = [('.v', "coq"), ('.json', "json"), ('.v.rst', "rst"), ('.rst', "rst")]
DEFAULT_BACKENDS = {
    'json': 'json',
    'coq': 'webpage',
    'coq+rst': 'webpage', # FIXME
    'rst': 'webpage' # FIXME
}

def infer_mode(fpath, kind, arg):
    for (ext, mode) in MODES_BY_EXTENSION:
        if fpath.endswith(ext):
            return mode
    MSG = """{}: Not sure what to do with {!r}.
Try passing {arg}?"""
    raise argparse.ArgumentTypeError(MSG.format(fpath, kind, arg))

def infer_frontend(fpath):
    return infer_mode(fpath, "input", "--frontend")

def infer_backend(frontend, out_fpath):
    if out_fpath:
        return infer_mode(out_fpath, "output", "--backend")
    return DEFAULT_BACKENDS[frontend]

def resolve_pipeline(fpath, args):
    frontend = args.frontend or infer_frontend(fpath)

    assert frontend in PIPELINES
    supported_backends = PIPELINES[frontend]

    backend = args.backend or infer_backend(frontend, args.output)
    if backend not in supported_backends:
        MSG = """argument --backend: Frontend {!r} does not support backend {!r}: \
expecting one of {}"""
        raise argparse.ArgumentTypeError(MSG.format(
            frontend, backend, ", ".join(map(repr, supported_backends))))

    return supported_backends[backend]

def fill_in_arguments(args):
    args.point, args.marker = args.mark_point
    if args.point is not None:
        try:
            args.point = int(args.point)
        except ValueError:
            MSG = "argument --mark-point: Expecting a number, not {!r}"
            raise argparse.ArgumentTypeError(MSG.format(args.point))

    if len(args.input) > 1 and args.output:
        MSG = "argument --output: Not valid with multiple inputs"
        raise argparse.ArgumentTypeError(MSG)

    if args.stdin_filename and "-" not in args.input:
        MSG = "argument --stdin-filename: input must be '-'"
        raise argparse.ArgumentTypeError(MSG)

    args.pipelines = [(fpath, resolve_pipeline(fpath, args))
                      for fpath in args.input]

def parse_arguments():
    parser = argparse.ArgumentParser(description="""\
Annotate segments of Coq code with responses and goals.
Take input in Coq, reStructuredText, or JSON format \
and produce reStructuredText, HTML, or JSON output.""")

    INPUT_HELP = "Configure the input."
    out = parser.add_argument_group("Input arguments", INPUT_HELP)

    INPUT_FILES_HELP = "Input files"
    parser.add_argument("input", nargs="+", help=INPUT_FILES_HELP)

    INPUT_STDIN_NAME_HELP = "Name of file passed on stdin, if any"
    parser.add_argument("--stdin-filename", default=None,
                        help=INPUT_STDIN_NAME_HELP)

    FRONTEND_HELP = "Choose a frontend. Defaults: "
    FRONTEND_HELP += "; ".join("{!r} → {}".format(ext, frontend)
                               for ext, frontend in MODES_BY_EXTENSION)
    FRONTEND_CHOICES = sorted(PIPELINES.keys())
    out.add_argument("--frontend", default=None, choices=FRONTEND_CHOICES,
                     help=FRONTEND_HELP)


    OUTPUT_HELP = "Configure the output."
    out = parser.add_argument_group("Output arguments", OUTPUT_HELP)

    BACKEND_HELP = "Choose a backend. Supported: "
    BACKEND_HELP += "; ".join("{} → {{{}}}".format(frontend, ", ".join(sorted(backends)))
                              for frontend, backends in PIPELINES.items())
    BACKEND_CHOICES = sorted(set(b for _, bs in PIPELINES.items() for b in bs))
    out.add_argument("--backend", default=None, choices=BACKEND_CHOICES,
                     help=BACKEND_HELP)

    OUT_FILE_HELP = "Set the output file (default: computed based on INPUT)."
    parser.add_argument("-o", "--output", default=None,
                        help=OUT_FILE_HELP)

    OUT_DIR_HELP = "Set the output directory."
    parser.add_argument("--output-directory", default=".",
                        help=OUT_DIR_HELP)

    NO_ASSETS_HELP = ("When creating webpages, " +
                      "do not copy assets along the generated file.")
    parser.add_argument("--no-assets", action="store_true",
                        default=False, help=NO_ASSETS_HELP)

    MARK_POINT_HELP = "Mark a point in the output with a given marker."
    parser.add_argument("--mark-point", nargs=2, default=(None, None),
                        metavar=("point", "marker"),
                        help=MARK_POINT_HELP)


    SUBP_HELP = "Pass arguments to the SerAPI process"
    subp = parser.add_argument_group("Subprocess arguments", SUBP_HELP)

    SERAPI_ARGS_HELP = "Pass a single argument to SerAPI (e.g. -Q dir,lib)."
    subp.add_argument("--serapi-arg", dest="serapi_args",
                      action="append", default=[],
                      help=SERAPI_ARGS_HELP)

    I_HELP="Pass -I DIR to the SerAPI subprocess."
    subp.add_argument("-I", "--ml-include-path", dest="coq_args_I",
                      metavar="dir", nargs=1, action="append",
                      default=[], help=I_HELP)

    Q_HELP="Pass -Q DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-Q", "--load-path", dest="coq_args_Q",
                      metavar="DIR COQDIR", nargs=2, action="append",
                      default=[], help=Q_HELP)

    R_HELP="Pass -R DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-R", "--rec-load-path", dest="coq_args_R",
                      metavar="DIR COQDIR", nargs=2, action="append",
                      default=[], help=R_HELP)


    DEBUG_HELP = "Print communications with SerAPI."
    parser.add_argument("--debug", action="store_true",
                        default=False, help=DEBUG_HELP)


    args = parser.parse_args()
    for dir in args.coq_args_I:
        args.serapi_args.extend(("-I", dir))
    for pair in args.coq_args_R:
        args.serapi_args.extend(("-R", ",".join(pair)))
    for pair in args.coq_args_Q:
        args.serapi_args.extend(("-Q", ",".join(pair)))

    try:
        fill_in_arguments(args)
    except argparse.ArgumentTypeError as e:
        parser.error(str(e))

    return args

def call_pipeline_step(step, state, ctx):
    params = list(inspect.signature(step).parameters.keys())[1:]
    return step(state, **{p: ctx[p] for p in params})

def read_input(fpath, args):
    if fpath == "-":
        return (args.stdin_filename or "-"), "-", sys.stdin.read()
    fname = os.path.basename(fpath)
    for ext, _ in MODES_BY_EXTENSION:
        if fpath.endswith(ext):
            fname = fpath[:-len(ext)]
            break
    with open(fpath) as f:
        return fpath, fname, f.read()

def write_output(in_fname, out_fpath, outdir, contents, ext):
    if out_fpath == "-" or (out_fpath is None and in_fname == "-"):
        sys.stdout.write(contents)
    else:
        out_fpath = out_fpath or os.path.join(outdir, in_fname + ext)
        with open(out_fpath, mode="w") as f:
            f.write(contents)

def main():
    args = parse_arguments()

    if args.debug:
        from . import core
        core.DEBUG = True
    try:
        for fpath, pipeline in args.pipelines:
            fpath, fname, state = read_input(fpath, args)
            ctx = { "fpath": fpath, "fname": fname, **vars(args) }
            for step in pipeline:
                state = call_pipeline_step(step, state, ctx)
            write_output(fname, args.output, args.output_directory, *state)
    except (ValueError, FileNotFoundError) as e:
        if args.debug:
            raise e
        sys.stderr.write("Exception: {}\n".format(e))
        sys.exit(1)
