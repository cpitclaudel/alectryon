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

def register_docutils(v, serapi_args):
    from .docutils import register, AlectryonTransform
    AlectryonTransform.SERAPI_ARGS = serapi_args
    register()
    return v

def _wrap_classes(*cls):
    return " ".join("alectryon-" + c for c in cls)

DOCUTILS_CSS = "https://cdn.rawgit.com/matthiaseisen/docutils-css/master/docutils_basic.css"
MATHJAX_URL = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/2.7.0/MathJax.js?config=TeX-AMS_HTML-full"

def _gen_docutils_html(source, fpath, webpage_style, html_assets, traceback, Parser, Reader):
    from .html import ASSETS
    from docutils.core import publish_string
    from docutils.writers import get_writer_class

    # The encoding/decoding dance below happens because setting output_encoding
    # to "unicode" causes reST to generate a bad <meta> tag, and setting
    # input_encoding to "unicode" breaks the ‘.. include’ directive.

    js = ASSETS.ALECTRYON_JS
    css = (*ASSETS.ALECTRYON_CSS, *ASSETS.DOCUTILS_CSS, *ASSETS.PYGMENTS_CSS)
    html_assets.extend(js + css)

    settings_overrides = {
        'traceback': traceback,
        'embed_stylesheet': False,
        'stylesheet_path': None,
        'stylesheet_dirs': [],
        'math_output': "MathJax " + MATHJAX_URL,
        'stylesheet': list(css), # Must be a list
        'syntax_highlight': 'short',
        'input_encoding': 'utf-8',
        'output_encoding': 'utf-8'
    }

    Writer = get_writer_class('html')

    class HtmlWriter(Writer):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.translator_class = HtmlTranslator

    class HtmlTranslator(Writer().translator_class):
        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            cls = _wrap_classes("standalone", webpage_style)
            self.body_prefix.append('<div class="{}">'.format(cls))
            self.body_suffix.insert(0, '</div>')
            for j in js:
                TEMPLATE = '<script type="text/javascript" src="{}"></script>'
                self.stylesheet.append(TEMPLATE.format(j))

    parser = Parser()
    return publish_string(
        source=source.encode("utf-8"),
        source_path=fpath, destination_path=None,
        reader=Reader(parser), reader_name=None,
        parser=parser, parser_name=None,
        writer=HtmlWriter(), writer_name=None,
        settings=None, settings_spec=None,
        settings_overrides=settings_overrides, config_section=None,
        enable_exit_status=True).decode("utf-8")

def gen_rstcoq_html(coq, fpath, webpage_style, html_assets, traceback):
    from .docutils import RSTCoqParser, RSTCoqStandaloneReader
    return _gen_docutils_html(coq, fpath, webpage_style, html_assets, traceback,
                         RSTCoqParser, RSTCoqStandaloneReader)

def gen_rst_html(rst, fpath, webpage_style, html_assets, traceback):
    from docutils.parsers.rst import Parser
    from docutils.readers.standalone import Reader
    return _gen_docutils_html(rst, fpath, webpage_style, html_assets, traceback,
                         Parser, Reader)

def _lint_docutils(source, fpath, Parser, traceback):
    from io import StringIO
    from docutils.utils import new_document
    from docutils.frontend import OptionParser
    from docutils.utils import Reporter
    from .docutils import JsErrorPrinter

    parser = Parser()
    settings = OptionParser(components=(Parser,)).get_default_values()
    settings.traceback = traceback
    observer = JsErrorPrinter(StringIO(), settings)
    document = new_document(fpath, settings)

    document.reporter.report_level = 0 # Report all messages
    document.reporter.halt_level = Reporter.SEVERE_LEVEL + 1 # Do not exit early
    document.reporter.stream = False # Disable textual reporting
    document.reporter.attach_observer(observer)
    parser.parse(source, document)

    return observer.stream.getvalue()

def lint_rstcoq(coq, fpath, traceback):
    from .docutils import RSTCoqParser
    return _lint_docutils(coq, fpath, RSTCoqParser, traceback)

def lint_rst(rst, fpath, traceback):
    from docutils.parsers.rst import Parser
    return _lint_docutils(rst, fpath, Parser, traceback)

def gen_html_snippets(annotated):
    from .html import HtmlWriter
    from .pygments import highlight
    return HtmlWriter(highlight).gen_html(annotated)

COQDOC_OPTIONS = ['--body-only', '--no-glob', '--no-index', '--no-externals',
                  '-s', '--html', '--stdout', '--utf8']

def _run_coqdoc(coq_snippets, coqdoc_bin=None):
    """Get the output of coqdoc on coq_code."""
    from tempfile import mkstemp
    from subprocess import check_output
    coqdoc_bin = coqdoc_bin or os.path.join(os.getenv("COQBIN", ""), "coqdoc")
    fd, filename = mkstemp(prefix="coqdoc_", suffix=".v")
    try:
        for snippet in coq_snippets:
            os.write(fd, snippet.encode("utf-8"))
            os.write(fd, b"\n(* --- *)\n") # Separator to prevent fusing
        os.close(fd)
        return check_output([coqdoc_bin] + COQDOC_OPTIONS + [filename], timeout = 10).decode("utf-8")
    finally:
        os.remove(filename)

def _gen_coqdoc_html(coqdoc_comments):
    from bs4 import BeautifulSoup
    coqdoc_output = _run_coqdoc(coqdoc_comments)
    soup = BeautifulSoup(coqdoc_output, "html.parser")
    docs = soup.find_all(class_='doc')
    assert len(docs) == len(coqdoc_comments)
    return docs

def _gen_html_snippets_with_coqdoc(annotated):
    from dominate.util import raw
    from .html import HtmlWriter
    from .pygments import highlight
    from .transforms import isolate_coqdoc, CoqdocFragment

    writer = HtmlWriter(highlight)

    coqdoc = [part.contents for fragments in annotated
              for part in isolate_coqdoc(fragments)
              if isinstance(part, CoqdocFragment)]
    coqdoc_html = iter(_gen_coqdoc_html(coqdoc))

    for fragments in annotated:
        for part in isolate_coqdoc(fragments):
            if isinstance(part, CoqdocFragment):
                yield [raw(str(next(coqdoc_html, None)))]
            else:
                yield writer.gen_fragments_html(part.fragments)

def gen_html_snippets_with_coqdoc(annotated, html_classes):
    html_classes.append("coqdoc")
    # ‘return’ instead of ‘yield from’ to update html_classes eagerly
    return _gen_html_snippets_with_coqdoc(annotated)

def copy_assets(state, html_assets, no_assets, output_directory):
    from .html import copy_assets as cp
    if not no_assets:
        cp(output_directory, assets=html_assets)
    return state

def dump_html_standalone(snippets, fname, webpage_style, html_assets, html_classes):
    from dominate import tags, document
    from .core import SerAPI
    from .html import gen_header, GENERATOR, ASSETS
    from .pygments import FORMATTER

    doc = document(title=fname)
    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))

    PLEX_CDN = ("https://fonts.googleapis.com/css2?family=IBM+Plex+Serif"
                ":ital,wght@0,400;0,700;1,400;1,700&display=swap")
    FIRA_CODE_CDN = "https://unpkg.com/firacode/distr/fira_code.css"
    for css in (PLEX_CDN, FIRA_CODE_CDN, *ASSETS.ALECTRYON_CSS):
        doc.head.add(tags.link(rel="stylesheet", href=css))
    for js in ASSETS.ALECTRYON_JS:
        doc.head.add(tags.script(src=js))

    html_assets.extend(ASSETS.ALECTRYON_CSS)
    html_assets.extend(ASSETS.ALECTRYON_JS)

    pygments_css = FORMATTER.get_style_defs('.highlight')
    doc.head.add(tags.style(pygments_css, type="text/css"))

    cls = _wrap_classes("standalone", webpage_style, *html_classes)
    root = doc.body.add(tags.article(cls=cls))
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
        io.write("<!-- alectryon-block-end -->")
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
        'lint': (register_docutils, lint_rstcoq, write_file(".lint.json")),
        'rst': (coq_to_rst, write_file(".v.rst"))
    },
    'coq+rst': {
        'webpage': (register_docutils, gen_rstcoq_html,
                    copy_assets, write_file(".html")),
        'lint': (register_docutils, lint_rstcoq, write_file(".lint.json")),
        'rst': (coq_to_rst, write_file(".v.rst"))
    },
    'coqdoc': {
        'webpage': (parse_coq_plain, annotate_chunks,
                    gen_html_snippets_with_coqdoc,
                    dump_html_standalone, copy_assets, write_file(".html")),
    },
    'rst': {
        'webpage': (register_docutils, gen_rst_html,
                    copy_assets, write_file(".html")),
        'lint': (register_docutils, lint_rst, write_file(".lint.json")),
        'coq': (rst_to_coq, write_file(".v")),
        'coq+rst': (rst_to_coq, write_file(".v"))
    }
}

EXTENSIONS = ['.v', '.json', '.v.rst', '.rst']
FRONTENDS_BY_EXTENSION = [
    ('.v', 'coq'), ('.json', 'json'), ('.rst', 'rst')
]
BACKENDS_BY_EXTENSION = [
    ('.v', 'coq'), ('.json', 'json'), ('.rst', 'rst'),
    ('.lint.json', 'lint'), ('.snippets.html', 'snippets-html'),
    ('.v.html', 'webpage'), ('.html', 'webpage')
]

DEFAULT_BACKENDS = {
    'json': 'json',
    'coq': 'webpage',
    'coqdoc': 'webpage',
    'coq+rst': 'webpage',
    'rst': 'webpage'
}

def infer_mode(fpath, kind, arg, table):
    for (ext, mode) in table:
        if fpath.endswith(ext):
            return mode
    MSG = """{}: Not sure what to do with {!r}.
Try passing {}?"""
    raise argparse.ArgumentTypeError(MSG.format(kind, fpath, arg))

def infer_frontend(fpath):
    return infer_mode(fpath, "input", "--frontend", FRONTENDS_BY_EXTENSION)

def infer_backend(frontend, out_fpath):
    if out_fpath:
        return infer_mode(out_fpath, "output", "--backend", BACKENDS_BY_EXTENSION)
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

    args.html_assets = []
    args.html_classes = []
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
                               for ext, frontend in FRONTENDS_BY_EXTENSION)
    FRONTEND_CHOICES = sorted(PIPELINES.keys())
    out.add_argument("--frontend", default=None, choices=FRONTEND_CHOICES,
                     help=FRONTEND_HELP)


    OUTPUT_HELP = "Configure the output."
    out = parser.add_argument_group("Output arguments", OUTPUT_HELP)

    BACKEND_HELP = "Choose a backend. Supported: "
    BACKEND_HELP += "; ".join(
        "{} → {{{}}}".format(frontend, ", ".join(sorted(backends)))
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

    WEBPAGE_STYLE_HELP = "Choose a style for standalone webpages."
    WEBPAGE_STYLE_CHOICES = ("centered", "floating", "windowed")
    parser.add_argument("--webpage-style", default="centered",
                        choices=WEBPAGE_STYLE_CHOICES,
                        help=WEBPAGE_STYLE_HELP)

    MARK_POINT_HELP = "Mark a point in the output with a given marker."
    parser.add_argument("--mark-point", nargs=2, default=(None, None),
                        metavar=("POINT", "MARKER"),
                        help=MARK_POINT_HELP)


    SUBP_HELP = "Pass arguments to the SerAPI process"
    subp = parser.add_argument_group("Subprocess arguments", SUBP_HELP)

    SERAPI_ARGS_HELP = "Pass a single argument to SerAPI (e.g. -Q dir,lib)."
    subp.add_argument("--serapi-arg", dest="serapi_args",
                      action="append", default=[],
                      metavar="SERAPI_ARG",
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

    TRACEBACK_HELP = "Print error traces."
    parser.add_argument("--traceback", action="store_true",
                        default=False, help=TRACEBACK_HELP)


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
    for ext in EXTENSIONS:
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
        if args.traceback:
            raise e
        sys.stderr.write("Exception: {}\n".format(e))
        sys.exit(1)
