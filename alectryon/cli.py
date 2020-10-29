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
import os
import os.path
import shutil
import sys

# Pipelines
# =========

def read_plain(_, fpath, fname):
    if fname == "-":
        return sys.stdin.read()
    with open(fpath) as f:
        return f.read()

def read_json(_, fpath, fname):
    from json import load
    if fname == "-":
        return load(sys.stdin)
    with open(fpath) as f:
        return load(f)

def parse_coq_plain(contents):
    return [contents]

def _catch_parsing_errors(fpath, k, *args):
    from .literate import ParsingError
    try:
        return k(*args)
    except ParsingError as e:
        raise ValueError("{}:{}".format(fpath, e))

def coq_to_rst(coq, fpath, point, marker):
    from .literate import coq2rst_marked
    return _catch_parsing_errors(fpath, coq2rst_marked, coq, point, marker)

def rst_to_coq(coq, fpath, point, marker):
    from .literate import rst2coq_marked
    return _catch_parsing_errors(fpath, rst2coq_marked, coq, point, marker)

def annotate_chunks(chunks, sertop_args):
    from .core import annotate
    return annotate(chunks, sertop_args)

def register_docutils(v, sertop_args):
    from .docutils import setup, AlectryonTransform
    AlectryonTransform.SERTOP_ARGS = sertop_args
    setup()
    return v

def _gen_docutils_html(source, fpath, webpage_style, no_header,
                       html_assets, traceback, Parser, Reader):
    from docutils.core import publish_string
    from .docutils import HtmlTranslator, HtmlWriter

    # The encoding/decoding dance below happens because setting output_encoding
    # to "unicode" causes reST to generate a bad <meta> tag, and setting
    # input_encoding to "unicode" breaks the ‘.. include’ directive.

    html_assets.extend(HtmlTranslator.JS + HtmlTranslator.CSS)

    settings_overrides = {
        'traceback': traceback,
        'embed_stylesheet': False,
        'stylesheet_path': None,
        'stylesheet_dirs': [],
        'no_header': no_header,
        'webpage_style': webpage_style,
        'input_encoding': 'utf-8',
        'output_encoding': 'utf-8'
    }

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

def gen_rstcoq_html(coq, fpath, webpage_style, no_header, html_assets, traceback):
    from .docutils import RSTCoqParser, RSTCoqStandaloneReader
    return _gen_docutils_html(coq, fpath, webpage_style, no_header, html_assets, traceback,
                         RSTCoqParser, RSTCoqStandaloneReader)

def gen_rst_html(rst, fpath, webpage_style, no_header, html_assets, traceback):
    from docutils.parsers.rst import Parser
    from docutils.readers.standalone import Reader
    return _gen_docutils_html(rst, fpath, webpage_style, no_header, html_assets, traceback,
                         Parser, Reader)

def _docutils_cmdline(description, Reader, Parser):
    import locale
    locale.setlocale(locale.LC_ALL, '')

    from docutils.core import publish_cmdline, default_description
    from .docutils import setup, HtmlWriter

    setup()

    parser = Parser()
    publish_cmdline(
        reader=Reader(parser), parser=parser,
        writer=HtmlWriter(),
        settings_overrides={'stylesheet_path': None},
        description=(description + default_description)
    )

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

def _scrub_fname(fname):
    import re
    return re.sub("[^-a-zA-Z0-9]", "-", fname)

def gen_html_snippets(annotated, fname):
    from .html import HtmlGenerator
    from .pygments import highlight_html
    return HtmlGenerator(highlight_html, _scrub_fname(fname)).gen(annotated)

def gen_latex_snippets(annotated):
    from .latex import LatexGenerator
    from .pygments import highlight_latex
    return LatexGenerator(highlight_latex).gen(annotated)

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
        coqdoc = [coqdoc_bin, *COQDOC_OPTIONS, filename]
        return check_output(coqdoc, timeout=10).decode("utf-8")
    finally:
        os.remove(filename)

def _gen_coqdoc_html(coqdoc_comments):
    from bs4 import BeautifulSoup
    coqdoc_output = _run_coqdoc(coqdoc_comments)
    soup = BeautifulSoup(coqdoc_output, "html.parser")
    docs = soup.find_all(class_='doc')
    if len(docs) != len(coqdoc_comments):
        from pprint import pprint
        print("Coqdoc mismatch:", file=sys.stderr)
        pprint(docs)
        pprint(coqdoc_comments)
        raise AssertionError()
    return docs

def _gen_html_snippets_with_coqdoc(annotated, fname):
    from dominate.util import raw
    from .html import HtmlGenerator
    from .pygments import highlight_html
    from .transforms import isolate_coqdoc, default_transform, CoqdocFragment

    writer = HtmlGenerator(highlight_html, _scrub_fname(fname))

    coqdoc = [part.contents for fragments in annotated
              for part in isolate_coqdoc(fragments)
              if isinstance(part, CoqdocFragment)]
    coqdoc_html = iter(_gen_coqdoc_html(coqdoc))

    for fragments in annotated:
        for part in isolate_coqdoc(fragments):
            if isinstance(part, CoqdocFragment):
                yield [raw(str(next(coqdoc_html, None)))]
            else:
                fragments = default_transform(part.fragments)
                yield writer.gen_fragments(fragments)

def gen_html_snippets_with_coqdoc(annotated, html_classes, fname):
    html_classes.append("coqdoc")
    # ‘return’ instead of ‘yield from’ to update html_classes eagerly
    return _gen_html_snippets_with_coqdoc(annotated, fname)

def copy_assets(state, html_assets, copy_fn, output_directory):
    from .html import copy_assets as cp
    if copy_fn:
        cp(output_directory, assets=html_assets, copy_fn=copy_fn)
    return state

def dump_html_standalone(snippets, fname, webpage_style, no_header, html_assets, html_classes):
    from dominate import tags, document
    from dominate.util import raw
    from .core import SerAPI
    from .html import gen_header, wrap_classes, GENERATOR, ASSETS
    from .pygments import HTML_FORMATTER

    doc = document(title=fname)
    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))
    doc.set_attribute("class", "alectryon-standalone")

    for css in ASSETS.ALECTRYON_CSS:
        doc.head.add(tags.link(rel="stylesheet", href=css))
    for link in (ASSETS.IBM_PLEX_CDN, ASSETS.FIRA_CODE_CDN):
        doc.head.add(raw(link))
    for js in ASSETS.ALECTRYON_JS:
        doc.head.add(tags.script(src=js))

    html_assets.extend(ASSETS.ALECTRYON_CSS)
    html_assets.extend(ASSETS.ALECTRYON_JS)

    pygments_css = HTML_FORMATTER.get_style_defs('.highlight')
    doc.head.add(tags.style(pygments_css, type="text/css"))

    cls = wrap_classes(webpage_style, *html_classes)
    root = doc.body.add(tags.article(cls=cls))
    if not no_header:
        root.add(raw(gen_header(SerAPI.version_info())))
    for snippet in snippets:
        root.add(snippet)

    return doc.render(pretty=False)

def prepare_json(obj):
    from .json import json_of_annotated
    return json_of_annotated(obj)

def dump_json(js):
    from json import dumps
    return dumps(js, indent=4)

def dump_html_snippets(snippets):
    s = ""
    for snippet in snippets:
        s += snippet.render(pretty=True)
        s += "<!-- alectryon-block-end -->\n"
    return s

def dump_latex_snippets(snippets):
    s = ""
    for snippet in snippets:
        s += str(snippet)
        s += "\n%% alectryon-block-end\n"
    return s

def strip_extension(fname):
    for ext in EXTENSIONS:
        if fname.endswith(ext):
            return fname[:-len(ext)]
    return fname

def write_output(ext, contents, fname, output, output_directory):
    if output == "-" or (output is None and fname == "-"):
        sys.stdout.write(contents)
    else:
        if not output:
            output = os.path.join(output_directory, strip_extension(fname) + ext)
        with open(output, mode="w") as f:
            f.write(contents)

def write_file(ext):
    return lambda contents, fname, output, output_directory: \
        write_output(ext, contents, fname, output, output_directory)

PIPELINES = {
    'json': {
        'json': (read_json, annotate_chunks,
                 prepare_json, dump_json, write_file(".io.json")),
        'snippets-html': (read_json, annotate_chunks, gen_html_snippets,
                          dump_html_snippets, write_file(".snippets.html")),
        'snippets-latex': (read_json, annotate_chunks, gen_latex_snippets,
                           dump_latex_snippets, write_file(".snippets.tex"))
    },
    'coq': {
        'null': (read_plain, parse_coq_plain, annotate_chunks),
        'webpage': (read_plain, parse_coq_plain, annotate_chunks,
                    gen_html_snippets, dump_html_standalone, copy_assets,
                    write_file(".v.html")),
        'snippets-html': (read_plain, parse_coq_plain, annotate_chunks,
                          gen_html_snippets, dump_html_snippets,
                          write_file(".snippets.html")),
        'snippets-latex': (read_plain, parse_coq_plain, annotate_chunks,
                           gen_latex_snippets, dump_latex_snippets,
                           write_file(".snippets.tex")),
        'lint': (read_plain, register_docutils, lint_rstcoq,
                 write_file(".lint.json")),
        'rst': (read_plain, coq_to_rst, write_file(".v.rst")),
        'json': (read_plain, parse_coq_plain, annotate_chunks, prepare_json,
                 dump_json, write_file(".io.json"))
    },
    'coq+rst': {
        'webpage': (read_plain, register_docutils, gen_rstcoq_html, copy_assets,
                    write_file(".html")),
        'lint': (read_plain, register_docutils, lint_rstcoq,
                 write_file(".lint.json")),
        'rst': (read_plain, coq_to_rst, write_file(".v.rst"))
    },
    'coqdoc': {
        'webpage': (read_plain, parse_coq_plain, annotate_chunks,
                    gen_html_snippets_with_coqdoc, dump_html_standalone,
                    copy_assets, write_file(".html")),
    },
    'rst': {
        'webpage': (read_plain, register_docutils, gen_rst_html, copy_assets,
                    write_file(".html")),
        'lint': (read_plain, register_docutils, lint_rst,
                 write_file(".lint.json")),
        'coq': (read_plain, rst_to_coq, write_file(".v")),
        'coq+rst': (read_plain, rst_to_coq, write_file(".v"))
    }
}

# CLI
# ===

EXTENSIONS = ['.v', '.json', '.v.rst', '.rst']
FRONTENDS_BY_EXTENSION = [
    ('.v', 'coq+rst'), ('.json', 'json'), ('.rst', 'rst')
]
BACKENDS_BY_EXTENSION = [
    ('.v', 'coq'), ('.json', 'json'), ('.rst', 'rst'),
    ('.lint.json', 'lint'),
    ('.snippets.html', 'snippets-html'),
    ('.snippets.tex', 'snippets-latex'),
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

COPY_FUNCTIONS = {
    "copy": shutil.copy,
    "symlink": os.symlink,
    "hardlink": os.link,
    "none": None
}

def post_process_arguments(parser, args):
    if len(args.input) > 1 and args.output:
        parser.error("argument --output: Not valid with multiple inputs")

    if args.stdin_filename and "-" not in args.input:
        parser.error("argument --stdin-filename: input must be '-'")

    for dirpath in args.coq_args_I:
        args.sertop_args.extend(("-I", dirpath))
    for pair in args.coq_args_R:
        args.sertop_args.extend(("-R", ",".join(pair)))
    for pair in args.coq_args_Q:
        args.sertop_args.extend(("-Q", ",".join(pair)))

    # argparse applies ‘type’ before ‘choices’, so we do the conversion here
    args.copy_fn = COPY_FUNCTIONS[args.copy_fn]

    args.point, args.marker = args.mark_point
    if args.point is not None:
        try:
            args.point = int(args.point)
        except ValueError:
            MSG = "argument --mark-point: Expecting a number, not {!r}"
            parser.error(MSG.format(args.point))

    args.html_assets = []
    args.html_classes = []
    args.pipelines = [(fpath, resolve_pipeline(fpath, args))
                      for fpath in args.input]

    return args

def build_parser():
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

    OUT_DIR_HELP = "Set the output directory (default: same as each INPUT)."
    parser.add_argument("--output-directory", default=None,
                        help=OUT_DIR_HELP)

    COPY_ASSETS_HELP = ("Chose the method to use to copy assets " +
                        "along the generated file(s) when creating webpages.")
    parser.add_argument("--copy-assets", choices=list(COPY_FUNCTIONS.keys()),
                        default="copy", dest="copy_fn",
                        help=COPY_ASSETS_HELP)

    CACHE_DIRECTORY_HELP = ("Cache Coq's output in DIRECTORY.")
    parser.add_argument("--cache-directory", default=None, metavar="DIRECTORY",
                        help=CACHE_DIRECTORY_HELP)

    NO_HEADER_HELP = "Do not insert a header with usage instructions in webpages."
    parser.add_argument("--no-header", action='store_true',
                        help=NO_HEADER_HELP)

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

    SERTOP_ARGS_HELP = "Pass a single argument to SerAPI (e.g. -Q dir,lib)."
    subp.add_argument("--sertop-arg", dest="sertop_args",
                      action="append", default=[],
                      metavar="SERAPI_ARG",
                      help=SERTOP_ARGS_HELP)

    I_HELP = "Pass -I DIR to the SerAPI subprocess."
    subp.add_argument("-I", "--ml-include-path", dest="coq_args_I",
                      metavar="DIR", nargs=1, action="append",
                      default=[], help=I_HELP)

    Q_HELP = "Pass -Q DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-Q", "--load-path", dest="coq_args_Q",
                      metavar=("DIR", "COQDIR"), nargs=2, action="append",
                      default=[], help=Q_HELP)

    R_HELP = "Pass -R DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-R", "--rec-load-path", dest="coq_args_R",
                      metavar=("DIR", "COQDIR"), nargs=2, action="append",
                      default=[], help=R_HELP)


    DEBUG_HELP = "Print communications with SerAPI."
    parser.add_argument("--debug", action="store_true",
                        default=False, help=DEBUG_HELP)

    TRACEBACK_HELP = "Print error traces."
    parser.add_argument("--traceback", action="store_true",
                        default=False, help=TRACEBACK_HELP)

    return parser

def parse_arguments():
    parser = build_parser()
    return post_process_arguments(parser, parser.parse_args())


# Entry point
# ===========

def call_pipeline_step(step, state, ctx):
    params = list(inspect.signature(step).parameters.keys())[1:]
    return step(state, **{p: ctx[p] for p in params})

def build_context(fpath, args):
    if fpath == "-":
        fname, fpath = "-", (args.stdin_filename or "-")
    else:
        fname = os.path.basename(fpath)

    ctx = {"fpath": fpath, "fname": fname, **vars(args)}

    if args.output_directory is None:
        if fname == "-":
            ctx["output_directory"] = "."
        else:
            ctx["output_directory"] = os.path.dirname(os.path.abspath(fpath))

    return ctx

def process_pipelines(args):
    if args.debug:
        from . import core
        core.DEBUG = True

    if args.cache_directory:
        from . import docutils
        docutils.CACHE_DIRECTORY = args.cache_directory

    try:
        for fpath, pipeline in args.pipelines:
            state, ctx = None, build_context(fpath, args)
            for step in pipeline:
                state = call_pipeline_step(step, state, ctx)
    except (ValueError, FileNotFoundError) as e:
        if args.traceback:
            raise e
        print("Exiting early due to an error:", file=sys.stderr)
        print(str(e), file=sys.stderr)
        sys.exit(1)


def main():
    args = parse_arguments()
    process_pipelines(args)

# Alternative CLIs
# ================

def rstcoq2html():
    from .docutils import RSTCoqStandaloneReader, RSTCoqParser
    DESCRIPTION = 'Build an HTML document from an Alectryon Coq file.'
    _docutils_cmdline(DESCRIPTION, RSTCoqStandaloneReader, RSTCoqParser)

def coqrst2html():
    from docutils.parsers.rst import Parser
    from docutils.readers.standalone import Reader
    DESCRIPTION = 'Build an HTML document from an Alectryon reStructuredText file.'
    _docutils_cmdline(DESCRIPTION, Reader, Parser)
