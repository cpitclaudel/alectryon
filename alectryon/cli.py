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

from typing import Tuple, List, Union

import argparse
import inspect
import os
import os.path
import re
import shutil
import sys

from . import __version__, core

# Pipelines
# =========

def read_plain(_, fpath, input_is_stdin):
    if input_is_stdin:
        return sys.stdin.read()
    with open(fpath, encoding="utf-8") as f:
        return f.read()

def read_json(_, fpath, input_is_stdin):
    from .json import loads
    return loads(read_plain(None, fpath, input_is_stdin))

def parse_plain(contents, fpath):
    return [core.PosStr(contents, core.Position(fpath, 1, 1), 0)]

def _catch_parsing_errors(fpath, k, *args):
    from .literate import ParsingError
    try:
        return k(*args)
    except ParsingError as e:
        raise ValueError("{}: {}".format(fpath, e)) from e

def code_to_rst(code, fpath, point, marker, input_language):
    if input_language == "coq":
        from .literate import coq2rst_marked as converter
    else:
        assert False
    return _catch_parsing_errors(fpath, converter, code, point, marker)

def rst_to_code(rst, fpath, point, marker, backend):
    if backend in ("coq", "coq+rst"):
        from .literate import rst2coq_marked as converter
    else:
        assert False
    return _catch_parsing_errors(fpath, converter, rst, point, marker)

def annotate_chunks(chunks, fpath, cache_directory, cache_compression,
                    input_language, driver_name, driver_args, exit_code):
    from .core import StderrObserver
    from .json import CacheSet
    driver_cls = core.resolve_driver(input_language, driver_name)
    driver = driver_cls(driver_args, fpath=fpath)
    with CacheSet(cache_directory, fpath, cache_compression) as caches:
        annotated = caches[input_language].update(chunks, driver)
        assert isinstance(driver.observer, StderrObserver)
        exit_code.val = int(driver.observer.exit_code >= 3)
        return annotated

def register_docutils(v, ctx):
    from . import docutils

    docutils.AlectryonTransform.DRIVER_ARGS = ctx["driver_args_by_name"]
    docutils.AlectryonTransform.LANGUAGE_DRIVERS = ctx["language_drivers"]
    docutils.CACHE_DIRECTORY = ctx["cache_directory"]
    docutils.CACHE_COMPRESSION = ctx["cache_compression"]
    docutils.HTML_MINIFICATION = ctx["html_minification"]
    docutils.LONG_LINE_THRESHOLD = ctx["long_line_threshold"]
    docutils.setup()

    # The encoding/decoding dance below happens because setting output_encoding
    # to "unicode" causes reST to generate a bad <meta> tag, and setting
    # input_encoding to "unicode" breaks the ‘.. include’ directive.

    # Setting ``traceback`` unconditionally allows us to catch and report errors
    # from our own docutils components and avoid asking users to make a report
    # to the docutils mailing list.

    ctx["docutils_settings_overrides"] = {
        'traceback': True,
        'stylesheet_path': None,
        'input_encoding': 'utf-8',
        'output_encoding': 'utf-8',
        'exit_status_level': 3,
        'pygments_style': ctx["pygments_style"],
        'alectryon_banner': ctx["include_banner"],
        'alectryon_vernums': ctx["include_vernums"],
        'alectryon_webpage_style': ctx["webpage_style"],
    }

    return v

def _gen_docutils(source, fpath,
                  Parser, Reader, Writer,
                  settings_overrides):
    from docutils.core import publish_programmatically
    from docutils.io import StringInput, StringOutput

    parser = Parser()

    # LATER: ``destination_path=None`` propagates to ``settings._destination``,
    # which means that ``stylesheet_path`` isn't actually resolved relative to
    # ``_destination``.  This isn't trivial to fix because the name of the
    # output is determined by the argument to ``write_file``.
    text, pub = publish_programmatically(
        source_class=StringInput, destination_class=StringOutput,
        source=source.encode("utf-8"), destination=None,
        source_path=fpath, destination_path=None,

        reader=Reader(parser), reader_name=None,
        parser=parser, parser_name=None,
        writer=Writer(), writer_name=None,

        settings=None, settings_spec=None,
        settings_overrides=settings_overrides, config_section=None,
        enable_exit_status=False)

    max_level = pub.document.reporter.max_level
    exit_code = max_level + 10 if max_level >= pub.settings.exit_status_level else 0
    return text.decode("utf-8"), pub, exit_code

def _record_assets(assets, path, names):
    for name in names:
        assets.append((path, name))

def gen_docutils(src, frontend, backend, fpath, dialect,
                 docutils_settings_overrides, assets, exit_code):
    from .docutils import get_pipeline, alectryon_state

    pipeline = get_pipeline(frontend, backend, dialect)
    text, pub, exit_code.val = \
        _gen_docutils(src, fpath,
                      pipeline.parser, pipeline.reader, pipeline.writer,
                      docutils_settings_overrides)

    embedded_assets = alectryon_state(pub.document).embedded_assets
    _record_assets(assets,
                   pipeline.translator.ASSETS_PATH,
                   [a for a in pipeline.translator.ASSETS if a not in embedded_assets])

    return text

def _docutils_cmdline(description, frontend, backend, dialect):
    import locale
    locale.setlocale(locale.LC_ALL, '')

    from docutils.core import publish_cmdline, default_description
    from .docutils import setup, get_pipeline

    setup()

    pipeline = get_pipeline(frontend, backend, dialect)
    return publish_cmdline(
        parser=pipeline.parser(), writer=pipeline.writer(),
        settings_overrides={'stylesheet_path': None},
        description="{} {}".format(description, default_description))

def _scrub_fname(fname):
    return re.sub("[^-a-zA-Z0-9]", "-", fname)

def apply_transforms(annotated, input_language):
    from .transforms import default_transform
    for fragments in annotated:
        yield default_transform(fragments, input_language)

def gen_html_snippets(annotated, fname, input_language,
                      html_minification, pygments_style):
    from .html import HtmlGenerator
    from .pygments import make_highlighter
    fname = _scrub_fname(fname)
    highlighter = make_highlighter("html", input_language, pygments_style)
    return HtmlGenerator(highlighter, fname, html_minification).gen(annotated)

def gen_latex_snippets(annotated, input_language, pygments_style):
    from .latex import LatexGenerator
    from .pygments import make_highlighter
    highlighter = make_highlighter("latex", input_language, pygments_style)
    return LatexGenerator(highlighter).gen(annotated)

COQDOC_OPTIONS = ['--body-only', '--no-glob', '--no-index', '--no-externals',
                  '-s', '--html', '--stdout', '--utf8']

def _run_coqdoc(coq_snippets, coqdoc_bin=None):
    """Get the output of coqdoc on coq_code."""
    from shutil import rmtree
    from tempfile import mkstemp, mkdtemp
    from subprocess import check_output
    coqdoc_bin = coqdoc_bin or os.path.join(os.getenv("COQBIN", ""), "coqdoc")
    dpath = mkdtemp(prefix="alectryon_coqdoc_")
    fd, filename = mkstemp(prefix="alectryon_coqdoc_", suffix=".v", dir=dpath)
    try:
        for snippet in coq_snippets:
            os.write(fd, snippet.encode("utf-8"))
            os.write(fd, b"\n(* --- *)\n") # Separator to prevent fusing
        os.close(fd)
        coqdoc = [coqdoc_bin, *COQDOC_OPTIONS, "-d", dpath, filename]
        return check_output(coqdoc, cwd=dpath, timeout=10).decode("utf-8")
    finally:
        rmtree(dpath)

def _gen_coqdoc_html_assert(docs, coqdoc_comments):
    if len(docs) != len(coqdoc_comments):
        from pprint import pprint
        print("Coqdoc mismatch:", file=sys.stderr)
        pprint(list(zip(coqdoc_comments, docs)))
        raise AssertionError()

def _gen_coqdoc_html(coqdoc_fragments):
    from bs4 import BeautifulSoup
    coqdoc_output = _run_coqdoc(fr.contents for fr in coqdoc_fragments)
    soup = BeautifulSoup(coqdoc_output, "html.parser")
    docs = soup.find_all(class_='doc')
    coqdoc_comments = [c for c in coqdoc_fragments if not c.special]
    _gen_coqdoc_html_assert(docs, coqdoc_comments)
    return docs

def _gen_html_snippets_with_coqdoc(annotated, fname, html_minification,
                                   input_language, pygments_style):
    from dominate.util import raw
    from .html import HtmlGenerator
    from .pygments import make_highlighter
    from .transforms import isolate_coqdoc, default_transform, CoqdocFragment

    fname = _scrub_fname(fname)
    highlighter = make_highlighter("html", input_language, pygments_style)
    writer = HtmlGenerator(highlighter, fname, html_minification)

    parts = [part for fragments in annotated
             for part in isolate_coqdoc(fragments)]
    coqdoc = [part for part in parts
              if isinstance(part, CoqdocFragment)]
    coqdoc_html = iter(_gen_coqdoc_html(coqdoc))

    for part in parts:
        if isinstance(part, CoqdocFragment):
            if not part.special:
                yield [raw(str(next(coqdoc_html, None)))]
        else:
            fragments = default_transform(part.fragments, input_language)
            yield writer.gen_fragments(fragments)

def gen_html_snippets_with_coqdoc(annotated, html_classes, fname,
                                  html_minification, input_language, pygments_style):
    html_classes.append("coqdoc")
    # ‘return’ instead of ‘yield from’ to update html_classes eagerly
    return _gen_html_snippets_with_coqdoc(
        annotated, fname, html_minification, input_language, pygments_style)

def copy_assets(state, assets: List[Tuple[str, Union[str, core.Asset]]],
                copy_fn, output_directory, ctx=None):
    if copy_fn is None:
        return state

    for (path, asset) in assets:
        src = os.path.join(path, asset)
        dst = os.path.join(output_directory, asset)

        if isinstance(asset, core.Asset):
            with open(dst, mode="w") as f:
                f.write(asset.gen(ctx or {}))
            continue

        if copy_fn is not shutil.copyfile:
            try:
                os.unlink(dst)
            except FileNotFoundError:
                pass
        try:
            copy_fn(src, dst)
        except (shutil.SameFileError, FileExistsError):
            pass

    return state

def dump_html_standalone(snippets, fname, webpage_style,
                         html_minification, include_banner, include_vernums,
                         assets, html_classes, input_language, driver_name):
    from dominate import tags, document
    from dominate.util import raw
    from . import GENERATOR
    from .html import ASSETS, ADDITIONAL_HEADS, JS_UNMINIFY, gen_banner, wrap_classes

    doc = document(title=fname)
    doc.set_attribute("class", "alectryon-standalone")

    doc.head.add(tags.meta(charset="utf-8"))
    doc.head.add(tags.meta(name="generator", content=GENERATOR))

    for hd in ADDITIONAL_HEADS:
        doc.head.add(raw(hd))
    if html_minification:
        doc.head.add(raw(JS_UNMINIFY))
    for css in ASSETS.ALECTRYON_CSS + ASSETS.PYGMENTS_CSS:
        doc.head.add(tags.link(rel="stylesheet", href=str(css)))
    for link in (ASSETS.IBM_PLEX_CDN, ASSETS.FIRA_CODE_CDN):
        doc.head.add(raw("\n    " + link))
    for js in ASSETS.ALECTRYON_JS:
        doc.head.add(tags.script(src=js))

    _record_assets(assets, ASSETS.PATH, ASSETS.ALECTRYON_CSS)
    _record_assets(assets, ASSETS.PATH, ASSETS.ALECTRYON_JS)
    _record_assets(assets, ASSETS.PATH, ASSETS.PYGMENTS_CSS)

    if html_minification:
        html_classes.append("minified")

    cls = wrap_classes(webpage_style, *html_classes)
    root = doc.body.add(tags.article(cls=cls))
    if include_banner:
        driver = core.resolve_driver(input_language, driver_name)
        root.add(raw(gen_banner([driver.version_info()], include_vernums)))
    for snippet in snippets:
        root.add(snippet)

    return doc.render(pretty=False)

def encode_json(obj):
    from .json import PlainSerializer
    return PlainSerializer.encode(obj)

def decode_json(obj):
    from .json import PlainSerializer
    return PlainSerializer.decode(obj)

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

def write_output(ext, contents, fname, output, output_directory, strip_re):
    if output == "-":
        sys.stdout.write(contents)
    else:
        if not output:
            fname = strip_re.sub("", fname)
            output = os.path.join(output_directory, fname + ext)
        os.makedirs(os.path.dirname(os.path.abspath(output)), exist_ok=True)
        with open(output, mode="w", encoding="utf-8") as f:
            f.write(contents)

def write_file(ext, strip):
    strip_re = re.compile("(" + "|".join(re.escape(ext) for ext in strip) + ")*\\Z")
    return lambda contents, fname, output, output_directory: \
        write_output(ext, contents, fname, output,
                     output_directory, strip_re=strip_re)

EXTENSIONS_BY_LANGUAGE = {
    "coq": (".v"),
}

assert EXTENSIONS_BY_LANGUAGE.keys() == core.ALL_LANGUAGES
CODE_EXTENSIONS = [ext for exts in EXTENSIONS_BY_LANGUAGE.values() for ext in exts]

# No ‘apply_transforms’ in JSON pipelines: we save the prover output without
# modifications.
def _add_code_pipelines(pipelines, lang, *exts):
    pipelines[lang + '.json'] = {
        'null':
        (read_json, annotate_chunks),
        'json':
        (read_json, annotate_chunks, encode_json, dump_json,
         write_file(".io.json", strip=(".json",))),
        'snippets-html':
        (read_json, annotate_chunks, apply_transforms, gen_html_snippets,
         dump_html_snippets, write_file(".snippets.html", strip=(*exts, ".json",))),
        'snippets-latex':
        (read_json, annotate_chunks, apply_transforms, gen_latex_snippets,
         dump_latex_snippets, write_file(".snippets.tex", strip=(*exts, ".json",)))
    }
    pipelines[lang + '.io.json'] = {
        'null':
        (read_json, decode_json),
        'snippets-html':
        (read_json, decode_json, apply_transforms,
         gen_html_snippets, dump_html_snippets,
         write_file(".snippets.html", strip=(*exts, ".io", ".json"))),
        'snippets-latex':
        (read_json, decode_json, apply_transforms,
         gen_latex_snippets, dump_latex_snippets,
         write_file(".snippets.tex", strip=(*exts, ".io", ".json"))),
        'webpage':
        (read_json, decode_json, apply_transforms, gen_html_snippets,
         dump_html_standalone, copy_assets,
         write_file(".html", strip=(".io", ".json",))),
    }
    pipelines[lang] = {
        'null':
        (read_plain, parse_plain, annotate_chunks),
        'webpage':
        (read_plain, parse_plain, annotate_chunks, apply_transforms,
         gen_html_snippets, dump_html_standalone, copy_assets,
         write_file(".html", strip=())),
        'snippets-html':
        (read_plain, parse_plain, annotate_chunks, apply_transforms,
         gen_html_snippets, dump_html_snippets,
         write_file(".snippets.html", strip=exts)),
        'snippets-latex':
        (read_plain, parse_plain, annotate_chunks, apply_transforms,
         gen_latex_snippets, dump_latex_snippets,
         write_file(".snippets.tex", strip=exts)),
        'lint':
        (read_plain, register_docutils, gen_docutils,
         write_file(".lint.json", strip=exts)),
        'json':
        (read_plain, parse_plain, annotate_chunks, encode_json, dump_json,
         write_file(".io.json", strip=()))
    }
    pipelines[lang + '+rst'] = {
        'webpage':
        (read_plain, register_docutils, gen_docutils, copy_assets,
         write_file(".html", strip=(*exts, ".rst"))),
        'latex':
        (read_plain, register_docutils, gen_docutils, copy_assets,
         write_file(".tex", strip=(*exts, ".rst"))),
        'lint':
        (read_plain, register_docutils, gen_docutils,
         write_file(".lint.json", strip=(*exts, ".rst"))),
    }

def _add_coqdoc_pipeline(pipelines):
    pipelines['coqdoc'] = {
        'webpage':
        (read_plain, parse_plain, annotate_chunks, # transforms applied later
         gen_html_snippets_with_coqdoc, dump_html_standalone, copy_assets,
         write_file(".html", strip=(".v",))),
    }

def _add_docutils_pipelines(pipelines, lang, *exts):
    exts = (*CODE_EXTENSIONS, *exts)
    pipelines[lang] = {
        'webpage':
        (read_plain, register_docutils, gen_docutils, copy_assets,
         write_file(".html", strip=exts)),
        'latex':
        (read_plain, register_docutils, gen_docutils, copy_assets,
         write_file(".tex", strip=exts)),
        'lint':
        (read_plain, register_docutils, gen_docutils,
         write_file(".lint.json", strip=exts))
    }

def _add_transliteration_pipelines(pipelines):
    exts = (*CODE_EXTENSIONS, ".rst")
    pipelines['rst']['coq'] = pipelines['rst']['coq+rst'] = \
        (read_plain, rst_to_code, write_file(".v", strip=exts))
    pipelines['coq']['rst'] = \
        (read_plain, code_to_rst, write_file(".rst", strip=()))
    pipelines['coq+rst']['rst'] = \
        (read_plain, code_to_rst, write_file(".v.rst", strip=(*exts, ".rst")))

def warn_renamed_json_pipeline(v, ctx):
    print("WARNING: Frontend `json` is ambiguous; use `coq.json` instead.",
          file=sys.stderr)
    ctx["frontend"] = 'coq.json'
    return v

def _add_compatibility_pipelines(pipelines):
    pipelines['json'] = {
        backend: (warn_renamed_json_pipeline, *steps)
        for (backend, steps) in pipelines['coq.json'].items()
    }

def _add_pipelines(pipelines):
    for lang, exts in EXTENSIONS_BY_LANGUAGE.items():
        _add_code_pipelines(pipelines, lang, *exts)
    _add_coqdoc_pipeline(pipelines)
    _add_docutils_pipelines(pipelines, "rst", ".rst")
    _add_docutils_pipelines(pipelines, "md", ".md")
    _add_transliteration_pipelines(pipelines)
    _add_compatibility_pipelines(pipelines)
    return pipelines

# LATER: Reorganize to separate concepts of language and frontend instead of
# generating (languages * frontend) entries in PIPELINES.
PIPELINES = _add_pipelines({})

# CLI
# ===

def _language_frontends_by_extension(ext, lang):
    return [
        (ext, lang + '+rst'),
        (ext + '.json', lang + '.json'),
        (ext + '.io.json', lang + '.io.json'),
    ]

FRONTENDS_BY_EXTENSION = [
    *(pair
      for lang, exts in EXTENSIONS_BY_LANGUAGE.items() for ext in exts
      for pair in _language_frontends_by_extension(ext, lang)),

    ('.rst', 'rst'),
    ('.md', 'md'),

    ('.json', 'json'), # LATER: Remove
]

BACKENDS_BY_EXTENSION = [
    *((ext, lang)
      for (lang, exts) in EXTENSIONS_BY_LANGUAGE.items() for ext in exts),
    ('.rst', 'rst'),
    ('.lint.json', 'lint'), ('.json', 'json'),
    ('.snippets.html', 'snippets-html'), ('.snippets.tex', 'snippets-latex'),
    ('.html', 'webpage'), ('.tex', 'latex')
]

def _default_language_backends(lang):
    return {
        lang: 'webpage',
        lang + '.json': 'json',
        lang + '.io.json': 'webpage',
        lang + '+rst': 'webpage',
    }

DEFAULT_BACKENDS = {
    **{fr: bk
       for lang in core.ALL_LANGUAGES
       for (fr, bk) in _default_language_backends(lang).items()},

    'coqdoc': 'webpage',
    'rst': 'webpage',
    'md': 'webpage',

    'json': 'json', # LATER: Remove
}

def _input_frontends(lang):
    return [lang, lang + '+rst', lang + '.json', lang + '.io.json']

INPUT_LANGUAGE_BY_FRONTEND = {
    **{fr: lang
       for lang in core.ALL_LANGUAGES
       for fr in _input_frontends(lang)},

    "coqdoc": "coq",

    "json": "coq", # LATER: Remove
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
    if out_fpath and out_fpath != "-":
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

    return frontend, backend, supported_backends[backend]

COPY_FUNCTIONS = {
    "copy": shutil.copyfile,
    "symlink": os.symlink,
    "hardlink": os.link,
    "none": None
}

def post_process_arguments(parser, args):
    if len(args.input) > 1 and args.output:
        parser.error("argument --output: Not valid with multiple inputs")

    if args.stdin_filename and "-" not in args.input:
        parser.error("argument --stdin-filename: input must be '-'")

    args.backend_dialects = {
        "webpage": args.html_dialect,
        "latex": args.latex_dialect
    }

    args.language_drivers = {
        **core.DEFAULT_DRIVERS,
        "coq": args.coq_driver
    }

    coq_args = []
    for (dirpath,) in args.coq_args_I:
        coq_args.extend(("-I", dirpath))
    for pair in args.coq_args_R:
        coq_args.extend(("-R", ",".join(pair)))
    for pair in args.coq_args_Q:
        coq_args.extend(("-Q", ",".join(pair)))

    args.sertop_args.extend(coq_args)
    args.coqc_args.extend(coq_args)

    args.driver_args_by_name = {
        "sertop": args.sertop_args,
        "sertop_noexec": args.sertop_args,
        "coqc_time": args.coqc_args,
    }
    assert set(core.ALL_DRIVERS) == args.driver_args_by_name.keys()

    # argparse applies ‘type’ before ‘choices’, so we do the conversion here
    args.copy_fn = COPY_FUNCTIONS[args.copy_fn]

    if args.long_line_threshold < 0:
        args.long_line_threshold = None

    args.point, args.marker = args.mark_point
    if args.point is not None:
        try:
            args.point = int(args.point)
        except ValueError:
            MSG = "argument --mark-point: Expecting a number, not {!r}"
            parser.error(MSG.format(args.point))

    args.pipelines = [(fpath, *resolve_pipeline(fpath, args))
                      for fpath in args.input]

    return args

def build_parser():
    parser = argparse.ArgumentParser(
        description="""\
Annotate segments of Coq code with responses and goals.
Take input in Coq, reStructuredText, Markdown, or JSON \
and produce reStructuredText, HTML, LaTeX, or JSON output.""",
        fromfile_prefix_chars='@')

    VERSION_HELP = "Print version and exit."
    parser.add_argument("--version", action="version",
                        version="Alectryon v{}".format(__version__),
                        help=VERSION_HELP)

    in_ = parser.add_argument_group("Input configuration")

    INPUT_FILES_HELP = "Input files"
    in_.add_argument("input", nargs="+", help=INPUT_FILES_HELP)

    INPUT_STDIN_NAME_HELP = "Name of file passed on stdin, if any"
    in_.add_argument("--stdin-filename", default=None,
                     help=INPUT_STDIN_NAME_HELP)

    FRONTEND_HELP = "Choose a frontend. Defaults: "
    FRONTEND_HELP += "; ".join("{!r} → {}".format(ext, frontend)
                               for ext, frontend in FRONTENDS_BY_EXTENSION)
    FRONTEND_CHOICES = sorted(PIPELINES.keys())
    in_.add_argument("--frontend", default=None, choices=FRONTEND_CHOICES,
                     help=FRONTEND_HELP)

    COQ_DRIVER_HELP = "Choose which driver to use to execute Coq proofs."
    COQ_DRIVER_CHOICES = sorted(core.DRIVERS_BY_LANGUAGE["coq"])
    in_.add_argument("--coq-driver", default="sertop",
                     choices=COQ_DRIVER_CHOICES,
                     help=COQ_DRIVER_HELP)

    out = parser.add_argument_group("Output configuration")

    BACKEND_HELP = "Choose a backend. Supported: "
    BACKEND_HELP += "; ".join(
        "{} → {{{}}}".format(frontend, ", ".join(sorted(backends)))
        for frontend, backends in PIPELINES.items())
    BACKEND_CHOICES = sorted(set(b for _, bs in PIPELINES.items() for b in bs))
    out.add_argument("--backend", default=None, choices=BACKEND_CHOICES,
                     help=BACKEND_HELP)

    OUT_FILE_HELP = "Set the output file (default: computed based on INPUT)."
    out.add_argument("-o", "--output", default=None,
                     help=OUT_FILE_HELP)

    OUT_DIR_HELP = "Set the output directory (default: same as each INPUT)."
    out.add_argument("--output-directory", default=None,
                     help=OUT_DIR_HELP)

    COPY_ASSETS_HELP = ("Chose the method to use to copy assets along the " +
                        "generated file(s) when creating webpages and TeX docs.")
    out.add_argument("--copy-assets", choices=list(COPY_FUNCTIONS.keys()),
                     default="copy", dest="copy_fn",
                     help=COPY_ASSETS_HELP)

    PYGMENTS_STYLE_HELP = "Choose a pygments style by name."
    out.add_argument("--pygments-style", default=None,
                     help=PYGMENTS_STYLE_HELP)

    MARK_POINT_HELP = "Mark a point in the output with a given marker."
    out.add_argument("--mark-point", nargs=2, default=(None, None),
                     metavar=("POINT", "MARKER"),
                     help=MARK_POINT_HELP)

    NO_HEADER_HELP = "Do not insert a header with usage instructions in webpages."
    out.add_argument("--no-header", action='store_false',
                     dest="include_banner", default="True",
                     help=NO_HEADER_HELP)

    NO_VERSION_NUMBERS = "Omit version numbers in meta tags and headers."
    out.add_argument("--no-version-numbers", action='store_false',
                     dest="include_vernums", default=True,
                     help=NO_VERSION_NUMBERS)

    cache_out = parser.add_argument_group("Cache configuration")

    CACHE_DIRECTORY_HELP = ("Cache prover output in DIRECTORY.")
    cache_out.add_argument("--cache-directory", default=None, metavar="DIRECTORY",
                           help=CACHE_DIRECTORY_HELP)

    CACHE_COMPRESSION_HELP = ("Compress caches.")
    CACHE_COMPRESSION_CHOICES = ("none", "gzip", "xz")
    cache_out.add_argument("--cache-compression", nargs='?',
                           default=None, const="xz",
                           choices=CACHE_COMPRESSION_CHOICES,
                           help=CACHE_COMPRESSION_HELP)

    html_out = parser.add_argument_group("HTML output configuration")

    WEBPAGE_STYLE_HELP = "Choose a style for standalone webpages."
    WEBPAGE_STYLE_CHOICES = ("centered", "floating", "windowed")
    html_out.add_argument("--webpage-style", default="centered",
                          choices=WEBPAGE_STYLE_CHOICES,
                          help=WEBPAGE_STYLE_HELP)

    HTML_MINIFICATION_HELP = (
        "Minify HTML files using backreferences for repeated content. "
        "(Backreferences are automatically expanded on page load,"
        " using a very small amount of JavaScript code.)"
    )
    html_out.add_argument("--html-minification", action='store_true',
                          default=False,
                          help=HTML_MINIFICATION_HELP)

    HTML_DIALECT_HELP = "Choose which HTML dialect to use."
    HTML_DIALECT_CHOICES = ("html4", "html5")
    html_out.add_argument("--html-dialect", default="html4",
                          choices=HTML_DIALECT_CHOICES,
                          help=HTML_DIALECT_HELP)

    latex_out = parser.add_argument_group("LaTeX output configuration")

    LATEX_DIALECT_HELP = "Choose which LaTeX dialect to use."
    LATEX_DIALECT_CHOICES = ("pdflatex", "xelatex", "lualatex")
    latex_out.add_argument("--latex-dialect", default="pdflatex",
                           choices=LATEX_DIALECT_CHOICES,
                           help=LATEX_DIALECT_HELP)

    subp = parser.add_argument_group("SerAPI process configuration")

    SERTOP_ARGS_HELP = ("Pass a single argument to SerAPI "
                        "(e.g. --sertop-arg=-Q --sertop-arg=dir,lib).")
    subp.add_argument("--sertop-arg", dest="sertop_args",
                      action="append", default=[],
                      metavar="SERTOP_ARG",
                      help=SERTOP_ARGS_HELP)

    COQC_ARGS_HELP = ("Pass a single argument to coqc "
                        "(e.g. --coqc-arg=-noinit).")
    subp.add_argument("--coqc-arg", dest="coqc_args",
                      action="append", default=[],
                      metavar="SERAPI_ARG",
                      help=COQC_ARGS_HELP)

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

    warn_out = parser.add_argument_group("Warnings configuration")

    LL_THRESHOLD_HELP = "Warn on lines longer than this threshold (docutils)."
    warn_out.add_argument("--long-line-threshold", type=int,
                          default=72, help=LL_THRESHOLD_HELP)

    debug = parser.add_argument_group("Debugging options")

    EXPECT_UNEXPECTED_HELP = "Ignore unexpected output from SerAPI."
    debug.add_argument("--expect-unexpected", action="store_true",
                       default=False, help=EXPECT_UNEXPECTED_HELP)

    DEBUG_HELP = "Print communications with prover process."
    debug.add_argument("--debug", action="store_true",
                       default=False, help=DEBUG_HELP)

    TRACEBACK_HELP = "Print error traces."
    debug.add_argument("--traceback", action="store_true",
                       default=False, help=TRACEBACK_HELP)

    return parser

def parse_arguments():
    parser = build_parser()
    return post_process_arguments(parser, parser.parse_args())


# Entry point
# ===========

class ExitCode:
    def __init__(self, n):
        self.val = n

def call_pipeline_step(step, state, ctx):
    params = list(inspect.signature(step).parameters.keys())[1:]
    return step(state, **{p: ctx[p] for p in params})

def build_context(fpath, args, frontend, backend):
    input_is_stdin = fpath == "-"

    if input_is_stdin:
        fpath = args.stdin_filename or fpath
    fname = os.path.basename(fpath)

    dialect = args.backend_dialects.get(backend)

    # These may be ``None`` (e.g. in reST mode)
    input_language = INPUT_LANGUAGE_BY_FRONTEND.get(frontend)
    driver_name = args.language_drivers.get(input_language)
    driver_args = args.driver_args_by_name.get(driver_name, ())

    ctx = {**vars(args),
           "fpath": fpath, "fname": fname, "input_is_stdin": input_is_stdin,
           "frontend": frontend, "backend": backend, "dialect": dialect,
           "input_language": input_language,
           "driver_name": driver_name, "driver_args": driver_args,
           "assets": [], "html_classes": [], "exit_code": ExitCode(0)}
    ctx["ctx"] = ctx

    if args.output_directory is None:
        if input_is_stdin:
            ctx["output_directory"] = "."
        else:
            refpath = fpath if args.output in (None, "-") else args.output
            ctx["output_directory"] = os.path.dirname(os.path.abspath(refpath))

    os.makedirs(os.path.abspath(ctx["output_directory"]), exist_ok=True)

    if args.output is None and input_is_stdin:
        ctx["output"] = "-"

    return ctx

def except_hook(etype, value, tb):
    from traceback import TracebackException
    for line in TracebackException(etype, value, tb, capture_locals=True).format():
        print(line, file=sys.stderr)

def process_pipelines(args):
    if args.debug:
        core.DEBUG = True

    if args.traceback:
        core.TRACEBACK = True
        sys.excepthook = except_hook

    if args.expect_unexpected:
        from . import serapi
        serapi.SerAPI.EXPECT_UNEXPECTED = True

    for fpath, frontend, backend, pipeline in args.pipelines:
        state, ctx = None, build_context(fpath, args, frontend, backend)
        for step in pipeline:
            state = call_pipeline_step(step, state, ctx)
        yield ctx["exit_code"].val

def main():
    try:
        args = parse_arguments()
        sys.exit(max(process_pipelines(args), default=0))
    except (ValueError, FileNotFoundError, ImportError, argparse.ArgumentTypeError) as e:
        if core.TRACEBACK:
            raise e
        MSG = "Exiting early due to an error; use --traceback to diagnose:"
        print(MSG, file=sys.stderr)
        print(core.indent(str(e), "  "), file=sys.stderr)
        sys.exit(1)

# Alternative CLIs
# ================

def rstcoq2html():
    """Docutils entry point for Coq → HTML conversion."""
    DESCRIPTION = 'Build an HTML document from an Alectryon Coq file.'
    return _docutils_cmdline(DESCRIPTION, "coq+rst", "webpage", "html4")

def coqrst2html():
    """Docutils entry point for reST → HTML conversion."""
    DESCRIPTION = 'Build an HTML document from an Alectryon reStructuredText file.'
    return _docutils_cmdline(DESCRIPTION, "rst", "webpage", "html4")

def rstcoq2latex():
    """Docutils entry point for Coq → LaTeX conversion."""
    DESCRIPTION = 'Build a LaTeX document from an Alectryon Coq file.'
    return _docutils_cmdline(DESCRIPTION, "coq+rst", "latex", "pdflatex")

def coqrst2latex():
    """Docutils entry point for reST → LaTeX conversion."""
    DESCRIPTION = 'Build a LaTeX document from an Alectryon reStructuredText file.'
    return _docutils_cmdline(DESCRIPTION, "rst", "latex", "pdflatex")
