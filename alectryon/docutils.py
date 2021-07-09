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

"""reStructuredText support for Alectryon.

This file defines a ``.. coq::`` directive, which formats its contents using
Alectryon::

       .. coq::

           Example test: nat.

This directive supports various arguments to control the appearance of the
output; check out the README for details.

To use it, call ``docutils_support.register()`` before running your
reStructuredText to HTML converter.  The generated code relies on CSS classes
defined in the ``assets/alectryon.css`` file.

A checkbox and an accompanying label (with classes ``alectryon-toggle`` and
``alectryon-toggle-label``) allowing users to reveal all goals and responses at
once is automatically added right before the document's first paragraph.  You
can change its location by inserting an explicit ``.. alectryon-toggle::``
directive in your document, and you can ommit it entirely by setting
``AlectryonTransform.insert_toggle`` to ``False`` (to make styling easier, all
contents following the checkbox are wrapped in a container with class
``alectryon-container``).

Inline Coq highlighting is provided by the ``:coq:`` role.  By default it uses
Pygments' default Coq highlighter (like ``.. code-block``), but you can change
that using ``alectryon.pygments.replace_builtin_coq_lexer()``.

If you write lots of inline Coq snippets, consider calling ``set_default_role``,
which will set the default role to ``:coq:``.

For convenience, ``alectryon.docutils.setup()`` can be used to perform all the
steps above at once.

A note on transforms: Sphinx has a nice API (``app.add_node``) for adding new
node types, so you can write visitors for each output format without creating
new translators.  Docutils doesn't have such an API: it forces you to subclass
the default translator instead, which is a pain.  The alternative is to use a
transform to replace custom nodes with "raw" nodes, but even this is non-trivial
because the transform doesn't know which output format the document uses.

To work around this issue we use a writer-dependent transform on the docutils
side, and a doctree-resolved event on the Sphinx side.
"""

import re
import os.path

import docutils
from docutils import nodes, frontend

from docutils.parsers.rst import directives, roles, Directive
from docutils.parsers.rst.directives.body import Sidebar
from docutils.readers.standalone import Reader
from docutils.transforms import Transform
from docutils.writers import html4css1, latex2e, xetex

from . import transforms
from .core import annotate, SerAPI
from .html import ADDITIONAL_HEADS, HtmlGenerator, gen_banner, wrap_classes, ASSETS as ASSETS_HTML
from .latex import LatexGenerator, ASSETS as ASSETS_LATEX
from .pygments import highlight_html, highlight_latex, added_tokens, replace_builtin_coq_lexer

# reST extensions
# ===============

def set_line(node, lineno, sm):
    node.source, node.line = sm.get_source_and_line(lineno)

# Nodes
# -----

class alectryon_pending(nodes.pending):
    pass

class alectryon_pending_toggle(nodes.pending):
    pass

class alectryon_io(docutils.nodes.Element):
    pass

# Transforms
# ----------

TOGGLE_HTML = """
<input type="checkbox" class="alectryon-toggle" id="alectryon-toggle-{id}" />
<label for="alectryon-toggle-{id}" class="alectryon-toggle-label">
Display all goals and responses
</label>""".replace('\n', '')

LONG_LINE_THRESHOLD = 72
"""Threshold above which to warn about long lines."""

CACHE_DIRECTORY = None
"""Directory in which to store cached annotations."""

# LATER: dataclass
class AlectryonState:
    def __init__(self):
        self.generator = None
        self.transform_executed = False

def _alectryon_state(document):
    st = getattr(document, "alectryon_state", None)
    if st is None:
        st = document.alectryon_state = AlectryonState()
    return st

class Config:
    def __init__(self, document):
        self.tokens = {}
        self.sertop_args = []
        # Sphinx doesn't translate ``field_list`` to ``docinfo``
        selector = lambda n: isinstance(n, (nodes.field_list, nodes.docinfo))
        for di in document.traverse(selector):
            for field in di.traverse(nodes.field):
                name, body = field.children
                self.parse_docinfo_field(field, name.rawsource, body.rawsource)

    def parse_docinfo_field(self, node, name, body):
        if name.startswith("alectryon/pygments/"):
            token = name[len("alectryon/pygments/"):]
            self.tokens.setdefault(token, []).extend(body.split())
        elif name == "alectryon/serapi/args":
            import shlex
            self.sertop_args.extend(self.parse_args(shlex.split(body)))
        else:
            return
        node.parent.remove(node)

    @staticmethod
    def parse_args(args):
        import argparse
        p = argparse.ArgumentParser(prog=":alectryon/serapi/args:", add_help=False)
        p.add_argument("-I", "--ml-include-path", dest="I", metavar="DIR",
                       nargs=1, action="append", default=[])
        p.add_argument("-Q", "--load-path", dest="Q", metavar=("DIR", "COQDIR"),
                       nargs=2, action="append", default=[])
        p.add_argument("-R", "--rec-load-path", dest="R", metavar=("DIR", "COQDIR"),
                       nargs=2, action="append", default=[])
        for (arg, instances) in p.parse_args(args)._get_kwargs():
            for vals in instances:
                yield "-" + arg
                yield ",".join(vals)

class AlectryonTransform(Transform):
    default_priority = 990
    auto_toggle = True

    SERTOP_ARGS = ()
    """Arguments to pass to SerAPI, in SerAPI format."""

    @staticmethod
    def set_fragment_annots(fragments, annots):
        """Apply relevant annotations to all unannotated fragments."""
        for fr in transforms.enrich_sentences(fragments):
            if hasattr(fr, 'annots'):
                fr.annots.inherit(annots)
            yield fr

    def check_for_long_lines(self, node, fragments):
        if LONG_LINE_THRESHOLD is None:
            return
        for linum, s in transforms.find_long_lines(fragments, threshold=LONG_LINE_THRESHOLD):
            msg = "Long line: {!r} ({} characters)".format(s, len(s))
            opts = dict(line=node.line + linum) if hasattr(node, "line") else {}
            self.document.reporter.warning(msg, base_node=node, **opts)

    def annotate_cached(self, chunks, sertop_args):
        from .json import Cache
        cache = Cache(CACHE_DIRECTORY, self.document['source'], sertop_args)
        annotated = cache.update(chunks, lambda c: annotate(c, sertop_args), SerAPI.version_info())
        return cache.generator, annotated

    def annotate(self, pending_nodes):
        config = Config(self.document)
        sertop_args = (*self.SERTOP_ARGS, *config.sertop_args)
        chunks = [pending.details["contents"] for pending in pending_nodes]
        return self.annotate_cached(chunks, sertop_args)

    def replace_node(self, pending, fragments):
        annots = transforms.IOAnnots(*pending.details['options'])
        if annots.hide:
            pending.parent.remove(pending)
            return
        fragments = self.set_fragment_annots(fragments, annots)
        fragments = transforms.default_transform(fragments)
        self.check_for_long_lines(pending, fragments)
        contents = pending.details["contents"]
        io = alectryon_io(fragments=fragments, contents=contents)
        pending.replace_self(io)

    def apply_coq(self):
        pending_nodes = list(self.document.traverse(alectryon_pending))
        generator, annotated = self.annotate(pending_nodes)
        _alectryon_state(self.document).generator = generator
        for node, fragments in zip(pending_nodes, annotated):
            self.replace_node(node, fragments)

    @staticmethod
    def split_around(node):
        parent = node.parent
        idx = node.parent.index(node)
        return parent.children[:idx], node, parent.children[idx + 1:]

    @staticmethod
    def insert_toggle_after(node, toggle, keep_node):
        pre, node, post = AlectryonTransform.split_around(node)
        if keep_node:
            pre.append(node)
        pre.append(toggle)
        pre.append(nodes.container('', *post, classes=['alectryon-container']))
        node.parent.children = pre

    def apply_toggle(self):
        toggle = lambda id: nodes.raw('', TOGGLE_HTML.format(id=id), format='html')
        toggles = list(self.document.traverse(alectryon_pending_toggle))
        for idx, node in enumerate(toggles):
            self.insert_toggle_after(node, toggle(idx), False)
            self.auto_toggle = False
        if self.auto_toggle:
            di = self.document.next_node(nodes.docinfo)
            if di:
                self.insert_toggle_after(di, toggle(0), True)

    def apply(self, **_kwargs):
        # The transform is added multiple times: once per directive, and once by
        # add_transform in Sphinx, so we need to make sure that running it twice
        # is safe (in particular, we must not overwrite the cache).
        state = _alectryon_state(self.document)
        if not state.transform_executed:
            state.transform_executed = True
            self.apply_coq()
            self.apply_toggle()

class AlectryonPostTransform(Transform):
    default_priority = 995

    @staticmethod
    def document_id(document):
        source = document.get('source', "")
        return nodes.make_id(os.path.basename(source))

    def init_writer(self):
        raise NotImplementedError("Unknown output format")

    def apply(self, **_kwargs):
        config = Config(self.document)
        fmt, writer = self.init_writer()
        with added_tokens(config.tokens):
            for node in self.document.traverse(alectryon_io):
                fragments, contents = node["fragments"], node["contents"]
                raw = writer.gen_fragments(fragments).render(pretty=False)
                node.replace_self(nodes.raw(contents, raw, format=fmt))

class AlectryonHTMLPostTransform(AlectryonPostTransform):
    def init_writer(self):
        gensym_stem = self.document_id(self.document)
        return "html", HtmlGenerator(highlight_html, gensym_stem=gensym_stem)

class AlectryonLatexPostTransform(AlectryonPostTransform):
    def init_writer(self):
        return "latex", LatexGenerator(highlight_latex)

# Directives
# ----------

INDENTATION_RE = re.compile(" *")
def measure_indentation(line):
    m = INDENTATION_RE.match(line)
    return m.end() - m.start()

def recompute_contents(directive, real_indentation):
    """Compute the contents of `directive` relative to `real_indentation`.

    This undoes the automatic gobbling performed by the reST parser, which is
    useful when a Coq fragment is split across multiple code blocks; in these
    cases reST's automatic gobbling would unindent all lines.  Here is a
    concrete example (reST renders it with all lines flushed left)::

    .. code::

       int main() {

    .. code::

           return 0;

    .. code::

       }
    """
    block_lines = directive.block_text.splitlines()
    block_header_len = directive.content_offset - directive.lineno + 1
    block_indentation = measure_indentation(directive.block_text)
    code_indentation = block_indentation + real_indentation
    return "\n".join(ln[code_indentation:] for ln in block_lines[block_header_len:])

class CoqDirective(Directive):
    """Highlight and annotate a Coq snippet."""
    name = "coq"

    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = {}
    has_content = True

    EXPECTED_INDENTATION = 3

    def run(self):
        self.assert_has_content()
        arguments = self.arguments[0].split() if self.arguments else []
        contents = recompute_contents(self, CoqDirective.EXPECTED_INDENTATION)
        details = {"options": set(arguments), "contents": contents}
        pending = alectryon_pending(AlectryonTransform, details=details)
        set_line(pending, self.lineno, self.state_machine)
        self.state_machine.document.note_pending(pending)
        return [pending]

class AlectryonToggleDirective(Directive):
    """Display a checkbox allowing readers to show all output at once."""
    name = "alectryon-toggle"

    required_arguments = 0
    optional_arguments = 0
    option_spec = {}
    has_content = False

    def run(self):
        pending = alectryon_pending_toggle(AlectryonTransform)
        set_line(pending, self.lineno, self.state_machine)
        self.state_machine.document.note_pending(pending)
        return [pending]

# This is just a small example
class ExperimentalExerciseDirective(Sidebar):
    """Introduce an exercise."""
    name = "exercise"

    node_class = nodes.sidebar
    required_arguments = 1
    option_spec = {**Sidebar.option_spec,
                   "difficulty": directives.nonnegative_int,
                   "optional": directives.flag}

    def run(self):
        [node] = super().run()
        node['difficulty'] = self.options['difficulty']
        node['optional'] = self.options['optional']
        for title in node.traverse(nodes.title):
            title.children.insert(0, nodes.Text("Exercise: "))
        return [node]

# Roles
# -----

# pylint: disable=dangerous-default-value,unused-argument
def alectryon_bubble(role, rawtext, text, lineno, inliner, options={}, content=[]):
    node = nodes.inline(rawtext, classes=['alectryon-bubble'])
    set_line(node, lineno, inliner.reporter)
    return [node], []

alectryon_bubble.name = "alectryon-bubble"

#pylint: disable=dangerous-default-value,unused-argument
def coq_code_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
    options = {**options, "language": "coq"}
    roles.set_classes(options)
    options.setdefault("classes", []).append("highlight")
    return roles.code_role(role, rawtext, text, lineno, inliner, options, content)

coq_code_role.name = "coq"

COQ_ID_RE = re.compile(r"^(?P<title>.*?)(?:\s*<(?P<target>.*)>)?$")
COQ_IDENT_DB_URLS = [
    ("Coq", "https://coq.inria.fr/library/$modpath.html#$ident")
]

def coq_id_role(# pylint: disable=dangerous-default-value,unused-argument
        role, rawtext, text, lineno, inliner, options={}, content=[]):
    mid = COQ_ID_RE.match(text)
    title, target = mid.group("title"), mid.group("target")
    implicit = target is None
    if implicit:
        target = title

    if "#" in target:
        modpath, ident = target.rsplit("#", 1)
        if implicit:
            # Convert `A#b` to `b` and `A#` to `A`
            title = ident if ident else modpath
    elif "." in target:
        modpath, ident = target.rsplit(".", 1)
    else:
        modpath, ident = "", target

    # Options are set using the ‘.. role’ directive
    url = options.get('url', None)
    if url is None:
        if not modpath:
            MSG = "{target!r} is not a fully-qualified name."
            msg = inliner.reporter.error(MSG.format(target=target), line=lineno)
            return [inliner.problematic(rawtext, rawtext, msg)], [msg]

        for prefix, url in COQ_IDENT_DB_URLS:
            if prefix == modpath or modpath.startswith(prefix + "."):
                break
        else:
            MSG = ("Not sure where to find documentation for {target}.\n"
                   "Make sure that ‘{target}’ is fully qualified"
                   " and that Alectryon knows where to find it.\n"
                   "Known prefixes: {prefixes}\n"
                   "(Add prefixes to alectryon.docutils.COQ_IDENT_DB_URLS or"
                   " derive a new role from ‘coqid’ with a custom :url:).")
            prefixes = [prefix for (prefix, _) in COQ_IDENT_DB_URLS]
            msg = MSG.format(target=target, prefixes=prefixes)
            err = inliner.reporter.error(msg, line=lineno)
            return [inliner.problematic(rawtext, rawtext, err)], [err]

    from string import Template
    uri = Template(url).safe_substitute(modpath=modpath, ident=ident)

    roles.set_classes(options)
    node = nodes.reference(rawtext, title, refuri=uri, **options)
    set_line(node, lineno, inliner.reporter)

    return [node], []

coq_id_role.name = "coqid"
coq_id_role.options = {'url': directives.unchanged}

# Error printer
# -------------

class JsErrorPrinter:
    @staticmethod
    def json_of_message(msg):
        message = msg.children[0].astext() if msg.children else "Unknown error"
        level = docutils.utils.Reporter.levels[msg['level']].lower()
        js = {"level": level,
              "message": message,
              "source": msg['source'],
              "line": msg.get('line', 1),
              "column": msg.get('column'),
              "end_line": msg.get('end_line'),
              "end_column": msg.get('end_column')}
        return js

    def __init__(self, stream, settings):
        self.stream = stream
        self.report_level = settings.report_level

    def __call__(self, msg):
        import json
        if msg['level'] >= self.report_level:
            js = self.json_of_message(msg)
            json.dump(js, self.stream)
            self.stream.write('\n')

# Parser
# ------

class RSTCoqParser(docutils.parsers.rst.Parser):
    """A wrapper around the reStructuredText parser for literate Coq files."""

    supported = ('coq',)
    config_section = 'Literate Coq parser'
    config_section_dependencies = ('parsers',)

    @staticmethod
    def rst_lines(coq_input):
        from .literate import coq2rst_lines, Line
        last_line = 0
        for line in coq2rst_lines(coq_input):
            if isinstance(line, Line):
                yield (str(line), line.num)
                last_line = line.num
            else:
                assert isinstance(line, str)
                yield (line, last_line)

    @staticmethod
    def coq_input_lines(coq_input, source):
        from docutils.statemachine import StringList
        lines = RSTCoqParser.rst_lines(coq_input)
        initlist, items = [], []
        # Don't use zip(): we need lists, not tuples, and the input can be empty
        for (line, i) in lines:
            initlist.append(line)
            items.append((source, i))
        return StringList(initlist, source, items)

    def report_parsing_error(self, e):
        self.document.append(self.document.reporter.severe(
            e.message, line=e.line, column=e.column,
            end_line=e.end_line, end_column=e.end_column))

    def parse(self, inputstring, document):
        """Parse `inputstring` and populate `document`, a document tree."""
        from .literate import ParsingError
        self.setup_parse(inputstring, document)
        # pylint: disable=attribute-defined-outside-init
        self.statemachine = docutils.parsers.rst.states.RSTStateMachine(
            state_classes=self.state_classes,
            initial_state=self.initial_state,
            debug=document.reporter.debug_flag)
        try:
            lines = RSTCoqParser.coq_input_lines(inputstring, document['source'])
            self.statemachine.run(lines, document, inliner=self.inliner)
        except ParsingError as e:
            self.report_parsing_error(e)
        if '' in roles._roles: # Reset the default role
            del roles._roles['']
        self.finish_parse()

class RSTCoqStandaloneReader(Reader):
    def __init__(self, parser=None, parser_name=None, extra_transforms=None):
        Reader.__init__(self, parser, parser_name)
        self.extra_transforms = extra_transforms or []

    def get_transforms(self):
        # AlectryonTransform not added here because the CoqDirective does it
        return Reader.get_transforms(self) + self.extra_transforms

# Writer
# ------

def register_stylesheets(translator, stylesheets):
    for name in stylesheets:
        if translator.settings.embed_stylesheet:
            # Expand only if we're going to inline; otherwise keep relative
            name = os.path.join(ASSETS_HTML.PATH, name)
        translator.stylesheet.append(translator.stylesheet_call(name))

class HtmlTranslator(html4css1.HTMLTranslator): \
      # pylint: disable=abstract-method
    JS = ASSETS_HTML.ALECTRYON_JS
    CSS = (*ASSETS_HTML.ALECTRYON_CSS, *ASSETS_HTML.DOCUTILS_CSS, *ASSETS_HTML.PYGMENTS_CSS)
    ADDITIONAL_HEADS = [ASSETS_HTML.IBM_PLEX_CDN, ASSETS_HTML.FIRA_CODE_CDN, *ADDITIONAL_HEADS]

    JS_TEMPLATE = '<script type="text/javascript" src="{}"></script>\n'
    MATHJAX_URL = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.1.2/es5/tex-mml-chtml.min.js"

    head_prefix_template = \
        '<html xmlns="http://www.w3.org/1999/xhtml" class="alectryon-standalone"' \
        ' xml:lang="%(lang)s" lang="%(lang)s">\n<head>\n'

    def __init__(self, document):
        document.settings.syntax_highlight = "short"
        document.settings.math_output = "MathJax " + self.MATHJAX_URL
        super().__init__(document)
        register_stylesheets(self, self.CSS)
        self.stylesheet.extend(self.JS_TEMPLATE.format(js) for js in self.JS)
        self.stylesheet.extend(hd + "\n" for hd in self.ADDITIONAL_HEADS)
        cls = wrap_classes(self.settings.webpage_style)
        self.body_prefix.append('<div class="{}">'.format(cls))
        if self.settings.alectryon_banner:
            generator = _alectryon_state(document).generator
            include_vernums = document.settings.alectryon_vernums
            self.body_prefix.append(gen_banner(generator, include_vernums))
        self.body_suffix.insert(0, '</div>')

ALECTRYON_SETTINGS = (
    ("Choose an Alectryon webpage style",
     ["--webpage-style"],
     {"choices": ("centered", "floating", "windowed"),
      "dest": "webpage_style",
      "default": "centered", "metavar": "STYLE"}),
    ("Omit Alectryon's explanatory header",
     ["--no-header"],
     {'default': True, 'action': 'store_false',
      'dest': "alectryon_banner",
      'validator': frontend.validate_boolean}),
    ("Omit Alectryon's version info",
     ["--no-version-numbers"],
     {'default': True, 'action': 'store_false',
      'dest': "alectryon_vernums",
      'validator': frontend.validate_boolean})
)

class HtmlWriter(html4css1.Writer):
    settings_spec = (html4css1.Writer.settings_spec +
                     ('Alectryon HTML writer options',
                      None, ALECTRYON_SETTINGS))

    def get_transforms(self):
        return super().get_transforms() + [AlectryonHTMLPostTransform]

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.translator_class = HtmlTranslator

def make_LatexTranslator(base):
    class Translator(base): \
          # pylint: disable=abstract-method
        STY = ASSETS_LATEX.ALECTRYON_STY + ASSETS_LATEX.PYGMENTS_STY

        def __init__(self, document, *args, **kwargs):
            super().__init__(document, *args, **kwargs)
            register_stylesheets(self, self.STY)
    return Translator

LatexTranslator = make_LatexTranslator(latex2e.LaTeXTranslator)
XeLatexTranslator = make_LatexTranslator(xetex.XeLaTeXTranslator)

def make_LatexWriter(base, translator_class):
    class Writer(base):
        def get_transforms(self):
            return super().get_transforms() + [AlectryonLatexPostTransform]

        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.translator_class = translator_class
    return Writer

LatexWriter = make_LatexWriter(latex2e.Writer, LatexTranslator)
XeLatexWriter = make_LatexWriter(xetex.Writer, XeLatexTranslator)

# Entry points
# ============

NODES = [alectryon_pending,
         alectryon_pending_toggle]
TRANSFORMS = [AlectryonTransform]
DIRECTIVES = [CoqDirective,
              AlectryonToggleDirective,
              ExperimentalExerciseDirective]
ROLES = [alectryon_bubble, coq_code_role, coq_id_role]

def register():
    """Tell Docutils about our roles and directives."""
    for directive in DIRECTIVES:
        directives.register_directive(directive.name, directive)
    for role in ROLES:
        roles.register_canonical_role(role.name, role)

def set_default_role():
    """Set the default role (the one used with single backticks) to :coq:."""
    roles.register_canonical_role(coq_code_role.name, coq_code_role)
    roles.DEFAULT_INTERPRETED_ROLE = coq_code_role.name

def setup():
    """Prepare docutils for writing Coq documents with Alectryon.

    This includes registering Alectryon's role and directives, loading an
    improved Coq highlighter, and setting the default role to ``:coq:``.
    """
    register()
    set_default_role()
    replace_builtin_coq_lexer()
