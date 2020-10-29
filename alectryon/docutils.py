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
"""

import re
import os.path

import docutils
from docutils import nodes, frontend

from docutils.parsers.rst import directives, roles, Directive
from docutils.parsers.rst.directives.body import Sidebar
from docutils.readers.standalone import Reader
from docutils.transforms import Transform
from docutils.writers import get_writer_class

from . import transforms
from .core import annotate
from .html import ASSETS, HtmlGenerator, gen_header, wrap_classes
from .pygments import highlight_html, added_tokens, replace_builtin_coq_lexer

# reST extensions
# ===============

# Nodes
# -----

class alectryon_pending(nodes.pending):
    pass

class alectryon_pending_toggle(nodes.pending):
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
    default_priority = 995
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

    @staticmethod
    def document_id(document):
        source = document.get('source', "")
        return nodes.make_id(os.path.basename(source))

    def check_for_long_lines(self, node, fragments):
        if LONG_LINE_THRESHOLD is None:
            return
        for line in transforms.find_long_lines(fragments, threshold=LONG_LINE_THRESHOLD):
            msg = "Long line: {!r} ({} characters)".format(line, len(line))
            self.document.reporter.warning(msg, base_node=node)
            return

    def annotate_cached(self, chunks, sertop_args):
        from .json import Cache
        cache = Cache(CACHE_DIRECTORY, self.document['source'], sertop_args)
        annotated = cache.get(chunks)
        if annotated is None:
            annotated = annotate(chunks, sertop_args)
            cache.put(chunks, annotated)
        return annotated

    def annotate(self, pending_nodes, config):
        sertop_args = (*self.SERTOP_ARGS, *config.sertop_args)
        chunks = [pending.details["contents"] for pending in pending_nodes]
        return self.annotate_cached(chunks, sertop_args) # if chunks else []

    def replace_node(self, config, writer, pending, fragments):
        annots = transforms.IOAnnots(*pending.details['options'])
        if annots.hide:
            pending.parent.remove(pending)
            return
        fragments = self.set_fragment_annots(fragments, annots)
        fragments = transforms.default_transform(fragments)
        self.check_for_long_lines(pending, fragments)
        with added_tokens(config.tokens):
            html = writer.gen_fragments(fragments).render(pretty=False)
        contents = pending.details["contents"]
        pending.replace_self(nodes.raw(contents, html, format='html'))

    def apply_coq(self):
        config = Config(self.document)
        pending_nodes = self.document.traverse(alectryon_pending)
        annotated = self.annotate(pending_nodes, config)
        writer = HtmlGenerator(highlight_html, gensym_stem=self.document_id(self.document))
        for node, fragments in zip(pending_nodes, annotated):
            self.replace_node(config, writer, node, fragments)

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
        if not getattr(self.document, 'alectryon_transform_executed', False):
            self.document.alectryon_transform_executed = True
            self.apply_coq()
            self.apply_toggle()

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
        self.state_machine.document.note_pending(pending)
        return [pending]

class AlectryonHeaderDirective(Directive):
    """Display an explanatory header."""
    name = "alectryon-header"

    required_arguments = 0
    optional_arguments = 0
    option_spec = {}
    has_content = False

    def run(self):
        from .core import SerAPI
        return [nodes.raw('', gen_header(SerAPI.version_info()))]

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
    return [nodes.inline(rawtext, classes=['alectryon-bubble'])], []

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
    """Aliases this parser supports."""

    settings_spec = ('Literate Coq Parser Options', None,
                     docutils.parsers.rst.Parser.settings_spec[2])
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

DefaultWriter = get_writer_class('html')

class HtmlTranslator(DefaultWriter().translator_class):
    JS = ASSETS.ALECTRYON_JS
    CSS = (*ASSETS.ALECTRYON_CSS, *ASSETS.DOCUTILS_CSS, *ASSETS.PYGMENTS_CSS)
    ADDITIONAL_HEADS = [ASSETS.IBM_PLEX_CDN, ASSETS.FIRA_CODE_CDN]

    JS_TEMPLATE = '<script type="text/javascript" src="{}"></script>\n'
    MATHJAX_URL = "https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.1.2/es5/tex-mml-chtml.min.js"

    head_prefix_template = ('<html xmlns="http://www.w3.org/1999/xhtml" class="alectryon-standalone"'
                            ' xml:lang="%(lang)s" lang="%(lang)s">\n<head>\n')

    def stylesheet_call(self, name):
        if self.settings.embed_stylesheet:
            # Expand only if we're going to inline; otherwise keep relative
            name = os.path.join(ASSETS.PATH, name)
        return super().stylesheet_call(name)

    def __init__(self, document):
        super().__init__(document)
        self.settings.syntax_highlight = "short"
        self.settings.math_output = "MathJax " + self.MATHJAX_URL
        self.stylesheet.extend(self.stylesheet_call(css) for css in self.CSS)
        self.stylesheet.extend(self.JS_TEMPLATE.format(js) for js in self.JS)
        self.stylesheet.extend(hd + "\n" for hd in self.ADDITIONAL_HEADS)
        cls = wrap_classes(self.settings.webpage_style)
        self.body_prefix.append('<div class="{}">'.format(cls))
        if not self.settings.no_header:
            from .core import SerAPI
            self.body_prefix.append(gen_header(SerAPI.version_info()))
        self.body_suffix.insert(0, '</div>')

class HtmlWriter(DefaultWriter):
    settings_spec = ('HTML-Specific Options', None,
                     (("Choose an Alectryon style",
                        ["--webpage-style"],
                        {"choices": ("centered", "floating", "windowed"),
                         "default": "centered", "metavar": "STYLE"}),
                       ("Omit Alectryon's explanatory header",
                        ["--no-header"],
                        {'default': False, 'action': 'store_true',
                         'validator': frontend.validate_boolean}),
                       *DefaultWriter.settings_spec[-1]))

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.translator_class = HtmlTranslator

# Entry points
# ============

NODES = [alectryon_pending, alectryon_pending_toggle]
TRANSFORMS = [AlectryonTransform]
DIRECTIVES = [CoqDirective,
              AlectryonToggleDirective, AlectryonHeaderDirective,
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
