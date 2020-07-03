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
"""

import re
import os.path

import docutils
from docutils import nodes, frontend

from docutils.parsers.rst import directives, roles, Directive
from docutils.readers.standalone import Reader
from docutils.transforms import Transform
from docutils.writers import get_writer_class

from . import transforms
from .core import annotate
from .html import ASSETS, HtmlGenerator, gen_header, wrap_classes
from .pygments import highlight, added_tokens

# reST extensions
# ===============

# Nodes
# -----

class alectryon_pending(nodes.Special, nodes.Invisible, nodes.Element):
    pass

class alectryon_pending_toggle(nodes.Special, nodes.Invisible, nodes.Element):
    pass

# Transforms
# ----------

TOGGLE_HTML = """
<input type="checkbox" class="alectryon-toggle" id="alectryon-toggle-{id}" />
<label for="alectryon-toggle-{id}" class="alectryon-toggle-label">
Display all goals and responses
</label>""".replace('\n', '')

LONG_LINE_THRESHOLD = 72

class Config:
    def __init__(self, document):
        self.tokens = {}
        self.serapi_args = []
        for di in document.traverse(nodes.docinfo):
            for field in di.traverse(nodes.field):
                name, body = field.children
                self.parse_docinfo_field(field, name.rawsource, body.rawsource)

    def parse_docinfo_field(self, node, name, body):
        if name.startswith("alectryon/pygments/"):
            token = name[len("alectryon/pygments/"):]
            self.tokens.setdefault(token, []).extend(body.split())
        elif name == "alectryon/serapi/args":
            self.parse_args(body)
        else:
            return
        node.parent.remove(node)

    def parse_args(self, args):
        import argparse
        import shlex
        p = argparse.ArgumentParser(prog=":alectryon/serapi/args:", add_help=False)
        p.add_argument("-I", "--ml-include-path", dest="I", metavar="DIR",
                       nargs=1, action="append", default=[])
        p.add_argument("-Q", "--load-path", dest="Q", metavar=("DIR", "COQDIR"),
                       nargs=2, action="append", default=[])
        p.add_argument("-R", "--rec-load-path", dest="R", metavar=("DIR", "COQDIR"),
                       nargs=2, action="append", default=[])
        for (arg, instances) in p.parse_args(shlex.split(args))._get_kwargs():
            for vals in instances:
                self.serapi_args.append("-" + arg)
                self.serapi_args.append(",".join(vals))

class AlectryonTransform(Transform):
    default_priority = 995
    auto_toggle = True

    SERAPI_ARGS = ()
    """Arguments to pass to SerAPI"""

    @staticmethod
    def set_fragment_annots(fragments, annots):
        """Apply relevant annotations to all unannotated fragments."""
        for fr in transforms.htmlify_sentences(fragments):
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

    def apply_coq(self):
        config = Config(self.document)
        writer = HtmlGenerator(highlight, gensym_stem=self.document_id(self.document))
        pending_nodes = list(self.document.traverse(alectryon_pending))
        pending = (n['content'] for n in pending_nodes)
        annotated = annotate(pending, (*self.SERAPI_ARGS, *config.serapi_args))
        for node, fragments in zip(pending_nodes, annotated):
            annots = transforms.IOAnnots(*node['options'])
            if annots.hide:
                node.parent.remove(node)
                continue
            fragments = self.set_fragment_annots(fragments, annots)
            fragments = transforms.default_transform(fragments)
            self.check_for_long_lines(node, fragments)
            with added_tokens(config.tokens):
                html = writer.gen_fragments(fragments).render(pretty=False)
            node.replace_self(nodes.raw(node['content'], html, format='html'))

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
        assert self.startnode is None
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
    lines = [ln[code_indentation:] for ln in block_lines[block_header_len:]]
    return lines

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

        stm = self.state_machine
        pos = stm.get_source_and_line(self.lineno)
        content_pos = stm.get_source_and_line(self.content_offset)

        if not getattr(stm.document, 'alectryon_transform_added', False):
            stm.document.alectryon_transform_added = True
            stm.document.transformer.add_transform(AlectryonTransform)

        arguments = self.arguments[0].split() if self.arguments else []
        lines = recompute_contents(self, CoqDirective.EXPECTED_INDENTATION)
        return [alectryon_pending(
            content="\n".join(lines),
            pos=pos, content_pos=content_pos, options=set(arguments))]

class AlectryonToggleDirective(Directive):
    """Display a checkbox allowing readers to show all output at once."""
    name = "alectryon-toggle"

    required_arguments = 0
    optional_arguments = 0
    option_spec = {}
    has_content = False

    def run(self):
        return [alectryon_pending_toggle()]


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

# Roles
# -----

def alectryon_bubble(# pylint: disable=dangerous-default-value
        _name, rawtext, _text, _lineno, _inliner, _options={}, _content=[]):
    return [nodes.inline(rawtext, classes=['alectryon-bubble'])], []

alectryon_bubble.name = "alectryon-bubble"

# Error printer
# -------------

class JsErrorPrinter:
    @staticmethod
    def json_of_message(level, message, source, line):
        js = { "level": level,
               "message": message,
               "source": source,
               "line": line }
        return js

    def __init__(self, stream, settings):
        self.stream = stream
        self.report_level = settings.report_level

    def __call__(self, msg):
        import json
        message = msg.children[0].astext() if msg.children else "Unknown error"
        level, source, line = msg['level'], msg['source'], msg.get('line', 1)
        if level >= self.report_level:
            level = docutils.utils.Reporter.levels[level].lower()
            js = JsErrorPrinter.json_of_message(level, message, source, line)
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

    def parse(self, inputstring, document):
        """Parse `inputstring` and populate `document`, a document tree."""
        self.setup_parse(inputstring, document)
        # pylint: disable=attribute-defined-outside-init
        self.statemachine = docutils.parsers.rst.states.RSTStateMachine(
              state_classes=self.state_classes,
              initial_state=self.initial_state,
              debug=document.reporter.debug_flag)
        lines = RSTCoqParser.coq_input_lines(inputstring, document['source'])
        self.statemachine.run(lines, document, inliner=self.inliner)
        if '' in roles._roles:
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

    JS_TEMPLATE = '<script type="text/javascript" src="{}"></script>'
    MATHJAX_URL = ("MathJax "
                   "https://cdnjs.cloudflare.com/ajax/libs/"
                   "mathjax/2.7.0/MathJax.js?config=TeX-AMS_HTML-full")

    def stylesheet_call(self, name):
        if self.settings.embed_stylesheet:
            # Expand only if we're going to inline; otherwise keep relative
            name = os.path.join(ASSETS.PATH, name)
        return super().stylesheet_call(name)

    def __init__(self, document):
        super().__init__(document)
        self.settings.syntax_highlight = "short"
        self.settings.math_output = self.MATHJAX_URL
        self.stylesheet.extend(self.stylesheet_call(css) for css in self.CSS)
        self.stylesheet.extend(self.JS_TEMPLATE.format(js) for js in self.JS)
        cls = wrap_classes("standalone", self.settings.webpage_style)
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

# Entry point
# ===========

NODES = [alectryon_pending, alectryon_pending_toggle]
TRANSFORMS = [AlectryonTransform]
DIRECTIVES = [CoqDirective, AlectryonToggleDirective, AlectryonHeaderDirective]
ROLES = [alectryon_bubble]

def register():
    """Tell Docutils about our directives (.. coq and .. alectryon-toggle).

    You can customize the name under which these are registered by adjusting the
    ``name`` field of ``CoqDirective`` and ``AlectryonToggleDirective``.
    """
    for directive in DIRECTIVES:
        directives.register_directive(directive.name, directive)
    for role in ROLES:
        roles.register_canonical_role(role.name, alectryon_bubble)
