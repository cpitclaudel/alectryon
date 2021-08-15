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

# pylint: disable=dangerous-default-value,unused-argument

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
``AlectryonTransform.auto_toggle`` to ``False`` (to make styling easier, all
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

from typing import Any, Dict, List, Optional

import re
import os.path
from copy import deepcopy
from collections import namedtuple, defaultdict
from importlib import import_module

import docutils
import docutils.frontend
import docutils.transforms
import docutils.utils
from docutils import nodes

from docutils.parsers.rst import directives, roles, Directive # type: ignore
from docutils.parsers.rst.directives.body import Sidebar # type: ignore
from docutils.readers.standalone import Reader as StandaloneReader
from docutils.transforms import Transform
from docutils.writers import html4css1, html5_polyglot, latex2e, xetex

from . import core, transforms, html, latex, markers
from .core import Gensym, annotate, SerAPI, Position, PosStr
from .pygments import highlight_html, highlight_latex, added_tokens, \
    resolve_token, replace_builtin_coq_lexer

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

class alectryon_pending_mref(nodes.pending):
    pass

class alectryon_pending_io(nodes.pending):
    pass

class alectryon_pending_quote(nodes.pending):
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

CACHE_COMPRESSION = None
"""Which compression to use for cache files.
See the documentation of --cache-compression."""

HTML_MINIFICATION = False
"""Whether to minify generated HTML files."""

def _node_error(document, node, msg):
    err = document.reporter.error(msg, base_node=node, line=node.line)
    errid = document.set_id(err)
    pb = nodes.problematic(node.rawsource, node.rawsource, refid=errid)
    pbid = document.set_id(pb)
    err.add_backref(pbid)
    node.replace_self(pb)

def _try(document, fn, node, *args, **kwargs):
    try:
        return fn(node, *args, **kwargs)
    except transforms.CollectedErrors as e:
        errs = e.args
    except ValueError as e:
        errs = [e]
    msg = "\n".join(map(str, errs))
    msg = "\n" + core.indent(msg, "   ") if len(errs) > 1 else  " " + msg
    msg = "In {}:{}".format(getattr(node, "text", node.rawsource), msg)
    _node_error(document, node, msg)
    return None

# LATER: dataclass
class AlectryonState:
    def __init__(self, document):
        self.generator: Optional[core.GeneratorInfo] = None
        self.root_language: Optional[str] = None
        self.transforms_executed = set()
        self.document = document
        self._config = None

    def populate_config(self):
        # Lazy because `document` isn't initialized right away, but cached
        # because constructing a ``Config`` mutates the document.
        self._config = self._config or Config(self.document)
        return self._config

    @property
    def config(self):
        return self.populate_config()

def _alectryon_state(document):
    st = getattr(document, "alectryon_state", None)
    if st is None:
        st = document.alectryon_state = AlectryonState(document)
    return st

def _gensym_stem(document, suffix=""):
    source = document.get('source', "")
    return nodes.make_id(os.path.basename(source)) + (source and suffix)

class Config:
    def __init__(self, document):
        self.tokens = {}
        self.sertop_args = []
        self.read_docinfo(document)

    def read_docinfo(self, document):
        # Sphinx doesn't translate ``field_list`` to ``docinfo``
        selector = lambda n: isinstance(n, (nodes.field_list, nodes.docinfo))
        for di in document.traverse(selector):
            for field in di.traverse(nodes.field):
                name, body = field.children
                field.text = "`:{}:`".format(name.rawsource)
                field.rawsource = ":{}: {}".format(name.rawsource, body.rawsource)
                _try(document, self.parse_docinfo_field, field, name.rawsource, body.rawsource)
        for di in document.traverse(selector):
            errors = []
            for field in di.traverse(nodes.problematic):
                errors.append(field)
                field.parent.remove(field)
            if errors:
                di.parent.insert(di.parent.index(di) + 1, errors)
            if not di.children:
                di.parent.remove(di)

    def parse_docinfo_field(self, node, name, body):
        if name.startswith("alectryon/pygments/"):
            token = name[len("alectryon/pygments/"):]
            resolve_token(token) # Check that this is a valid token
            # LATER: It would be nice to support multi-words tokens.  Using
            # ``shlex.split(body)`` instead of ``body.split()`` would work find
            # here, but the filter added by ``added_tokens`` processes words
            # (“names”) one by one, so multi-word tokens would never match.
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

class OneTimeTransform(Transform):
    def _apply(self):
        raise NotImplementedError()

    def _try(self, fn, node, *args, **kwargs):
        return _try(self.document, fn, node, *args, **kwargs)

    def apply(self, **_kwargs):
        # Transforms added by pending() nodes are added multiple times: once per
        # directive, and potentially once by add_transform in Sphinx, so we need
        # to make sure that running them twice is safe (in particular, we must
        # not overwrite the cache).
        state = _alectryon_state(self.document)
        if type(self).__name__ not in state.transforms_executed:
            state.transforms_executed.add(type(self).__name__)
            self._apply()

class LoadConfigTransform(OneTimeTransform):
    """Process ``field_list`` and ``docinfo`` configuration.

    This transform is not strictly necessary: a ``Config`` object will be
    initialized anyway when later code calls ``AlectryonState.config``.
    The point of this transform it to detect config issues at lint time.
    """
    default_priority = 300

    def _apply(self):
        _alectryon_state(self.document).populate_config()

class ActivateMathJaxTransform(Transform):
    """Add the ``mathjax_process`` class on math nodes.

    This is needed when another part of the pipeline adds mathjax_ignore on the
    root of the document to turn off MathJax's math-detection heuristics.
    """
    default_priority = 700

    @staticmethod
    def is_math(node):
        return isinstance(node, (nodes.math, nodes.math_block))

    def apply(self, **kwargs):
        for node in self.document.traverse(self.is_math):
            node.attributes.setdefault("classes", []).append("mathjax_process")

class AlectryonTransform(OneTimeTransform):
    default_priority = 800
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
            msg = "Long line ({} characters)\n   {}".format(len(s), s)
            opts = dict(line=node.line + linum) if hasattr(node, "line") else {}
            w = self.document.reporter.warning(msg, base_node=node, **opts)
            # We want a message on the command line but not in the document, so
            # remove the node created by ``Reporter.system_message``:
            self.document.transform_messages.remove(w)

    def annotate_cached(self, chunks, sertop_args):
        from .json import Cache
        metadata = {"sertop_args": sertop_args}
        cache = Cache(CACHE_DIRECTORY, self.document['source'], metadata, CACHE_COMPRESSION)
        annotated = cache.update(chunks, lambda c: annotate(c, sertop_args), SerAPI.version_info())
        return cache.generator, annotated

    def annotate(self, pending_nodes):
        config = _alectryon_state(self.document).config
        sertop_args = (*self.SERTOP_ARGS, *config.sertop_args)
        chunks = [pending.details["contents"] for pending in pending_nodes]
        return self.annotate_cached(chunks, sertop_args)

    def replace_node(self, pending, fragments):
        directive_annots = pending.details["directive_annots"]
        fragments = self.set_fragment_annots(fragments, directive_annots)
        fragments = transforms.default_transform(fragments, delay_errors=True)
        if transforms.all_hidden(fragments, directive_annots):
            pending.parent.remove(pending)
            return
        self.check_for_long_lines(pending, fragments)
        details = {**pending.details, "fragments": fragments}
        io = alectryon_pending_io(AlectryonPostTransform, details)
        self.document.note_pending(io)
        pending.replace_self(io)

    def apply_coq(self):
        pending_nodes = list(self.document.traverse(alectryon_pending))
        generator, annotated = self.annotate(pending_nodes)
        _alectryon_state(self.document).generator = generator
        for node, fragments in zip(pending_nodes, annotated):
            self._try(self.replace_node, node, fragments)

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

    def _apply(self):
        self.apply_coq()
        self.apply_toggle()

class CounterStyle(namedtuple("CounterStyle", "start digits")):
    def fmt(self, num):
        raise NotImplementedError

    @staticmethod
    def of_str(style):
        digits = tuple(style.split())
        if len(digits) < 2:
            raise ValueError("Invalid counter style: {}".format(style))
        if digits[0] == "_":
            return Alphabetic(0, digits[1:])
        return Numeric(1, digits)

class Alphabetic(CounterStyle):
    def fmt(self, num):
        s, num = "", num + 1 + self.start
        while num:
            num -= 1
            num, rem = divmod(num, len(self.digits))
            s = self.digits[rem] + s
        return s

class Numeric(CounterStyle):
    def fmt(self, num):
        s, num = "", num + self.start
        while num:
            num, rem = divmod(num, len(self.digits))
            s = self.digits[rem] + s
        return s or self.digits[0]

class RefCounter:
    def __init__(self):
        self.counters = defaultdict(lambda: -1)

    def next(self, style):
        num = self.counters[style] = self.counters[style] + 1
        return style.fmt(num)

class AlectryonMrefTransform(OneTimeTransform):
    """Convert Alectryon input/output pairs into HTML or LaTeX.

    This transform is triggered by a ``pending`` node added by
    the ``:mref:`` role.
    """
    default_priority = 810

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.refcounter = RefCounter()
        self.gensym = Gensym(_gensym_stem(self.document, "-"))

    @classmethod
    def _validate_target(cls, target):
        if not target:
            raise ValueError("Target is null")

    @classmethod
    def _find_mref_target(cls, path, ios, last_io):
        io_name = path["io"]
        io = ios.get(io_name) if io_name else last_io
        if io is None:
            if io_name:
                raise ValueError("Reference to unknown Alectryon block.")
            raise ValueError("Not sure which code block this refers to; "
                             "add ``.io#…`` to disambiguate.")

        fragments = io.details["fragments"]
        # LATER: Add a way to name sentences to make them easier to select
        sentences = (fr for fr in fragments if isinstance(fr, core.RichSentence))
        sentence = markers.find_one("sentence", markers.find_sentences, sentences, path["s"])

        if "in" in path:
            return sentence
        if "msg" in path:
            msgs = list(transforms.fragment_messages(sentence))
            return markers.find_one("message", markers.find_contents, msgs, path["msg"])
        if "g" in path:
            goals = list(transforms.fragment_goals(sentence))
            goal = markers.find_one("goal", markers.find_goals, goals, path["g"])
            if "ccl" in path:
                return goal.conclusion
            if "h" in path:
                hyps = goal.hypotheses
                hyp = markers.find_one("hypothesis", markers.find_hyps, hyps, path["h"])
                # Unfold to ensure visibility (but only if search succeeded)
                if sentence.annots.unfold is None:
                    sentence.annots.unfold = True
                goal.flags.setdefault("unfold", True)
                if "type" in path:
                    return hyp.type
                if "body" in path:
                    return hyp.body
                if "name" in path:
                    return hyp.names
                return hyp
            if "name" in path:
                return goal.name
            return goal

        return sentence

    def format_one_ref(self, target, node):
        if not target.ids:
            target_id = nodes.make_id(node.details["target"])
            target.ids.append(self.gensym(target_id + "-")) # “-” avoids collisions
        if not target.markers:
            style = node.details["counter-style"]
            target.markers.append(node.details["title"] or self.refcounter.next(style))
        marker, refid = target.markers[-1], target.ids[-1]
        return nodes.reference(node.rawsource, marker,
                               classes=["alectryon-mref"], refid=refid)

    @staticmethod
    def format_one_quote(target, node):
        if isinstance(target, core.RichSentence):
            target = target.input
        details = {**node.details, "target": target}
        return alectryon_pending_quote(
            AlectryonPostTransform, details, node.rawsource)

    def replace_one_mref(self, node, ios, last_io):
        kind, path = node.details["kind"], node.details["path"]
        target = self._find_mref_target(path, ios, last_io)
        self._validate_target(target)

        if kind == "ref":
            repl = self.format_one_ref(target, node)
        elif kind == "quote":
            repl = self.format_one_quote(target, node)
        else:
            assert False

        node.replace_self(repl)

    def _apply(self, **_kwargs):
        ios = {id: node
               for node in self.document.traverse(alectryon_pending_io)
               for id in node.get("ids", ())}
        last_io = None
        io_or_mref = lambda n: isinstance(n, (alectryon_pending_io, alectryon_pending_mref))
        for node in self.document.traverse(io_or_mref):
            if isinstance(node, alectryon_pending_io):
                last_io = node
            elif isinstance(node, alectryon_pending_mref):
                self._try(self.replace_one_mref, node, ios, last_io)

class AlectryonPostTransform(OneTimeTransform):
    """Convert Alectryon input/output pairs into HTML or LaTeX.

    This transform is triggered by a ``pending`` node added by
    ``AlectryonTransform``.  See ``docutils.components.transforms.Filter``.
    """
    default_priority = 820

    def init_generator(self):
        formats = set(self.document.transformer.components['writer'].supported)
        if 'html' in formats:
            return "html", html.HtmlGenerator(
                highlight_html, _gensym_stem(self.document), HTML_MINIFICATION)
        if {'latex', 'xelatex', 'lualatex'} & formats:
            return "latex", latex.LatexGenerator(highlight_latex)
        raise NotImplementedError("Unknown output format")

    @staticmethod
    def replace_one_io(node, fmt, generator):
        fragments, contents = node.details["fragments"], node.details["contents"]
        ids = node.attributes.get("ids", ())
        classes = node.attributes.pop("classes", ()) # visit_raw adds a <div> if it finds classes
        dom = generator.gen_fragments(fragments, ids=ids, classes=classes)
        node.replace_self(nodes.raw(contents, dom.render(pretty=False), format=fmt))

    @staticmethod
    def replace_one_quote(node, fmt, generator):
        target = transforms.strip_ids_and_flags(deepcopy(node.details["target"]))
        dom = generator.gen_inline(target)
        raw = nodes.raw(node.details["path"], dom.render(pretty=False), format=fmt)
        node.replace_self(raw)

    def _apply(self, **_kwargs):
        fmt, generator = self.init_generator()
        with added_tokens(_alectryon_state(self.document).config.tokens):
            for node in self.document.traverse(alectryon_pending_io):
                self.replace_one_io(node, fmt, generator)
            for node in self.document.traverse(alectryon_pending_quote):
                self.replace_one_quote(node, fmt, generator)


# Directives
# ----------

INDENTATION_RE = re.compile(r"^ *(?=[^\s])")
def measure_indentation(line):
    m = INDENTATION_RE.match(line)
    return m.end() - m.start() if m else None

def measure_min_indentation(lines):
    indents = (measure_indentation(l) for l in lines)
    return min((i for i in indents if i is not None), default=0)

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

    But beware: with alternative input languages like reCommonMark or MyST,
    there's no guarantee that the contents are indented by at least three
    spaces, so we must also measure the minimum indentation and respect that.
    """
    if directive.content_offset <= directive.lineno: # MyST bug
        return (0, "\n".join(directive.content))
    block_lines = directive.block_text.splitlines()
    block_header_len = directive.content_offset - directive.lineno + 1
    header_indentation = measure_indentation(directive.block_text)
    assert header_indentation is not None
    body_lines = block_lines[block_header_len:]
    min_indentation = measure_min_indentation(body_lines)
    body_indentation = min(header_indentation + real_indentation, min_indentation)
    contents = "\n".join(ln[body_indentation:] for ln in body_lines)
    return body_indentation, contents

class CoqDirective(Directive):
    """Highlight and annotate a Coq snippet."""
    name = "coq"

    required_arguments = 0
    optional_arguments = 1
    final_argument_whitespace = True
    option_spec = {'class': directives.class_option,
                   'name': directives.unchanged}
    has_content = True

    EXPECTED_INDENTATION = 3

    @property
    def header(self):
        return "`{}`".format(self.block_text.partition('\n')[0])

    def _error(self, msg):
        msg = 'Error in "{}" directive:\n{}'.format(self.name, msg)
        literal = nodes.literal_block(self.block_text, self.block_text)
        err = self.state_machine.reporter.error(msg, literal, line=self.lineno)
        return [err]

    def _annots_of_arguments(self):
        annots = transforms.IOAnnots()
        try:
            leftover = transforms.read_io_flags(annots, " ".join(self.arguments)).strip()
            if leftover:
                raise ValueError("Unrecognized directive flags: {}".format(leftover))
        except ValueError as e:
            return annots, self._error(str(e))
        return annots, []

    def run(self):
        self.assert_has_content()

        document = self.state_machine.document
        annots, errors = self._annots_of_arguments()
        indent, contents = recompute_contents(self, CoqDirective.EXPECTED_INDENTATION)
        source, line = self.state_machine.get_source_and_line(self.content_offset + 1)

        col_offset = indent
        if document.get('source', "") == source \
           and _alectryon_state(document).root_language == "coq":
            col_offset = 0

        pos = Position(source, line, col_offset)
        contents = PosStr(contents, pos, indent)

        roles.set_classes(self.options)
        details = {"directive_annots": annots, "contents": contents}
        pending = alectryon_pending(AlectryonTransform, details=details,
                                    rawsource=self.header, **self.options)

        set_line(pending, self.lineno, self.state_machine)
        self.add_name(pending)
        document.note_pending(pending)

        return [pending] + errors

class AlectryonToggleDirective(Directive):
    """Display a checkbox allowing readers to show all output at once."""
    name = "alectryon-toggle"

    required_arguments = 0
    optional_arguments = 0
    option_spec: Dict[str, Any] = {}
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

def alectryon_bubble(role, rawtext, text, lineno, inliner,
                     options: Dict[str, Any]={}, content=[]):
    node = nodes.inline(rawtext, classes=['alectryon-bubble'])
    set_line(node, lineno, inliner.reporter)
    return [node], []

alectryon_bubble.name = "alectryon-bubble" # type: ignore

def coq_code_role(role, rawtext, text, lineno, inliner,
                  options: Dict[str, Any]={}, content=[]):
    options = {**options, "language": "coq"}
    roles.set_classes(options)
    options.setdefault("classes", []).append("highlight")
    return roles.code_role(role, rawtext, text, lineno, inliner, options, content)

coq_code_role.name = "coq" # type: ignore

COQ_ID_RE = re.compile(r"^(?P<title>.*?)(?:\s*<(?P<target>.*)>)?$")
COQ_IDENT_DB_URLS = [
    ("Coq", "https://coq.inria.fr/library/$modpath.html#$ident")
]

def _role_error(inliner, rawtext, msg, lineno):
    msg = "In {}: {}".format(rawtext, msg)
    err = inliner.reporter.error(msg, line=lineno)
    return [inliner.problematic(rawtext, rawtext, err)], [err]

def _parse_ref(text):
    mid = COQ_ID_RE.match(text)
    title, target = mid.group("title"), mid.group("target")
    return title, target

def coq_id_role(role, rawtext, text, lineno, inliner,
                options: Dict[str, Any]={}, content=[]):
    title, target = _parse_ref(text)

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
            msg = "{target!r} is not a fully-qualified name.".format(target=target)
            return _role_error(inliner, rawtext, msg, lineno)

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
            return _role_error(inliner, rawtext, msg, lineno)

    from string import Template
    uri = Template(url).safe_substitute(modpath=modpath, ident=ident)

    roles.set_classes(options)
    node = nodes.reference(rawtext, title, refuri=uri, **options)
    set_line(node, lineno, inliner.reporter)

    return [node], []

coq_id_role.name = "coqid" # type: ignore
coq_id_role.options = {'url': directives.unchanged} # type: ignore

COUNTER_STYLES = {
    'decimal': '0 1 2 3 4 5 6 7 8 9',
    'lower-alpha': '_ a b c d e f g h i j k l m n o p q r s t u v w x y z',
    'upper-alpha': '_ A B C D E F G H I J K L M N O P Q R S T U V W X Y Z',
    'lower-greek': '_ α β γ δ ε ζ η θ ι κ λ μ ν ξ ο π ρ σ τ υ φ χ ψ ω',
    'upper-greek': '_ Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω',
}
DEFAULT_COUNTER_STYLE = CounterStyle.of_str(COUNTER_STYLES['decimal'])

MREF_KINDS = ['ref', 'quote']

def _parse_mref_target(kind, target, prefix):
    if target[0] in "#." or kind == "quote":
        path = markers.parse_path(target)
    else:
        path = {"s": markers.PlainMatcher(target), "str": ".s({})".format(target)}

    path = markers.merge_paths(prefix, path)
    path.setdefault("io", None)

    if "s" not in path:
        raise ValueError("Missing .s(…) sentence component in path.")
    if "ccl" in path or "h" in path:
        path.setdefault("g", markers.NameMatcher("1"))
    if kind == "ref" and "name" in path:
        raise ValueError("``.name`` is not supported in ``:mref:`` queries.")

    leaf = markers.set_leaf(path)
    if kind == "quote" and leaf not in ("msg", "h", "in", "type", "body", "name", "ccl"):
        MSG = "Cannot quote a full {} (``.{}``) inline."
        raise ValueError(MSG.format(markers.FULL_NAMES[leaf], leaf))

    return path

def _marker_ref_role(role, rawtext, text, lineno, inliner, options, content):
    kind = options.pop("kind", "ref")

    title, target = _parse_ref(text)
    if target is None:
        title, target = None, title

    if kind == "quote" and title:
        raise ValueError("Title syntax (``… <…>``) not supported with ``:mquote:``.")

    path = _parse_mref_target(kind, target, options.pop("prefix", {}))
    cs = options.pop("counter-style", None) or DEFAULT_COUNTER_STYLE
    details = {"title": title,
               "target": target,
               "path": path,
               "counter-style": cs,
               "kind": kind}

    roles.set_classes(options)
    node = alectryon_pending_mref(AlectryonMrefTransform, details, rawtext, **options)
    set_line(node, lineno, inliner.reporter)
    inliner.document.note_pending(node)
    return [node], []

def marker_ref_role(role, rawtext, text, lineno, inliner,
                    options: Dict[str, Any]={}, content=[]):
    try:
        return _marker_ref_role(
            role, rawtext, text, lineno, inliner, options, content)
    except ValueError as e:
        return _role_error(inliner, rawtext, str(e), lineno)

def _opt_mref_counter_style(arg):
    if " " not in arg:
        arg = COUNTER_STYLES[directives.choice(arg, list(COUNTER_STYLES))]
    return CounterStyle.of_str(arg)

def _opt_mref_prefix(prefix):
    try:
        return markers.parse_path(directives.unchanged_required(prefix))
    except ValueError as e:
        raise ValueError(str(e)) from e

def _opt_mref_kind(arg):
    return directives.choice(arg, list(MREF_KINDS))

marker_ref_role.name = "mref" # type: ignore
marker_ref_role.options = { # type: ignore
    'counter-style': _opt_mref_counter_style,
    'prefix': _opt_mref_prefix,
    'kind': _opt_mref_kind
}

def marker_quote_role(role, rawtext, text, lineno, inliner,
                      options: Dict[str, Any]={}, content=[]):
    options.setdefault("kind", "quote")
    return marker_ref_role(role, rawtext, text, lineno, inliner, options, content)

marker_quote_role.name = "mquote" # type: ignore
marker_quote_role.options = { # type: ignore
    'prefix': _opt_mref_prefix
}

# Error printer
# -------------

class JsErrorPrinter:
    @staticmethod
    def json_of_message(msg):
        message = msg.children[0].astext() if msg.children else "Unknown error"
        level = docutils.utils.Reporter.levels[msg['level']].lower() # type: ignore
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

class RSTCoqParser(docutils.parsers.rst.Parser): # type: ignore
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
        _alectryon_state(document).root_language = "coq"
        self.statemachine = docutils.parsers.rst.states.RSTStateMachine( # type: ignore
            state_classes=self.state_classes,
            initial_state=self.initial_state,
            debug=document.reporter.debug_flag)
        try:
            lines = RSTCoqParser.coq_input_lines(inputstring, document['source'])
            self.statemachine.run(lines, document, inliner=self.inliner)
        except ParsingError as e:
            self.report_parsing_error(e)
        roles._roles.pop('', None) # Reset the default role
        self.finish_parse()

# Writer
# ------

def register_stylesheets(translator, stylesheets, assets_path):
    for name in stylesheets:
        if translator.settings.embed_stylesheet:
            # Expand only if we're going to inline; otherwise keep relative
            name = os.path.join(assets_path, name)
        translator.stylesheet.append(translator.stylesheet_call(name))

def make_HtmlTranslator(base):
    class Translator(base):
        JS = html.ASSETS.ALECTRYON_JS
        CSS = (*html.ASSETS.ALECTRYON_CSS,
               *html.ASSETS.DOCUTILS_CSS,
               *html.ASSETS.PYGMENTS_CSS)
        ADDITIONAL_HEADS = [html.ASSETS.IBM_PLEX_CDN,
                            html.ASSETS.FIRA_CODE_CDN,
                            *html.ADDITIONAL_HEADS]

        ASSETS = JS + CSS
        ASSETS_PATH = html.ASSETS.PATH

        JS_TEMPLATE = '<script type="text/javascript" src="{}"></script>\n'
        MATHJAX_URL = \
            'https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.0/es5/tex-mml-chtml.min.js'
        mathjax_script = '<script type="text/javascript" defer src="%s"></script>\n'

        head_prefix_template = \
            '<html xmlns="http://www.w3.org/1999/xhtml" class="alectryon-standalone"' \
            ' xml:lang="%(lang)s" lang="%(lang)s">\n<head>\n'

        def __init__(self, document):
            document.settings.math_output = "MathJax " + self.MATHJAX_URL
            super().__init__(document)

            classes = [self.settings.alectryon_webpage_style]
            register_stylesheets(self, self.CSS, self.ASSETS_PATH)
            self.stylesheet.extend(self.JS_TEMPLATE.format(js) for js in self.JS)
            self.stylesheet.extend(hd + "\n" for hd in self.ADDITIONAL_HEADS)
            if HTML_MINIFICATION:
                classes.append("minified")
                self.stylesheet.extend(html.JS_UNMINIFY + "\n")

            cls = html.wrap_classes(*classes)
            self.body_prefix.append('<div class="{}">'.format(cls))

            if self.settings.alectryon_banner:
                generator = _alectryon_state(document).generator
                include_vernums = document.settings.alectryon_vernums
                self.body_prefix.append(html.gen_banner(generator, include_vernums))

            self.body_suffix.insert(0, '</div>')
    return Translator

HtmlTranslator = make_HtmlTranslator(html4css1.HTMLTranslator)
Html5Translator = make_HtmlTranslator(html5_polyglot.HTMLTranslator)

# WISH: Either remove these settings and expose global constants (like
# HTML_MINIFICATION), or add missing settings here.
ALECTRYON_SETTINGS = (
    ("Choose an Alectryon webpage style",
     ["--webpage-style"],
     {"choices": ("centered", "floating", "windowed"),
      "dest": "alectryon_webpage_style",
      "default": "centered", "metavar": "STYLE"}),
    ("Omit Alectryon's explanatory header",
     ["--no-header"],
     {'default': True, 'action': 'store_false',
      'dest': "alectryon_banner",
      'validator': docutils.frontend.validate_boolean}),
    ("Omit Alectryon's version info",
     ["--no-version-numbers"],
     {'default': True, 'action': 'store_false',
      'dest': "alectryon_vernums",
      'validator': docutils.frontend.validate_boolean})
)

def make_HtmlWriter(base, translator):
    class Writer(base):
        settings_spec = (base.settings_spec +
                         ('Alectryon HTML writer options',
                          None, ALECTRYON_SETTINGS))

        settings_default_overrides = { # By default:
            # We embed the short-classes Pygments stylesheet, not the long-classes one…
            "syntax_highlight": "short",
            # … and we want to link to Alectryon's stylesheet, not embed it
            "embed_stylesheet": False,
        }

        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.translator_class = translator
    return Writer

HtmlWriter = make_HtmlWriter(html4css1.Writer, HtmlTranslator)
Html5Writer = make_HtmlWriter(html5_polyglot.Writer, Html5Translator)

def make_LatexTranslator(base):
    class Translator(base):
        STY = latex.ASSETS.ALECTRYON_STY + latex.ASSETS.PYGMENTS_STY

        ASSETS = STY
        ASSETS_PATH = latex.ASSETS.PATH

        def __init__(self, document, *args, **kwargs):
            super().__init__(document, *args, **kwargs)
            register_stylesheets(self, self.STY, self.ASSETS_PATH)
    return Translator

LatexTranslator = make_LatexTranslator(latex2e.LaTeXTranslator)
XeLatexTranslator = make_LatexTranslator(xetex.XeLaTeXTranslator)
LuaLatexTranslator = make_LatexTranslator(xetex.XeLaTeXTranslator) # Same translator

def make_LatexWriter(base, translator_class):
    class Writer(base):
        settings_default_overrides = {
            # We want short-name Pygments macros; alectryon.sty then maps
            # \DUrole to \PY.
            "syntax_highlight": "short",
        }

        def __init__(self, *args, **kwargs):
            super().__init__(*args, **kwargs)
            self.translator_class = translator_class
    return Writer

LatexWriter = make_LatexWriter(latex2e.Writer, LatexTranslator)
XeLatexWriter = make_LatexWriter(xetex.Writer, XeLatexTranslator)
LuaLatexWriter = make_LatexWriter(xetex.Writer, LuaLatexTranslator) # Same writer

class DummyTranslator:
    ASSETS: List[str] = []

Pipeline = namedtuple("Pipeline", "parser reader translator writer")

PARSERS = {
    "coq+rst": (__name__, "RSTCoqParser"),
    "rst": ("docutils.parsers.rst", "Parser"),
    "md": ("alectryon.myst", "Parser"),
}

BACKENDS = {
    'webpage': {
        'html4': (HtmlTranslator, HtmlWriter),
        'html5': (Html5Translator, Html5Writer),
    },
    'latex': {
        'pdflatex': (LatexTranslator, LatexWriter),
        'xelatex': (XeLatexTranslator, XeLatexWriter),
        'lualatex': (LuaLatexTranslator, LuaLatexWriter),
    },
    'pseudoxml': {
        None: (DummyTranslator, ("docutils.writers.pseudoxml", "Writer")),
    }
}

# Linter
# ======

class EarlyTransformer(docutils.transforms.Transformer):
    """A transformer that only applies transforms below a certain threshold."""
    PRIORITY_THRESHOLD = "700-000"

    def apply_transforms(self):
        self.transforms = [t for t in self.transforms if t[0] < self.PRIORITY_THRESHOLD]
        super().apply_transforms()

class LintingReader(StandaloneReader):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        from io import StringIO
        self.error_stream = StringIO()

    def get_transforms(self):
        return super().get_transforms() + [LoadConfigTransform]

    def new_document(self):
        doc = super().new_document()
        doc.transformer = EarlyTransformer(doc)

        observer = JsErrorPrinter(self.error_stream, self.settings)
        doc.reporter.report_level = 0 # Report all messages
        doc.reporter.halt_level = docutils.utils.Reporter.SEVERE_LEVEL + 1 # Do not exit early
        doc.reporter.stream = False # Disable textual reporting
        doc.reporter.attach_observer(observer)

        return doc

# API
# ===

def _maybe_import(tp):
    return getattr(import_module(tp[0]), tp[1]) if isinstance(tp, tuple) else tp

def get_parser(frontend):
    if frontend not in PARSERS:
        raise ValueError("Unsupported docutils frontend: {}".format(frontend))
    return _maybe_import(PARSERS[frontend])

def get_writer(backend, dialect):
    if backend not in BACKENDS:
        raise ValueError("Unsupported docutils backend: {}".format(backend))
    if dialect not in BACKENDS[backend]:
        raise ValueError("Unsupported {} dialect: {}".format(backend, dialect))
    translator, writer = BACKENDS[backend][dialect]
    return _maybe_import(translator), _maybe_import(writer)

def get_pipeline(frontend, backend, dialect):
    parser = get_parser(frontend)
    translator, writer = get_writer(backend, dialect)
    return Pipeline(parser, StandaloneReader, translator, writer)

# Entry points
# ============

NODES = [alectryon_pending,
         alectryon_pending_toggle,
         alectryon_pending_io]
TRANSFORMS = [ActivateMathJaxTransform,
              AlectryonTransform,
              AlectryonMrefTransform,
              AlectryonPostTransform]
DIRECTIVES = [CoqDirective,
              AlectryonToggleDirective,
              ExperimentalExerciseDirective]
ROLES = [alectryon_bubble,
         coq_code_role,
         coq_id_role,
         marker_ref_role,
         marker_quote_role]

def register():
    """Tell Docutils about our roles and directives."""
    for directive in DIRECTIVES:
        directives.register_directive(directive.name, directive)
    for role in ROLES:
        roles.register_canonical_role(role.name, role)

def set_default_role():
    """Set the default role (the one used with single backticks) to :coq:."""
    roles.register_canonical_role(coq_code_role.name, coq_code_role)
    roles.DEFAULT_INTERPRETED_ROLE = coq_code_role.name # type: ignore

def setup():
    """Prepare docutils for writing Coq documents with Alectryon.

    This includes registering Alectryon's role and directives, loading an
    improved Coq highlighter, and setting the default role to ``:coq:``.
    """
    register()
    set_default_role()
    replace_builtin_coq_lexer()
