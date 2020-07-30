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

from collections import defaultdict
from os import path, unlink
import shutil

from dominate import tags

from .core import CoqText, HTMLSentence
from . import transforms, __version__

GENERATOR = "Alectryon v{}".format(__version__)

_SELF_PATH = path.dirname(path.realpath(__file__))

class ASSETS:
    PATH = path.join(path.dirname(_SELF_PATH), "assets")

    ALECTRYON_CSS = ("alectryon.css",)
    ALECTRYON_JS = ("alectryon.js",)

    PYGMENTS_CSS = ("tango_subtle.css", "tango_subtle.min.css")
    DOCUTILS_CSS = ("docutils_basic.css",)

def copy_assets(output_directory,
                assets=ASSETS.ALECTRYON_CSS + ASSETS.ALECTRYON_JS,
                copy_fn=shutil.copy):
    for name in assets:
        src = path.join(ASSETS.PATH, name)
        dst = path.join(output_directory, name)
        if copy_fn is not shutil.copy:
            try:
                unlink(dst)
            except FileNotFoundError:
                pass
        try:
            copy_fn(src, dst)
        except shutil.SameFileError:
            pass

class Gensym():
    def __init__(self, stem):
        self.stem = stem
        self.counters = defaultdict(lambda: -1)

    def __call__(self, prefix):
        self.counters[prefix] += 1
        return self.stem + prefix + hex(self.counters[prefix])[len("0x"):]

HEADER = (
    '<div class="alectryon-header">'
    'Built with <a href="https://github.com/cpitclaudel/alectryon/">Alectryon</a>, running <a href="https://coq.inria.fr/">Coq</a>+<a href="https://github.com/ejgallego/coq-serapi">SerAPI</a> v{}. '
    'Coq sources are in this panel; goals and messages will appear in the other. '
    'Bubbles (<span class="alectryon-bubble"></span>) indicate interactive fragments: hover for details, tap to reveal contents. '
    'Use <kbd>Ctrl+↑</kbd> <kbd>Ctrl+↓</kbd> to navigate, <kbd>Ctrl+🖱️</kbd> to focus.'
    '</div>'
)

def gen_header(version):
    return HEADER.format(version)

def wrap_classes(*cls):
    return " ".join("alectryon-" + c for c in ("root", *cls))

class HtmlGenerator:
    def __init__(self, highlighter, gensym_stem=""):
        self.highlight = highlighter
        self.gensym = Gensym(gensym_stem + "-" if gensym_stem else "")

    def gen_hyps(self, hyps):
        with tags.div(cls="goal-hyps"):
            for hyp in hyps:
                with tags.div(cls="goal-hyp"):
                    tags.span(", ".join(hyp.names), cls="hyp-names")
                    with tags.span():
                        if hyp.body:
                            with tags.span(cls="hyp-body"):
                                tags.span(":=", cls="hyp-punct")
                                self.highlight(hyp.body)
                        with tags.span(cls="hyp-type"):
                            tags.span(":", cls="hyp-punct")
                            self.highlight(hyp.type)

    def gen_goal(self, goal, toggle=None):
        """Serialize a goal to HTML."""
        with tags.blockquote(cls="coq-goal"):
            if goal.hypotheses:
                # Chrome doesn't support the ‘gap’ property in flex containers,
                # so properly spacing hypotheses requires giving them margins
                # and giving negative margins to their container.  This breaks
                # when the container is empty, so just omit the hypotheses if
                # there are none.
                self.gen_hyps(goal.hypotheses)
            sep_attrs = {"cls": "goal-separator"}
            if toggle and goal.hypotheses:
                sep_attrs["for"] = toggle
                sep_attrs["cls"] += " coq-extra-goal-label"
            with tags.label(**sep_attrs):
                tags.hr()
                if goal.name:
                    tags.span(goal.name, cls="goal-name")
            tags.div(self.highlight(goal.conclusion), cls="goal-conclusion")

    def gen_checkbox(self, checked, cls):
        nm = self.gensym("chk")
        attrs = {"style": "display: none"} # Most RSS readers ignore stylesheets
        if checked:
            attrs["checked"] = "checked"
        tags.input(type="checkbox", id=nm, cls=cls, **attrs)
        return nm

    def gen_goals(self, first, more):
        self.gen_goal(first)
        if more:
            with tags.div(cls='coq-extra-goals'):
                for goal in more:
                    nm = self.gen_checkbox(False, "coq-extra-goal-toggle")
                    self.gen_goal(goal, toggle=nm)

    def gen_input_toggle(self, fr):
        if not (fr.goals or fr.responses):
            return None
        return self.gen_checkbox(fr.annots.unfold, "coq-toggle")

    def gen_input(self, fr, toggle):
        cls = {"cls": "coq-input" + (" alectryon-failed" if fr.annots.fails else "")}
        contents = self.highlight(fr.contents)
        if toggle:
            tags.label(contents, **cls, **{"for": toggle})
        else:
            tags.span(contents, **cls)

    def gen_output(self, fr):
        # Using <small> improves rendering in RSS feeds
        wrapper = tags.div(cls="coq-output-sticky-wrapper")
        with tags.small(cls="coq-output").add(wrapper):
            if fr.responses:
                with tags.div(cls="coq-responses"):
                    for response in fr.responses:
                        tags.blockquote(self.highlight(response), cls="coq-response")
            if fr.goals:
                with tags.div(cls="coq-goals"):
                    self.gen_goals(fr.goals[0], fr.goals[1:])

    @staticmethod
    def gen_whitespace(wsps):
        for wsp in wsps:
            tags.span(wsp, cls="coq-wsp")

    def gen_sentence(self, fr):
        if fr.annots.hide:
            return

        responses = fr.annots['messages'] and fr.responses
        goals = fr.annots['goals'] and fr.goals
        fr = fr._replace(responses=responses, goals=goals)

        if fr.annots['in']:
            self.gen_whitespace(fr.prefixes)
        with tags.span(cls="coq-sentence"):
            toggle = self.gen_input_toggle(fr)
            if fr.annots['in']:
                self.gen_input(fr, toggle)
            if fr.responses or fr.goals:
                if not fr.annots['in'] and not fr.annots.unfold:
                    MSG = "Cannot show output of {!r} without .in or .unfold."
                    raise ValueError(MSG.format(fr.contents))
                self.gen_output(fr)
            if fr.annots['in']:
                self.gen_whitespace(fr.suffixes)

    def gen_fragment(self, fr):
        if isinstance(fr, CoqText):
            tags.span(self.highlight(fr.contents), cls="coq-nc")
        else:
            assert isinstance(fr, HTMLSentence)
            self.gen_sentence(fr)

    def gen_fragments(self, fragments, classes=()):
        """Serialize a list of `fragments` to HTML."""
        with tags.pre(cls=" ".join(("alectryon-io", *classes))) as div:
            tags.comment(" Generator: {} ".format(GENERATOR))
            for fr in transforms.group_whitespace_with_code(fragments):
                self.gen_fragment(fr)
            return div

    def gen(self, annotated):
        for fragments in annotated:
            yield self.gen_fragments(fragments)
