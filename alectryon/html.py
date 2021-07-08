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
from os import path

from dominate import tags

from .core import Text, RichSentence, Goals, Messages
from . import transforms, GENERATOR

_SELF_PATH = path.dirname(path.realpath(__file__))

ADDITIONAL_HEADS = [
    '<meta name="viewport" content="width=device-width, initial-scale=1">'
]

class ASSETS:
    PATH = path.join(_SELF_PATH, "assets")

    ALECTRYON_CSS = ("alectryon.css",)
    ALECTRYON_JS = ("alectryon.js",)

    PYGMENTS_CSS = ("tango_subtle.css", "tango_subtle.min.css")
    DOCUTILS_CSS = ("docutils_basic.css",)

    IBM_PLEX_CDN = '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/IBM-type/0.5.4/css/ibm-type.min.css" integrity="sha512-sky5cf9Ts6FY1kstGOBHSybfKqdHR41M0Ldb0BjNiv3ifltoQIsg0zIaQ+wwdwgQ0w9vKFW7Js50lxH9vqNSSw==" crossorigin="anonymous" />' # pylint: disable=line-too-long
    FIRA_CODE_CDN = '<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/firacode/5.2.0/fira_code.min.css" integrity="sha512-MbysAYimH1hH2xYzkkMHB6MqxBqfP0megxsCLknbYqHVwXTCg9IqHbk+ZP/vnhO8UEW6PaXAkKe2vQ+SWACxxA==" crossorigin="anonymous" />' # pylint: disable=line-too-long

class Gensym():
    def __init__(self, stem):
        self.stem = stem
        self.counters = defaultdict(lambda: -1)

    def __call__(self, prefix):
        self.counters[prefix] += 1
        return self.stem + prefix + hex(self.counters[prefix])[len("0x"):]

# pylint: disable=line-too-long
HEADER = (
    '<div class="alectryon-banner">'
    'Built with <a href="https://github.com/cpitclaudel/alectryon/">Alectryon</a>, running {}. '
    'Bubbles (<span class="alectryon-bubble"></span>) indicate interactive fragments: hover for details, tap to reveal contents. '
    'Use <kbd>Ctrl+↑</kbd> <kbd>Ctrl+↓</kbd> to navigate, <kbd>Ctrl+🖱️</kbd> to focus. '
    'On Mac, use <kbd>⌘</kbd> instead of <kbd>Ctrl</kbd>.'
    '</div>'
)

def gen_banner(generator, include_version_info=True):
    return HEADER.format(generator.fmt(include_version_info)) if generator else ""

def wrap_classes(*cls):
    return " ".join("alectryon-" + c for c in ("root", *cls))

class HtmlGenerator:
    def __init__(self, highlighter, gensym_stem=""):
        self.highlight = highlighter
        self.gensym = Gensym(gensym_stem + "-" if gensym_stem else "")

    @staticmethod
    def gen_label(toggle, cls, *contents):
        if toggle:
            return tags.label(*contents, cls=cls, **{"for": toggle})
        return tags.span(*contents, cls=cls)

    def gen_hyps(self, hyps):
        with tags.div(cls="goal-hyps"):
            for hyp in hyps:
                with tags.div(cls="goal-hyp"):
                    tags.span(", ".join(hyp.names), cls="hyp-names")
                    with tags.span():
                        if hyp.body:
                            with tags.span(cls="hyp-body-block"):
                                tags.span(":=", cls="hyp-punct")
                                with tags.span(cls="hyp-body"):
                                    self.highlight(hyp.body)
                        with tags.span(cls="hyp-type-block"):
                            tags.span(":", cls="hyp-punct")
                            with tags.span(cls="hyp-type"):
                                self.highlight(hyp.type)

    def gen_goal(self, goal, toggle=None):
        """Serialize a goal to HTML."""
        with tags.blockquote(cls="alectryon-goal"):
            if goal.hypotheses:
                # Chrome doesn't support the ‘gap’ property in flex containers,
                # so properly spacing hypotheses requires giving them margins
                # and giving negative margins to their container.  This breaks
                # when the container is empty, so just omit the hypotheses if
                # there are none.
                self.gen_hyps(goal.hypotheses)
            toggle = goal.hypotheses and toggle
            cls = "goal-separator" + (" alectryon-extra-goal-label" if toggle else "")
            with self.gen_label(toggle, cls):
                tags.hr()
                if goal.name:
                    tags.span(goal.name, cls="goal-name")
            tags.div(self.highlight(goal.conclusion), cls="goal-conclusion")

    def gen_checkbox(self, checked, cls):
        nm = self.gensym("chk")
        attrs = {"style": "display: none"} # Most RSS readers ignore stylesheets
        if checked:
            attrs["checked"] = "checked"
        tags.input_(type="checkbox", id=nm, cls=cls, **attrs)
        return nm

    def gen_goals(self, first, more):
        self.gen_goal(first)
        if more:
            with tags.div(cls='alectryon-extra-goals'):
                for goal in more:
                    nm = self.gen_checkbox(False, "alectryon-extra-goal-toggle")
                    self.gen_goal(goal, toggle=nm)

    def gen_input_toggle(self, fr):
        if not fr.outputs:
            return None
        return self.gen_checkbox(fr.annots.unfold, "alectryon-toggle")

    def gen_input(self, fr, toggle):
        cls = "alectryon-input" + (" alectryon-failed" if fr.annots.fails else "")
        self.gen_label(toggle, cls, self.highlight(fr.contents))

    def gen_output(self, fr):
        # Using <small> improves rendering in RSS feeds
        wrapper = tags.div(cls="alectryon-output-sticky-wrapper")
        with tags.small(cls="alectryon-output").add(wrapper):
            for output in fr.outputs:
                if isinstance(output, Messages):
                    assert output.messages, "transforms.commit_io_annotations"
                    with tags.div(cls="alectryon-messages"):
                        for message in output.messages:
                            tags.blockquote(self.highlight(message.contents),
                                            cls="alectryon-message")
                if isinstance(output, Goals):
                    assert output.goals, "transforms.commit_io_annotations"
                    with tags.div(cls="alectryon-goals"):
                        self.gen_goals(output.goals[0], output.goals[1:])

    @staticmethod
    def gen_whitespace(wsps):
        for wsp in wsps:
            tags.span(wsp, cls="alectryon-wsp")

    def gen_sentence(self, fr):
        if fr.contents is not None:
            self.gen_whitespace(fr.prefixes)
        with tags.span(cls="alectryon-sentence"):
            toggle = self.gen_input_toggle(fr)
            if fr.contents is not None:
                self.gen_input(fr, toggle)
            if fr.outputs:
                self.gen_output(fr)
            if fr.contents is not None:
                self.gen_whitespace(fr.suffixes)

    def gen_fragment(self, fr):
        if isinstance(fr, Text):
            tags.span(self.highlight(fr.contents), cls="alectryon-wsp")
        else:
            assert isinstance(fr, RichSentence)
            self.gen_sentence(fr)

    def gen_fragments(self, fragments, classes=()):
        """Serialize a list of `fragments` to HTML."""
        with tags.pre(cls=" ".join(("alectryon-io", *classes))) as pre:
            tags.comment(" Generator: {} ".format(GENERATOR))
            fragments = transforms.group_whitespace_with_code(fragments)
            fragments = transforms.commit_io_annotations(fragments)
            for fr in fragments:
                self.gen_fragment(fr)
            return pre

    def gen(self, annotated):
        for fragments in annotated:
            yield self.gen_fragments(fragments)
