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
from dominate import tags
from dominate.util import raw

from .core import GENERATOR, CoqText, HTMLSentence
from . import transforms

class Gensym():
    def __init__(self):
        self.counters = defaultdict(lambda: -1)

    def next(self, prefix):
        self.counters[prefix] += 1
        return hex(self.counters[prefix]).replace("0x", prefix)

HEADER = (
    '<div class="alectryon-header">'
    'Built with <a href="https://github.com/cpitclaudel/alectryon/">Alectryon</a>, running <a href="https://coq.inria.fr/">Coq</a>+<a href="https://github.com/ejgallego/coq-serapi">SerAPI</a> v{}. '
    'Coq sources are in this panel; goals and messages will appear in the other. '
    'Bubbles (<span class="alectryon-bubble"></span>) indicate interactive fragments: hover for details, tap to reveal contents. '
    'Use <kbd>⇞</kbd> <kbd>⇟</kbd> or <kbd>Ctrl+↑</kbd> <kbd>Ctrl+↓</kbd> to navigate, <kbd>Ctrl+🖱️</kbd> to focus.'
    '</div>'
)

def gen_header(version):
    return raw(HEADER.format(version))

class HtmlWriter():
    def __init__(self, highlighter):
        self.highlight = highlighter
        self.gensym = Gensym()

    def gen_goal_html(self, goal):
        """Serialize a goal to HTML."""
        with tags.span(cls="coq-goal"):
            with tags.span(cls="goal-hyps"):
                for hyp in goal.hypotheses:
                    with tags.span(cls="goal-hyp"):
                        tags.span(", ".join(hyp.names), cls="hyp-names")
                        with tags.span():
                            if hyp.body:
                                with tags.span(cls="hyp-body"):
                                    tags.span(":=", cls="hyp-punct")
                                    self.highlight(hyp.body)
                            with tags.span(cls="hyp-type"):
                                tags.span(":", cls="hyp-punct")
                                self.highlight(hyp.type)
            with tags.span(cls="goal-separator"):
                tags.hr()
                if goal.name:
                    tags.span(goal.name, cls="goal-name")
            tags.span(self.highlight(goal.conclusion), cls="goal-conclusion")

    def gen_goals_html(self, first, more):
        self.gen_goal_html(first)
        if more:
            nm = self.gensym.next("chk")
            tags.input(type="checkbox", id=nm, cls="coq-extra-goals-toggle")
            lbl = "{} more goal{}".format(len(more), "s" * (len(more) > 1))
            tags.label(lbl, cls="coq-extra-goals-label", **{'for': nm})
            with tags.div(cls='coq-extra-goals'):
                for goal in more:
                    self.gen_goal_html(goal)

    def gen_input_html(self, fr):
        attrs, tag = {}, tags.span
        # print(repr(fr.contents), fr.annots.__dict__,
        #       fr.annots['in'], fr.annots['goals'], fr.annots['messages'])
        if fr.goals or fr.responses:
            tag = tags.label
            nm = attrs['for'] = self.gensym.next("chk")
            chk = { "checked": "checked" } if fr.annots.unfold else dict()
            tags.input(type="checkbox", id=nm, cls="coq-toggle", **chk)
        if fr.annots['in']:
            tag(self.highlight(fr.contents), cls="coq-input", **attrs)

    def gen_output_html(self, fr):
        id = self.gensym.next("goal")
        wrapper = tags.div(cls="coq-output-sticky-wrapper")
        with tags.span(cls="coq-output", id=id).add(wrapper):
            if fr.responses:
                with tags.span(cls="coq-responses"):
                    for response in fr.responses:
                        tags.span(self.highlight(response), cls="coq-response")
            if fr.goals:
                with tags.span(cls="coq-goals"):
                    self.gen_goals_html(fr.goals[0], fr.goals[1:])

    @staticmethod
    def gen_whitespace(wsps):
        for wsp in wsps:
            tags.span(wsp, cls="coq-wsp")

    def gen_sentence_html(self, fr):
        if fr.annots.hide:
            return

        responses = fr.annots['messages'] and fr.responses
        goals = fr.annots['goals'] and fr.goals
        fr = fr._replace(responses=responses, goals=goals)

        if fr.annots['in']:
            self.gen_whitespace(fr.prefixes)
        with tags.span(cls="coq-sentence"):
            self.gen_input_html(fr)
            if fr.responses or fr.goals:
                if not fr.annots['in'] and not fr.annots.unfold:
                    MSG = "Cannot show output of {!r} without .in or .unfold."
                    raise ValueError(MSG.format(fr.contents))
                self.gen_output_html(fr)
            if fr.annots['in']:
                self.gen_whitespace(fr.suffixes)

    def gen_fragments_html(self, fragments, classes=()):
        """Serialize a list of `fragments` to HTML."""
        with tags.pre(cls=" ".join(("alectryon-io", *classes))) as div:
            tags.comment(" Generator: {} ".format(GENERATOR))
            for fr in transforms.htmlify_sentences(fragments):
                if isinstance(fr, CoqText):
                    tags.span(self.highlight(fr.contents), cls="coq-nc")
                else:
                    assert isinstance(fr, HTMLSentence)
                    self.gen_sentence_html(fr)
            return div

    def gen_html(self, annotated):
        for idx, fragments in enumerate(annotated):
            if idx > 0:
                yield tags.comment(" alectryon-block-end ")
            fragments = transforms.group_whitespace_with_code(fragments)
            yield self.gen_fragments_html(fragments)
