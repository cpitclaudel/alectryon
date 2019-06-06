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

from dominate import tags

from .core import GENERATOR, CoqText, CoqSentence, HTMLSentence, group_whitespace_with_code

class Gensym():
    def __init__(self):
        self.counter = -1

    def next(self, prefix):
        self.counter += 1
        return hex(self.counter).replace("0x", prefix)

class HtmlWriter():
    def __init__(self, highlighter):
        self.highlight = highlighter
        self.gensym = Gensym()

    def gen_goal_html(self, goal):
        """Serialize a goal to HTML."""
        with tags.span(cls="coq-goal"):
            if goal.name:
                tags.span(goal.name, cls="goal-name")
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
            tags.span(cls="goal-separator")
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
        sentence, cls = self.highlight(fr.sentence), "coq-input"
        if fr.goals or fr.responses:
            nm = self.gensym.next("chk")
            tags.input(type="checkbox", id=nm, cls="coq-toggle")
            tags.label(sentence, cls=cls, **{'for': nm})
        else:
            tags.span(sentence, cls=cls)

    def gen_output_html(self, fr):
        wrapper = tags.div(cls="coq-output-sticky-wrapper")
        with tags.span(cls="coq-output").add(wrapper):
            if fr.responses:
                with tags.span(cls="coq-responses"):
                    for response in fr.responses:
                        tags.span(self.highlight(response), cls="coq-response")
            if fr.goals:
                with tags.span(cls="coq-goals"):
                    self.gen_goals_html(fr.goals[0], fr.goals[1:])

    def gen_sentence_html(self, fr):
        with tags.span(cls="coq-fragment"):
            self.gen_input_html(fr)
            if fr.responses or fr.goals:
                self.gen_output_html(fr)
            for wsp in getattr(fr, 'wsp', ()):
                tags.span(wsp.string, cls="coq-wsp")

    def gen_fragments_html(self, fragments):
        """Serialize a list of `fragments` to HTML."""
        with tags.pre(cls="alectryon-io") as div:
            tags.comment(" Generator: {} ".format(GENERATOR))
            for fr in fragments:
                if isinstance(fr, CoqText):
                    tags.span(self.highlight(fr.string), cls="coq-nc")
                else:
                    assert isinstance(fr, (CoqSentence, HTMLSentence))
                    self.gen_sentence_html(fr)
            return div

    def gen_html(self, annotated):
        for idx, fragments in enumerate(annotated):
            if idx > 0:
                yield tags.comment(" alectryon-block-end ")
            yield self.gen_fragments_html(group_whitespace_with_code(fragments))
