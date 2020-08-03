# Copyright © 2020 Clément Pit-Claudel
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

import re
import textwrap

from .core import CoqText, RichSentence, CoqMessages, CoqGoals
from . import transforms, __version__, GENERATOR

def format_macro(name, args, optargs):
    args = "".join("{" + str(arg) + "}" for arg in args)
    optargs = "".join("[" + str(optarg) + "]" for optarg in optargs)
    return "\\" + name + optargs + args

CONTEXT_STACK = []

def add_top(element):
    if CONTEXT_STACK:
        CONTEXT_STACK[-1].add(element)

class Context:
    def __init__(self, name, children, args=(), optargs=(), verbatim=False):
        self.name = name
        self.args = args
        self.optargs = optargs
        self.verbatim=verbatim
        self.children = []
        add_top(self)
        for c in children:
            self.add(c)
        self.claim(*args, *optargs)

    def claim(self, *children):
        for child in children:
            child.parent = self

    def add(self, child):
        if isinstance(child, str):
            child = Text(child)
        self.children.append(child)
        self.claim(child)

    def __enter__(self):
        CONTEXT_STACK.append(self)
        return self

    def __exit__(self, *_):
        CONTEXT_STACK.pop()
        self.children = [c for c in self.children if c.parent is self]

    def format(self, indent, verbatim):
        raise NotImplementedError()

    def __str__(self):
        return self.format(indent=0, verbatim=False)

class Environment(Context):
    INDENT = {} # FIXME separator should be a Text element, not plain, so verbatim would work on it
    CHILDREN_SEPARATOR = {
        "coqHyps": "\n\\coqHypSep{}\n",
        "coqOutput": "\n\\coqOutputSep{}\n",
    }

    def __init__(self, name, *children, args=(), optargs=(), verbatim=False):
        super().__init__(name, children, args, optargs, verbatim)
        self.indent = Environment.INDENT.get(name, 2)
        self.children_sep = Environment.CHILDREN_SEPARATOR.get(name, "\n")

    def format(self, indent, verbatim):
        args = (self.name, *self.args)
        begin = format_macro("begin", args, self.optargs)
        end = format_macro("end", (self.name,), ())
        outside_indent = "" if verbatim else ' ' * indent
        verbatim = verbatim or self.verbatim
        indent = indent + self.indent
        inside_indent = "" if verbatim else ' ' * indent
        children = [c.format(indent, verbatim) for c in self.children]
        if verbatim:
            children_sep = Raw.VERB_REPLACE(self.children_sep)
        else:
            children_sep = self.children_sep.replace("\n", "\n" + inside_indent)
        if children:
            return (begin +
               ("" if self.verbatim else "\n" + inside_indent) +
               children_sep.join(children) +
               ("" if self.verbatim else "\n" + outside_indent) +
               end)
        return begin + end

class Macro(Context):
    CHILDREN_SEPARATOR = {}

    def __init__(self, name, *children, args=(), optargs=(), verbatim=False):
        super().__init__(name, children, args, optargs, verbatim)
        self.children_sep = Macro.CHILDREN_SEPARATOR.get(name, "")

    def format(self, indent, verbatim):
        children = "".join(c.format(indent, self.verbatim or verbatim) for c in self.children)
        return format_macro(self.name, (*self.args, children), self.optargs)

class Replacements:
    def __init__(self, replacements):
        self.replacements = replacements
        keys = (re.escape(src) for src in replacements.keys())
        self.regexp = re.compile("|".join("(?:{})".format(k) for k in keys))

    def replace_one(self, m):
        return self.replacements[m.group()]

    def __call__(self, s):
        return self.regexp.sub(self.replace_one, s)

class Raw:
    VERB_REPLACE = Replacements({" ": "~", "\n": "\n\\coqNl{}"})

    def __init__(self, s):
        self.s = s
        self.parent = None
        add_top(self)

    def format(self, indent, verbatim):
        return self.VERB_REPLACE(self.s) if verbatim else self.s

class Text(Raw):
    ESCAPES = Replacements({"\\": "\\textbackslash"}) # FIXME

    def format(self, indent, verbatim):
        quoted = self.ESCAPES(self.s)
        if verbatim:
            return self.VERB_REPLACE(quoted)
        return textwrap.indent(quoted, ' ' * indent)

class environments:
    def __getattribute__(self, env_name):
        return lambda *args, **kwargs: Environment(env_name, *args, **kwargs)
environments = environments()

class macros:
    def __getattribute__(self, macro_name):
        return lambda *args, **kwargs: Macro(macro_name, *args, **kwargs)
macros = macros()

class LatexGenerator:
    def __init__(self, highlighter):
        self.highlight = lambda s: [Raw(highlighter(s, open="", close=""))]

    def gen_goal(self, goal):
        """Serialize a goal to HTML."""
        with environments.coqGoal():
            with environments.coqHyps():
                for hyp in goal.hypotheses:
                    names = macros.coqHypNames(", ".join(hyp.names))
                    htype = self.highlight(hyp.type)
                    hbody = self.highlight(hyp.body) if hyp.body else []
                    environments.coqHyp(*htype, args=[names], optargs=hbody, verbatim=True)
            environments.coqConclusion(*self.highlight(goal.conclusion), verbatim=True)

    def gen_goals(self, first, more):
        self.gen_goal(first)
        if more:
            with environments.coqExtraGoals():
                for goal in more:
                    self.gen_goal(goal)

    def gen_input(self, fr):
        environments.coqInput(*self.highlight(fr.contents), verbatim=True)

    def gen_output(self, fr):
        with environments.coqOuput():
            for output in fr.outputs:
                if isinstance(output, CoqMessages):
                    assert output.messages, "transforms.commit_io_annotations"
                    with environments.coqMessages():
                        for message in output.messages:
                            environments.coqMessage(*self.highlight(message.contents), verbatim=True)
                if isinstance(output, CoqGoals):
                    assert output.goals, "transforms.commit_io_annotations"
                    with environments.coqGoals():
                        self.gen_goals(output.goals[0], output.goals[1:])

    @staticmethod
    def gen_whitespace(wsps):
        for wsp in wsps:
            macros.coqWsp(wsp, verbatim=True)

    def gen_sentence(self, fr):
        if fr.contents is not None:
            self.gen_whitespace(fr.prefixes)
        with environments.coqSentence():
            if fr.contents is not None:
                self.gen_input(fr)
            if fr.outputs:
                self.gen_output(fr)
            if fr.contents is not None:
                self.gen_whitespace(fr.suffixes)

    def gen_fragment(self, fr):
        if isinstance(fr, CoqText):
            macros.coqWsp(*self.highlight(fr.contents), verbatim=True)
        else:
            assert isinstance(fr, RichSentence)
            self.gen_sentence(fr)

    def gen_fragments(self, fragments, classes=()):
        """Serialize a list of `fragments` to LaTeX."""
        with environments.alectryonIo(optargs=[",".join(classes)] if classes else []) as env:
            Raw("% Generator: {}".format(GENERATOR))
            fragments = transforms.group_whitespace_with_code(fragments)
            fragments = transforms.commit_io_annotations(fragments)
            for fr in fragments:
                self.gen_fragment(fr)
            return env

    def gen(self, annotated):
        for fragments in annotated:
            yield self.gen_fragments(fragments)
