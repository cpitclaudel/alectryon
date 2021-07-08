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

from .core import Text, RichSentence, Messages, Goals
from . import transforms, GENERATOR

class ASSETS:
    PYGMENTS_STY = ("tango_subtle.sty",)
    ALECTRYON_STY = ("alectryon.sty",)

def format_macro(name, args, optargs):
    args = "".join("{" + str(arg) + "}" for arg in args)
    optargs = "".join("[" + str(optarg) + "]" for optarg in optargs)
    return "\\" + name + optargs + args

CONTEXT_STACK = []

## FIXME just set Verbatim to true by default, and special-case comments?

def add_top(element):
    if CONTEXT_STACK:
        CONTEXT_STACK[-1].add(element)

class Context:
    def __init__(self, name, children, args=(), optargs=(), verbatim=False):
        self.name = name
        self.args = args
        self.optargs = optargs
        self.verbatim = verbatim
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
            child = PlainText(child)
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

    def render(self, pretty=False): # pylint: disable=unused-argument
        # For compatibility with the HTML backend (dominate)
        return str(self)

    def __str__(self):
        return self.format(indent=0, verbatim=False)

class Environment(Context):
    INDENT = {}

    def __init__(self, name, *children, args=(), optargs=(), verbatim=False):
        super().__init__(name, children, args, optargs, verbatim)
        self.indent = Environment.INDENT.get(name, 2)

    def format(self, indent, verbatim):
        args = (self.name, *self.args)
        begin = format_macro("begin", args, self.optargs)
        end = format_macro("end", (self.name,), ())
        outside_indent = "" if verbatim else ' ' * indent
        verbatim = verbatim or self.verbatim
        indent = indent + self.indent
        inside_indent = ' ' * indent
        children = [c.format(indent, verbatim) for c in self.children]
        children_sep = "" if verbatim else "\n\\sep\n".replace("\n", "\n" + inside_indent)
        if children:
            return (begin + "\n" +
                    inside_indent + children_sep.join(children) + "\n" +
                    outside_indent + end)
        return begin + end

class Macro(Context):
    def __init__(self, name, *children, args=(), optargs=(), verbatim=False):
        super().__init__(name, children, args, optargs, verbatim)

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
    VERB_REPLACE = Replacements({
        " ": "~",
        "\n": "\\nl\n"})

    def __init__(self, s):
        self.s = s
        self.parent = None
        add_top(self)

    @classmethod
    def raw_format(cls, tex, indent, verbatim):
        if verbatim:
            # strip final spaces to avoid a blank line causing a \par
            tex = cls.VERB_REPLACE(tex).strip()
        return tex.replace('\n', '\n' + ' ' * indent)

    def format(self, indent, verbatim):
        return self.raw_format(self.s, indent, verbatim)

class PlainText(Raw):
    ESCAPES = Replacements({c: r"\char`\{}".format(c)
                            for c in '\\{}&^$">-<%#\'~_'})

    def format(self, indent, verbatim):
        return self.raw_format(self.ESCAPES(self.s), indent, verbatim)

class Environments:
    def __getattribute__(self, env_name):
        return lambda *args, **kwargs: Environment(env_name, *args, **kwargs)
environments = Environments()

class Macros:
    def __getattribute__(self, macro_name):
        return lambda *args, **kwargs: Macro(macro_name, *args, **kwargs)
macros = Macros()

class LatexGenerator:
    def __init__(self, highlighter):
        self.highlighter = highlighter

    def highlight(self, s):
        return [Raw(self.highlighter(s, prefix="", suffix=""))]

    def gen_goal(self, goal):
        """Serialize a goal to LaTeX."""
        with environments.goal():
            with environments.hyps():
                for hyp in goal.hypotheses:
                    names = macros.hypn(", ".join(hyp.names)) # FIXME
                    htype = self.highlight(hyp.type)
                    hbody = self.highlight(hyp.body) if hyp.body else []
                    environments.hyp(*htype, args=[names], optargs=hbody, verbatim=True)
            environments.conclusion(*self.highlight(goal.conclusion), verbatim=True)

    def gen_goals(self, first, more):
        self.gen_goal(first)
        if more:
            with environments.extragoals():
                for goal in more:
                    self.gen_goal(goal)

    @staticmethod
    def gen_whitespace(wsps):
        # Unlike in HTML, we don't need a separate wsp environment
        for wsp in wsps:
            yield PlainText(wsp)

    def gen_input(self, fr):
        contents = []
        contents.extend(self.gen_whitespace(fr.prefixes))
        contents.extend(self.highlight(fr.contents))
        # In HTML this space is hidden dynamically when the outputs are visible;
        # in LaTeX we hide it statically.  Hiding these spaces makes our lives
        # easier because we can unconditionally add a line break before output
        # blocks; otherwise we'd have to handle sentences that end the line
        # differently from sentences in the middle of a line.
        if not fr.outputs:
            contents.extend(self.gen_whitespace(fr.suffixes))
        environments.input(*contents, verbatim=True)

    def gen_output(self, fr):
        with environments.output():
            for output in fr.outputs:
                if isinstance(output, Messages):
                    assert output.messages, "transforms.commit_io_annotations"
                    with environments.messages():
                        for message in output.messages:
                            environments.message(*self.highlight(message.contents), verbatim=True)
                if isinstance(output, Goals):
                    assert output.goals, "transforms.commit_io_annotations"
                    with environments.goals():
                        self.gen_goals(output.goals[0], output.goals[1:])

    def gen_sentence(self, fr):
        with environments.sentence():
            if fr.contents is not None:
                self.gen_input(fr)
            if fr.outputs:
                self.gen_output(fr)

    def gen_fragment(self, fr):
        if isinstance(fr, Text):
            if fr.contents:
                environments.txt(*self.highlight(fr.contents), verbatim=True)
        else:
            assert isinstance(fr, RichSentence)
            self.gen_sentence(fr)

    def gen_fragments(self, fragments, _classes=()):
        """Serialize a list of `fragments` to LaTeX."""
        # FIXME: classes. optargs=[",".join(classes)] if classes else [] ?
        with environments.alectryon() as env:
            Raw("% Generator: {}".format(GENERATOR))
            # fragments = transforms.merge_fragments_by_line(fragments) # FIXME
            fragments = transforms.group_whitespace_with_code(fragments)
            fragments = transforms.commit_io_annotations(fragments)#, discard_folded=True)
            for fr in fragments:
                self.gen_fragment(fr)
            return env

    def gen(self, annotated):
        for fragments in annotated:
            yield self.gen_fragments(fragments)
