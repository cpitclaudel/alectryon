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
defined in the ``alectryon.css`` file.

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

from docutils.nodes import raw, inline, docinfo, Special, Invisible, Element, container
from docutils.parsers.rst import directives, roles, Directive
from docutils.transforms import Transform

from .core import annotate, group_whitespace_with_code, group_hypotheses, IOAnnots, process_io_annotations, find_long_lines, strip_contents
from .html import HtmlWriter
from .pygments import highlight

class alectryon_pending(Special, Invisible, Element):
    pass

class alectryon_pending_toggle(Special, Invisible, Element):
    pass

TOGGLE_HTML = """
<input type="checkbox" class="alectryon-toggle" id="alectryon-toggle-{id}" />
<label for="alectryon-toggle-{id}" class="alectryon-toggle-label">
Display all goals and responses
</label>""".replace('\n', '')

LONG_LINE_THRESHOLD = 72

class AlectryonTransform(Transform):
    default_priority = 995
    auto_toggle = True

    @staticmethod
    def set_fragment_annots(fragments, annots):
        """Apply relevant annotations to all unannotated fragments."""
        for fr in fragments:
            if hasattr(fr, 'annots'):
                fr.annots.inherit(annots)

    def check_for_long_lines(self, node, fragments):
        if LONG_LINE_THRESHOLD is None:
            return
        for line in find_long_lines(fragments, threshold=LONG_LINE_THRESHOLD):
            msg = "Long line: {!r} ({} characters)".format(line, len(line))
            self.document.reporter.warning(msg, base_node=node)
            return

    def apply_coq(self):
        writer = HtmlWriter(highlight)
        nodes = list(self.document.traverse(alectryon_pending))
        annotated = annotate(n['content'] for n in nodes)
        for node, fragments in zip(nodes, annotated):
            annots = IOAnnots(*node['options'])
            if annots.hide:
                node.parent.remove(node)
            else:
                classes = ("alectryon-floating",)
                fragments = group_hypotheses(fragments)
                fragments = process_io_annotations(fragments)
                fragments = strip_contents(fragments)
                fragments = group_whitespace_with_code(fragments)
                self.check_for_long_lines(node, fragments)
                AlectryonTransform.set_fragment_annots(fragments, annots)
                html = writer.gen_fragments_html(fragments, classes=classes).render(pretty=False)
                node.replace_self(raw(node['content'], html, format='html'))

    @staticmethod
    def split_around(node):
        parent = node.parent
        idx = node.parent.index(node)
        return parent.children[:idx], node, parent.children[idx + 1:]

    @staticmethod
    def insert_toggle_after(node, toggle, keep_node):
        before, node, after = AlectryonTransform.split_around(node)
        if keep_node:
            before.append(node)
        before.append(toggle)
        before.append(container('', *after, classes=['alectryon-container']))
        node.parent.children = before

    def apply_toggle(self):
        toggle = lambda id: raw('', TOGGLE_HTML.format(id=id), format='html')
        nodes = list(self.document.traverse(alectryon_pending_toggle))
        for idx, node in enumerate(nodes):
            self.insert_toggle_after(node, toggle(idx), False)
            self.auto_toggle = False
        if self.auto_toggle:
            p = self.document.next_node(docinfo)
            if p:
                self.insert_toggle_after(p, toggle(0), True)

    def apply(self, **_kwargs):
        assert self.startnode is None
        self.apply_coq()
        self.apply_toggle()

INDENTATION_RE = re.compile("^ *")
def measure_indentation(line):
    return INDENTATION_RE.match(line).end()

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

        document = self.state_machine.document
        if not getattr(document, 'alectryon_transform_added', False):
            document.alectryon_transform_added = True
            document.transformer.add_transform(AlectryonTransform)
        arguments = self.arguments[0].split() if self.arguments else []
        lines = recompute_contents(self, CoqDirective.EXPECTED_INDENTATION)
        return [alectryon_pending(content="\n".join(lines), options=set(arguments))]

class AlectryonToggleDirective(Directive):
    """Display a checkbox allowing readers to show all output at once."""
    name = "alectryon-toggle"

    required_arguments = 0
    optional_arguments = 0
    option_spec = {}
    has_content = False

    def run(self):
        return [alectryon_pending_toggle()]

def alectryon_bubble(# pylint: disable=dangerous-default-value
        _name, rawtext, _text, _lineno, _inliner, _options={}, _content=[]):
    return [inline(rawtext, classes=['alectryon-bubble'])], []

def register():
    """Tell Docutils about our directives (.. coq and .. alectryon-toggle).

    If `auto_toggle` is true, also register a transform to add a top-level

    You can customize the name under which these are registered by adjusting the
    ``name`` field of ``CoqDirective`` and ``AlectryonToggleDirective``.
    """
    for directive in [CoqDirective, AlectryonToggleDirective]:
        directives.register_directive(directive.name, directive)
    roles.register_canonical_role('alectryon-bubble', alectryon_bubble)
