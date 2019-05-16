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

To use it, call ``docutils_support.register()`` before running your
reStructuredText to HTML converter.  The generated code relies on CSS classes
defined in the ``alectryon.css`` file.

A checkbox and an accompanying label (with classes ``alectryon-toggle`` and
``alectryon-toggle-label``) allowing users to reveal all goals and responses at
once is automatically added right before the document's first paragraph.  You
can change its location by inserting an explicit ``.. alectryon-toggle::``
directive in your document, and you can ommit it entirely by setting
``AlectryonTransform.insert_toggle`` to ``False``.
"""

from docutils.nodes import raw, docinfo, Special, Invisible, Element
from docutils.parsers.rst import directives, Directive
from docutils.transforms import Transform

from .core import annotate, group_whitespace_with_code
from .html import HtmlWriter
from .pygments import highlight

class alectryon_pending(Special, Invisible, Element):
    def __init__(self, content):
        super().__init__()
        self.content = content

class alectryon_pending_toggle(Special, Invisible, Element):
    pass

TOGGLE_HTML = """
<input type="checkbox" class="alectryon-toggle" id="alectryon-toggle-{id}" />
<label for="alectryon-toggle-{id}" class="alectryon-toggle-label">
Display all goals and responses
</label>""".replace('\n', '')

class AlectryonTransform(Transform):
    default_priority = 995
    auto_toggle = True

    def apply_coq(self):
        writer = HtmlWriter(highlight)
        nodes = list(self.document.traverse(alectryon_pending))
        chunks = [n.content for n in nodes]
        for node, fragments in zip(nodes, annotate(chunks)):
            fragments = group_whitespace_with_code(fragments)
            html = writer.gen_fragments_html(fragments).render(pretty=False)
            node.replace_self(raw(node.content, html, format='html'))

    def apply_toggle(self):
        toggle = lambda id: raw('', TOGGLE_HTML.format(id=id), format='html')
        nodes = self.document.traverse(alectryon_pending_toggle)
        for idx, node in enumerate(nodes):
            node.replace_self(toggle(idx))
            self.auto_toggle = False
        if self.auto_toggle:
            p = self.document.next_node(docinfo)
            if p:
                p.parent.insert(p.parent.index(p) + 1, toggle(0))

    def apply(self, **_kwargs):
        assert self.startnode is None
        self.apply_coq()
        self.apply_toggle()

class Alectryon(Directive):
    """Highlight and annotate a Coq snippet."""
    name = "coq"

    required_arguments = 0
    optional_arguments = 0
    final_argument_whitespace = True
    option_spec = {}
    has_content = True

    def run(self):
        self.assert_has_content()

        document = self.state_machine.document
        if not getattr(document, 'alectryon_transform_added', False):
            document.alectryon_transform_added = True
            document.transformer.add_transform(AlectryonTransform)

        content = '\n'.join(self.content)
        return [alectryon_pending(content)]

class AlectryonToggle(Directive):
    """Display a checkbox allowing readers to show all output at once."""
    name = "alectryon-toggle"

    required_arguments = 0
    optional_arguments = 0
    option_spec = {}
    has_content = False

    def run(self):
        return [alectryon_pending_toggle()]

def register():
    """Tell Docutils about our directives (.. coq and .. alectryon-toggle).

    If `auto_toggle` is true, also register a transform to add a top-level

    You can customize the name under which these are registered by adjusting the
    ``name`` field of ``Alectryon`` and ``AlectryonToggle``.
    """
    for directive in [Alectryon, AlectryonToggle]:
        directives.register_directive(directive.name, directive)
