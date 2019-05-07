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
"""

from docutils.nodes import raw, Special, Invisible, Element
from docutils.parsers.rst import directives, Directive
from docutils.transforms import TransformError, Transform

from alectryon import annotate, gen_fragments_html, group_whitespace_with_code

class alectryon_pending(Special, Invisible, Element):
    def __init__(self, content):
        super().__init__()
        self.content = content

class AlectryonTransform(Transform):
    default_priority = 995

    def apply(self, **_kwargs):
        assert self.startnode is None
        nodes = list(self.document.traverse(alectryon_pending))
        chunks = [n.content for n in nodes]
        for node, fragments in zip(nodes, annotate(chunks)):
            fragments = group_whitespace_with_code(fragments)
            html = gen_fragments_html(fragments).render(pretty=False)
            node.replace_self(raw(node.content, html, format='html'))
            # FIXME handle errors

class Alectryon(Directive):
    """Highlight and annotate a Coq snippet."""

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

def register():
    directives.register_directive('coq', Alectryon)
