=========================
 References corner-cases
=========================

To compile::

   alectryon references.rst # reST → HTML; produces ‘references.html’

reST normalizes block names, so `.io` references need to be normalized too:

.. coq::
   :name: Named_Block

   Print eq.

- :mquote:`.io#NAMED_BLOCK.s(Print).in`.
- :mquote:`.io#named_block.s(Print).msg`.
