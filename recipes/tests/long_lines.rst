============
 Long lines
============

To compile::

   alectryon long_lines.rst -o /dev/null --long-line-threshold=18 2> long_lines.txt
     # Long lines; produces ‘long_lines.txt’

.. coq::

   Check nat.
   Definition over_seventeen := 1.
   Definition very_very_long_name := 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
