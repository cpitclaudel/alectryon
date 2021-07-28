=======================
 Coq directive options
=======================

.. raw:: latex

   \let\oldalltt\alltt
   \def\alltt{\oldalltt\scriptsize}

This file checks that ``:class:`` and ``:name:`` attributes work on ``.. coq::`` directives::

   alectryon directive-options.rst
     # reST → Coq; produces ‘directive-options.html’
   alectryon directive-options.rst --latex-dialect xelatex -o directive-options.xe.tex
     # reST → LaTeX; produces ‘directive-options.xe.tex’

.. coq:: none

   From Coq Require Import String.
   Open Scope string_scope.

.. raw:: html

   <style type="text/css">.upside-down { transform: rotate(180deg) } #test { border: solid; } </style>

.. coq::
   :class: upside-down
   :name: test

   Definition test := " =: ʇsǝʇ uoıʇıuıɟǝᗡ".

Link to `first Coq fragment <test_>`__.
