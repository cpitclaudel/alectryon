=============================
 Compiling without Alectryon
=============================

Coq files can always be compiled without Alectryon.  reST files are tricker, since they have ``..coq ::`` directives.  The repository contains a standalone compiler that treats these directives as code blocks and includes no-op definitions for Alectryon-specific roles::

   alectryon minimal.rst # reST → HTML; produces ‘minimal.html’

   $ cd ..; python -m alectryon.minimal recipes/minimal.rst recipes/minimal.no-alectryon.html
   # Minimal reST → HTML; produces ‘minimal.no-alectryon.html’

Directives
==========

Coq code:
  .. coq::

     Print nat. (* .unfold *)

.. alectryon-toggle::

Quotes:
  .. mquote:: .s(Print).in

Assertions:
  .. massert::

     .s(Print).msg{*nat*}

.. exercise:: Title
   :difficulty: 1

   Body

Roles
=====

- :alectryon-bubble:`-`
- :coq:`fun x => x + 1`
- :coqid:`Coq.Even.even`
- :mref:`.s(Print).msg{*nat*}`
- :mquote:`.s(Print).msg{*nat*}`
