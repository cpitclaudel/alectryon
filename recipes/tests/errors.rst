=====================
 Errors and warnings
=====================

:alectryon/pygments/xyz: test

To compile::

   alectryon errors.rst --backend lint
     # reST → JSON errors; produces ‘errors.lint.json’
   alectryon errors.rst --copy-assets none --backend webpage -o /dev/null 2> errors.txt
     # reST → HTML + errors; produces ‘errors.txt’

.. coq::

   Goal True.
     exact I. (* A very long line *) (* whose contents are split *) (* across *) (* multiple *) (* comments *)
   Qed.

Markup
======

A reST error: *here.

Roles
=====

``coqid``
---------

Not fully qualified:
  - :coqid:`A`

Not registered:
  - :coqid:`Lib.A`

``mref``, ``mquote``
--------------------

Bad syntax:
  - :mref:`...`
  - :mref:`.io`
  - :mref:`.abc`
  - :mref:`.s()`
  - :mref:`.s.g`
  - :mref:`.io{*}.g`
  - :mref:`.s[a-z]`
  - :mref:`.s(abc)[a-z]`

Bad targets (static):
  - :mref:`.s(Goal).g#0.name`

Incompatible selectors:
  - :mref:`.s(Goal).in.ccl`

Unquotable:
  - :mquote:`.s(Goal)`
  - :mquote:`.s(Goal).g#1`

Quote and title
  - :mquote:`test <.s(Goal)>`

Bad prefix:
  .. role:: mq2(mquote)
     :prefix:
  .. role:: mq2(mquote)
     :prefix: .s.i

Bad targets (dynamic):
  - :mref:`.io#nope.s(123)`
  - :mref:`.s(Goal).g#25`

Flags
=====

Unknown directive flags
  .. coq:: unknown

     Check nat.

Bad syntax in directive flags
  .. coq:: .s.g

     Check nat.

Bad syntax in inline flags (dynamic)
  .. coq::

     Check nat. (* .io.s *)
     Check nat. (* .unfold .xyz *)

Inapplicable targets (dynamic)
  .. coq::

     Check nat. (* .io#abc *)
     Check nat. (* .g#1.ccl .in .g#1.name *)
     Check nat. (* .g#1.h{*}.body .g#1.h{*}.type .g#1.h{*}.name *)

Inconsistent flags
  .. coq:: unfold out

     Check nat. (* .fold *)

Broken code
===========

.. coq::

   Notation "'🆄🄽🅘ⓒ⒪𝖉∈' α ⊕ ⤋ β" := α ++ β. (* Bytes vs. str *)

.. coq::

   Definition a
     : true := 1. (* Next line *)
