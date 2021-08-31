=====================
 Errors and warnings
=====================

:alectryon/pygments/xyz: test

The ``lint`` backend in Alectryon runs the compiler and reports errors on ``stderr``::

   alectryon errors.rst --backend lint; echo "exit: $?" >> errors.lint.json
     # reST → JSON errors; produces ‘errors.lint.json’
   alectryon errors.rst --copy-assets none --backend webpage -o /dev/null 2> errors.txt; echo "exit: $?" >> errors.txt
     # reST → HTML + errors; produces ‘errors.txt’

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
  - .. massert:: <.s(Goal)>

Bad targets (static):
  - :mref:`.s(Goal).g#0.name`

Missing sentence:
  - :mref:`.g#0.in`

Incompatible selectors:
  - :mref:`.s(Goal).in.ccl`

Unquotable:
  - :mquote:`.s(Goal)`
  - :mquote:`.s(Goal).g#1`
  - .. mquote:: .s(Goal)
  - .. mquote:: .s(Goal).g#1

Quote and title
  - :mquote:`test <.s(Goal)>`
  - .. mquote:: test <.s(Goal)>
  - .. massert::

       test <.s(Goal)>

Bad prefix:
  .. role:: mq2(mquote)
     :prefix:
  .. role:: mq2(mquote)
     :prefix: .s.i

No block to reference (dynamic):
  - :mref:`.s(Goal True)`

.. coq::

   Goal True.
     pose proof 1 as n.
     exact I. (* A very long line *) (* whose contents are split *) (* across *) (* multiple *) (* comments *)
   Qed.

Bad targets (dynamic):
  - :mref:`.io#nope.s(123)`
  - :mref:`.s(Goal).g#25`
  - :mref:`.s(pose proof).h#n.body`

Bad assertions (dynamic):
  .. massert:: .s(Goal True)

     .g{*not found*}

     .msg

Directives
==========

.. exercise:: Title

   (Missing :difficulty: flag.)

Flags
-----

Unknown directive flags
  .. coq:: unknown

     Check nat.

Leftover flags
  .. coq:: unfold out .xyz

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
     Check nat. (* .g#1 *)
     Goal True. (* .g#1.ccl .in .g#1.name *)
       idtac. (* .g#1.h{*}.body .g#1.h{*}.type .g#1.h{*}.name *)
     Abort. (* .msg{*} *)

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
