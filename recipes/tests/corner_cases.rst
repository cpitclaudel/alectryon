==============
 Corner cases
==============

To compile::

   alectryon --stdin-filename corner_cases.rst --frontend rst \
     -o corner_cases.html - < corner_cases.rst
       # Coq → HTML; produces ‘corner_cases.html’
   alectryon corner_cases.rst -o corner_cases.xe.tex \
     --latex-dialect xelatex
       # Coq → LaTeX; produces ‘corner_cases.xe.tex’

Goal names
==========

.. coq::

   Goal True -> True /\ True.
     intros; refine (conj ?[G1] ?[G2]). (* .unfold *)
     [G1]: exact I.
     [G2]: exact I.
   Qed.

Self-reference
==============

.. coq::

   Definition a := 1.
   Check corner_cases.a.

Blanks at beginning of snippet
==============================

.. coq::

   Goal True.

.. coq::

       - (* .out .unfold *) exact I. Qed.

Blanks around sentences
=======================

Bubble: :alectryon-bubble:`-`

.. alectryon-toggle::

.. coq::

   (* xyz *) Goal True /\ True.
     - idtac.
       pose (a := 1).
       (* xyz *) split.  (* xyz *)
       + (* xyz *) idtac.
         idtac. (* x
         yz *)
         split.
       + (* xyz *) { (* xyz *) split. }
   Qed. (* xyz *)

References
==========

:mref:`.s(pose).h#a.body`, :mref:`.s(pose).h#a.type`, :mref:`.s(pose).h#a`.

.. role:: mq(mref)
   :kind: quote
