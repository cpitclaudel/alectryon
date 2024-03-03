=================================================
 Literate programming with Alectryon (Coq input)
=================================================

Alectryon supports literate programs and documents (combinations of code and prose) written in Coq and reStructuredText.  Here is an example, written in Coq.  It can be converted to reST, HTML, or LaTeX using the following commands::

   alectryon literate_coq.v
       # Coq+reST → HTML;  produces ‘literate_coq.html’
   $ DOCUTILSCONFIG=literate.docutils.conf alectryon \
     literate_coq.v --backend latex
       # Coq+reST → LaTeX; produces ‘literate_coq.tex’
   alectryon literate_coq.v --backend rst
       # Coq+reST → reST;  produces ‘literate_coq.v.rst’

   $ cd ..; python -m alectryon.literate \
       recipes/literate_coq.v > recipes/literate_coq.min.rst
     # Minimal Coq → reST; produces ‘literate_coq.min.rst’
   $ cd ..; python -m alectryon.literate --coq2rst - \
       < recipes/literate_coq.v > recipes/literate_coq.min.stdin.rst
     # Minimal Coq → reST; produces ‘literate_coq.min.stdin.rst’

-----

.. coq:: none

   Require Import PeanoNat.

Here's an *inductive specification* of evenness:

.. coq::

   Inductive Even : nat -> Prop :=
   | EvenO : Even O
   | EvenS : forall n, Even n -> Even (S (S n)).

… and a corresponding decision procedure:

.. coq::

   Fixpoint even (n: nat): bool :=
     match n with
     | 0 => true
     | 1 => false
     | S (S n) => even n
     end.

   (* Ensure that we never unfold [even (S n)] *)
   Arguments even : simpl nomatch.

Can we prove it correct?

.. coq:: unfold

   Lemma even_Even :
     forall n, even n = true <-> Even n. (* .fold *)
   Proof. (* .fold *)
     induction n.
     all: cbn.
     - (* n ← 0 *)
       split.
       all: constructor.
     - (* n ← S _ *)
       Fail apply IHn. (* .fails .no-goals *) (* stuck! *)

The induction hypothesis doesn't apply — maybe we need to destruct ``n``?

.. coq:: unfold

       destruct n.
       + (* n ← 1 *)
         split; inversion 1.
       + (* n ← S (S _) *)

Stuck again!

.. coq::

   Abort.

Strengthening the spec
======================

The usual approach is to strengthen the spec to work around the weakness of the inductive principle.

.. coq:: unfold

   Lemma even_Even :
     forall n, (even n = true <-> Even n) /\
          (even (S n) = true <-> Even (S n)). (* .fold *)
   Proof. (* .fold *)
     induction n; cbn.
     - (* n ← 0 *)
       repeat split; cbn.
       all: try constructor.
       all: inversion 1.
     - (* n ← S _ *)
       destruct IHn as ((Hne & HnE) & (HSne & HSnE)).
       repeat split; cbn.
       all: eauto using EvenS.
       inversion 1; eauto.
   Qed.

Writing a fixpoint
==================

But writing a fixpoint (either with the :coq:`Fixpoint` command or with the `fix` tactic) is much nicer:

.. coq:: unfold

   Fixpoint even_Even_fp (n: nat):
     even n = true <-> Even n. (* .fold *)
   Proof. (* .fold *)
     destruct n as [ | [ | n ] ]; cbn.
     - (* n ← 0 *)
       repeat constructor.
     - (* n ← 1 *)
       split; inversion 1.
     - (* n ← S (S _) *)
       split.
       + constructor; apply even_Even_fp; assumption.
       + inversion 1; apply even_Even_fp; assumption.
   Qed.

.. raw:: latex

   \setlength{\emergencystretch}{4em}

Alectryon defined a ``:coqid:`` role to link to definitions in Coqdoc-generated documentation; for example:

    Note that the standard library already contains a :coqid:`boolean <Coq.Init.Nat.even>` :coqid:`predicate <Coq.Init.Nat#even>` for `even` (called :coqid:`Coq.Init.Nat.even`, or :coqid:`Coq.Init.Nat#even` for short), as well as an :coqid:`inductive one <Coq.Arith.PeanoNat#Nat.Even>` (called :coqid:`Coq.Arith.PeanoNat#Nat.Even` in module :coqid:`Coq.Arith.PeanoNat#`).

If you have your own documentation, you can use a custom role to point to your own URL:

.. role:: mq(coqid)
   :url: https://coq.inria.fr/library/Coq.$modpath.html#$ident

With this definition, for example, you can write :mq:`Arith.PeanoNat#Nat.Even` instead of :coqid:`Coq.Arith.PeanoNat#Nat.Even`.
