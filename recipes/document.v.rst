==================================================================
 Forget abut strengthening induction hypotheses: write fixpoints!
==================================================================

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
     - split.
       all: constructor.
     - Fail apply IHn. (* .fails .no-goals *)

The induction hypothesis doesn't apply — maybe we need to destruct ``n``?

.. coq:: unfold

       destruct n.
       + split; inversion 1.
       +

Stuck again!

.. coq::

   Abort.

Strengthening the spec
======================

The usual approach is to strengthen the spec:

.. coq:: unfold

   Lemma even_Even :
     forall n, (even n = true <-> Even n) /\
          (even (S n) = true <-> Even (S n)). (* .fold *)
   Proof. (* .fold *)
     induction n; cbn.
     - repeat split; cbn.
       all: try constructor.
       all: inversion 1.
     - destruct IHn as ((Hne & HnE) & (HSne & HSnE)).
       repeat split; cbn.
       all: eauto using EvenS.
       inversion 1; eauto.
   Qed.

Writing a fixpoint
==================

But writing a fixpoint is much nicer:

.. coq:: unfold

   Fixpoint even_Even_fp (n: nat):
     even n = true <-> Even n. (* .fold *)
   Proof. (* .fold *)
     destruct n as [ | [ | n ] ]; cbn.
     - repeat constructor.
     - split; inversion 1.
     - split.
       + constructor; apply even_Even_fp; assumption.
       + inversion 1; apply even_Even_fp; assumption.
   Qed.
