(*|
==================================================================
 Forget abut strengthening induction hypotheses: write fixpoints!
==================================================================

Here's an *inductive specification* of evenness:
|*)

Inductive Even : nat -> Prop :=
| EvenO : Even O
| EvenS : forall n, Even n -> Even (S (S n)).

(*|
… and a corresponding decision procedure:
|*)

Fixpoint even (n: nat): bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => even n
  end.

(* Ensure that we never unfold [even (S n)] *)
Arguments even : simpl nomatch.

(*|
Can we prove it correct?

.. coq:: unfold
|*)

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

(*|
The induction hypothesis doesn't apply — maybe we need to destruct ``n``?

.. coq:: unfold
|*)

    destruct n.
    + (* n ← 1 *)
      split; inversion 1.
    + (* n ← S (S _) *)

(*|
Stuck again!
|*)

Abort.

(*|
Strengthening the spec
======================

The usual approach is to strengthen the spec to work around the weakness of the inductive principle.

.. coq:: unfold
|*)

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

(*|
Writing a fixpoint
==================

But writing a fixpoint (either with the :coq:`Fixpoint` command or with the `fix` tactic) is much nicer:

.. coq:: unfold
|*)

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

(*|
.. role:: mycoqid(coqid)
   :url: https://coq.inria.fr/library/Coq.$modpath.html#$ident

Note that the standard library already contains a :mycoqid:`boolean <Init.Nat.even>` :coqid:`predicate <Coq.Init.Nat#even>` for `even` (called :coqid:`Coq.Init.Nat.even`, or :coqid:`Coq.Init.Nat#even` for short), as well as an :mycoqid:`inductive one <Arith.PeanoNat#Nat.Even>` (called :coqid:`Coq.Arith.PeanoNat#Nat.Even` in module :coqid:`Coq.Arith.PeanoNat#`).
|*)
