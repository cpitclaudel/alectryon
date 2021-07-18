==============
 Output flags
==============

This file tests various combinations of display flags.

.. coq:: none

   Require Import Coq.Unicode.Utf8. (* .none *)
   Require Import NArith ArithRing.

   Fixpoint nsum max f :=
     match max with
     | O => f 0
     | S max' => f max + nsum max' f
     end.

.. coq:: no-hyps unfold

   Lemma Gauss: ∀ n,
       2 * (nsum n (fun x => x)) =
       n * (n + 1).
   Proof. (* .fold *)
     induction n; cbn [nsum]. (* .hyps *)
     - (* n ← 0 *) (* .hyps *)
       Show Proof. (* .in .messages *)
       reflexivity.
     - (* n ← S _ *) (* .hyps *)
       rewrite Mult.mult_plus_distr_l. (* .fold *)
       rewrite IHn.
       Show Proof. (* .no-goals *)
       ring.
   Qed.

.. coq:: unfold out

   Check nat.
   About bool.

.. coq::

   Require Coq.Arith. (* .none *)      ← Executed but hidden
   Goal True. (* .unfold *)            ← Goal unfolded
     Fail exact 1. (* .in .messages *) ← Goal omitted
     Fail fail. (* .messages *)        ← Error message shown, input hidden
