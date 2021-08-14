==============
 Output flags
==============

This file tests various combinations of display flags.  To compile::

   alectryon display-flags.rst # reST → HTML; produces ‘display-flags.html’

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
       Show Proof. (* .all .no-goals *)
       ring.
   Qed.

.. coq:: unfold

   Check nat.
   About bool. (* .fold *)

.. coq:: fails

   Fail Check 1 + true.
   Fail Definition a := asd.
   Definition xyz := 123. (* .succeeds *)

.. coq::

   Fail Definition a := (* .fails .unfold *)
     (* `.fails` adds red highlight and removes "indeed failed". *)
     1 + true.

   Require Coq.Arith.Arith. (* ← Executed but hidden *) (* .none *)
   Goal True.               (* ← Goal unfolded *) (* .unfold *)
     Fail exact 1.          (* ← Goal omitted *) (* .in .messages *)
     Fail fail.             (* ← Error message shown, input hidden *) (* .unfold .messages *)
