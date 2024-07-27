==============
 Output flags
==============

This file tests various combinations of display flags.  To compile::

   alectryon display-flags.rst # reST → HTML; produces ‘display-flags.html’

.. coq:: none

   Require Import Coq.Unicode.Utf8. (* .none *)
   Require Import PeanoNat ArithRing.

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
       rewrite Nat.mul_add_distr_l. (* .fold *)
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

.. coq:: none

   Set Printing Implicit.
   Check id. (* .all *)
   Unset Printing Implicit.

.. coq::

   (* Visible *)

.. coq:: none

   (* Hidden *)

.. coq::

   Fail Definition a := (* .fails .unfold *)
     (* `.fails` adds red highlight and removes "indeed failed". *)
     1 + true.

   Require PeanoNat.     (* ← Executed but hidden *) (* .none *)
   Goal True.            (* ← Goal unfolded *) (* .unfold *)
     Fail exact 1.       (* ← Goal omitted *) (* .in .messages *)
     Fail fail.          (* ← Error message shown, input hidden *) (* .unfold .messages *)
     exact I.            (* ← Executed but hidden *) (* -.s{*} *)
   Qed.

.. coq:: -.h#l* -.h#[aA] -.s(Check let).msg(Check) -.s{Proof.}.in -.s{Proof.}.g#* -.s{Proof.}.msg(*)
   :name: pr

   Require Import Coq.Sorting.Permutation. (* .none *)
   Check let t := nat in forall {n: t}, n >= 0. (* .unfold *)
   Theorem Permutation_In {A} (l l' : list A) (a: A) :
     Permutation l l' -> List.In a l -> List.In a l'. (* .unfold *)
   Proof.
     induction 1; intros * Hin; [ | refine ?[gg] | .. ]. (*
       .unfold -.g#* .g#2 .g#4 .g#4.h{list A} *)
     all: simpl in *. (* -.g#*.ccl *)
     all: tauto.
   Qed.
