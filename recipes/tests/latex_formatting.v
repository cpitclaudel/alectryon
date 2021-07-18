(*|
========================
 LaTeX formatting tests
========================

This files tests various aspects of the conversion to LaTeX, including spacing and formatting::

   alectryon latex_formatting.v --backend latex # Coq+reST → LaTeX; produces ‘latex_formatting.tex’
|*)

Require Import List.

Lemma skipn_app {A}:
  forall (l1 l2: list A) n,
    n <= List.length l1 ->
    skipn n (List.app l1 l2) =
    List.app (skipn n l1) l2.
Proof.
  induction l1.
  - destruct n. (* same line *)
    all: cbn.
    + reflexivity.
      Show Proof. (* .messages .unfold *)

      Check nat. (* .messages .unfold *)
    + inversion 1.
  - destruct n. cbn.
    + reflexivity.
    + intros. apply IHl1.
      Check le_S_n.
      apply le_S_n.
      match goal with
      | [ H: _ <= _ |- _ ] => simpl in H
      end.
      assumption.
Qed.

(* Some spacing tests: *)
(* ^ 0 lines *)

(* ^ 1 *)


(* ^ 2 *)



(* ^ 3 *)

(* ---
   ^ 0

   ^ 1


   ^ 2



   ^ 3 *)
