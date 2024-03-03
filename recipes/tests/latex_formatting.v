(*|
========================
 LaTeX formatting tests
========================

This files tests various aspects of the conversion to LaTeX, including spacing and formatting::

   alectryon latex_formatting.v --backend latex
     # Coq+reST → LaTeX; produces ‘latex_formatting.tex’

.. raw:: latex

   \setlength{\parskip}{8pt}

Space after punctuation
=======================

.. coq:: in
|*)

Module Space.
  Infix "?" := plus (at level 10).
  Infix ":" := plus (at level 10).
  Infix ";" := plus (at level 10).
  Infix "," := plus (at level 10).

  Check (1 ? 1).
  Check (1 : 1).
  Check (1 ; 1).
  Check (1 , 1).

  Goal True -> True.
    intros. intros.
    intros; intros. generalize 0 1.
    intros? intros. refine ?[gggg].
    [gggg]: intros.
    exact I.
  Qed.
End Space.

(*|
Long hypotheses
===============
|*)
From Coq Require List.
Import List.ListNotations.
Open Scope list_scope.

Section Long.
  Context {A B: Type}.

  Fixpoint map (l: list A)
           (f: forall (n: nat) (a: A)
                 (_in: List.nth_error l n = Some a), B)
           {struct l}
    : list B.
  Proof.
    pose proof f; pose map.
    destruct l.
    - exact nil.
    - refine (_ :: _).
      apply (f 0 a eq_refl).
      specialize (fun n => f (S n)).
      simpl in f.
      apply (map l f).
  Defined.
End Long.

Compute (map [11; 22; 33] (fun n a _ => (n, a * a))).


Definition t := True.
Definition ign {A} (_: A) := Prop.

(*|
.. role:: ltx(raw)
   :format: latex

:ltx:`\begin{small}`
|*)

Goal forall
    (a: ign (t -> t -> t -> t -> t -> t -> t))
    (aaa: ign (t -> t -> t -> t -> t -> t))
    (aaaaa: ign (t -> t -> t -> t -> t -> t))
    (aaaaaaa: ign (t -> t -> t -> t -> t))
    (aaaaaaaaa: ign (t -> t -> t -> t -> t))
    (aaaaaaaaaaa: ign (t -> t -> t -> t))
    (aaaaaaaaaaaaa: ign (t -> t -> t -> t))
    (aaaaaaaaaaaaaaa: ign (t -> t -> t))
    (aaaaaaaaaaaaaaaaa: ign (t -> t -> t))
    (aaaaaaaaaaaaaaaaaaa: ign (t -> t))
    (aaaaaaaaaaaaaaaaaaaaa: ign (t -> t))
    (aaaaaaaaaaaaaaaaaaaaaaa: ign t)
    (aaaaaaaaaaaaaaaaaaaaaaaaa: ign t),
    a -> aaa -> aaaaa -> aaaaaaa -> aaaaaaaaa ->
    aaaaaaaaaaa -> aaaaaaaaaaaaa -> aaaaaaaaaaaaaaa ->
    aaaaaaaaaaaaaaaaa -> aaaaaaaaaaaaaaaaaaa ->
    aaaaaaaaaaaaaaaaaaaaa -> aaaaaaaaaaaaaaaaaaaaaaa ->
    aaaaaaaaaaaaaaaaaaaaaaaaa -> True.
Proof. auto. Qed.

(*|
:ltx:`\end{small}`

Paragraph-code spacing
======================

Some text.
|*)

(* Some code *)

(*|
Some text.
|*)

(* Some code *)

(*|
Some text.

Some text.
|*)

(* Some code *)

(*||*)

(* Some code *)

(*|
Some text.

.. code::

   Some code

-----

.. compound::

   Some text in compound.

   Some text in compound.  Spacing used to be wrong; see `<https://sourceforge.net/p/docutils/patches/183/>`__.
|*)

(* Some code in compound *)

(*||*)

(* Some code in compound *)

(*|
   Some text in compound.

   .. code::

      Some code in compound

Line breaks in input-only fragments
===================================

There should be no extra line breaks when showing only inputs:

.. coq:: in
|*)

Goal True /\ True.
  - idtac.
Abort.

Goal True /\ True.
Proof.
  split.
  - idtac "message". cut True.
    + tauto. + { tauto. }
  - { match goal with
      | _ => idtac
      end. exact I. }
Qed.

(*|
Showing outputs may still introduce line breaks:
|*)

Goal True /\ True.
  - idtac.
Abort.

Goal True /\ True.
Proof.
  split.
  - idtac "message". cut True.
    + tauto. + { tauto. }
  - { match goal with
      | _ => idtac
      end. exact I. }
Qed.

(*|
Newlines
========
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
