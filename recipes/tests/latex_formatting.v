(*|
========================
 LaTeX formatting tests
========================

This file tests various aspects of the conversion to LaTeX, including spacing and formatting::

   $ DOCUTILSCONFIG=tests/geometry.docutils.conf \
       alectryon latex_formatting.v --backend latex
     # Coq+reST → LaTeX; produces ‘latex_formatting.tex’

.. raw:: latex

   \setlength{\parskip}{8pt}
   \pagestyle{empty}
   \thispagestyle{empty}

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
.. role:: ltx(raw)
   :format: latex

:ltx:`\newgeometry{top=1cm,left=1cm,right=1cm}`

Hypothesis wrapping
===================

.. coq:: none
|*)

Definition type {A} (a: A) := a.
Definition body {A} (a: A) := a.
Definition br {A B} (f: A -> B) (a: A) := f a.
Opaque type body br.

Notation "'TYPE' a" := (type a)
 (at level 0, a at level 1).
Notation "'BODY' a" := (body a)
 (at level 0, a at level 1).
Notation "'BRK_' f a" := (br f a)
 (at level 0, f at level 1, a at level 1,
   format "'BRK_'  f '//' a").

Definition ONE_ := 1.
Definition NAT0 := nat.
Definition NAT1 := nat.
Definition NAT2 := nat.

Ltac p name body type :=
  pose body as name;
  change _ with type in (type of name).

Ltac p_223_33 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE type) (TYPE TYPE v)).
Ltac p_223_35 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE TYPE TYPE type) (TYPE TYPE v)).
Ltac p_223_53 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE type) (TYPE TYPE TYPE TYPE v)).
Ltac p_2_97 n v :=
  p n (BODY ONE_)
   (BRK_ (TYPE TYPE TYPE TYPE TYPE TYPE TYPE type)
    (TYPE TYPE TYPE TYPE TYPE TYPE v)).
Ltac p_489_97 n v :=
  p n (BRK_ (BODY BODY body)
       (BRK_ (BODY BODY BODY BODY BODY BODY body)
        (BODY BODY BODY BODY BODY BODY BODY BODY ONE_)))
   (BRK_ (TYPE TYPE TYPE TYPE TYPE TYPE TYPE type)
    (TYPE TYPE TYPE TYPE TYPE TYPE v)).
Ltac p_4F_2F n v :=
  p n (BRK_ (BODY BODY body)
       (BODY BODY BODY BODY BODY BODY BODY BODY
        BODY BODY BODY BODY BODY BODY BODY ONE_))
   (BRK_ type
    (TYPE TYPE TYPE TYPE TYPE TYPE TYPE TYPE
     TYPE TYPE TYPE TYPE TYPE TYPE TYPE v)).

(*|
.. coq:: no-in unfold
|*)

Goal True. (* .none *)
  p_223_33 ffffffff0 NAT0; p_223_33 ffffffff1 NAT1;
    p_223_33 ffffffff2 NAT0; p_223_53 ffffffff3 NAT1;
    p_223_33 ffffffff4 NAT0; p_223_35 ffffffff5 NAT1;

    p_2_97 ffffffff6 NAT0;
    p_489_97 ffffffff7 NAT1;

    p_489_97 ffffffffffffffffffffffffffffffffffffff8 NAT0;
    p_489_97 fffffffffffffffffffffffffffffffffffffffffffffffffff9 NAT1;

    p_489_97 fffffffffffffffffffffffffffffffffffff10 NAT0;
    p_489_97 ffffffffffffffffffffffffffffffffffffffffffffffffff10b NAT0;

    p_4F_2F fffffffffffffffffffffffffffffffffffff11 NAT1.
  repeat match goal with
         | [ H := _ : _ |- _ ] => clearbody H
         end. (* .no-in *)
  exact I. (* .none *)
Qed. (* .none *)

(*|
:ltx:`\restoregeometry`

More hypotheses
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

(*|
Compound directive
==================

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
|*)
