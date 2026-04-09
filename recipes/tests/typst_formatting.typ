/*
Typst version of tests/latex_formatting.v.  To compile:

    $ alectryon typst_formatting.typ # Typst formatting test; produces ‘typst_formatting.alectryon.json’
    $ typst compile --root . typst_formatting.typ typst_formatting.pdf # Typst → PDF; produces ‘typst_formatting.pdf’
*/

#import "/_output/tests/alectryon.typ"
#show: alectryon.setup.with("/_output/tests/typst_formatting.alectryon.json")

#set page(paper: "a4")
#set text(size: 10pt)
#set par(spacing: 8pt)

= Space after punctuation

```coq
Module Space. (* .none *)
  Infix "?" := plus (at level 10). (* .none *)
  Infix ":" := plus (at level 10). (* .none *)
  Infix ";" := plus (at level 10). (* .none *)
  Infix "," := plus (at level 10). (* .none *)

  Check (1 ? 1). (* .in *)
  Check (1 : 1). (* .in *)
  Check (1 ; 1). (* .in *)
  Check (1 , 1). (* .in *)

  Goal True -> True. (* .in *)
    intros. intros. (* .in *)
    intros; intros. generalize 0 1. (* .in *)
    intros? intros. refine ?[gggg]. (* .in *)
    [gggg]: intros. (* .in *)
    exact I. (* .in *)
  Qed. (* .in *)
End Space. (* .in *)
```

#pagebreak()

= Hypothesis wrapping

```coq
Definition type {A} (a: A) := a. (* .none *)
Definition body {A} (a: A) := a. (* .none *)
Definition br {A B} (f: A -> B) (a: A) := f a. (* .none *)
Opaque type body br. (* .none *)

Notation "'TYPE' a" := (type a)
 (at level 0, a at level 1). (* .none *)
Notation "'BODY' a" := (body a)
 (at level 0, a at level 1). (* .none *)
Notation "'BRK_' f a" := (br f a)
 (at level 0, f at level 1, a at level 1,
   format "'BRK_'  f '//' a"). (* .none *)

Definition ONE_ := 1. (* .none *)
Definition NAT0 := nat. (* .none *)
Definition NAT1 := nat. (* .none *)
Definition NAT2 := nat. (* .none *)

Ltac p name body type :=
  pose body as name;
  change _ with type in (type of name). (* .none *)

Ltac p_223_33 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE type) (TYPE TYPE v)). (* .none *)
Ltac p_223_35 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE TYPE TYPE type) (TYPE TYPE v)). (* .none *)
Ltac p_223_53 n v :=
  p n (BRK_ body (BRK_ body (BODY BODY ONE_)))
   (BRK_ (TYPE type) (TYPE TYPE TYPE TYPE v)). (* .none *)
Ltac p_2_97 n v :=
  p n (BODY ONE_)
   (BRK_ (TYPE TYPE TYPE TYPE TYPE TYPE TYPE type)
    (TYPE TYPE TYPE TYPE TYPE TYPE v)). (* .none *)
Ltac p_489_97 n v :=
  p n (BRK_ (BODY BODY body)
       (BRK_ (BODY BODY BODY BODY BODY BODY body)
        (BODY BODY BODY BODY BODY BODY BODY BODY ONE_)))
   (BRK_ (TYPE TYPE TYPE TYPE TYPE TYPE TYPE type)
    (TYPE TYPE TYPE TYPE TYPE TYPE v)). (* .none *)
Ltac p_4F_2F n v :=
  p n (BRK_ (BODY BODY body)
       (BODY BODY BODY BODY BODY BODY BODY BODY
        BODY BODY BODY BODY BODY BODY BODY ONE_))
   (BRK_ type
    (TYPE TYPE TYPE TYPE TYPE TYPE TYPE TYPE
     TYPE TYPE TYPE TYPE TYPE TYPE TYPE v)). (* .none *)
```

```coq
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
         end. (* .no-in .unfold *)
  exact I. (* .none *)
Qed. (* .none *)
```

= More hypotheses

```coq
From Coq Require List. (* .none *)
Import List.ListNotations. (* .none *)
Open Scope list_scope. (* .none *)

Section Long. (* .none *)
  Context {A B: Type}. (* .none *)

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
End Long. (* .none *)

Compute (map [11; 22; 33] (fun n a _ => (n, a * a))).
```

= Many hypothesis names

```coq
Definition t := True. (* .none *)
Definition ign {A} (_: A) := Prop. (* .none *)

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
```

= Newlines

```coq
Require Import List. (* .none *)

Lemma skipn_app {A}:
  forall (l1 l2: list A) n,
    n <= List.length l1 ->
    skipn n (List.app l1 l2) =
    List.app (skipn n l1) l2.
Proof.
  induction l1.
  - destruct n.
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
```
