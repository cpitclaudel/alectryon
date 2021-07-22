(** * An example using Coqdoc

    This is a hybrid rendering mode: coqdoc is used to render literate comments,
    and Alectryon is used to render code, responses, and goals.  It's a bit as
    if coqdoc was just a markup language, _without anything specific to
    Coq_. Cons:

    - There's a dependency on [coqdoc]
    - It doesn't use a standard markup language like reST, Markdown, etc.
    - You can't switch back and forth between a code view and a prose view: all
      prose editing happens in comments.
    - Annotations can't be applied to whole blocks, so if you want to unfold all
      sentences in a block you have to say (* .unfold *) on every sentence, for
      example.

    Use the following command to compile this file:

<<
    alectryon coqdoc.v --frontend coqdoc # Coqdoc → HTML; produces ‘coqdoc.html’
>>
**)

(** ** Some code **)

(**
Here's an *inductive specification* of evenness:
**)

Inductive Even : nat -> Prop :=
| EvenO : Even O
| EvenS : forall n, Even n -> Even (S (S n)).

(**
… and a corresponding decision procedure:
**)

Fixpoint even (n: nat): bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => even n
  end.

(* Ensure that we never unfold [even (S n)] *)
Arguments even : simpl nomatch.

(**
Can we prove it correct?
**)

Lemma even_Even :
  forall n, even n = true <-> Even n. (* .fold *)
Proof.
  induction n. (* .unfold *)
  all: cbn. (* .unfold *)
  - (* .unfold *) split. (* .unfold *)
    all: constructor. (* .unfold *)
  - (* .unfold *) Fail apply IHn. (* .fails .no-goals .unfold *)

(**
The induction hypothesis doesn't apply — maybe we need to destruct ``n``?
**)

    destruct n. (* .unfold *)
    + (* .unfold *) split; inversion 1. (* .unfold *)
    + (* .unfold *)

(**
Stuck again!
**)

Abort.

(** ** Strengthening the spec **)

(** The usual approach is to strengthen the spec: **)

Lemma even_Even :
  forall n, (even n = true <-> Even n) /\
       (even (S n) = true <-> Even (S n)). (* .fold *)
Proof.
  induction n; cbn. (* .unfold *)
  - (* .unfold *) repeat split; cbn. (* .unfold *)
    all: try constructor. (* .unfold *)
    all: inversion 1. (* .unfold *)
  - (* .unfold *) destruct IHn as ((Hne & HnE) & (HSne & HSnE)). (* .unfold *)
    repeat split; cbn. (* .unfold *)
    all: eauto using EvenS. (* .unfold *)
    inversion 1; eauto.
Qed.

(** ** Writing a fixpoint

But writing a fixpoint is much nicer: **)

Fixpoint even_Even_fp (n: nat):
  even n = true <-> Even n. (* .fold *)
Proof.
  destruct n as [ | [ | n ] ]; cbn. (* .unfold *)
  - (* .unfold *) repeat constructor. (* .unfold *)
  - (* .unfold *) split; inversion 1. (* .unfold *)
  - (* .unfold *) split. (* .unfold *)
    + (* .unfold *) constructor; apply even_Even; assumption.
    + (* .unfold *) inversion 1; apply even_Even; assumption.
Qed.
