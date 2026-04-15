#import "/_output/alectryon.typ"
#show: alectryon.setup.with("/_output/literate_typst.alectryon.json")

= Literate programming with Alectryon (Typst input)

Alectryon supports Typst documents with embedded Coq code blocks.  Here is
an example.  It can be compiled using the following commands:

```
$ alectryon literate_typst.typ # Typst → JSON; produces ‘literate_typst.alectryon.json’
$ typst compile --root . literate_typst.typ literate_typst.pdf # Typst → PDF; produces ‘literate_typst.pdf’
```

A `<noal>` label opts a block out of Alectryon processing; it renders as a
plain syntax-highlighted Typst raw (the prover never sees it):

```coq
Check 1 + 1.
``` <noal>

```coq
Require Import PeanoNat.
```

Here's an _inductive specification_ of evenness:

```coq
Inductive Even : nat -> Prop :=
| EvenO : Even O
| EvenS : forall n, Even n -> Even (S (S n)).
```

... and a corresponding decision procedure:

```coq
Fixpoint even (n: nat): bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n) => even n
  end.

Arguments even : simpl nomatch.
```

Can we prove it correct?

```coq
Lemma even_Even :
  forall n, even n = true <-> Even n.
Proof.
  induction n.
  all: cbn.
  - split.
    all: constructor.
  - Fail apply IHn.
```

The induction hypothesis doesn't apply --- maybe we need to destruct `n`?

```coq
    destruct n.
    + split; inversion 1.
    +
```

Stuck again!

```coq
Abort.
```

== Strengthening the spec

The usual approach is to strengthen the spec to work around the weakness
of the inductive principle.

```coq
Lemma even_Even :
  forall n, (even n = true <-> Even n) /\
       (even (S n) = true <-> Even (S n)).
Proof.
  induction n; cbn.
  - repeat split; cbn.
    all: try constructor.
    all: inversion 1.
  - destruct IHn as ((Hne & HnE) & (HSne & HSnE)).
    repeat split; cbn.
    all: eauto using EvenS.
    inversion 1; eauto.
Qed.
```

== Writing a fixpoint

But writing a fixpoint is much nicer:

```coq
Fixpoint even_Even_fp (n: nat):
  even n = true <-> Even n.
Proof.
  destruct n as [ | [ | n ] ]; cbn.
  - repeat constructor.
  - split; inversion 1.
  - split.
    + constructor; apply even_Even_fp; assumption.
    + inversion 1; apply even_Even_fp; assumption.
Qed.
```
