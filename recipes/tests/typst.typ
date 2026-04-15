/*
  Comprehensive Typst backend test.

  $ alectryon typst.typ # Typst → JSON; produces ‘typst.alectryon.json’
  $ typst compile --root . typst.typ typst.pdf # Typst → PDF; produces ‘typst.pdf’
*/

#import "/_output/tests/alectryon.typ"
#show: alectryon.setup.with("/_output/tests/typst.alectryon.json")

#set page(width: 6in, height: auto, margin: 0.5in)
#set text(size: 10pt)

= Alectryon Typst Tests

== Syntax highlighting

```coq
Definition a : nat :=
  let '(x, y) := (1, 2) in
  let ' (z, t) := (x, y) in
  let 'tt := tt in
  let fix f (x: nat) {struct x} : nat := x in
  (fun ' (f, x, y) => f (x + y)) (f, t, y).
Print a.
```

== Position-based indexing

Two identical `Check nat.` blocks at different proof points:

```coq
Goal True /\ True.
  split.
```

```coq
  - Check nat.
    exact I.
```

```coq
  - Check nat.
    exact I.
Qed.
```

== String escaping

Backslash in notation:

```coq
Goal True \/ False.
  left. exact I.
Qed.
```

Quotes in output:

```coq
Fail Check "hello".
```

== Goal names

```coq
Goal forall b: bool, b = b.
  destruct b; [ refine ?[true] | refine ?[false] ].
  all: reflexivity.
Qed.
```

== Coq in a Typst table

#table(
  columns: (1fr, 1fr),
  align: top,
  [*Definition*], [*Usage*],
    [
```coq
Definition double (n : nat) := n + n.
```
    ],
    [
```coq
Check double.
Compute double 21.
```
    ],
)

== Coq in Typst columns

#columns(2)[
  A simple proof:

  ```coq
  Lemma add_0_r : forall n, n + 0 = n.
  Proof.
    induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.
  ```

  #colbreak()

  Using it:

  ```coq
  Require Import Arith.
  Check Nat.add_0_r.
  ```
]

== Coq alongside Typst math

Coq's `Nat.add_comm` proves that $n + m = m + n$:

```coq
Require Import Arith.
Check Nat.add_comm.
```

== Raw blocks across \#include

Verifies that `typst query` enumerates raw blocks across \#include-d files
in source order.

Before the include:

```coq
Definition main_defn := 42.
```

#include "included.typ"

After the include:

```coq
Check main_defn.
```

== Failed commands

```coq
Fail Check (1 + true).
```

== `-noexec` suffix

``coq-noexec`` blocks are rendered as ``coq`` blocks, but without invoking Coq:

```coq-noexec
Definition skipped: nat := 1 + nat.
Compute skipped + "?".
```

== Multi-line block annotation comments

```coq
(* .no-in
   .unfold *)
Goal True /\ True.
  split; exact I.
Qed.
```
