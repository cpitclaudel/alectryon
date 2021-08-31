(** * Minification

This file ensures that minification works with plain Coq files (the
``minification.rst`` recipe uses the Docutils pipeline.

To run it::

    alectryon --frontend coq --html-minification minification.v
      # Plain Coq → HTML (minified); produces ‘minification.v.html’ **)

Require Import Arith.

Section Redundant.
  Context (non_negative := le_0_n).

  Fixpoint tree (n: nat) :=
    match n with
    | 0 => forall m: nat, m >= 0
    | S n => tree n /\ tree n
    end.

  Goal tree 4.
    repeat split.
    all: simpl.
    all: intros.
    all: idtac.
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
    1: { apply non_negative. }
  Qed.
End Redundant.
