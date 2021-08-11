(*|
=====================
 Syntax highlighting
=====================

To compile::

   alectryon syntax_highlighting.v
     # Coq → HTML; produces ‘syntax_highlighting.html’

..
|*)

Definition a : nat :=
  let '(x, y) := (1, 2) in
  let ' (z, t) := (x, y) in
  let 'tt := tt in
  let fix f (x: nat) {struct x} : nat := x in
  (fun ' (f, x, y) => f (x + y)) (f, t, y).
Print a.

Definition test (as' is' with': nat) :=
  match match 1 with
        | S is' => 0
        | 0 => 1
        end with
  | S with' => None
  | 0 => Some 1
  end.
Print test.

Notation "$0" := (0, 0).
Infix "$+" := (fun '(u, a) '(_, b) => (u, a + b)) (at level 39).

Definition b := fun '(x, y) '(pair x' y') => (x + x', y + y').
Print b.

Notation "` x '' y `" := (x + y).
Check (1 + 2).
