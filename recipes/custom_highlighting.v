(*|
=====================
 Custom highlighting
=====================

:alectryon/pygments/tacn: app but_first
:alectryon/pygments/tacn-solve: must_eauto

This file shows how to highlight custom keywords, like custom tactic names.  To compile it, use::

   alectryon custom_highlighting.v # Coq → HTML, produces ‘custom_highlighting.html’

Currently Alectryon recognizes the following token kinds:

- ``cmd``: top-level commands: `About`, `Locate Ltac`, …
- ``gallina-constants``: `Prop`, `Set`, `True`, …
- ``gallina-keywords``: `fix`, `forall`, `fun`, `if`, `with`, `as`, …
- ``ltac-builtins``: `abstract`, `all`, `assert_fails`, `constr`, …
- ``ltac-keywords``: `match goal with`, `lazy_match! goal with`, …
- ``tacn``: `absurd`, `admit`, `etransitivity`, …
- ``tacn-solve``: `assumption`, `by`, `congruence`, `tauto`, …
|*)

Tactic Notation "app" constr(thm) "but_first" tactic1(t) :=
  t; simple apply thm.

Ltac must_eauto := eauto; fail.

Goal forall x, x = 1 -> x >= 0.
  unfold ge.
  app le_S but_first intros ? ->.
  must_eauto.
Qed.

(*|
Using a custom driver for advanced highlighting
-----------------------------------------------

More advanced custom highlighting is possible using a custom driver, as demonstrated in ``alectryon_custom_driver.py``.  To compile this part of the file with full highlighting, use::

   $ python alectryon_custom_driver.py custom_highlighting.v -o custom_highlighting.with_driver.html
       # Custom driver; produces ‘custom_highlighting.with_driver.html’

The following demonstrates three examples: highlighting C code within strings, highlighting Markdown within comments, and highlighting a custom mini-language within ``calc:()`` delimiters:
|*)

Require Import Coq.Strings.String.
Open Scope string_scope.

(*|
The Pygments lexer in ``custom_lexer.py`` is set up to highlight text within ``C:{{…}}`` blocks as C code:
|*)

Definition c_program := "C:{{
  #include <stdio.h>

  int main(int argc, char** argv) {
    for (int i = 0; i < argc; i++) {
      while (*argv[i])
        putchar(*argv[i]++);
      putchar('\n');
    }
    return 0;
  }
}}".

(*|
Additionally, the lexer recognizes Coq comments and highlights them as Markdown:
|*)

Fixpoint dmap {A B} (l: list A) (f: forall a: A, List.In a l -> B) :=
  (* Apply function `f` to each element of list `l`.

     Note the **order of arguments**: `f` comes second because its
     *type* depends on `l`.  This allows callers to pass a partial
     function whose domain is only those elements found in the list. *)
  match l return (forall a: A, List.In a l -> B) -> list B with
  | nil => fun _ => nil
  | cons h t => fun f =>
    cons (f h (or_introl eq_refl))
         (dmap t (fun a pr => f a (or_intror pr)))
  end f.

(*|
And finally, the lexer is set up to highlight text within ``calc:()`` blocks using a custom lexer:
|*)

Declare Custom Entry calc.
Infix "add" := Nat.add (in custom calc at level 50, left associativity).
Infix "sub" := Nat.sub (in custom calc at level 50, left associativity).
Infix "mul" := Nat.mul (in custom calc at level 50, left associativity).
Infix "div" := Nat.div (in custom calc at level 50, left associativity).
Notation "n" := n (in custom calc at level 0, n constr).
Notation "( x )" := x (in custom calc at level 0).
Notation "'calc:' arg" := arg (at level 0, arg custom calc).

Definition miniprog lvl pb dc rll :=
  calc:(3 add (rll add 1 add pb) sub dc mul 4 div lvl).

(*|
Check out ``alectryon_custom_driver.py`` for all the details.
|*)
