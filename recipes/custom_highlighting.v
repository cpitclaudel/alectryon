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
