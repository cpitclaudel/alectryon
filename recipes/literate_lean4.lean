/-!
==================================================
 Literate programming with Alectryon (Lean4 input)
==================================================

Alectryon supports literate programs and documents (combinations of code and prose) written in Lean4 and reStructuredText.  Here is an example written in Lean4.  It can be converted to reST, HTML, or LaTeX using the following commands::

   alectryon literate_lean4.lean
       # Lean4+reST → HTML;  produces ‘literate_lean4.html’
   alectryon literate_lean4.lean --backend latex \
        --latex-dialect xelatex \
        -o literate_lean4.xe.tex
       # Lean4+reST → LaTeX; produces ‘literate_lean4.xe.tex’
   alectryon literate_lean4.lean --backend rst
       # Lean4+reST → reST;  produces ‘literate_lean4.lean.rst’

-----

.. default-role:: lean4

Running queries
===============

Alectryon captures the results of `#check`, `#eval`, and the like:
-/

def x : Nat := 5
#reduce 5 + x

/-!
By default, these results are folded and are displayed upon hovering or clicking.  We can unfold them by default using annotations or directives:
-/

#check Nat /- .unfold -/

/-!
.. lean4:: unfold
-/

#check Bool
#eval 1 + 1

/-! Other flags can be used to control display, like ``.no-in``: -/

#print Iff /- .unfold .no-in -/

/-!
Documenting proofs
==================

Alectryon also captures goals and hypotheses as proofs progress:
-/

theorem test (p q : Prop) (hp : p) (hq : q): p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact hq
    . exact hp
  . intro h
    apply And.intro
    . exact hp
    . exact hq
