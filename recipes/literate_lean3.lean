/-!
==================================================
 Literate programming with Alectryon (Lean3 input)
==================================================

Alectryon supports literate programs and documents (combinations of code and prose) written in Lean3 and reStructuredText.  Here is an example written in Lean3.  It can be converted to reST, HTML, or LaTeX using the following commands::

   alectryon literate_lean3.lean
       # Coq+reST → HTML;  produces ‘literate_lean3.html’
   alectryon literate_lean3.lean --backend latex \
        --latex-dialect xelatex \
        -o literate_lean3.xe.tex
       # Coq+reST → LaTeX; produces ‘literate_lean3.xe.tex’
   alectryon literate_lean3.lean --backend rst
       # Coq+reST → reST;  produces ‘literate_lean3.lean.rst’

-----

.. default-role:: lean3

Running queries
===============

Alectryon captures the results of `#check`, `#eval`, and the like:
-/

#reduce let x := 5 in x + 3

/-!
By default, these results are folded and are displayed upon hovering or clicking.  We can unfold them by default using annotations or directives:
-/

#check nat /- .unfold -/

/-!
.. lean3:: unfold
-/

#check bool
#eval 1 + 1

/-! Other flags can be used to control display, like ``.no-in``: -/

#print iff /- .unfold .no-in -/

/-!
Documenting proofs
==================

Alectryon also captures goals and hypotheses as proofs progress:
-/

example (p q r : Prop) : p ∧ q ↔ q ∧ p :=
begin /- .none -/
  apply iff.intro, {
    intro H,
    apply and.intro, /- .unfold -/
    apply (and.elim_right H),
    apply (and.elim_left H),
  }, {
    intro H,
    apply and.intro,
    apply (and.elim_right H),
    apply (and.elim_left H),
  }
end

/-!
Most features available for Coq are also available for Lean3; in particular, references (:mref:`.s(intro H)`, :mref:`.s(and.intro).h#H`), quotes (:mquote:`.s(and.intro).h#H.type`) and assertions should work.

.. massert:: .s(apply iff.intro).g#2
.. mquote:: .s(apply iff.intro).g#2.ccl

For now, please refer to the main README and to the Coq examples for more information.
-/
