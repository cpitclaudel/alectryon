/-!
Theorem Proving in Lean 4 - Tactics
===================================

.. alectryon-toggle::

To compile::

   alectryon lean4-tactics.rst
       # reST+Lean4 → HTML; produces ‘lean4-tactics.html’
   alectryon lean4-tactics.rst -o lean4-tactics.lean
       # reST+Lean4 → Lean4; produces ‘lean4-tactics.lean’

.. note::

   The original document is at https://leanprover.github.io/theorem_proving_in_lean4/
   and has been converted from .md to .rst.

Tactics
=======

In this chapter, we describe an alternative approach to constructing
proofs, using *tactics*. A proof term is a representation of a
mathematical proof; tactics are commands, or instructions, that describe
how to build such a proof. Informally, you might begin a mathematical
proof by saying "to prove the forward direction, unfold the definition,
apply the previous lemma, and simplify." Just as these are instructions
that tell the reader how to find the relevant proof, tactics are
instructions that tell Lean how to construct a proof term. They
naturally support an incremental style of writing proofs, in which you
decompose a proof and work on goals one step at a time.

We will describe proofs that consist of sequences of tactics as
"tactic-style" proofs, to contrast with the ways of writing proof terms
we have seen so far, which we will call "term-style" proofs. Each style
has its own advantages and disadvantages. For example, tactic-style
proofs can be harder to read, because they require the reader to predict
or guess the results of each instruction. But they can also be shorter
and easier to write. Moreover, tactics offer a gateway to using Lean's
automation, since automated procedures are themselves tactics.

Entering Tactic Mode
--------------------

Conceptually, stating a theorem or introducing a ``have`` statement
creates a goal, namely, the goal of constructing a term with the
expected type. For example, the following creates the goal of
constructing a term of type ``p ∧ q ∧ p``, in a context with constants
``p q : Prop``, ``hp : p`` and ``hq : q``:
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  sorry

/-!
You can write this goal as follows:

::

       p : Prop, q : Prop, hp : p, hq : q ⊢ p ∧ q ∧ p

Indeed, if you replace the "sorry" by an underscore in the example
above, Lean will report that it is exactly this goal that has been left
unsolved.

Ordinarily, you meet such a goal by writing an explicit term. But
wherever a term is expected, Lean allows us to insert instead a
``by <tactics>`` block, where ``<tactics>`` is a sequence of commands,
separated by semicolons or line breaks. You can prove the theorem above
in that way:
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

/-!
We often put the ``by`` keyword on the preceding line, and write the
example above as
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

/-!
The ``apply`` tactic applies an expression, viewed as denoting a
function with zero or more arguments. It unifies the conclusion with the
expression in the current goal, and creates new goals for the remaining
arguments, provided that no later arguments depend on them. In the
example above, the command ``apply And.intro`` yields two subgoals:

::

       case left
       p : Prop,
       q : Prop,
       hp : p,
       hq : q
       ⊢ p

       case right
       p : Prop,
       q : Prop,
       hp : p,
       hq : q
       ⊢ q ∧ p

The first goal is met with the command ``exact hp``. The ``exact``
command is just a variant of ``apply`` which signals that the expression
given should fill the goal exactly. It is good form to use it in a
tactic proof, since its failure signals that something has gone wrong.
It is also more robust than ``apply``, since the elaborator takes the
expected type, given by the target of the goal, into account when
processing the expression that is being applied. In this case, however,
``apply`` would work just as well.

You can see the resulting proof term with the ``#print`` command:
-/

# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro
#  exact hp
#  apply And.intro
#  exact hq
#  exact hp
#print test

/-!
You can write a tactic script incrementally. In VS Code, you can open a
window to display messages by pressing ``Ctrl-Shift-Enter``, and that
window will then show you the current goal whenever the cursor is in a
tactic block. In Emacs, you can see the goal at the end of any line by
pressing ``C-c C-g``, or see the remaining goal in an incomplete proof
by putting the cursor after the first character of the last tactic. If
the proof is incomplete, the token ``by`` is decorated with a red
squiggly line, and the error message contains the remaining goals.

Tactic commands can take compound expressions, not just single
identifiers. The following is a shorter version of the preceding proof:
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

/-!
Unsurprisingly, it produces exactly the same proof term.
-/

# theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
#  apply And.intro hp
#  exact And.intro hq hp
#print test

/-!
Multiple tactic applications can be written in a single line by
concatenating with a semicolon.
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

/-!
Tactics that may produce multiple subgoals often tag them. For example,
the tactic ``apply And.intro`` tagged the first sugoal as ``left``, and
the second as ``right``. In the case of the ``apply`` tactic, the tags
are inferred from the parameters names used in the ``And.intro``
declaration. You can structure your tactics using the notation
``case <tag> => <tactics>``. The following is a structured version of
our first tactic proof in this chapter.
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

/-!
You can solve the subgoal ``right`` before ``left`` using the ``case``
notation
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

/-!
Note that Lean hides the other goals inside the ``case`` block. We say
it is "focusing" on the selected goal. Moreover, Lean flags an error if
the selected goal is not fully solved at the end of the ``case`` block.

For simple sugoals, it may not be worth selecting a subgoal using its
tag, but you may still want to structure the proof. Lean also provides
the "bullet" notation ``. <tactics>`` (or ``· <tactics>``) for
structuring proof.
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

/-!
Basic Tactics
-------------

In addition to ``apply`` and ``exact``, another useful tactic is
``intro``, which introduces a hypothesis. What follows is an example of
an identity from propositional logic that we proved in a previous
chapter, now proved using tactics.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

/-!
The ``intro`` command can more generally be used to introduce a variable
of any type:
-/

example (α : Type) : α → α := by
  intro a
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

/-!
You can use it to introduce several variables:
-/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

/-!
As the ``apply`` tactic is a command for constructing function
applications interactively, the ``intro`` tactic is a command for
constructing function abstractions interactively (i.e., terms of the
form ``fun x => e``). As with lambda abstraction notation, the ``intro``
tactic allows us to use an implicit ``match``.
-/

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

/-!
You can also provide multiple alternatives like in the ``match``
expression.
-/

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
    | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

/-!
The ``intros`` tactic can be used without any arguments, in which case,
it chooses names and introduces as many variables as it can. You will
see an example of this in a moment.

The ``assumption`` tactic looks through the assumptions in context of
the current goal, and if there is one matching the conclusion, it
applies it.
-/

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption   -- applied h₃

/-!
It will unify metavariables in the conclusion if necessary:
-/

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption      -- solves x = ?b with h₁
  apply Eq.trans
  assumption      -- solves y = ?h₂.b with h₂
  assumption      -- solves z = w with h₃

/-!
The following example uses the ``intros`` command to introduce the three
variables and two hypotheses automatically:
-/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

/-!
Note that names automatically generated by Lean are inaccessible by
default. The motivation is to ensure your tactic proofs do not rely on
automatically generated names, and are consequently more robust.
However, you can use the combinator ``unhygienic`` to disable this
restriction.
-/

example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  exact a_2
  exact a_1

/-!
You can also use the ``rename_i`` tactic to rename the most recent
inaccessible names in your context. In the following example, the tactic
``rename_i h1 _ h2`` renames two of the last three hypotheses in your
context.
-/

example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1

/-!
The ``rfl`` tactic is syntax sugar for ``exact rfl``.
-/

example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl

/-!
The ``repeat`` combinator can be used to apply a tactic several times.
-/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

/-!
Another tactic that is sometimes useful is the ``revert`` tactic, which
is, in a sense, an inverse to ``intro``.
-/

example (x : Nat) : x = x := by
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

/-!
Moving a hypothesis into the goal yields an implication:
-/

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is x y : Nat ⊢ x = y → y = x
  intro h₁
  -- goal is x y : ℕ, h₁ : x = y ⊢ y = x
  apply Eq.symm
  assumption

/-!
But ``revert`` is even more clever, in that it will revert not only an
element of the context but also all the subsequent elements of the
context that depend on it. For example, reverting ``x`` in the example
above brings ``h`` along with it:
-/

example (x y : Nat) (h : x = y) : y = x := by
  revert x
  -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

/-!
You can also revert multiple elements of the context at once:
-/

example (x y : Nat) (h : x = y) : y = x := by
  revert x y
  -- goal is ⊢ ∀ (x y : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

/-!
You can only ``revert`` an element of the local context, that is, a
local variable or hypothesis. But you can replace an arbitrary
expression in the goal by a fresh variable using the ``generalize``
tactic.
-/

example : 3 = 3 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ x = x,
  revert x
  -- goal is ⊢ ∀ (x : Nat), x = x
  intro y
  -- goal is y : Nat ⊢ y = y
  rfl

/-!
The mnemonic in the notation above is that you are generalizing the goal
by setting ``3`` to an arbitrary variable ``x``. Be careful: not every
generalization preserves the validity of the goal. Here, ``generalize``
replaces a goal that could be proved using ``rfl`` with one that is not
provable:
-/

example : 2 + 3 = 5 := by
  generalize  3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit

/-!
In this example, the ``admit`` tactic is the analogue of the ``sorry``
proof term. It closes the current goal, producing the usual warning that
``sorry`` has been used. To preserve the validity of the previous goal,
the ``generalize`` tactic allows us to record the fact that ``3`` has
been replaced by ``x``. All you need to do is to provide a label, and
``generalize`` uses it to store the assignment in the local context:
-/

example : 2 + 3 = 5 := by
  generalize h : 3 = x
  -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]

/-!
Here the ``rewrite`` tactic, abbreviated ``rw``, uses ``h`` to replace
``x`` by ``3`` again. The ``rewrite`` tactic will be discussed below.

More Tactics
------------

Some additional tactics are useful for constructing and destructing
propositions and data. For example, when applied to a goal of the form
``p ∨ q``, you use tactics such as ``apply Or.inl`` and
``apply Or.inr``. Conversely, the ``cases`` tactic can be used to
decompose a disjunction.
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

/-!
Note that the syntax is similar to the one used in ``match``
expressions. The new subgoals can be solved in any order.
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inr hq => apply Or.inl; exact hq
  | inl hp => apply Or.inr; exact hp

/-!
You can also use a (unstructured) ``cases`` without the ``with`` and a
tactic for each alternative.
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

/-!
The (unstructured) ``cases`` is particularly useful when you can close
several subgoals using the same tactic.
-/

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h
  repeat assumption

/-!
You can also use the combinator ``tac1 <;> tac2`` to apply ``tac2`` to
each subgoal produced by tactic ``tac1``
-/

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption

/-!
You can combine the unstructured ``cases`` tactic with the ``case`` and
``.`` notation.
-/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  case inl h =>
    apply Or.inr
    assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr h =>
    apply Or.inl
    assumption
  . apply Or.inr
    assumption

/-!
The ``cases`` tactic can also be used to decompose a conjunction.
-/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h
  cases h with
  | intro hp hq => constructor; exact hq; exact hp

/-!
In this example, there is only one goal after the ``cases`` tactic is
applied, with ``h : p ∧ q`` replaced by a pair of assumptions,
``hp : p`` and ``hq : q``. The ``constructor`` tactic applies the unique
constructor for conjunction, ``And.intro``. With these tactics, an
example from the previous section can be rewritten as follows:
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr

/-!
You will see in `Chapter Inductive Types <./inductive_types.md>`__ that
these tactics are quite general. The ``cases`` tactic can be used to
decompose any element of an inductively defined type; ``constructor``
always applies the first applicable constructor of an inductively
defined type. For example, you can use ``cases`` and ``constructor``
with an existential quantifier:
-/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

/-!
Here, the ``constructor`` tactic leaves the first component of the
existential assertion, the value of ``x``, implicit. It is represented
by a metavariable, which should be instantiated later on. In the
previous example, the proper value of the metavariable is determined by
the tactic ``exact px``, since ``px`` has type ``p x``. If you want to
specify a witness to the existential quantifier explicitly, you can use
the ``exists`` tactic instead:
-/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px

/-!
Here is another example:
-/

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
      constructor <;> assumption

/-!
These tactics can be used on data just as well as propositions. In the
next two examples, they are used to define functions which swap the
components of the product and sum types:
-/

def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

/-!-/

def swap_sum : Sum α β → Sum β α := by
  intro p
  cases p
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption

/-!
Note that up to the names we have chosen for the variables, the
definitions are identical to the proofs of the analogous propositions
for conjunction and disjunction. The ``cases`` tactic will also do a
case distinction on a natural number:
-/

open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
 cases m with
 | zero    => exact h₀
 | succ m' => exact h₁ m'

/-!
The ``cases`` tactic, and its companion, the ``induction`` tactic, are
discussed in greater detail in the `Tactics for Inductive
Types <./inductive_types.md#tactics_for_inductive_types>`__ section.

The ``contradiction`` tactic searches for a contradiction among the
hypotheses of the current goal:
-/

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

/-!
You can also use ``match`` in tactic blocks.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨_, Or.inl _⟩ => apply Or.inl; constructor <;> assumption
    | ⟨_, Or.inr _⟩ => apply Or.inr; constructor <;> assumption
  . intro h
    match h with
    | Or.inl ⟨hp, hq⟩ => constructor; exact hp; apply Or.inl; exact hq
    | Or.inr ⟨hp, hr⟩ => constructor; exact hp; apply Or.inr; exact hr

/-!
You can "combine" ``intro h`` with ``match h ...`` and write the
previous examples as follows
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
     | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
     | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
     | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
     | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption

/-!
Structuring Tactic Proofs
-------------------------

Tactics often provide an efficient way of building a proof, but long
sequences of instructions can obscure the structure of the argument. In
this section, we describe some means that help provide structure to a
tactic-style proof, making such proofs more readable and robust.

One thing that is nice about Lean's proof-writing syntax is that it is
possible to mix term-style and tactic-style proofs, and pass between the
two freely. For example, the tactics ``apply`` and ``exact`` expect
arbitrary terms, which you can write using ``have``, ``show``, and so
on. Conversely, when writing an arbitrary Lean term, you can always
invoke the tactic mode by inserting a ``by`` block. The following is a
somewhat toy example:
-/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

/-!
The following is a more natural example:
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq => exact Or.inl ⟨h.left, hq⟩
    | inr hr => exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

/-!
In fact, there is a ``show`` tactic, which is similar to the ``show``
expression in a proof term. It simply declares the type of the goal that
is about to be solved, while remaining in tactic mode.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

/-!
The ``show`` tactic can actually be used to rewrite a goal to something
definitionally equivalent:
-/

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

/-!
There is also a ``have`` tactic, which introduces a new subgoal, just as
when writing proof terms:
-/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

/-!
As with proof terms, you can omit the label in the ``have`` tactic, in
which case, the default label ``this`` is used:
-/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

/-!
The types in a ``have`` tactic can be omitted, so you can write
``have hp := h.left`` and ``have hqr := h.right``. In fact, with this
notation, you can even omit both the type and the label, in which case
the new fact is introduced with the label ``this``.
-/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr =>
    have := And.intro hp hr
    apply Or.inr; exact this

/-!
Lean also has a ``let`` tactic, which is similar to the ``have`` tactic,
but is used to introduce local definitions instead of auxiliary facts.
It is the tactic analogue of a ``let`` in a proof term.
-/

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a
  rfl

/-!
As with ``have``, you can leave the type implicit by writing
``let a := 3 * 2``. The difference between ``let`` and ``have`` is that
``let`` introduces a local definition in the context, so that the
definition of the local declaration can be unfolded in the proof.

We have used ``.`` to create nested tactic blocks. In a nested block,
Lean focuses on the first goal, and generates an error if it has not
been fully solved at the end of the block. This can be helpful in
indicating the separate proofs of multiple subgoals introduced by a
tactic. The notation ``.`` is whitespace sensitive and relies on the
indentation to detect whether the tactic block ends. Alternatively, you
can define tactic blocks usind curly braces and semicolons.
-/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }

/-!
It useful to use indendation to structure proof: every time a tactic
leaves more than one subgoal, we separate the remaining subgoals by
enclosing them in blocks and indenting. Thus if the application of
theorem ``foo`` to a single goal produces four subgoals, one would
expect the proof to look like this:

::

     apply foo
     . <proof of first goal>
     . <proof of second goal>
     . <proof of third goal>
     . <proof of final goal>

or

::

     apply foo
     case <tag of first goal>  => <proof of first goal>
     case <tag of second goal> => <proof of second goal>
     case <tag of third goal>  => <proof of third goal>
     case <tag of final goal>  => <proof of final goal>

or

::

     apply foo
     { <proof of first goal>  }
     { <proof of second goal> }
     { <proof of third goal>  }
     { <proof of final goal>  }

Tactic Combinators
------------------

*Tactic combinators* are operations that form new tactics from old ones.
A sequencing combinator is already implicit in the ``by`` block:
-/

example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption

/-!
Here, ``apply Or.inl; assumption`` is functionally equivalent to a
single tactic which first applies ``apply Or.inl`` and then applies
``assumption``.

In ``t₁ <;> t₂``, the ``<;>`` operator provides a *parallel* version of
the sequencing operation: ``t₁`` is applied to the current goal, and
then ``t₂`` is applied to *all* the resulting subgoals:
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

/-!
This is especially useful when the resulting goals can be finished off
in a uniform way, or, at least, when it is possible to make progress on
all of them uniformly.

The ``first | t₁ | t₂ | ... | tₙ`` applies each ``tᵢ`` until one
succeeds, or else fails:
-/

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

/-!
In the first example, the left branch succeeds, whereas in the second
one, it is the right one that succeeds. In the next three examples, the
same compound tactic succeeds in each case.
-/

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

/-!
The tactic tries to solve the left disjunct immediately by assumption;
if that fails, it tries to focus on the right disjunct; and if that
doesn't work, it invokes the assumption tactic.

You will have no doubt noticed by now that tactics can fail. Indeed, it
is the "failure" state that causes the *first* combinator to backtrack
and try the next tactic. The ``try`` combinator builds a tactic that
always succeeds, though possibly in a trivial way: ``try t`` executes
``t`` and reports success, even if ``t`` fails. It is equivalent to
``first | t | skip``, where ``skip`` is a tactic that does nothing (and
succeeds in doing so). In the next example, the second ``constructor``
succeeds on the right conjunct ``q ∧ r`` (remember that disjunction and
conjunction associate to the right) but fails on the first. The ``try``
tactic ensures that the sequential composition succeeds.
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

/-!
Be careful: ``repeat (try t)`` will loop forever, because the inner
tactic never fails.

In a proof, there are often multiple goals outstanding. Parallel
sequencing is one way to arrange it so that a single tactic is applied
to multiple goals, but there are other ways to do this. For example,
``all_goals t`` applies ``t`` to all open goals:
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

/-!
In this case, the ``any_goals`` tactic provides a more robust solution.
It is similar to ``all_goals``, except it fails unless its argument
succeeds on at least one goal.
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

/-!
The first tactic in the ``by`` block below repeatedly splits
conjunctions:
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

/-!
In fact, we can compress the full tactic down to one line:
-/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

/-!
The combinator ``focus t`` ensures that ``t`` only effects the current
goal, temporarily hiding the others from the scope. So, if ``t``
ordinarily only effects the current goal, ``focus (all_goals t)`` has
the same effect as ``t``.

Rewriting
---------

The ``rewrite`` tactic (abbreviated ``rw``) and the ``simp`` tactic were
introduced briefly in `Calculational
Proofs <./quantifiers_and_equality.md#calculational_proofs>`__. In this
section and the next, we discuss them in greater detail.

The ``rewrite`` tactic provides a basic mechanism for applying
substitutions to goals and hypotheses, providing a convenient and
efficient way of working with equality. The most basic form of the
tactic is ``rewrite [t]``, where ``t`` is a term whose type asserts an
equality. For example, ``t`` can be a hypothesis ``h : x = y`` in the
context; it can be a general lemma, like
``add_comm : ∀ x y, x + y = y + x``, in which the rewrite tactic tries
to find suitable instantiations of ``x`` and ``y``; or it can be any
compound term asserting a concrete or general equation. In the following
example, we use this basic form to rewrite the goal using a hypothesis.
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0

/-!
In the example above, the first use of ``rw`` replaces ``k`` with ``0``
in the goal ``f k = 0``. Then, the second one replaces ``f 0`` with
``0``. The tactic automatically closes any goal of the form ``t = t``.
Here is an example of rewriting using a compound expression:
-/

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h hq]; assumption

/-!
Here, ``h hq`` establishes the equation ``x = y``. The parentheses
around ``h hq`` are not necessary, but we have added them for clarity.

Multiple rewrites can be combined using the notation
``rw [t_1, ..., t_n]``, which is just shorthand for
``rw t_1; ...; rw t_n``. The previous example can be written as follows:
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

/-!
By default, ``rw`` uses an equation in the forward direction, matching
the left-hand side with an expression, and replacing it with the
right-hand side. The notation ``←t`` can be used to instruct the tactic
to use the equality ``t`` in the reverse direction.
-/

example (f : Nat → Nat) (a b : Nat) (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

/-!
In this example, the term ``←h₁`` instructs the rewriter to replace
``b`` with ``a``. In the editors, you can type the backwards arrow as
``\l``. You can also use the ascii equivalent, ``<-``.

Sometimes the left-hand side of an identity can match more than one
subterm in the pattern, in which case the ``rw`` tactic chooses the
first match it finds when traversing the term. If that is not the one
you want, you can use additional arguments to specify the appropriate
subterm.
-/

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

/-!
In the first example above, the first step rewrites ``a + b + c`` to
``a + (b + c)``. Then next applies commutativity to the term ``b + c``;
without specifying the argument, the tactic would instead rewrite
``a + (b + c)`` to ``(b + c) + a``. Finally, the last step applies
associativity in the reverse direction rewriting ``a + (c + b)`` to
``a + c + b``. The next two examples instead apply associativity to move
the parenthesis to the right on both sides, and then switch ``b`` and
``c``. Notice that the last example specifies that the rewrite should
take place on the right-hand side by specifying the second argument to
``Nat.add_comm``.

By default, the ``rewrite`` tactic affects only the goal. The notation
``rw [t] at h`` applies the rewrite ``t`` at hypothesis ``h``.
-/

example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

/-!
The first step, ``rw [Nat.add_zero] at h``, rewrites the hypothesis
``a + 0 = 0`` to ``a = 0``. Then the new hypothesis ``a = 0`` is used to
rewrite the goal to ``f 0 = f 0``.

The ``rewrite`` tactic is not restricted to propositions. In the
following example, we use ``rw [h] at t`` to rewrite the hypothesis
``t : Tuple α n`` to ``t : Tuple α 0``.
-/

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

/-!
Using the Simplifier
--------------------

Whereas ``rewrite`` is designed as a surgical tool for manipulating a
goal, the simplifier offers a more powerful form of automation. A number
of identities in Lean's library have been tagged with the ``[simp]``
attribute, and the ``simp`` tactic uses them to iteratively rewrite
subterms in an expression.
-/

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y))
        : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

/-!
In the first example, the left-hand side of the equality in the goal is
simplified using the usual identities involving 0 and 1, reducing the
goal to ``x * y = x * y``. At that point, ``simp`` applies reflexivity
to finish it off. In the second example, ``simp`` reduces the goal to
``p (x * y)``, at which point the assumption ``h`` finishes it off. Here
are some more examples with lists:
-/

open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
 simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
 simp [Nat.add_comm]

/-!
As with ``rw``, you can use the keyword ``at`` to simplify a hypothesis:
-/

example (x y z : Nat) (p : Nat → Prop)
        (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) := by
  simp at h; assumption

/-!
Moreover, you can use a "wildcard" asterisk to simplify all the
hypotheses and the goal:
-/

attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p  (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption

/-!
For operations that are commutative and associative, like multiplication
on the natural numbers, the simplifier uses these two facts to rewrite
an expression, as well as *left commutativity*. In the case of
multiplication the latter is expressed as follows:
``x * (y * z) = y * (x * z)``. The ``local`` modifier tells the
simplifier to use these rules in the current file (or section or
namespace, as the case may be). It may seem that commutativity and
left-commutativity are problematic, in that repeated application of
either causes looping. But the simplifier detects identities that
permute their arguments, and uses a technique known as *ordered
rewriting*. This means that the system maintains an internal ordering of
terms, and only applies the identity if doing so decreases the order.
With the three identities mentioned above, this has the effect that all
the parentheses in an expression are associated to the right, and the
expressions are ordered in a canonical (though somewhat arbitrary) way.
Two expressions that are equivalent up to associativity and
commutativity are then rewritten to the same canonical form.
-/

# attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
# attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
example (w x y z : Nat) (p : Nat → Prop)
        : x * y + z * w  * x = x * w * z + y * x := by
  simp

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w  * x)) : p (x * w * z + y * x) := by
  simp; simp at h; assumption

/-!
As with ``rewrite``, you can send ``simp`` a list of facts to use,
including general lemmas, local hypotheses, definitions to unfold, and
compound expressions. The ``simp`` tactic also recognizes the ``←t``
syntax that ``rewrite`` does. In any case, the additional rules are
added to the collection of identities that are used to simplify a term.
-/

def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

/-!
A common idiom is to simplify a goal using local hypotheses:
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

/-!
To use all the hypotheses present in the local context when simplifying,
we can use the wildcard symbol, ``*``:
-/

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

/-!
Here is another example:
-/

example (u w x y z : Nat) (h₁ : x = y + z) (h₂ : w = u + x)
        : w = z + y + u := by
  simp [*, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-!
The simplifier will also do propositional rewriting. For example, using
the hypothesis ``p``, it rewrites ``p ∧ q`` to ``q`` and ``p ∨ q`` to
``true``, which it then proves trivially. Iterating such rewrites
produces nontrivial propositional reasoning.
-/

example (p q : Prop) (hp : p) : p ∧ q ↔ q := by
  simp [*]

example (p q : Prop) (hp : p) : p ∨ q := by
  simp [*]

example (p q r : Prop) (hp : p) (hq : q) : p ∧ (q ∨ r) := by
  simp [*]

/-!
The next example simplifies all the hypotheses, and then uses them to
prove the goal.
-/

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *
  simp [*]

/-!
One thing that makes the simplifier especially useful is that its
capabilities can grow as a library develops. For example, suppose we
define a list operation that symmetrizes its input by appending its
reversal:
-/

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

/-!
Then for any list ``xs``, ``reverse (mk_symm xs)`` is equal to
``mk_symm xs``, which can easily be proved by unfolding the definition:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

/-!
We can now use this theorem to prove new results:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
# theorem reverse_mk_symm (xs : List α)
#        : (mk_symm xs).reverse = mk_symm xs := by
#  simp [mk_symm]
example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp [reverse_mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp [reverse_mk_symm] at h; assumption

/-!
But using ``reverse_mk_symm`` is generally the right thing to do, and it
would be nice if users did not have to invoke it explicitly. You can
achieve that by marking it as a simplification rule when the theorem is
defined:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/-!
The notation ``@[simp]`` declares ``reverse_mk_symm`` to have the
``[simp]`` attribute, and can be spelled out more explicitly:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/-!
The attribute can also be applied any time after the theorem is
declared:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp[reverse_mk_symm]

attribute [simp] reverse_mk_symm

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

/-!
Once the attribute is applied, however, there is no way to permanently
remove it; it persists in any file that imports the one where the
attribute is assigned. As we will discuss further in
`Attributes <TBD>`__, one can limit the scope of an attribute to the
current file or section using the ``local`` modifier:
-/

# def mk_symm (xs : List α) :=
#  xs ++ xs.reverse
theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

section
attribute [local simp] reverse_mk_symm

example (xs ys : List Nat)
        : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption
end

/-!
Outside the section, the simplifier will no longer use
``reverse_mk_symm`` by default.

Note that the various ``simp`` options we have discussed --- giving an
explicit list of rules, and using ``at`` to specify the location --- can
be combined, but the order they are listed is rigid. You can see the
correct order in an editor by placing the cursor on the ``simp``
identifier to see the documentation string that is associated with it.

There are two additional modifiers that are useful. By default, ``simp``
includes all theorems that have been marked with the attribute
``[simp]``. Writing ``simp only`` excludes these defaults, allowing you
to use a more explicitly crafted list of rules. In the examples below,
the minus sign and ``only`` are used to block the application of
``reverse_mk_symm``.
-/

def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption

/-!
Extensible Tactics
------------------

In the following example, we define the notation ``triv`` using the
command ``syntax``. Then, we use the command ``macro_rules`` to specify
what should be done when ``triv`` is used. You can provide different
expansions, and the tactic interpreter will try all of them until one
succeeds.
-/

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv

/-!
Exercises
---------

1. Go back to the exercises in `Chapter Propositions and
   Proofs <./propositions_and_proofs.md>`__ and `Chapter Quantifiers and
   Equality <./quantifiers_and_equality.md>`__ and redo as many as you
   can now with tactic proofs, using also ``rw`` and ``simp`` as
   appropriate.

2. Use tactic combinators to obtain a one line proof of the following:
-/

 example (p q r : Prop) (hp : p)
         : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
   admit
