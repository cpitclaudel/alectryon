An Introduction to Lean
=======================

.. alectryon-toggle::

.. note::

   The original document is at https://leanprover.github.io/introduction_to_lean/

1 Overview
----------

This introduction offers a tour of Lean and its features, with a number
of examples for you to play around with and explore. If you are reading
this in our online tutorial system, you can run examples like the one
below by clicking the button that says “try it yourself.”

.. lean3::

    #check "hello world!"

The response from Lean appears in the small window underneath the editor
text, and also in popup windows that you can read when you hover over
the indicators in the left margin. Alternatively, if you have installed
Lean and have it running in a stand-alone editor, you can copy and paste
examples and try them there.

1.1 Perspectives on Lean
~~~~~~~~~~~~~~~~~~~~~~~~

Lean is an implementation of a logical foundation known as *dependent
type theory*. Specifically, it implements a version of dependent type
theory known as the *Calculus of Inductive Constructions*. The *CIC* is
a formal language with a small and precise set of rules that governs the
formation of expressions. In this formal system, moreover, every
expression has a *type*. The type of expression indicates what sort of
object the expression denotes. For example, an expression may denote a
mathematical object like a natural number, a data type, an assertion, or
a proof.

Lean has a small and carefully written kernel, which serves to check
that an expression is well-formed and confirm that it has a given type.
It is this kernel that gives Lean its special character. Dependent type
theory serves as a foundational language, allowing us to describe all
sorts of objects and prove things about them. The foundational language
fixes the meaning of the objects we introduce, and the kernel ensures
that the things we prove about them are correct.

Put simply, Lean is designed to help you construct, manipulate, and
check expressions in this foundational language. This may not sound like
much, but what makes the system powerful is the fact that dependent type
theory is expressive enough to allow us to define and reason about all
sorts of objects. For example, Lean’s standard library defines the
natural numbers to be the structure generated freely and inductively by
a constant, *zero*, and a unary function *succ*:

.. lean3::

   namespace hidden
     inductive nat : Type
     | zero : nat
     | succ : nat → nat

If you copy this definition into the editor window at right you will see
that we have wrapped it in a *namespace* to avoid conflicting with the
standard definition, which is loaded by default. Even so, choosing the
name ``nat`` means that within the namespace this identifier is
overloaded, which can cause confusion. Thus we will do this only
sparingly, for purposes of illustration.

Having specified this data type, we can go on to define addition by
recursion on the second argument:

.. lean3::

     def add : nat → nat → nat
     | m nat.zero     := m
     | m (nat.succ n) := nat.succ (add m n)
   end hidden

Lean compiles definitions like these down to a single axiomatic
primitive that governs use of both induction and recursion on
inductively defined structures. The library defines notation for the
data type, as well as for ``zero`` and ``add``. (In fact, Lean uses
*type classes*, a very handy mechanism used by functional programming
languages like Haskell, to share notation and properties across
algebraic structures.) Lean uses the Unicode character ``ℕ`` as
alternative notation for the type ``nat``. You can enter this in an
editor by writing ``\nat``.

Of course, we can also define non-recursive functions by giving an
explicit definition:

.. lean3::

   def double (n : ℕ) : ℕ := n + n

We can then go on to define other data types like the integers, the
rationals, and the real numbers, the booleans, characters and strings,
lists, products, disjoint sums, and so on. We can also define algebraic
structures like groups, rings, fields, vector spaces, and categories. In
fact, dependent type theory was designed to serve as a foundation for
all conventional mathematics.

This points to a first intended use of Lean: it serves as a
*specification language*, that is, a means to specify and define
mathematical objects in precise terms. With these specifications, Lean
can interpret basic objects and infer their types:

.. lean3::

   #check (27 + 9) * 33
   #check [(1, 2), (3, 4), (5, 6)] ++ [(7, 8), (9, 10)]

When there is no other information present to constrain the type of a
numeral, Lean assumes it denotes a natural, by default. Thus Lean can
recognize that the first expression denotes a natural number, and that
the second, a concatenation of two lists of pairs of natural numbers, is
again a list of pairs. It also remembers that ``double`` is a function
from the natural numbers to the natural numbers, and can print out the
definition when requested to do so:

.. lean3::

   #check double
   #print double

Lean can reason about abstract objects as well as it can reason about
concrete ones. In the following example, we declare a type ``G`` with a
group structure, and variables ``g₁`` and ``g₂`` that range over ``G``.
With those declarations, Lean knows that the expression
``g₂⁻¹ * g₁ * g₂`` denotes an element of ``G``.

.. lean3::

   section
     variables (G : Type) [has_mul G] [has_inv G]

     variables g₁ g₂ : G

     #check g₂⁻¹ * g₁ * g₂
   end

Putting the declarations in a ``section``, as we do here, delimits their
scope. In this case, the section declaration is not needed, and no harm
would be done if we had declared these variables at the top level.

An important feature of dependent type theory is that every expression
has a computational interpretation, which is to say, there are rules
that specify how they can be *reduced* to a normal form. Moreover,
expressions in a computationally pure fragment of the language evaluate
to *values* in the way you would expect. For example, assuming the
definition does not depend on nonconstructive components in an essential
way, every closed term of type ``ℕ`` evaluates to a numeral. Lean’s
kernel can carry out this evaluation:

.. lean3::

   #eval (27 + 9) * 33

As part of the kernel, the results of this evaluation can be highly
trusted. The evaluator is not very efficient, however, and is not
intended to be used for substantial computational tasks. For that
purpose, Lean also generates bytecode for every definition of a
computable object, and can evaluate it on demand. To process the
bytecode quickly, it uses an efficient *virtual machine*, similar to the
ones used to interpret OCaml and Python.

.. lean3::

   #eval (27 + 9) * 33
   #eval (2227 + 9999) * 33
   #eval double 9999
   #eval [(1, 2), (3, 4), (5, 6)] ++ [(7, 8), (9, 10)]

Relying on results from the bytecode evaluator requires a higher level
of trust than relying on the kernel. For example, for efficiency, the
bytecode evaluator uses the GNU multiple precision library to carry out
numerical computations involving the natural numbers and integers, so
the correctness of those computations are no longer underwritten by the
axiomatic foundation.

This points to a second intended use of Lean, namely, as a *programming
language*. Because dependent type theory is so expressive, we can make
use of all the usual methods and techniques of functional programming,
including higher types, type classes, records, monads, and other
abstractions. In fact, we have the entire Lean library at our disposal.
With just a few lines of code, we can write a generic sort procedure
that sorts elements of a list according to a specified binary relation
``r`` on an arbitrary type ``α``, assuming only that we can determine
computationally when ``r`` holds.

.. lean3::

   section sort
     universe u
     parameters {α : Type u} (r : α → α → Prop) [decidable_rel r]
     local infix `≼` : 50 := r

     def ordered_insert (a : α) : list α → list α
     | []       := [a]
     | (b :: l) := if a ≼ b then a :: (b :: l) else b :: ordered_insert l

     def insertion_sort : list α → list α
     | []       := []
     | (b :: l) := ordered_insert b (insertion_sort l)
   end sort

For foundational reasons, types in Lean have to be stratified into a
hierarchy of *type universes*, and the definitions above work for any
type ``α`` in any such universe. We can run the procedure above on a
list of natural numbers, using the usual ordering:

.. lean3::

   #eval insertion_sort (λ m n : ℕ, m ≤ n) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12]

Substantial programs can be written in Lean and run by the bytecode
interpreter. In fact, a full-blown `resolution theorem
prover <https://github.com/leanprover/super>`__ for Lean has been
written in Lean itself.

You can profile your code by setting the relevant options:

.. lean3::

   set_option profiler true set_option profiler.freq 10

The second option determines the frequency that the virtual machine is
polled with. Be careful: if the task you profile is too short, there
won’t be any output! You can even implement your own
`debugger <https://github.com/leanprover/lean/tree/master/library/tools/debugger>`__
in Lean itself.

What makes Lean special as a programming language is that the programs
we write define functions in a precise axiomatic framework. Which brings
us to third, and central, intended use of Lean: namely we can make
assertions about the objects we define and then go on to prove those
assertions. We can do this because the language of dependent type theory
is rich enough to encode such assertions and proofs. For example, we can
express the property that a natural number is even:

.. lean3::

   def even (n : ℕ) : Prop := ∃ m, n = 2 * m

As presented, it is not clear that the property of being even is
decidable, since we cannot in general test every natural number to
determine whether any of them serves as a witness to the given
existential statement. But we can nonetheless use this definition to
form compound statements:

.. lean3::

   #check even 10
   #check even 11
   #check ∀ n, even n ∨ even (n + 1)
   #check ∀ n m, even n → even m → even (n + m)

In each case, the expression has type ``Prop``, indicating that Lean
recognizes it as an assertion.

Incidentally, of course, we do know that the property of being
``even n`` is algorithmically decidable. We can develop any algorithm we
want for that purpose. Provided we can prove that it behaves as
advertised, we can then use Lean’s type class mechanism to associate
this decision procedure to the predicate. Once we do so, we can use the
predicate ``even`` in conditional statements in any program.

In any case, in order to *prove* assertions like the ones above (at
least, the ones that are true), we need a proof language. Fortunately,
dependent type theory can play that role: proofs are nothing more than
certain kinds of expressions in the formal language. In the encoding
used, if ``p`` is any proposition, a proof of ``p`` is just an
expression ``e`` of type ``p``. Thus, in Lean, checking a proof is just
a special case of checking that an expression is well-formed and has a
given type. We can prove that 10 is even as follows:

.. lean3::

   example : even 10 := ⟨5, rfl⟩

In general, to prove an existential statement, it is enough to present a
witness to the existential quantifier and then show that the subsequent
claim is true of that witness. The Unicode angle brackets just package
this data together; you can enter them in an editor with ``\<`` and
``\>``, or use the ASCII equivalents ``(|`` and ``|)``. The second
component, ``rfl``, is short for reflexivity. Lean’s kernel can verify
that ``10 = 2 * 5`` by reducing both sides and confirming that they are,
in fact, identical. (For longer expressions, Lean’s simplifier, which
will be discussed below, can do this more efficiently, producing a proof
instead that carries out the calculation using binary representations.)

As noted above, dependent type theory is designed to serve as a
mathematical foundation, so that any conventional mathematical assertion
can be reasonably expressed, and any theorem that can be proved using
conventional mathematical means can be carried out formally, with enough
effort. Here is a proof that the sum of two even numbers is even:

.. lean3::

   -- theorem even_add : ∀ m n, even m → even n → even (n + m) :=
   --   take m n,
   --   assume ⟨k, (hk : m = 2 * k)⟩,
   --   assume ⟨l, (hl : n = 2 * l)⟩,
   --   have n + m = 2 * (k + l),
   --     by simp [hk, hl, mul_add],
   --   show even (n + m),
   --     from ⟨_, this⟩

Again, we emphasize that the proof is really just an expression in
dependent type theory, presented with syntactic sugar that makes it look
somewhat like any informal mathematical proof. There is also a tiny bit
of automated reasoning thrown in: the command ``by simp`` calls on
Lean’s built-in simplifier to prove the assertion after the ``have``,
using the two facts labelled ``hk`` and ``hl``, and the distributivity
of multiplication over addition.

Lean supports another style of writing proofs, namely, using *tactics*.
These are instructions, or procedures, that tell Lean how to construct
the requisite expression. Here is a tactic-style proof of the theorem
above:

.. lean3::

   axiom mul_add: ∀ m n p: nat, m * (n + p) = m * n + m * p
   axiom add_sym: ∀ m n: nat, n + m = m + n

   theorem even_add : ∀ m n, even m → even n → even (n + m) :=
   begin
     intros m n hm hn,
     cases hm with k hk,
     cases hn with l hl,
     unfold even,
     existsi (k + l),
     simp [hk, hl, mul_add, add_sym]
   end

Just as we can prove statements about the natural numbers, we can also
reason about computer programs written in Lean, because these, too, are
no different from any other definitions. This enables us to specify
properties of computer programs, prove that the programs meet their
specifications, and run the code with confidence that the results mean
what we think they mean.

The use of ``simp`` in the proof above points to another aspect of Lean,
namely, that it can serve as a gateway to the use of automated
reasoning. Terms in dependent type theory can be very verbose, and
formal proofs can be especially long. One of Lean’s strengths is that it
can help you construct these terms, and hide the details from you. We
have already seen hints of this: in the examples above, Lean inferred
the fact that the natural numbers form an instance of a semiring in
order to make use of the theorem ``mul_add``, it found a procedure for
comparing two natural numbers when we applied ``insertion_sort`` with
the less-than ordering, and it did some work behind the scenes (though
in this case, not much) when transforming the recursive specification of
addition on the natural numbers to a formal definition. But a central
goal of the Lean project is to develop powerful automation that will
assist in the verification of programs and the construction of proofs as
well.

It is the tactic framework that serves as a gateway to the use of
automation. Lean provides means of implementing automated reasoning
procedures in such a way that they produce formal proofs that their
results are correct. This imposes an extra burden on the implementation,
but it comes with benefits as well: automated procedures can make full
use of the Lean library and API, and the formal justifications they
produce provide a strong guarantee that the results are indeed correct.

Which brings us to yet another aspect of Lean, namely, its role as a
*metaprogramming language*. Many of Lean’s internal data structures and
procedures are exposed and available within the language of Lean itself,
via a monadic interface. We refer to the use of these procedures as
“metaprogramming” because they take us outside the formal framework: the
access points to the API are declared as constants, and the formal
framework knows nothing about them, other than their type. Lean keeps
track of which objects in the environment are part of the trusted kernel
and which make use of this special API, and requires us to annotate the
latter definitions with the special keyword ``meta``. The virtual
machine, however, handles calls to the API appropriately. This makes it
possible to write Lean tactics in Lean itself.

For example, the procedure ``contra_aux`` searches through two lists of
expressions, assumed to be hypotheses available in the context of a
tactic proof, in search of a pair of the form ``h₁ : p`` and
``h₂ : ¬ p``. When it finds such a pair, it uses it to produce a proof
of the resulting theorem. The procedure ``contra`` then applies
``contra_aux`` to the hypotheses in the local context.

.. lean3::

   open expr tactic

   private meta def contra_aux : list expr → list expr → tactic unit
   | []         hs := failed
   | (h₁ :: rs) hs :=
     do t₀ ← infer_type h₁,
        t  ← whnf t₀,
        (do a ← match_not t,
            h₂ ← find_same_type a hs,
            tgt ← target,
            pr ← mk_app `absurd [tgt, h₂, h₁],
            exact pr)
        <|> contra_aux rs hs

   meta def contra : tactic unit :=
   do ctx ← local_context,
      contra_aux ctx ctx

Having defined this procedure, we can then use it to prove theorems:

.. lean3::

   example (p q r : Prop) (h₁ : p ∧ q) (h₂ : q → r) (h₃ : ¬ (p ∧ q)) : r :=
     by contra

The results of such a tactic are always checked by the Lean kernel, so
they can be trusted, even if the code itself is buggy. If the kernel
fails to type check the resulting term, it raises an error, and the
resulting theorem is not added to the environment.

Substantial tactics can be written in such a way, even, as noted above,
a full-blown resolution theorem prover. Indeed, many of Lean’s core
tactics *are* implemented in Lean itself. The code from ``contra`` above
is, in fact, part of the ``contradiction`` tactic that is part of Lean’s
standard library. Thus Lean offers a language for expressing not just
mathematical knowledge, construed as a body of definitions and theorems,
but also other kinds of mathematical expertise, namely the algorithms,
procedures, and heuristics that are part and parcel of mathematical
understanding.

1.2 Where To Go From Here
~~~~~~~~~~~~~~~~~~~~~~~~~

We have surveyed a number of ways that Lean can be used, namely, as

-  a specification language
-  a programming language
-  an assertion language
-  a proof language
-  a gateway to using automation with fully verified results, and
-  a metaprogramming language.

Subsequent chapters provide a compendium of examples for you to play
with and enjoy. These chapters are fairly short on explanation, however,
and are not meant to serve as definitive references. If you are
motivated to continue using Lean in earnest, we recommend continuing,
from here, to either of the following more expansive introductions:

-  `Theorem Proving in
   Lean <https://leanprover.github.io/theorem_proving_in_lean>`__
-  `Programming in
   Lean <https://leanprover.github.io/programming_in_lean/>`__

The first focuses on the use of Lean as a theorem prover, whereas the
second focuses on aspects of Lean related to programming and
metaprogramming.
