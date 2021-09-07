==============
 Proof Engine
==============

To compile::

   alectryon literate_easycrypt.ec.rst
       # reST → HTML; produces ‘literate_easycrypt.html’
   $ DOCUTILSCONFIG=literate.docutils.conf alectryon \
     literate_easycrypt.ec.rst --backend latex
       # reST → HTML; produces ‘literate_easycrypt.tex’

.. default-role:: easycrypt
.. |EasyCrypt| replace:: EasyCrypt

|EasyCrypt|’s proof engine works with goal lists, where a *goal* has
two parts:

-  A *context* consisting of a

   -  a set of type variables, and

   -  an *ordered* set of *assumptions*, consisting of identifiers with
      their types, memories, module names with their module types and
      restrictions, local definitions, and *hypotheses*, i.e., formulas.
      An identifier’s type may involve the type variables, the local
      definitions and formulas may involve the type variables,
      identifiers, memories and module names.

-  A *conclusion*, consisting of a single formula, with the same
   constraints as the assumption formulas.

Informally, to prove a goal, one must show the conclusion to be true,
given the truth of the hypotheses, for all valid instantiations of the
assumption identifiers, memories and module names.

For example, the following is a goal:

.. easycrypt:: none unfold

    lemma PairEq0 ['a, 'b] :
      forall (x x' : 'a) (y y' : 'b),
      x = x' => y = y' => (x, y) = (x', y').
    proof.
      move=> x x' y y'.
      move=> eq_xx' eq_yy'. (* .out *)
      rewrite eq_xx' eq_yy'.
      reflexivity.
    qed.

And, in the context of the following declarations:

.. easycrypt::

   require import Bool Int IntDiv Real. (* .none *)
   module type T = {
     proc f() : unit
   }.
   module G(X : T) = {
     var x : int
     proc g() : unit = {
       X.f();
     }
   }.

… the following is a goal:

.. easycrypt:: none unfold

   lemma Invar (X <: T{G}) (n : int) :
     islossless X.f =>
     phoare [G(X).g : G.x = n ==> G.x = n] = 1%r.
   proof.
     move=> LL.
     proc. (* .out *)
     call (_ : true).
     skip.
     trivial.
   qed.

The conclusion of this goal is just a nonlinear rendering of the following
formula, as |EasyCrypt|’s pretty printer renders *pRHL*, *pHL* and *HL*
judgements in such a nonlinear style when the judgements appear as (as opposed
to in) the conclusions of goals

.. code-block:: easycrypt

   phoare [G(X).g : G.x = n ==> G.x = n] = 1%r.

Internally, |EasyCrypt|’s proof engine also works with *pRHL*,
*pHL* and *HL* judgments involving lists of statements rather than
procedure names, which we’ll call *statement judgements*, below. For
example, take the following declaration:

.. easycrypt::

   module M = {
     proc f(y : int) = {
       if (y %% 3 = 1) y <- y + 4;
       else y <- y + 2;
       return y;
     }
   }.

This is a *pHL* statement judgement:

.. easycrypt:: none unfold

   lemma L (x : int) :
     x = 1 \/ x = 2 =>
     hoare[M.f : y %% 3 = x ==> res %% 3 = (x %% 2) + 1].
   proof.
    move=> zor1_x.
    proc.
    if. (* .out *)
   abort.

The pre- and post-conditions of a statement judgement may refer to the
parameters and local variables of the *procedure context* of the
conclusion—\ `M.f` in the preceding example. They may also refer to
the memories `&1` and `&2` in the case of *pRHL* statement
judgements. When a statement judgement appears anywhere other than as
the conclusion of a goal, the pretty printer renders it in abbreviated
linear syntax. E.g., the preceding goal is rendered as

.. code-block:: easycrypt

   hoare[if (x %% 3 = 1) {...} : x %% 3 = n ==> x %% 3 = n %% 2 + 1]

Statement judgements can’t be directly input by the user.

We use the term *program* to refer to *either* a procedure appearing in
a *pRHL*, *pHL* or *HL* judgement, *or* a statement list
appearing in a *pRHL*, *pHL* or *HL* statement judgement. In
the case of *pRHL* (statement) judgements, we speak of the *left* and
*right* programs, also using *program 1* for the left program, and
*program 2* for the right one. We will only speak of a program’s
*length* when it’s a statement list we are referring to. By the *empty*
program, we mean the statement list with no statements.

When the proof of a lemma is begun, the proof engine starts out with a
single goal, consisting of the lemma’s statement:

.. easycrypt:: unfold

   lemma PairEq ['a, 'b] :
     forall (x x' : 'a) (y y' : 'b),
     x = x' => y = y' => (x, y) = (x', y').
   abort. (* .none *)

For parameterized lemmas, the goal includes the lemma’s parameters as
assumptions. E.g.,

.. easycrypt:: unfold

   lemma PairEq_param (x x' : 'a) (y y' : 'b) :
     x = x' => y = y' => (x, y) = (x', y').
   abort. (* .none *)

|EasyCrypt|’s tactics, when applicable, reduce the first goal to zero or
more subgoals.  Here is a detailed example.  We start with a lemma
statement:

.. easycrypt:: unfold

   lemma L (x : int) :
     x = 1 \/ x = 2 =>
     hoare[M.f : y %% 3 = x ==> res %% 3 = (x %% 2) + 1].

Then, we proceed through the proof step by step:

.. easycrypt:: unfold

   proof.
     move=> zor1_x.
     proc.

The `proof` command :mref:`.s(proof)` starts the tactic script.  The `move` :mref:`.s(move)` then introduces the left part of the implication into the context, creating hypothesis :mquote:`.s(move).h(x = 1)` (:mref:`.s(move).h(x = 1)`).  The following tactic, `proc` :mref:`.s(proc)`, unfold `M.f` and displays its code.  Given that the code includes a branch, we then invoke the `if` tactic, which creates two goals: one for the `if` branch and one for the `else` branch:

.. easycrypt:: unfold

     if. (* .out *)

We handle both goals in the same way; first, the `if` branch:

.. easycrypt:: unfold

       wp.
       skip.
       smt. (* -.g#1 *)

The `wp` tactic :mref:`.s(wp)` runs a weakest-precondition calculation, consuming the program and yielding a new postcondition; then `skip` :mref:`.s(skip)` transforms the statement judgment about an empty program into a logic formula, and finally the `smt` tactic :mref:`.s(smt)` solves the goal using
SMT provers, leaving no subgoals for this branch.

We solve the `else` branch in the same way;

.. easycrypt::

       wp.
       skip.
       smt.

A finally, the lemma’s proof may be saved, using the step `qed`, when
the list of goals becomes empty. And this must be done before anything
else may be done.

.. easycrypt:: unfold

   qed.

Here is how the proof of the pair-equality lemma goes:

.. easycrypt:: unfold

   lemma PairEq ['a, 'b] :
     forall (x x' : 'a) (y y' : 'b),
     x = x' => y = y' => (x, y) = (x', y').
   proof.
     move=> x x' y y'.
     move=> eq_xx' eq_yy'.
     rewrite eq_xx' eq_yy'.
     reflexivity.
   qed.

.. note::

   Applying a tactic may fail; in this case an error message is issued and
   the list of goals is left unchanged.

   .. FIXME: needs a way to allow errors in compilation mode too.

      For example:

      .. easycrypt::

         lemma eq_refl ['a] (x: 'a) : x = x.
         proof.
           move=> y. (* .unfold *)
         abort.
