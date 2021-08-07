==========================================
 Using the marker-placement mini-language
==========================================

To compile::

   $ alectryon references.rst
       # ReST → HTML; produces ‘references.html’
   $ DOCUTILSCONFIG=references.docutils.conf alectryon \
       references.rst -o references.xe.tex --latex-dialect xelatex
       # ReST → HTML; produces ‘references.xe.tex’

Referring to parts of a goal
============================

Alectryon supports references to individual sentences and hypotheses within a code fragment.  The easiest way to reference a sentence is to use :literal:`:mref:\`search-term\``.  Alectryon will search for that text and automatically add a label to the first matching sentence of the proof.  For example:

    .. coq::
       :name: setup

       Fixpoint plus_comm (n m: nat) {struct n} : n + m = m + n.
       Proof.
         destruct n eqn:Heq. (* .unfold *)
         - (* Base case *)
           rewrite <- plus_n_O; reflexivity.

    The `Fixpoint` command (:mref:`Fixpoint plus_comm`) indicates that we are beginning an inductive proof.

Optionally, the label can be picked manually, using :literal:`:mref:\`label <target>\``:

    The proof starts with a case analysis, indicated by “:mref:`◉ <destruct n>`”.

Instead of whole sentences, is possible to refer to individual goals and hypotheses:

    In the first case (:mref:`.s(destruct n).g#1`), we see the variable `n` in the context (:mref:`.s(destruct n).g#1.h#n`), and we see that it is `0` (:mref:`.s(destruct n).g#1.h(n = 0)`); notice how the conclusion of the first goal :mref:`.s(destruct n).ccl` does not mention `n` (it says `0` instead).  In the second case :mref:`.s(destruct n).g(S n0)`, the conclusion (:mref:`.s(destruct n).g{*S n0*}.ccl`) mentions `S n0` instead.

Note that we can safely refer multiple times to the same object, even using a different reference:

    - :mref:`.s(destruct n).g#1.h#plus_comm`
    - :mref:`.s(destruct n).h#plus_comm`
    - :mref:`.s(destruct n).h(forall)`
    - :mref:`.s(destruct n).h{forall*}`

To allow forward- and back-references, counters are not reset from one block to the next:

    .. coq::

         - (* Induction *)
           simpl.
           rewrite (plus_comm n0).
           rewrite plus_n_Sm.
           reflexivity.
       Qed.

    - Bullets (``-``, ``+``, ``*``) delimit subproofs (:mref:`.io#setup.s(Base case)`, :mref:`Induction`)
    - It all started at :mref:`.io#setup.s(Fixpoint)`

Custom counter styles can be defined like using the ``.. role::`` directive and the ``:counter-style:`` option:

.. role:: aref(mref)
   :counter-style: lower-greek

.. role:: jref(mref)
   :counter-style: _ い ろ は に ほ へ と ち り ぬ る を わ か よ た れ そ つ ね な ら む う ゐ の お く や ま け ふ こ え て あ さ き ゆ め み し ゑ ひ も せ す

Here is how it looks:

    The following commands print information about an identifier :aref:`.io#cp.s(About)`, print its definition :aref:`.io#cp.s(Print)`, and compute the type of a term :aref:`.io#cp.s(Check)` or its reduction :aref:`.io#cp.s(Compute)`.

    .. coq::
       :name: cp

       About Nat.add.
       Print Nat.add.
       Check Nat.add 2 3.
       Compute Nat.add 2 3.

       Eval simpl in Nat.add 2 3.
       Eval cbn in Nat.add 2 3.
       Eval cbv in Nat.add 2 3.
       Eval lazy in Nat.add 2 3.
       Eval vm_compute in Nat.add 2 3.
       Eval pattern 2 in Nat.add 2 3.

    The second batch of commands perform reduction with a custom strategy: :jref:`.io#cp.s(simpl)` :jref:`.io#cp.s(cbn)` :jref:`.io#cp.s(cbv)` :jref:`.io#cp.s(lazy)` :jref:`.io#cp.s(vm_compute)` :jref:`.io#cp.s(pattern)`.

Each inline reference is a link to the corresponding code fragment.

Using references to customize display (**experimental**)
========================================================

References can also be used to customize the display of goals and hypotheses.  In the following, hypotheses whose name start with ``l`` are omitted, and so are hypotheses named ``a`` and ``A``.  After the call to ``induction`` (:mref:`.io#pr.s(induction 1)`) the output is further limited to just goals 2 and 4, by excluding all goals and re-including only 2 and 4.  In goal 4, hypotheses whose type is exactly ``list A`` are shown, regardless of previous status, so ``l``, ``l'``, ``l''`` are visible (:mref:`.io#pr.s(induction 1).g#4.h#l`).

    .. coq:: -.h#l* -.h#[aA]
       :name: pr

       Require Import Coq.Sorting.Permutation. (* .none *)
       Theorem Permutation_In {A} (l l' : list A) (a: A) :
         Permutation l l' -> List.In a l -> List.In a l'. (* .unfold *)
       Proof.
         induction 1; intros * Hin. (* .unfold -.g#* .g#2 .g#4 .g#4.h{list A} *)
         all: simpl in *; tauto.
       Qed.
