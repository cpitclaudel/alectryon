==================
 Using references
==================

To compile::

   $ alectryon references.rst
       # ReST → HTML; produces ‘references.html’
   $ DOCUTILSCONFIG=references.docutils.conf alectryon \
       references.rst -o references.xe.tex --latex-dialect xelatex
       # ReST → HTML; produces ‘references.xe.tex’

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

    - Bullets (``-``, ``+``, ``*``) delimit subproofs (:mref:`#setup.s(Base case)`, :mref:`Induction`)
    - It all started at :mref:`#setup.s(Fixpoint)`

Custom counter styles can be defined like using the ``.. role::`` directive and the ``:counter-style:`` option:

.. role:: aref(mref)
   :counter-style: lower-greek

.. role:: jref(mref)
   :counter-style: _ い ろ は に ほ へ と ち り ぬ る を わ か よ た れ そ つ ね な ら む う ゐ の お く や ま け ふ こ え て あ さ き ゆ め み し ゑ ひ も せ す

Here is how it looks:

    The following commands print information about an identifier :aref:`#cp.s(About)`, print its definition :aref:`#cp.s(Print)`, and compute the type of a term :aref:`#cp.s(Check)` or its reduction :aref:`#cp.s(Compute)`.

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

    The second batch of commands perform reduction with a custom strategy: :jref:`#cp.s(simpl)` :jref:`#cp.s(cbn)` :jref:`#cp.s(cbv)` :jref:`#cp.s(lazy)` :jref:`#cp.s(vm_compute)` :jref:`#cp.s(pattern)`.

Each inline reference is a link to the corresponding code fragment.
