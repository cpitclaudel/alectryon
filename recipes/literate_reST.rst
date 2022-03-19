==================================================
 Literate programming with Alectryon (reST input)
==================================================

.. raw:: latex

   \makeatletter\def\alectryon@nobreakspace{\alectryon@breakspace}\makeatother

Alectryon supports literate programs and documents (combinations of code and prose) written in Coq and reStructuredText.  Here is an example, written in reST.  It can be converted to Coq, HTML, or LaTeX using the following commands::

   alectryon literate_reST.rst
       # reST+Coq → HTML;  produces ‘literate_reST.html’
   $ DOCUTILSCONFIG=literate.docutils.conf alectryon \
     literate_reST.rst --backend latex
       # reST+Coq → LaTeX; produces ‘literate_reST.tex’
   alectryon literate_reST.rst --backend coq
       # reST+Coq → Coq;   produces ‘literate_reST.v’

   $ cd ..; python -m alectryon.literate --rst2coq \
       recipes/literate_reST.rst > recipes/literate_reST.min.v
     # Minimal reST → Coq; produces ‘literate_reST.min.v’
   $ cd ..; python -m alectryon.literate --rst2coq - \
       < recipes/literate_reST.rst > recipes/literate_reST.min.stdin.v
     # Minimal reST → Coq; produces ‘literate_reST.min.stdin.v’

----

Coq fragments are introduced with ``.. coq::``:

.. coq::

   Lemma le_l : forall y x, S x <= y -> x <= y.
     induction y; inversion 1; subst.
     all: info_eauto.
   Qed.

   Goal forall x y z, x <= y <= z -> x <= z.

They can be nested nested into other reST directives, such as tables:

.. list-table:: Coq commands
   :header-rows: 1
   :width: 90%

   - * Coq command
     * Description

   - *
       .. coq:: unfold

            intros x y.

     * Move the variables `x` and `y` into the context.

   - *
       .. coq:: unfold

            revert x; induction y.

     * Perform induction on `y`, generalizing `x`.

   - *
       .. coq:: unfold

            all: intros x z (Hl & Hr).

     * Move conjunction into the context, splitting it into `Hl` and `Hr`.

   - *
       .. coq:: unfold

            - inversion Hl; assumption.

     * Solve base case; `inversion` changes `x <= 0` into `x = 0`.

   - *
       .. coq:: unfold

            - inversion Hl; subst; try congruence.
              apply IHy; split; info_eauto using le_l.

     * Solve inductive case using the `le_l` lemma.

