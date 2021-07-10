==============================
 Using MathJax with Alectryon
==============================

This example shows how to combine Alectryon with MathJax.  We'll do a pretty-printed version of the proof that :math:`\sum_{i = 0}^n i = \frac{n \cdot (n + 1)}{2}`.

First, we start with a definition of ``sum``:

.. coq::

   Require Import Coq.Unicode.Utf8. (* .none *)
   Require Import NArith ArithRing.

   Fixpoint nsum max f :=
     match max with
     | O => f 0
     | S max' => f max + nsum max' f
     end.

Then, we add notations to print LaTeX code (this is only one way to do it; another way would be to parse Coq's output to reconstruct LaTeX):

.. coq::

   Notation "'\ccNat{}'" := nat.
   Notation "'\ccSucc{' n '}'" := (S n).
   Infix "\times" := mult
     (at level 30).
   Notation "'\ccNsum{' x '}{' max '}{' f '}'" :=
     (nsum max (fun x => f))
       (format "'\ccNsum{' x '}{' max '}{' f '}'").
   Notation "\ccNot{ x }" := (not x)
     (at level 100).
   Infix "\wedge" := and
     (at level 190, right associativity).
   Notation "A \Rightarrow{} B" := (∀ (_ : A), B)
     (at level 200, right associativity).
   Notation "'\ccForall{' x .. y '}{' P '}'" := (∀ x, .. (∀ y, P) ..)
     (at level 200, x binder, y binder, right associativity,
      format "'\ccForall{' x .. y '}{' P '}'").

Then, we add MathJax definitions for each of these custom macros (look at the page source to see them):

.. raw:: html

   <div style="display: none">
       \(\newcommand{\ccQ}{\mathbb{Q}}\)
       \(\newcommand{\ccNat}{\mathbb{N}}\)
       \(\newcommand{\ccSucc}[1]{\mathrm{S}\:#1}\)
       \(\newcommand{\ccFrac}[2]{\frac{#1}{#2}}\)
       \(\newcommand{\ccPow}[2]{{#1}^{#2}}\)
       \(\newcommand{\ccNot}[1]{{\lnot #1}}\)
       \(\newcommand{\ccEvar}[1]{\textit{\texttt{#1}}}\)
       \(\newcommand{\ccForall}[2]{\forall \: #1. \; #2}\)
       \(\newcommand{\ccNsum}[3]{\sum_{#1 = 0}^{#2} #3}\)
   </div>

Then we set up MathJax to render the proofs properly (look at the page source to see the relevant script):

.. raw:: html

   <script type="text/javascript">
     function addMathDelimiters() {
        // 1. Find all relevant Alectryon tags
        var spans = document.querySelectorAll(".goal-conclusion .highlight, .goal-hyps > div .highlight");

        // 2. Wrap the contents of each in \(\) math delimiters
        spans.forEach(function (e) {
            e.innerText = '\\[' + e.innerText + '\\]';
        });
     }

     MathJax = {
         options: {
             // Alectryon code is wrapped in <pre> blocks, so MathJax would skip
             // them if we didn't add an exception for 'alectryon-io'
             processHtmlClass: 'alectryon-io'
         },
         startup: {
             pageReady: function () {
                 addMathDelimiters(); // First add \(\) math delimiters
                 return MathJax.startup.defaultPageReady(); // Then run MathJax
             }
         }
     };
   </script>

   <style type="text/css"> /* Override MathJax margins */
       .goal-conclusion .highlight > *, .goal-hyps > div .highlight > * {
           margin: 0 !important;
       }
   </style>

And finally we write the actual proofs:

.. coq::

   Lemma Gauss: ∀ n,
       2 * (nsum n (fun i => i)) = n * (n + 1).
     induction n; cbn [nsum].
     - (* n ← 0 *)
       reflexivity.
     - (* n ← S _ *)
       rewrite Mult.mult_plus_distr_l.
       rewrite IHn.
       ring.
   Qed.

Note that Alectryon loads MathJax with the ``defer`` attribute, so if you need to call ``MathJax.typeset()`` or ``MathJax.typesetPromise()``, you'll want to do that from a deferred script or from a ``DOMContentLoaded`` event listener.
