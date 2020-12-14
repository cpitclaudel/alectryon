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

Then, we add setup to load MathJax and render notations:

.. raw:: html

   <div>
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

Then, we wrap each conclusion and each hypothesis in math markers, and we load MathJax:

.. raw:: html

   <script type="text/javascript">
     function setup() {
        var spans = document.querySelectorAll(".goal-conclusion .highlight, .goal-hyp .highlight");
        spans.forEach(function (e) {
            var text = e.innerText;
            var node = document.createTextNode('\\[' + text + '\\]');
            e.parentNode.replaceChild(node, e);
        });
     }

     MathJax = {
         options: {
             skipHtmlTags: [
                 'script', 'noscript', 'style', 'textarea',
                 'annotation', 'annotation-xml'
             ]
         },
         startup: {
             pageReady: function () {
                 setup();
                 return MathJax.startup.defaultPageReady();
             }
         }
     };
   </script>

   <style type="text/css"> /* Override MathJax margins */
       .hyp-type > *, .goal-conclusion > * {
           margin: 0 !important;
       }
   </style>

   <script type="text/javascript" id="MathJax-script" async
      src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js">
   </script>

Finally, here's the actual proof:

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
