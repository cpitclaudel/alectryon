==============================
 Using MathJax with Alectryon
==============================

This example shows how to combine Alectryon with MathJax.  We'll do a pretty-printed version of the proof that :math:`\sum_{i = 0}^n i = \frac{n \cdot (n + 1)}{2}`.  Use the following command to compile it::

   alectryon mathjax.rst # reST → HTML; produces ‘mathjax.html’

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
     document.addEventListener("DOMContentLoaded", () => {
        // 1. Find all relevant Alectryon tags
        var spans = document.querySelectorAll(
            ".coq-math .message, " +
            ".coq-math .goal-conclusion, " +
            ".coq-math .hyp-body > span, " +
            ".coq-math .hyp-type > span"
        );

        // 2. Wrap the contents of each in \(\) math delimiters, add mathjax class
        spans.forEach(function (e) {
            e.innerText = '\\[' + e.innerText + '\\]';
            e.classList.add("mathjax_process");
        });

        // 3. If MathJax has already loaded, force reprocessing
        window.MathJax && MathJax.typesetPromise(spans);
     });
   </script>

   <style type="text/css"> /* Override MathJax margins */
       .coq-math .goal-conclusion > *,
       .coq-math .hyp-body span > *,
       .coq-math .hyp-type span > * {
           margin: 0 !important;
       }
   </style>

And finally we write the actual proofs:

.. coq::
   :class: coq-math

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

Configuring MathJax
===================

MathJax needs to be configured before it is loaded.  This makes configuring it particularly tricky when you don't have full control on the generated webpage.

- If you're using Docutils directly through Alectryon's command line, MathJax is loaded with the ``defer`` flag, so you can include a ``<script>`` block with your `MathJax config <https://docs.mathjax.org/en/latest/web/configuration.html>`__ anywhere in the document: use a ``.. raw:: html`` directive, like this::

     .. raw:: html

        <script type="text/javascript">
          MathJax = { options: { … } };
        </script>

- If you're using Sphinx, MathJax is loaded with the `async` flag (see `this issue <https://github.com/sphinx-doc/sphinx/issues/9450>`__), so there's a race condition and you can't depend on your configuration being processed early: you need to move the config to a separate file, or use the ``mathjax3_config`` option of Sphinx if does enough for your needs.  See the tricks in ``recipes/sphinx/conf.py``.

- For other processors like Pelican, you need to either move your configuration to a separate file and make sure that it is loaded first, as in Sphinx, or find a way to defer ``MathJax``.  The following usually works::

   from docutils.writers._html_base import HTMLTranslator
   HTMLTranslator.mathjax_script = '<script type="text/javascript" defer src="%s"></script>\n'


Additional notes and background
===============================

Instead of adding explicit ``mathjax_process`` classes on each math element, you might want to use the ``processHtmlClass`` option of MathJax.  This is more complicated, but here's the process in a nutshell.

1. Configure MathJax to stop ignoring ``<pre>`` blocks by adding a ``MathJax = …`` `config block <http://docs.mathjax.org/en/latest/web/configuration.html>`__::

      MathJax = {}
      MathJax.options = { processHtmlClass: 'mathjax_process|alectryon-io' };

2. Add ``\( … \)`` math markers to tell MathJax where to look::

      MathJax.startup = {
          pageReady: function () {
              // … Custom code to add \( … \) delimiters
              return MathJax.startup.defaultPageReady(); // Then run MathJax
          }
      }

3. Ensure that these definitions are processed *before* MathJax itself is loaded, since it's not easy to `reconfigure MathJax after loading it <http://docs.mathjax.org/en/latest/web/configuration.html#configuring-mathjax-after-it-is-loaded>`__.  Concretely, this means either adding ``defer`` to the MathJax ``<script>`` tag, moving the configuration to a separate script loaded before MathJax, or moving the MathJax ``<script>`` to the end of the file (past the configuration above).

   The problem is that docutils automatically inserts the MathJax ``<script>`` tag for you if you use some math in the document, so you don't have much control over it (if you don't have any ``:math:`` roles then there's no problem: you can include the MathJax script yourself as explained in the previous section).

Alectryon already configures docutils to load MathJax with the ``defer`` option, so the steps above should work reliably when using Alectryon in standalone mode (point [3.] is already taken care of).

Sphinx loads MathJax in ``async`` mode by default, so the above won't work reliably, and the ``mathjax3_config`` option is not always enough (it does not let you customize the ``pageReady`` function; see `Sphinx issue 9450 <https://github.com/sphinx-doc/sphinx/issues/9450>`__).  Instead, put the configuration above in a separate script and include it in ``html_js_files`` with sufficiently low priority (must be < 500).  See `<sphinx/conf.py>`__ and `<sphinx/_static/mathjax_config.js>`__ for an example (you can also inline the body of the script directly in ``conf.py``).
