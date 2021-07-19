===================
 MathJax in Sphinx
===================

Using any math on a page causes Sphinx to automatically load MathJax: `e^{i\pi} = -1`:math:.

If you want to highlight pieces of code with MathJax, too, then you can either:

- Use a custom mathjax config script (see the discussion in ``recipes/mathjax.rst``, the configuration in ``conf.py``, and the implementation in ``recipes/sphinx/_static/mathjax_config.js``).  Math in the following snippet is highlighted using this technique; look for the link to ``mathjax_config.js`` in the ``<head>`` of this webpage:

  .. coq::
     :class: coq-math

     Notation "\mathbb{N}" := nat.
     Print nat. (* .unfold *)

- Use a custom script on a single page; this works best if you need MathJax on just one page and you do not need to customize MathJax further.  Math in the following Coq snippet is highlighted that way (view the source of this page to see the custom script):

  .. raw:: html

     <script type="text/javascript">
       document.addEventListener("DOMContentLoaded", () => {
          // Find math blocks
          blocks = document.querySelectorAll(".alectryon-io");

          // Add math delimiters
          blocks.forEach(function (e) {
              e.innerHTML = e.innerHTML.replace(/([\\]mathbb{B})/g, '\\($1\\)');
              e.classList.add("mathjax_process");
          });

          // Force reprocessing if MathJax already ran
          window.MathJax?.typesetPromise?.(blocks);
       });
     </script>

  .. coq::
     :class: coq-math-2

     Notation "\mathbb{B}" := bool.
     Print bool. (* .unfold *)
