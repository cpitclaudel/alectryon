===================
 MathJax in Sphinx
===================

Using any math on a page causes Sphinx to automatically load MathJax: `e^{i\pi} = -1`:math:.

If you want to highlight pieces of code with MathJax, too, then see ``README.rst`` and the implementation of ``_static/mathjax_config.js``:

.. coq::
   :class: coq-math

   Notation "\mathbb{N}" := nat.
   Print nat. (* .unfold *)
