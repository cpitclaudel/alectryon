==================
 Body-only output
==================

To compile::

   alectryon --body-only body_only.rst -o body_only.html
       # reST → HTML; produces ‘body_only.html’
   alectryon --body-only --backend latex body_only.rst -o body_only.tex
       # reST → LaTeX; produces ‘body_only.tex’

``--body-only`` keeps only the document’s body (no ``<html>``/``<head>`` for HTML, no preamble or ``\begin{document}`` for LaTeX):

.. coq::

   Print nat.
