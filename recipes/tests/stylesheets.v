(*|
======================================
 Stylesheets and Pygments stylesheets
======================================

To compile::

   $ DOCUTILSCONFIG=tests/stylesheets.docutils.conf \
       alectryon stylesheets.v --pygments-style emacs -o - \
       | sed -r '/^ *<style type="text.css">/,/^ *<.style>/ { /^ *<style |<.style>|Alectryon/b; d}' \
       > stylesheets.html
     # reST → HTML; produces ‘stylesheets.html’

   $ DOCUTILSCONFIG=tests/stylesheets.docutils.conf \
       alectryon stylesheets.v --pygments-style emacs --backend latex -o - \
       | sed -r '/^% embedded stylesheet/,/^\\makeatother/ { /^\\makeat|Alectryon/b; d}' \
       > stylesheets.part.tex
     # reST → LaTeX; produces ‘stylesheets.part.tex’

.. coq::
|*)

Print Nat.add.
