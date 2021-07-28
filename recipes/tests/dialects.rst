=========================
 LaTeX and HTML dialects
=========================

.. raw:: latex

   \let\oldalltt\alltt
   \def\alltt{\oldalltt\scriptsize}

This simple file demos LaTeX and HTML dialect configuration::

   alectryon --html-dialect=html4 -o dialects.4.html dialects.rst
     # HTML4; produces ‘dialects.4.html’
   alectryon --html-dialect=html5 -o dialects.5.html dialects.rst
     # HTML5; produces ‘dialects.5.html’

   alectryon --latex-dialect=pdflatex -o dialects.tex dialects.rst
     # LaTeX; produces ‘dialects.tex’
   alectryon --latex-dialect=xelatex -o dialects.xe.tex dialects.rst
     # XeLaTeX; produces ‘dialects.xe.tex’
   alectryon --latex-dialect=lualatex -o dialects.lua.tex dialects.rst
     # LuaLaTeX; produces ‘dialects.lua.tex’

.. coq:: unfold

   Goal True.
     exact I.
     Show Proof.
