# -*- makefile -*-
### Auto-generated with etc/regen_recipes_makefile.py ###
### Do not edit! ###

_output/tests:
	mkdir -p $@

# HTML4
_output/tests/dialects.4.html: tests/dialects.rst
	$(alectryon) --html-dialect=html4 -o $@ $<
# HTML5
_output/tests/dialects.5.html: tests/dialects.rst
	$(alectryon) --html-dialect=html5 -o $@ $<
# LaTeX
_output/tests/dialects.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=pdflatex -o $@ $<
# XeLaTeX
_output/tests/dialects.xe.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=xelatex -o $@ $<
# LuaLaTeX
_output/tests/dialects.lua.tex: tests/dialects.rst
	$(alectryon) --latex-dialect=lualatex -o $@ $<

# reST → Coq
_output/tests/directive-options.html: tests/directive-options.rst
	$(alectryon) $<
# reST → LaTeX
_output/tests/directive-options.xe.tex: tests/directive-options.rst
	$(alectryon) $< -o $@

# Coq+reST → LaTeX
_output/tests/latex_formatting.tex: tests/latex_formatting.v
	$(alectryon) $< --backend latex

_output/tests/dialects.4.html _output/tests/dialects.5.html _output/tests/dialects.tex _output/tests/dialects.xe.tex _output/tests/dialects.lua.tex _output/tests/directive-options.html _output/tests/directive-options.xe.tex _output/tests/latex_formatting.tex: out_dir := _output/tests

targets += _output/tests/dialects.4.html _output/tests/dialects.5.html _output/tests/dialects.tex _output/tests/dialects.xe.tex _output/tests/dialects.lua.tex _output/tests/directive-options.html _output/tests/directive-options.xe.tex _output/tests/latex_formatting.tex
