# -*- makefile -*-
### Auto-generated with etc/regen_makefile.py ###
### Do not edit! ###

_output/:
	mkdir -p $@

# Direct API usage
_output/api.out: api.py | _output/
	$(PYTHON) $< > $@

# run Doctests
_output/api.rst.out: api.rst | _output/
	$(PYTHON) -m doctest -v -o NORMALIZE_WHITESPACE $< > $@

# Coq+reST → HTML, cached to _output/caching.v.cache
_output/caching.html: caching.v
	$(alectryon) --cache-directory _output/ --cache-compression=xz $<

# Coqdoc → HTML
_output/coqdoc.html: coqdoc.v
	$(alectryon) $< --frontend coqdoc

# Custom driver
_output/custom_driver.out: custom_driver.py | _output/
	$(PYTHON) $< --version | grep -o Alectryon > $@

# Coq → HTML
_output/custom_highlighting.html: custom_highlighting.v
	$(alectryon) $<

# JSON → JSON
_output/fragments.io.json: fragments.json
	$(alectryon) $<
# JSON → HTML
_output/fragments.snippets.html: fragments.json
	$(alectryon) $< --backend snippets-html
# JSON → LaTeX
_output/fragments.snippets.tex: fragments.json
	$(alectryon) $< --backend snippets-latex

# MyST → HTML
_output/literate_MyST.html: literate_MyST.md
	$(alectryon) $<

# Coq+reST → HTML
_output/literate_coq.html: literate_coq.v
	$(alectryon) $<
# Coq+reST → LaTeX
_output/literate_coq.tex: literate_coq.v
	$(alectryon) $< --backend latex
# Coq+reST → reST
_output/literate_coq.v.rst: literate_coq.v
	$(alectryon) $< --backend rst

# reST+Coq → HTML
_output/literate_reST.html: literate_reST.rst
	$(alectryon) $<
# reST+Coq → LaTeX
_output/literate_reST.tex: literate_reST.rst
	DOCUTILSCONFIG=literate_reST.docutils.conf $(alectryon) $< --backend latex
# reST+Coq → Coq
_output/literate_reST.v: literate_reST.rst
	$(alectryon) $< --backend coq

# reST → HTML
_output/mathjax.html: mathjax.rst
	$(alectryon) $<

# reST → HTML
_output/minification.html: minification.rst
	$(alectryon) --html-minification $<

# reST → HTML
_output/minimal.html: minimal.rst
	$(alectryon) $<
# Minimal reST → HTML
_output/minimal.no-alectryon.html: minimal.rst | _output/
	cd ..; $(PYTHON) -m alectryon.minimal recipes/$< recipes/$@

# Coq → HTML
_output/plain.v.html: plain.v
	$(alectryon) --frontend coq $<

# ReST → HTML
_output/references.html: references.rst
	$(alectryon) $<
# ReST → HTML
_output/references.xe.tex: references.rst
	DOCUTILSCONFIG=references.docutils.conf $(alectryon) $< -o $@ --latex-dialect xelatex

_output/api.out _output/api.rst.out _output/caching.html _output/coqdoc.html _output/custom_driver.out _output/custom_highlighting.html _output/fragments.io.json _output/fragments.snippets.html _output/fragments.snippets.tex _output/literate_MyST.html _output/literate_coq.html _output/literate_coq.tex _output/literate_coq.v.rst _output/literate_reST.html _output/literate_reST.tex _output/literate_reST.v _output/mathjax.html _output/minification.html _output/minimal.html _output/minimal.no-alectryon.html _output/plain.v.html _output/references.html _output/references.xe.tex: out_dir := _output

targets += _output/api.out _output/api.rst.out _output/caching.html _output/coqdoc.html _output/custom_driver.out _output/custom_highlighting.html _output/fragments.io.json _output/fragments.snippets.html _output/fragments.snippets.tex _output/literate_MyST.html _output/literate_coq.html _output/literate_coq.tex _output/literate_coq.v.rst _output/literate_reST.html _output/literate_reST.tex _output/literate_reST.v _output/mathjax.html _output/minification.html _output/minimal.html _output/minimal.no-alectryon.html _output/plain.v.html _output/references.html _output/references.xe.tex
