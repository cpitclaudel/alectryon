# -*- makefile -*-
### Auto-generated with etc/regen_makefile.py ###
### Do not edit! ###

_output/:
	mkdir -p $@

recipes_targets :=

# Custom driver
_output/alectryon_custom_driver.out: alectryon_custom_driver.py | _output/
	$(PYTHON) $< --version | grep -o Alectryon > $@
recipes_targets += _output/alectryon_custom_driver.out

# Direct API usage
_output/api.out: api.py | _output/
	$(PYTHON) $< > $@
recipes_targets += _output/api.out

# run Doctests
_output/api.rst.out: api.rst | _output/
	$(PYTHON) -m doctest -v -o NORMALIZE_WHITESPACE $< > $@
recipes_targets += _output/api.rst.out

# Coq+reST → HTML, cached to _output/caching.v.cache
_output/caching.html: caching.v
	$(alectryon) --cache-directory _output/ --cache-compression=xz $<
recipes_targets += _output/caching.html

# Coq+reST → HTML
_output/coq_drivers.html: coq_drivers.v
	$(alectryon) --coq-driver=sertop $< -o $@
recipes_targets += _output/coq_drivers.html
# Coq+reST → HTML
_output/coq_drivers.coqc.html: coq_drivers.v
	$(alectryon) --coq-driver=coqc_time $< -o $@
recipes_targets += _output/coq_drivers.coqc.html
# Coq+reST → HTML
_output/coq_drivers.noexec.html: coq_drivers.v
	$(alectryon) --coq-driver=sertop_noexec $< -o $@
recipes_targets += _output/coq_drivers.noexec.html

# Coqdoc → HTML
_output/coqdoc.html: coqdoc.v
	$(alectryon) $< --frontend coqdoc
recipes_targets += _output/coqdoc.html

# Coq → HTML
_output/custom_highlighting.html: custom_highlighting.v
	$(alectryon) $<
recipes_targets += _output/custom_highlighting.html
# Custom driver
_output/custom_highlighting.with_driver.html: custom_highlighting.v | _output/
	$(PYTHON) alectryon_custom_driver.py $(alectryon_opts) $< -o $@
recipes_targets += _output/custom_highlighting.with_driver.html

# Coq+reST → HTML
_output/custom_stylesheet.html: custom_stylesheet.rst
	DOCUTILSCONFIG=custom_stylesheet.docutils.conf $(alectryon) $<
recipes_targets += _output/custom_stylesheet.html

# JSON → JSON
_output/fragments.v.io.json: fragments.v.json
	$(alectryon) $<
recipes_targets += _output/fragments.v.io.json
# JSON → HTML
_output/fragments.snippets.html: fragments.v.json
	$(alectryon) $< --backend snippets-html
recipes_targets += _output/fragments.snippets.html
# JSON → LaTeX
_output/fragments.snippets.tex: fragments.v.json
	$(alectryon) $< --backend snippets-latex
recipes_targets += _output/fragments.snippets.tex

# reST+Lean → HTML
_output/lean3-tutorial.html: lean3-tutorial.rst
	$(alectryon) $<
recipes_targets += _output/lean3-tutorial.html
# reST+Lean → Lean
_output/lean3-tutorial.lean3: lean3-tutorial.rst
	$(alectryon) $< -o $@
recipes_targets += _output/lean3-tutorial.lean3

# MyST → HTML
_output/literate_MyST.html: literate_MyST.md
	$(alectryon) $<
recipes_targets += _output/literate_MyST.html

# Coq+reST → HTML
_output/literate_coq.html: literate_coq.v
	$(alectryon) $<
recipes_targets += _output/literate_coq.html
# Coq+reST → LaTeX
_output/literate_coq.tex: literate_coq.v
	DOCUTILSCONFIG=literate.docutils.conf $(alectryon) $< --backend latex
recipes_targets += _output/literate_coq.tex
# Coq+reST → reST
_output/literate_coq.v.rst: literate_coq.v
	$(alectryon) $< --backend rst
recipes_targets += _output/literate_coq.v.rst
# Minimal Coq → reST
_output/literate_coq.min.rst: literate_coq.v | _output/
	cd ..; $(PYTHON) -m alectryon.literate recipes/$< > recipes/$@
recipes_targets += _output/literate_coq.min.rst
# Minimal Coq → reST
_output/literate_coq.min.stdin.rst: literate_coq.v | _output/
	cd ..; $(PYTHON) -m alectryon.literate --coq2rst - < recipes/$< > recipes/$@
recipes_targets += _output/literate_coq.min.stdin.rst

# Coq+reST → HTML
_output/literate_lean3.html: literate_lean3.lean
	$(alectryon) --frontend lean3+rst $<
recipes_targets += _output/literate_lean3.html
# Coq+reST → LaTeX
_output/literate_lean3.xe.tex: literate_lean3.lean
	$(alectryon) --frontend lean3+rst $< --backend latex --latex-dialect xelatex -o $@
recipes_targets += _output/literate_lean3.xe.tex
# Coq+reST → reST
_output/literate_lean3.lean3.rst: literate_lean3.lean
	$(alectryon) --frontend lean3+rst $< --backend rst
recipes_targets += _output/literate_lean3.lean3.rst

# Lean4+reST → HTML
_output/literate_lean4.html: literate_lean4.lean
	$(alectryon) $<
recipes_targets += _output/literate_lean4.html
# Lean4+reST → LaTeX
_output/literate_lean4.xe.tex: literate_lean4.lean
	$(alectryon) $< --backend latex --latex-dialect xelatex -o $@
recipes_targets += _output/literate_lean4.xe.tex
# Lean4+reST → reST
_output/literate_lean4.lean.rst: literate_lean4.lean
	$(alectryon) $< --backend rst
recipes_targets += _output/literate_lean4.lean.rst

# reST+Coq → HTML
_output/literate_reST.html: literate_reST.rst
	$(alectryon) $<
recipes_targets += _output/literate_reST.html
# reST+Coq → LaTeX
_output/literate_reST.tex: literate_reST.rst
	DOCUTILSCONFIG=literate.docutils.conf $(alectryon) $< --backend latex
recipes_targets += _output/literate_reST.tex
# reST+Coq → Coq
_output/literate_reST.v: literate_reST.rst
	$(alectryon) $< --backend coq
recipes_targets += _output/literate_reST.v
# Minimal reST → Coq
_output/literate_reST.min.v: literate_reST.rst | _output/
	cd ..; $(PYTHON) -m alectryon.literate --rst2coq recipes/$< > recipes/$@
recipes_targets += _output/literate_reST.min.v
# Minimal reST → Coq
_output/literate_reST.min.stdin.v: literate_reST.rst | _output/
	cd ..; $(PYTHON) -m alectryon.literate --rst2coq - < recipes/$< > recipes/$@
recipes_targets += _output/literate_reST.min.stdin.v

# reST → HTML
_output/mathjax.html: mathjax.rst
	$(alectryon) $<
recipes_targets += _output/mathjax.html

# reST → HTML
_output/minification.html: minification.rst
	$(alectryon) --html-minification $<
recipes_targets += _output/minification.html

# reST → HTML
_output/minimal.html: minimal.rst
	$(alectryon) $<
recipes_targets += _output/minimal.html
# Minimal reST → HTML
_output/minimal.no-alectryon.html: minimal.rst | _output/
	cd ..; $(PYTHON) -m alectryon.minimal recipes/$< recipes/$@
recipes_targets += _output/minimal.no-alectryon.html

# Lean → HTML
_output/plain-lean3.lean.html: plain-lean3.lean
	$(alectryon) --frontend lean3 $<
recipes_targets += _output/plain-lean3.lean.html

# Lean → HTML
_output/plain-lean4.lean.html: plain-lean4.lean
	$(alectryon) --frontend lean4 $<
recipes_targets += _output/plain-lean4.lean.html

# Coq → HTML
_output/plain.v.html: plain.v
	$(alectryon) --frontend coq $<
recipes_targets += _output/plain.v.html

# reST+… → HTML
_output/polyglot.html: polyglot.rst
	$(alectryon) $<
recipes_targets += _output/polyglot.html

# ReST → HTML
_output/references.html: references.rst
	$(alectryon) $<
recipes_targets += _output/references.html
# ReST → HTML
_output/references.xe.tex: references.rst
	DOCUTILSCONFIG=references.docutils.conf $(alectryon) $< -o $@ --latex-dialect xelatex
recipes_targets += _output/references.xe.tex

$(recipes_targets): out_dir := _output
targets += $(recipes_targets)
