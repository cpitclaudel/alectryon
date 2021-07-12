PYTHON ?= python3 -Wd # -X tracemalloc

alectryon := $(PYTHON) ../alectryon.py --output-directory output --no-version-numbers --traceback
minimal := $(PYTHON) -m alectryon.minimal

asset_names := alectryon.css alectryon.js alectryon.sty tango_subtle.sty
assets := $(patsubst %,output/%,$(asset_names))

all := .version-info \
	plain.v.html literate.v.html coqdoc.v.html \
	coqdoc.html \
	literate.html literate.pdflatex.pdf \
	document.html hyps.html mathjax.html \
	document.pdflatex.pdf hyps.xelatex.pdf \
	document.minimal.html \
	document.v literate.v.rst \
	fragments.io.json \
	fragments.snippets.html fragments.snippets.tex \
	api.out

all: $(patsubst %,output/%,$(all)) $(assets) sphinx/_build/html/index.html;

output:
	mkdir $@

output/.version-info: | output
	@echo "Coq: $$(coqc -v)" > $@
	@echo "Pygments: $$($(PYTHON) -c 'import pygments; print(pygments.__version__)')" >> $@
	@echo "Docutils: $$($(PYTHON) -c 'import docutils; print(docutils.__version__)')" >> $@
	@echo "Sphinx: $$($(PYTHON) -c 'import sphinx; print(sphinx.__version__)')" >> $@

# Coq → HTML
output/plain.v.html: plain.v | output
	$(alectryon) --frontend coq $<
output/literate.v.html: literate.v | output
	$(alectryon) --frontend coq $<
output/coqdoc.v.html: coqdoc.v | output
	$(alectryon) --frontend coq $<

# No plain Coq → LaTeX for now
# output/plain.v.tex: plain.v | output
# 	$(alectryon) --frontend coq --backend latex $<
# output/literate.v.tex: literate.v | output
# 	$(alectryon) --frontend coq --backend latex $<
# output/coqdoc.v.tex: coqdoc.v | output
# 	$(alectryon) --frontend coq --backend latex $<

# Coqdoc → HTML
output/coqdoc.html: coqdoc.v | output
	$(alectryon) $< --frontend coqdoc --cache-directory output/

# Coq+reST → HTML
output/literate.html: literate.v | output
	$(alectryon) $<

# Coq+reST → LaTeX
output/literate.tex: literate.v | output
	$(alectryon) --backend latex $<

# reST+Coq → HTML
output/document.html: document.v.rst | output
	$(alectryon) $<
output/hyps.html: hyps.rst | output
	$(alectryon) $<
output/mathjax.html: mathjax.rst | output
	$(alectryon) $<

# reST+Coq → LaTeX
output/document.tex: document.v.rst | output
	$(alectryon) --backend latex $<
output/hyps.tex: hyps.rst | output
	$(alectryon) --backend latex --latex-dialect xelatex $<

# TODO
# output/mathjax.html: mathjax.rst | output
# 	$(alectryon) --backend latex $<

# Minimal reST+Coq → HTML
output/document.minimal.html: document.v.rst | output
	cd ..; $(minimal) recipes/$< recipes/$@

# reST+Coq → Coq+reST
output/document.v: document.v.rst | output
	$(alectryon) $< -o $@

# Coq+reST → reST+Coq
output/literate.v.rst: literate.v | output
	$(alectryon) $< -o $@

# JSON → JSON
output/fragments.io.json: fragments.json | output
	$(alectryon) $<

# JSON → HTML snippets
output/fragments.snippets.html: fragments.json | output
	$(alectryon) $< -o $@

# JSON → Latex snippets
output/fragments.snippets.tex: fragments.json | output
	$(alectryon) $< -o $@

# Sphinx
sphinx/_build/html/index.html: sphinx/index.rst
	+$(MAKE) -C sphinx html

# API
output/api.out: api.py
	$(PYTHON) $< > $@

# LaTeX → PDF
output/latex.aux:
	mkdir $@

output/%.pdf: output/latex.aux/%.pdf
	mv $< $@

output/latex.aux/%.pdflatex.pdf: output/%.tex $(assets) | output/latex.aux
	cd output/; pdflatex -output-directory=latex.aux -jobname=$*.pdflatex $*.tex

output/latex.aux/%.xelatex.pdf: output/%.tex $(assets) | output/latex.aux
	cd output/; xelatex -output-directory=latex.aux -jobname=$*.xelatex $*.tex

output/%.css output/%.js output/%.sty: | output
	cp --link --force $(patsubst %,../alectryon/assets/%,$(asset_names)) output/

clean:
	rm -rf output/ sphinx/_build sphinx/*.cache

.PHONY: clean assets
