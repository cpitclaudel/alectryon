default: all

export PYTHON ?= python3 -Wd # -X tracemalloc
export SPHINXBUILD ?= $(PYTHON) "$(shell which sphinx-build)"
export COVERAGE_FILE := $(abspath coverage/.coverage)
export COVERAGE_RCFILE := $(abspath ../pyproject.toml)

COVERAGE ?=
ifneq (, $(COVERAGE))
PYTHON := $(PYTHON) -m coverage run --source=$(abspath ../alectryon) --parallel-mode
endif

PYTHONPATH ?=
export PYTHONPATH:=$(realpath ../):$(PYTHONPATH)

ALECTRYON_OPTS ?=

alectryon_opts = --copy-assets hardlink --output-directory $(out_dir) --no-version-numbers $(ALECTRYON_OPTS)
alectryon = $(PYTHON) ../alectryon.py $(alectryon_opts)

targets :=
other :=

%/:
	mkdir -p $@
.PRECIOUS: %/

_output/.version-info: | _output/
	@echo "Coq: $(shell coqc -v | tr '\n' ' ' | sed 's/.*version \([0-9.]\+\).*/\1/')" > $@
	@echo "Pygments: $(shell $(PYTHON) -c 'import pygments; print(pygments.__version__)')" >> $@
	@echo "Docutils: $(shell $(PYTHON) -c 'import docutils; print(docutils.__version__)')" >> $@
	@echo "Sphinx: $(shell $(PYTHON) -c 'import sphinx; print(sphinx.__version__)')" >> $@

ifeq (, $(COVERAGE))
other += _output/.version-info
endif

########################
# Auto-generated rules #
########################

recipes.mk: ../etc/regen_makefile.py $(filter-out %.mk,$(wildcard *.*))
	./$< recipes _output $(filter-out $<,$^) > $@

tests.mk: ../etc/regen_makefile.py $(filter-out %.mk,$(wildcard tests/*.*))
	./$< tests _output/tests/ $(filter-out $<,$^) > $@

include recipes.mk tests.mk

# TODO
# _output/mathjax.tex: mathjax.rst | _output/
# 	$(alectryon) --backend latex $<

##########
# Sphinx #
##########

sphinx/_build/html/index.html: export SPHINXBUILD := $(PYTHON) "$(shell which sphinx-build)"
sphinx/_build/html/index.html: sphinx/index.rst
	+$(MAKE) -C sphinx html

targets += sphinx/_build/html/index.html

##############
# Screenshot #
##############

_output/tests/screenshot.pdf: backstop/screenshot.js _output/tests/screenshot.html
	./$^ $@
../etc/screenshot.svg: _output/tests/screenshot.pdf
	pdf2svg $< $@
	svgcleaner --multipass --indent 2 $@ $@

################
# LaTeX → PDF #
################

_output/%.pdf: _output/latex.aux/%.pdf
	mv $< $@

.SECONDEXPANSION:

_output/latex.aux/%.xe.pdf: _output/%.xe.tex | $$(dir $$@)
	texfot --tee=/dev/null --no-stderr latexmk -cd -pdfxe -output-directory=$(shell realpath --relative-to $(dir $<) $(dir $@)) $<

_output/latex.aux/%.lua.pdf: _output/%.lua.tex | $$(dir $$@)
	texfot --tee=/dev/null --no-stderr latexmk -cd -pdflua -output-directory=$(shell realpath --relative-to $(dir $<) $(dir $@)) $<

_output/latex.aux/%.pdf: _output/%.tex | $$(dir $$@)
	texfot --tee=/dev/null --no-stderr latexmk -cd -pdf -output-directory=$(shell realpath --relative-to $(dir $<) $(dir $@)) $<

other += $(patsubst %.tex,%.pdf,$(filter-out %.snippets.tex %.part.tex,$(filter %.tex,$(targets))))

###############
# Entry point #
###############

alectryon: $(targets)

all: $(targets) $(other)

coverage:
	mkdir -p coverage
	+$(MAKE) clean
	+$(MAKE) COVERAGE=1 alectryon
	cd coverage && coverage combine && coverage html
.PHONY: coverage

###########
# Cleanup #
###########

clean:
	rm -rf *.mk coverage/ _output/ sphinx/_build/

.PHONY: clean
FORCE:
