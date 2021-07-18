default: all

PYTHON ?= python3 -Wd # -X tracemalloc
alectryon = $(PYTHON) ../alectryon.py --copy-assets hardlink --output-directory $(out_dir) --no-version-numbers --traceback

targets :=

%/:
	mkdir -p $@
.PRECIOUS: %/

_output/.version-info: | _output/
	@echo "Coq: $(shell coqc -v | tr '\n' ' ' | sed 's/.*version \([0-9.]\+\).*/\1/')" > $@
	@echo "Pygments: $(shell $(PYTHON) -c 'import pygments; print(pygments.__version__)')" >> $@
	@echo "Docutils: $(shell $(PYTHON) -c 'import docutils; print(docutils.__version__)')" >> $@
	@echo "Sphinx: $(shell $(PYTHON) -c 'import sphinx; print(sphinx.__version__)')" >> $@

targets += _output/.version-info

########################
# Auto-generated rules #
########################

recipes.mk: ../etc/regen_makefile.py $(filter-out %.mk,$(wildcard *.*))
	./$< _output $(filter-out $<,$^) > $@

tests.mk: ../etc/regen_makefile.py $(filter-out %.mk,$(wildcard tests/*.*))
	./$< _output/tests/ $(filter-out $<,$^) > $@

include *.mk

# TODO
# _output/mathjax.tex: mathjax.rst | _output
# 	$(alectryon) --backend latex $<

##########
# Sphinx #
##########

sphinx/_build/html/index.html: sphinx/index.rst
	+$(MAKE) -C sphinx html

targets += sphinx/_build/html/index.html

################
# LaTeX → PDF #
################

_output/%.pdf: _output/latex.aux/%.pdf
	mv $< $@

.SECONDEXPANSION:

_output/latex.aux/%.xe.pdf: _output/%.xe.tex | $$(dir $$@)
	TEXINPUTS=$(dir $<): texfot --quiet xelatex -output-directory=$(dir $@) $(notdir $<)

_output/latex.aux/%.lua.pdf: _output/%.lua.tex | $$(dir $$@)
	TEXINPUTS=$(dir $<): texfot --quiet xelatex -output-directory=$(dir $@) $(notdir $<)

_output/latex.aux/%.pdf: _output/%.tex | $$(dir $$@)
	TEXINPUTS=$(dir $<): texfot --quiet pdflatex -output-directory=$(dir $@) $(notdir $<)

targets += $(patsubst %.tex,%.pdf,$(filter-out %.snippets.tex,$(filter %.tex,$(targets))))

###############
# Entry point #
###############

all: $(targets)

###########
# Cleanup #
###########

clean:
	rm -rf _output/ sphinx/_build/

.PHONY: clean
FORCE:
