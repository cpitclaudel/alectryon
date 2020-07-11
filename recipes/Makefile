alectryon := ../alectryon.py --output-directory output --no-header
assets := alectryon.css alectryon.js
all := plain.v.html literate.v.html coqdoc.v.html coqdoc.html literate.html document.html document.v literate.v.rst fragments.io.json fragments.snippets.html

all: $(patsubst %,output/%,$(all) $(assets)) sphinx/_build/html/index.html;

output:
	mkdir $@

# HTML ← Coq
output/plain.v.html: plain.v | output
	$(alectryon) --frontend coq $<
output/literate.v.html: literate.v | output
	$(alectryon) --frontend coq $<
output/coqdoc.v.html: coqdoc.v | output
	$(alectryon) --frontend coq $<

# HTML ← Coqdoc
output/coqdoc.html: coqdoc.v | output
	$(alectryon) $< --frontend coqdoc

# HTML ← Coq+reST
output/literate.html: literate.v | output
	$(alectryon) $<

# HTML ← reST+Coq
output/document.html: document.v.rst | output
	$(alectryon) $<

# Coq+reST ← reST+Coq
output/document.v: document.v.rst | output
	$(alectryon) $< -o $@

# reST+Coq ← Coq+reST
output/literate.v.rst: literate.v | output
	$(alectryon) $< -o $@

# JSON ← JSON
output/fragments.io.json: fragments.json | output
	$(alectryon) $<

# HTML snippets ← JSON
output/fragments.snippets.html: fragments.json | output
	$(alectryon) $< -o $@

# Sphinx
sphinx/_build/html/index.html: sphinx/index.rst
	+$(MAKE) -C sphinx html

output/alectryon%css output/alectryon%js: FORCE
	cp --link --force ../assets/* output/
FORCE:

clean:
	rm -rf output/ sphinx/_build

.PHONY: clean assets
