alectryon := ../alectryon.py --output-directory output
assets := alectryon.css alectryon-slideshow.js
all := plain.v.html literate.v.html literate.html document.html document.v literate.v.rst fragments.io.json fragments.snippets.html

all: $(patsubst %,output/%,$(all) $(assets));

output:
	mkdir $@

# HTML ← Coq
output/plain.v.html: plain.v | output
	$(alectryon) $<
output/literate.v.html: literate.v | output
	$(alectryon) $<

# HTML ← Coq+reST
output/literate.html: literate.v | output
	$(alectryon) --frontend coq+rst $<

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

output/alectryon%css output/alectryon%js:
	cp ../assets/* output/

clean:
	rm -rf output/

.PHONY: clean assets
