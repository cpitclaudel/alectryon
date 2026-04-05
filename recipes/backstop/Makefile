export BACKSTOP_DIR ?= ../_output/

.PHONY: test approve reference recipes update clean

test: recipes pdf.js/build/pdf.mjs node_modules
	./backstop.sh test

approve: node_modules
	./backstop.sh approve

reference: recipes pdf.js/build/pdf.mjs node_modules
	./backstop.sh reference

recipes:
	../../etc/docker.sh make -O -j test

node_modules: package.json
	npm install

update:
	npm install backstopjs@latest

pdfjs_url := https://github.com/mozilla/pdf.js/releases/download/v5.6.205/pdfjs-5.6.205-dist.zip
pdf.js/pdfjs.zip:
	mkdir pdf.js
	wget -O $@ $(pdfjs_url)

pdf.js/build/pdf.mjs: pdf.js/pdfjs.zip
	cd pdf.js; unzip "pdfjs.zip"

clean:
	rm -fr backstop_data/html_report/ backstop_data/bitmaps_test/
