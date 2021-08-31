export BACKSTOP_DIR ?= ../_output/

test: recipes pdf.js/build/pdf.js
	./backstop.sh test

approve:
	./backstop.sh approve

reference: recipes pdf.js/build/pdf.js
	./backstop.sh reference

recipes:
	+$(MAKE) -C .. clean
	+$(MAKE) -C ..

pdfjs_url := https://github.com/mozilla/pdf.js/releases/download/v2.9.359/pdfjs-2.9.359-dist.zip
pdf.js/pdfjs.zip:
	mkdir pdf.js
	wget -O $@ $(pdfjs_url)

pdf.js/build/pdf.js: pdf.js/pdfjs.zip
	cd pdf.js; unzip "pdfjs.zip"

clean:
	rm -fr backstop_data/html_report/ backstop_data/bitmaps_test/
