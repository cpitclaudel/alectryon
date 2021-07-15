backstop := ./node_modules/.bin/backstop --config=backstop.config.js

test: recipes
	$(backstop) test

approve: recipes
	$(backstop) approve

reference: recipes
	$(backstop) reference

recipes:
	+$(MAKE) -C ..

clean:
	rm -fr /backstop_data/html_report/ /backstop_data/bitmaps_test/
