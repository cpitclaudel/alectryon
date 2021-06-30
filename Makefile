test:
	+$(MAKE) -C recipes clean
	+$(MAKE) -C recipes

.PHONY: dist

dist:
	python3 -m build

upload: dist
	python3 -m twine upload dist/*

lint:
	pylint --rcfile=setup.cfg alectryon
