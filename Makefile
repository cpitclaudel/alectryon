test:
	+$(MAKE) -C recipes clean
	+$(MAKE) -C recipes

develop:
	(which opam || { echo "OPAM not found; please install it"; exit 1; })
	eval $$(opam env); opam install coq-serapi
	@# Local install; should be ‘pip install -e .[md,sphinx]’ but see https://github.com/pypa/pip/issues/7953
	python3 -c 'import setuptools, site, sys; site.ENABLE_USER_SITE = 1; sys.argv[1:] = ["develop", "--user"]; setuptools.setup()'

.PHONY: dist

dist:
	python3 -m build

upload: dist
	python3 -m twine upload dist/*

lint:
	etc/lint_changes.sh CHANGES.rst
	pylint --rcfile=setup.cfg alectryon
