PYTHON ?= python3

test:
	+$(MAKE) -C recipes clean
	+$(MAKE) -C recipes

coverage:
	+$(MAKE) -C recipes coverage

develop:
	(which opam || { echo "OPAM not found; please install it"; exit 1; })
	eval $$(opam env); opam install coq-serapi
	pip install coverage[toml]
	@# Local install; should be ‘pip install -e .[full]’ but see https://github.com/pypa/pip/issues/7953
	$(PYTHON) -c 'import setuptools, site, sys; site.ENABLE_USER_SITE = 1; sys.argv[1:] = ["develop", "--user"]; setuptools.setup()'

.PHONY: dist

dist:
	$(PYTHON) -m build

upload: dist
	$(PYTHON) -m twine upload dist/*

lint:
	etc/lint_changes.sh CHANGES.rst
	pylint --rcfile=setup.cfg alectryon
	mypy alectryon/
	pyright --project .
