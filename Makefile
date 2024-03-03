python_venv := deps/.venv
python_bin := $(python_venv)/bin
export PATH := $(abspath $(python_bin)):$(PATH)

binaries := $(python_bin)/pip
dependencies := $(binaries)

.PHONY: test coverage develop dist upload lint-changes lint

## Main targets

test: $(dependencies)
	+$(MAKE) -C recipes clean
	+$(MAKE) -C recipes

dist: $(dependencies)
	python -m build

upload: dist
	python -m twine upload dist/*

FORCE:
recipes/%: FORCE
	+$(MAKE) -C recipes --always-make "$*"

## Dependencies

ifeq ($(MAKECMDGOALS), init)

$(python_venv):
	python3 -m venv $(python_venv)

init: $(python_venv)
	pip install -r deps/requirements.txt

else

$(dependencies):
	$(error Dependency $(notdir $@) not set up; try `make init`?)

endif

## Local development

lint-changes: $(dependencies)
	etc/lint_changes.py CHANGES.rst

lint: $(dependencies)
	pylint --rcfile=setup.cfg alectryon
	mypy alectryon/
	pyright --project .

coverage: $(dependencies)
	+$(MAKE) -C recipes coverage

develop: $(dependencies)
	(which opam || { echo "OPAM not found; please install it"; exit 1; })
	eval $$(opam env); opam install coq-serapi
	pip install coverage[toml]
	pip install -e .[full]
