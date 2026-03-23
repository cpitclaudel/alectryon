PYTHON ?= python3
python_venv := deps/.venv.$(shell hostname)
python_bin := $(python_venv)/bin
export PATH := $(abspath $(python_bin)):$(PATH)
export PYTHONIOENCODING ?= utf-8

binaries := $(python_bin)/pip
dependencies := $(binaries)

.PHONY: test coverage develop dist upload lint-changes lint

## Main targets

make := $(MAKE)
ifneq (,$(wildcard $(HOME)/.opam/alectryon))
make := eval $$(opam env --switch=alectryon); $(make)
endif

test: $(dependencies)
	+$(make) -C recipes clean
	+$(make) -C recipes all

rocq: $(dependencies)
	+$(make) -C recipes --always-make rocq

dist: $(dependencies)
	python -m build

upload: dist
	python -m twine upload dist/*

FORCE:
recipes/%: FORCE
	+$(make) -C recipes --always-make "$*"

## Dependencies

ifeq ($(MAKECMDGOALS), init)

$(python_venv):
	$(PYTHON) -m venv $(python_venv)

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
	vermin --target=3.9- --eval-annotations --violations alectryon
	pylint --rcfile=setup.cfg alectryon
	mypy alectryon/
	pyright --project .

coverage: $(dependencies)
	+$(make) -C recipes coverage

develop: $(dependencies)
	(which opam || { echo "OPAM not found; please install it"; exit 1; })
	pip install mypy coverage[toml]
	python -m mypy --install-types alectryon/
	pip install -e .[full]

opam_switch := alectryon
_opam:
	deps/opam.sh 5.4.0 9.1.0
