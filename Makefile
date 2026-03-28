export OPAM_SWITCH ?= alectryon
export OCAML_VERSION ?= 5.4.0
export ROCQ_VERSION ?= 9.1.0
export EASYCRYPT_VERSION ?= r2026.03

PYTHON ?= python3
PYTHON_VENV ?= deps/.venv.$(shell hostname)

python_bin := $(PYTHON_VENV)/bin
export PATH := $(abspath $(python_bin)):$(PATH)
export PYTHONIOENCODING ?= utf-8

dependencies := $(python_bin)/pip

.PHONY: test coverage develop dist upload lint-changes lint

## Main targets

make := $(MAKE)

ifneq (,$(wildcard $(HOME)/.opam/$(OPAM_SWITCH)))
make := eval $$(opam env --switch=$(OPAM_SWITCH)); $(make)
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

$(PYTHON_VENV):
	$(PYTHON) -m venv $(PYTHON_VENV)

init: $(PYTHON_VENV)
	pip install -r deps/requirements.txt

else

$(dependencies):
	$(error Dependency $(notdir $@) not set up; try `make init`?)

endif

## Local development

.PHONY: _opam

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

_opam:
	deps/opam.sh $(OCAML_VERSION) \
		--switch $(OPAM_SWITCH) \
		--rocq-version $(ROCQ_VERSION) \
		--easycrypt-version $(EASYCRYPT_VERSION)

## Docker

### Use `etc/docker.sh make …` to run in docker

# Either .dev or .ci
docker-build%: deps/Dockerfile%
	docker build -t alectryon$* -f $< \
		--build-arg UID=$(shell id -u) --build-arg GID=$(shell id -g) \
		--build-arg OPAM_SWITCH --build-arg OCAML_VERSION \
		--build-arg ROCQ_VERSION --build-arg EASYCRYPT_VERSION \
		.
