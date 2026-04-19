export OPAM_SWITCH ?= alectryon
export OCAML_VERSION ?= 5.4.0
export ROCQ_VERSION ?= 9.1.0
export ROCQ_VERSIONS ?= $(ROCQ_VERSION)
export EASYCRYPT_VERSION ?= r2026.03
export DAFNY_VERSION ?= 4.11.0
export LEAN3_VERSION ?= 3.51.1
export ELAN_VERSION ?= 4.2.1
export LEAN4_VERSION ?= 4.28.0

PYTHON ?= python3
PYTHON_VENV ?= deps/.venv.$(shell hostname)

python_bin := $(PYTHON_VENV)/bin
export PATH := $(abspath $(python_bin)):$(PATH)
export PYTHONIOENCODING ?= utf-8

dependencies := $(python_bin)/pip

.PHONY: test rocq coverage develop lint-changes lint elisp init git-init pixel-diff

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

elisp:
	etc/tests/elisp.sh

FORCE:
recipes/%: FORCE
	+$(make) -C recipes --always-make "$*"

## Screenshot

recipes/_output/tests/screenshot.pdf: recipes/_output/tests/screenshot.html
	etc/pixel-diffs/screenshot.sh $< $@
etc/screenshot.svg: recipes/_output/tests/screenshot.pdf
	pdf2svg $< $@
	svgcleaner --multipass --indent 2 $@ $@

## Pixel diff

pixel-diff:
	etc/pixel-diffs/diff.sh $$(git describe --tags --abbrev=0)

## Dependencies

ifeq ($(MAKECMDGOALS), init)

$(PYTHON_VENV):
	$(PYTHON) -m venv $(PYTHON_VENV)

init: $(PYTHON_VENV)
	python -m pip install -r deps/requirements.dev

git-init:
	git config --local include.path ../etc/gitconfig

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
	pylint alectryon
	mypy --install-types alectryon/
	pyright --project .
	pyrefly check alectryon/

coverage: $(dependencies)
	+$(make) -C recipes coverage

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
		--build-arg ROCQ_VERSION --build-arg ROCQ_VERSIONS \
		--build-arg EASYCRYPT_VERSION \
		--build-arg DAFNY_VERSION \
		--build-arg LEAN3_VERSION \
		--build-arg ELAN_VERSION  --build-arg LEAN4_VERSION \
		.
