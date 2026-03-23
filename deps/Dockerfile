FROM python:3.14

## APT

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential curl git rsync unzip \
    m4 libgmp-dev zlib1g-dev pkg-config \
    cmake libuv1-dev ccache \
    nodejs npm \
    texlive-xetex texlive-luatex latexmk \
    texlive-fonts-recommended texlive-latex-extra texlive-extra-utils \
    fonts-linuxlibertine fonts-firacode \
    && rm -rf /var/lib/apt/lists/*

## OPAM

RUN curl -sSfL -o /usr/local/bin/opam https://github.com/ocaml/opam/releases/download/2.5.0/opam-2.5.0-x86_64-linux \
    && chmod +x /usr/local/bin/opam

## Python

COPY deps/requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir -r /tmp/requirements.txt

# User setup

ARG UID
ARG GID

RUN groupadd -g "$GID" docker
RUN useradd -m -u "$UID" -g "$GID" --create-home --shell /bin/bash docker

USER docker
WORKDIR /home/docker

## Dafny

RUN curl -sSfL https://github.com/dafny-lang/dafny/releases/download/v4.11.0/dafny-4.11.0-x64-ubuntu-22.04.zip -o /tmp/dafny.zip
RUN unzip -q /tmp/dafny.zip -d /home/docker && rm /tmp/dafny.zip

## OPAM

ARG OPAM_SWITCH
ARG OCAML_VERSION
ARG ROCQ_VERSION
ARG EASYCRYPT_VERSION

COPY --chown=docker:docker deps/opam.sh /tmp/opam.sh
RUN opam init --bare --auto-setup --disable-sandboxing \
    && bash /tmp/opam.sh "$OCAML_VERSION" --switch "$OPAM_SWITCH" --rocq-version "$ROCQ_VERSION" --easycrypt-version "$EASYCRYPT_VERSION"

## Lean 3

RUN curl -sSfL https://github.com/leanprover-community/lean/releases/download/v3.51.1/lean-3.51.1-linux.tar.gz -o /tmp/lean3.tar.gz
RUN tar xzf /tmp/lean3.tar.gz -C /home/docker/ && rm -rf /tmp/lean3.tar.gz

## Lean 4 (via elan)

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain leanprover/lean4:v4.28.0
RUN /home/docker/.elan/bin/lean || true # Force installation

## Symlinks

RUN mkdir -p /home/docker/.local/bin/
RUN ln -s /home/docker/dafny/dafny /home/docker/.local/bin/dafny
RUN ln -s /home/docker/lean-3.51.1-linux/bin/lean /home/docker/.local/bin/lean3

## Path

ENV COLORTERM=truecolor
ENV PYTHON_VENV=/usr/local
ENV PATH="/home/docker/.elan/bin:/home/docker/dafny:/home/docker/.local/bin/:${PATH}"
