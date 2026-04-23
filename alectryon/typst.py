# Copyright © 2026 Clément Pit-Claudel
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

"""Typst integration for Alectryon.

This file extracts code blocks from Typst files with ``typst query`` (frontend)
and generates Typst code from annotated fragments (backend).
"""

from __future__ import annotations

import dataclasses
import json
import re
import subprocess

from collections.abc import Iterable
from functools import cached_property, wraps
from pathlib import Path
from typing import Any, Callable, List, Optional, Tuple, TypeVar, Union

from .cli import CodeSnippet
from .core import JSON, Backend, Goals, Messages, Text, \
    RichCode, RichFragment, RichGoal, RichHypothesis, RichMessage, RichSentence

class ASSETS:
    PATH: Path = (Path(__file__).parent / "assets").resolve()
    ALECTRYON_TYP: tuple[str, ...] = ("alectryon.typ",)

## Backend

# LATER: Switch to ``|`` annotations.
Node = Optional[Union[str, List["Node"]]]

def _decorated(fn):
    """Wrap `fn`'s result in ``marker``/``id`` nodes."""
    @wraps(fn)
    def wrapper(self: "TypstBackend", item, *args, **kwargs) -> Node:
        if (node := fn(self, item, *args, **kwargs)) is None:
            return None
        return self._decorate(node, ids=item.ids, markers=item.markers)
    return wrapper

class TypstBackend(Backend[Node]):
    """Render annotated fragments as a JSON S-expression."""

    def __init__(self) -> None:
        super().__init__(highlighter=None)

    def highlight(self, s: str) -> str:
        return s

    @staticmethod
    def _plus(xs: Iterable[Node]) -> Node:
        xs = list(xs)
        return ["+", *xs] if xs else None

    @staticmethod
    def _decorate(node: Node, ids: Iterable[Any] = (),
                  markers: Iterable[str] = ()) -> Node:
        """Wrap `node` in ``marker``/``id`` nodes.

        Most nodes use this decorator, except goals (which render markers
        themselves on their the separator) and sentences (next to the input).
        """
        if markers := list(markers):
            node = ["marker", node, *markers]
        if ids := [str(i) for i in ids]:
            node = ["id", node, *ids]
        return node

    @_decorated
    def gen_code(self, code: RichCode | None) -> Node:
        if code is None:
            return None
        return ["code", code.contents]

    def gen_txt(self, s: str | None) -> Node:
        return ["txt", s] if s is not None else None

    def gen_names(self, names: Iterable[str]) -> Node:
        return self.gen_txt(", ".join(names))

    @_decorated
    def gen_message(self, message: RichMessage) -> Node:
        return ["message", self.gen_txt(message.contents)]

    @_decorated
    def gen_hyp(self, hyp: RichHypothesis) -> Node:
        return ["hyp", self.gen_names(hyp.names),
                self.gen_code(hyp.body), self.gen_code(hyp.type)]

    def gen_goal(self, goal: RichGoal) -> Node:
        hyps: Node = self._plus(self.gen_hyp(h) for h in goal.hypotheses)
        node: Node = ["goal", self.gen_txt(goal.name), hyps,
                      self.gen_code(goal.conclusion), *goal.markers]
        return self._decorate(node, ids=goal.ids)

    def gen_output_group(self, fr: Goals | Messages) -> Node:
        if isinstance(fr, Goals):
            return ["goals", self._plus(self.gen_goal(g) for g in fr.goals)]
        assert isinstance(fr, Messages)
        return ["messages", self._plus(self.gen_message(m) for m in fr.messages)]

    def gen_sentence(self, s: RichSentence) -> Node:
        outputs = self._plus(self.gen_output_group(fr) for fr in s.outputs)
        node = ["sentence", self.gen_code(s.input), outputs, *s.markers]
        return self._decorate(node, ids=s.ids)

    def gen_fragment(self, fr: RichFragment) -> Node:
        if isinstance(fr, Text):
            return self.gen_txt(fr.contents)
        assert isinstance(fr, RichSentence)
        return self.gen_sentence(fr)

    def gen_fragments(self, fragments: Iterable[RichFragment],
                      ids: tuple[str, ...] = (),
                      classes: tuple[str, ...] = ()) -> Node:
        from . import transforms
        fragments = transforms.apply_transforms(fragments, [
            transforms.group_whitespace_with_code,
            transforms.commit_io_annotations,
            transforms.commit_affixes,
        ], delay_errors=False)
        return ["io", self._plus(self.gen_fragment(fr) for fr in fragments)]

## Frontend

TYPST_QUERY: str = ("selector(raw.where(block: true))"
                    ".or(<alectryon-mrefs>)"
                    ".or(<alectryon-mquotes>)"
                    ".or(<alectryon-masserts>)")

TYPST_QUERY_CMD: list[str] = ["typst", "query", "--input", "alectryon-mode=query"]

def _run_typst_query(root: Path, fpath: Path) -> list[dict[str, Any]]:
    try:
        result = subprocess.run([*TYPST_QUERY_CMD, "--root", root, fpath, TYPST_QUERY],
                                capture_output=True, check=True, text=True, cwd=root)
        return json.loads(result.stdout)
    except FileNotFoundError as e:
        raise FileNotFoundError("Typst binary not found.") from e
    except subprocess.CalledProcessError as e:
        raise ValueError(f"Call to ``typst query`` failed on {fpath}:\n{e.stderr}") from e

# ``fence-re`` in ``assets/alectryon.typ``.
FENCE_RE = re.compile(r"^[{]([a-z0-9]+)[}]$")

@dataclasses.dataclass
class TypstCodeSnippet(CodeSnippet):
    src: str
    label: Optional[str] = None

    def to_json(self) -> dict[str, Any]:
        return {"src": self.src, "lang": self.lang, "rendered": self.contents}

## Mref / mquote resolution

@dataclasses.dataclass
class TypstReference:
    """Fields shared by every ``mref`` / ``mquote`` / ``massert`` reference."""
    path: str
    block_idx: Optional[int] = None
    prefix: Optional[str] = None

    @staticmethod
    def of_metadata(item: dict[str, Any],
                    block_idx: Optional[int]) -> "TypstReference":
        """Return a typed reference for `item` based on its label."""
        label, values = item["label"], item["value"]
        values = {k.replace("-", "_"): v for k, v in values.items()}
        if label == "<alectryon-mrefs>":
            return MRef(block_idx=block_idx, **values)
        if label == "<alectryon-mquotes>":
            return MQuote(block_idx=block_idx, **values)
        if label == "<alectryon-masserts>":
            return MAssert(block_idx=block_idx, **values)
        assert False, f"Unexpected Typst label {label!r}"

@dataclasses.dataclass
class MRef(TypstReference):
    counter_style: Optional[str] = None
    title: Optional[str] = None

    @cached_property
    def style(self) -> Any:
        from .docutils import _counter_style
        return _counter_style(self.counter_style)

@dataclasses.dataclass
class MQuote(TypstReference):
    pass

@dataclasses.dataclass
class MAssert(TypstReference):
    pass

@dataclasses.dataclass
class References:
    """Reference calls extracted from a Typst document, sorted by kind."""
    mrefs: list[MRef]
    mquotes: list[MQuote]
    masserts: list[MAssert]

    def append(self, ref: TypstReference) -> None:
        if isinstance(ref, MRef):
            self.mrefs.append(ref)
        elif isinstance(ref, MQuote):
            self.mquotes.append(ref)
        elif isinstance(ref, MAssert):
            self.masserts.append(ref)
        else:
            assert False, f"Unexpected Typst reference {ref!r}"

class TypstDocument:
    """Data extracted from a Typst file by ``typst query``."""

    def __init__(self, fname: str, items: Iterable[JSON], snippets: list[TypstCodeSnippet]) -> None:
        self.fname: str = fname
        self.resolver: Optional["TypstResolver"] = None
        self.references: References = References([], [], [])
        self._parse_query_output(items, snippets)

    @classmethod
    def from_path(cls, root: Path, fpath: Path) -> Tuple["TypstDocument", list[TypstCodeSnippet]]:
        """Run ``typst query`` on `fpath` and build a document from its output."""
        items = _run_typst_query(root, fpath)
        snippets: list[TypstCodeSnippet] = []
        document = cls(fpath.name, items, snippets)
        return document, snippets

    @staticmethod
    def _parse_snippet(item: dict[str, Any]) -> Optional[TypstCodeSnippet]:
        """Return a ``TypstCodeSnippet`` for `item`, or ``None``."""
        lang, text = item.get("lang"), item["text"]
        if lang is None: # Typst <= 0.14.2 doesn't parse {coq}
            # LATER: Discard this branch
            lang, _, text = text.partition("\n")
        if not (m := FENCE_RE.fullmatch(lang)):
            return None # Not a snippet we support
        # Typst labels come wrapped as ``<name>``
        label = re.sub(r"\A<(.*)>\Z", r"\1", lbl) if (lbl := item.get("label")) else None
        return TypstCodeSnippet.of_text(m.group(1), "", text, src=text, label=label)

    def _parse_query_output(self, items: Iterable[JSON], snippets: list[TypstCodeSnippet]) -> None:
        block_idx: Optional[int] = None
        for item in items:
            if item["func"] == "metadata":
                self.references.append(TypstReference.of_metadata(item, block_idx))
            elif snippet := self._parse_snippet(item):
                block_idx = 0 if block_idx is None else block_idx + 1
                snippets.append(snippet)

    def resolve(self, snippets: list[TypstCodeSnippet]) -> None:
        """Resolve ``mref``/``mquote``/``massert`` references."""
        self.resolver = TypstResolver(self.references, self.fname, snippets)
        self.resolver.run()

    def to_json(self, snippets: list[TypstCodeSnippet]) -> JSON:
        assert self.resolver
        return {"version": 1,
                "marker-info": {"mrefs": self.resolver.mrefs,
                                "mquotes": self.resolver.mquotes},
                "snippets": [s.to_json() for s in snippets]}

class TypstResolver:
    def __init__(self, references: References, fname: str,
                 snippets: list[TypstCodeSnippet]) -> None:
        from docutils import nodes
        from .core import Gensym
        from .docutils import RefCounter
        self.references = references
        self.snippets = snippets
        self.by_label = {label: s for s in snippets if (label := s.label)}
        self.gensym = Gensym(nodes.make_id(fname) + "-")
        self.refcounter = RefCounter()
        self.mrefs: list[dict[str, Any]] = []
        self.mquotes: list[dict[str, Any]] = []

    def run(self) -> None:
        _ = [self._lookup_ref(r, "assert") for r in self.references.masserts]
        self.mrefs = [self._resolve_mref(r) for r in self.references.mrefs]
        self.mquotes = [self._resolve_mquote(r) for r in self.references.mquotes]

    def _lookup_ref(self, ref: TypstReference, kind: str) -> Tuple[TypstCodeSnippet, Any]:
        from .docutils import AlectryonMrefTransform as MT, _parse_mref_target
        path = _parse_mref_target(kind, ref.path, ref.prefix)
        last_io = self.snippets[ref.block_idx] if ref.block_idx is not None else None
        snippet = MT._find_io(path, self.by_label, last_io)
        target = MT._find_target_in_fragments(path, snippet.contents or [])
        return snippet, target

    def _resolve_mref(self, ref: MRef) -> dict[str, Any]:
        from docutils import nodes
        _, target = self._lookup_ref(ref, "ref")
        if not target.ids:
            target.ids.append(self.gensym(nodes.make_id(ref.path) + "-"))
        if not target.markers:
            target.markers.append(ref.title or self.refcounter.next(ref.style))
        return {"path": ref.path,
                "id": str(target.ids[-1]),
                "marker": target.markers[-1]}

    def _resolve_mquote(self, ref: MQuote) -> dict[str, Any]:
        from copy import deepcopy
        from .transforms import strip_ids_and_props
        snippet, target = self._lookup_ref(ref, "quote")
        if isinstance(target, RichSentence):
            target = target.input
        target = strip_ids_and_props(deepcopy(target), {"enabled", "markers"})
        rendered = TypstBackend()._gen_any(target)
        return {"path": ref.path, "rendered": rendered, "lang": snippet.lang}
