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

import json
import re
import subprocess

from collections.abc import Iterable
from pathlib import Path
from typing import List, Optional, Union

from .core import Backend, Goals, Messages, Text, \
    RichCode, RichFragment, RichGoal, RichHypothesis, RichMessage, RichSentence

class ASSETS:
    PATH: Path = (Path(__file__).parent / "assets").resolve()
    ALECTRYON_TYP: tuple[str, ...] = ("alectryon.typ",)

## Backend

# LATER: Switch to ``|`` annotations.
Node = Optional[Union[str, List["Node"]]]

class TypstBackend(Backend[Node]):
    """Render annotated fragments as a JSON S-expression."""

    def __init__(self) -> None:
        super().__init__(highlighter=None)

    def highlight(self, s: str) -> str:
        return s

    @staticmethod
    def _plus(xs: list[Node]) -> Node:
        return ["+", *xs] if xs else None

    def gen_names(self, names: Iterable[str]) -> Node:
        return ["txt", ", ".join(names)]

    def gen_code(self, code: RichCode | None) -> Node:
        return ["code", code.contents] if code else None

    def gen_txt(self, s: str | None) -> Node:
        return ["txt", s] if s is not None else None

    def gen_message(self, message: RichMessage) -> Node:
        return ["message", self.gen_txt(message.contents)]

    def gen_hyp(self, hyp: RichHypothesis) -> Node:
        return ["hyp", self.gen_names(hyp.names),
                self.gen_code(hyp.body), self.gen_code(hyp.type)]

    def gen_goal(self, goal: RichGoal) -> Node:
        hyps = self._plus([self.gen_hyp(h) for h in goal.hypotheses])
        return ["goal", self.gen_txt(goal.name), hyps, self.gen_code(goal.conclusion)]

    def gen_output_group(self, fr: Goals | Messages) -> Node:
        if isinstance(fr, Goals):
            return ["goals", self._plus([self.gen_goal(g) for g in fr.goals])]
        if isinstance(fr, Messages):
            return ["messages", self._plus([self.gen_message(m) for m in fr.messages])]
        return None

    def gen_sentence(self, s: RichSentence) -> Node:
        outputs = self._plus([self.gen_output_group(fr) for fr in s.outputs])
        return ["sentence", self.gen_code(s.input), outputs]

    def gen_fragment(self, fr: RichFragment) -> Node:
        if isinstance(fr, Text):
            return self.gen_code(fr)
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
        return ["io", self._plus([self.gen_fragment(fr) for fr in fragments])]

## Frontend

TYPST_QUERY: str = 'raw.where(block: true)'
TYPST_QUERY_CMD: list[str] = ["typst", "query", "--input", "alectryon-mode=query"]

def _run_typst_query(root: Path, fpath: Path) -> list[dict[str, str | None]]:
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

def extract_raw_blocks(root: Path, fpath: Path) -> Iterable[dict[str, str]]:
    """Use ``typst query`` with ``--root=`root``` to extract code blocks from `fpath`."""
    for raw in _run_typst_query(root, fpath):
        lang, text = raw.get("lang"), raw.get("text") or ""
        if lang is None: # Typst <= 0.14.2 doesn't parse {coq}
            # LATER: Discard this branch
            lang, _, text = text.partition("\n")
        if m := FENCE_RE.fullmatch(lang):
            yield {"lang": m.group(1), "text": text}
