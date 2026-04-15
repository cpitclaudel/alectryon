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
import subprocess

from pathlib import Path
from typing import Iterable, Optional, Union

from .core import ALL_LANGUAGES, Backend, Goals, Messages, Text, \
    RichCode, RichGoal, RichHypothesis, RichMessage, RichSentence

class ASSETS:
    PATH: Path = (Path(__file__).parent / "assets").resolve()
    ALECTRYON_TYP: tuple[str, ...] = ("alectryon.typ",)

## Backend

Node = Optional[Union[str, list]]

class TypstBackend(Backend[Node]):
    """Render annotated fragments as a JSON S-expression."""

    def __init__(self, lang: str):
        super().__init__(highlighter=None)
        self.lang = lang

    def highlight(self, s: str) -> str:
        return s

    @staticmethod
    def _plus(xs: list[Node]) -> Node:
        return ["+", *xs] if xs else None

    def gen_names(self, names: Iterable[str]) -> Node:
        return ["txt", ", ".join(names)]

    def gen_code(self, code: Optional[RichCode]) -> Node:
        return ["code", code.contents] if code else None

    def gen_txt(self, s: Optional[str]) -> Node:
        return ["txt", s] if s is not None else None

    def gen_message(self, message: RichMessage) -> Node:
        return ["message", self.gen_txt(message.contents)]

    def gen_hyp(self, hyp: RichHypothesis) -> Node:
        return ["hyp", self.gen_names(hyp.names),
                self.gen_code(hyp.body), self.gen_code(hyp.type)]

    def gen_goal(self, goal: RichGoal) -> Node:
        hyps = self._plus([self.gen_hyp(h) for h in goal.hypotheses])
        return ["goal", self.gen_txt(goal.name), hyps, self.gen_code(goal.conclusion)]

    def gen_output_group(self, fr: Union[Goals, Messages]) -> Node:
        if isinstance(fr, Goals):
            return ["goals", self._plus([self.gen_goal(g) for g in fr.goals])]
        if isinstance(fr, Messages):
            return ["messages", self._plus([self.gen_message(m) for m in fr.messages])]
        return None

    def gen_sentence(self, s: RichSentence) -> Node:
        outputs = self._plus([self.gen_output_group(fr) for fr in s.outputs])
        return ["sentence", self.gen_code(s.input), outputs]

    def gen_fragment(self, fr) -> Node:
        if isinstance(fr, Text):
            return self.gen_code(fr)
        assert isinstance(fr, RichSentence)
        return self.gen_sentence(fr)

    def gen_fragments(self, fragments, ids=(), classes=()) -> Node:
        from . import transforms
        fragments = transforms.apply_transforms(fragments, [
            transforms.group_whitespace_with_code,
            transforms.commit_io_annotations,
            transforms.commit_affixes,
        ], delay_errors=False)
        return ["io", self.lang, self._plus([self.gen_fragment(fr) for fr in fragments])]

## Frontend

TYPST_QUERY = 'raw.where(block: true)'
TYPST_QUERY_CMD = ["typst", "query", "--input", "alectryon-mode=query"]

def extract_raw_blocks(root: Path, fpath: Path) -> Iterable[dict[str, str]]:
    """Use ``typst query`` with ``--root=`root``` to extract code blocks from `fpath`."""
    try:
        result = subprocess.run([*TYPST_QUERY_CMD, "--root", root, fpath, TYPST_QUERY],
                                capture_output=True, check=True, text=True, cwd=root)
    except FileNotFoundError as e:
        raise FileNotFoundError("Typst binary not found.") from e
    except subprocess.CalledProcessError as e:
        raise ValueError(f"Call to ``typst query`` failed on {fpath}:\n{e.stderr}") from e
    for raw in json.loads(result.stdout):
        if raw.get("lang") in ALL_LANGUAGES and raw.get("label") != "<noal>":
            yield raw
