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

class TypstBackend(Backend[str]):
    """Render annotated fragments as Typst code expression strings."""

    def __init__(self, lang: str):
        super().__init__(highlighter=None)
        self.lang = lang

    NONE = "none"

    TYPST_ESCAPES = str.maketrans(
        {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\r": "\\r", "\t": "\\t"})

    @classmethod
    def _typst_string(cls, s: str) -> str:
        return f'"{s.translate(cls.TYPST_ESCAPES)}"'

    def highlight(self, s: str) -> str:
        return self._typst_string(s)

    def gen_names(self, names: Iterable[str]) -> str:
        return self.gen_txt(", ".join(names))

    def gen_code(self, code: Optional[RichCode]) -> str:
        return f"code({self._typst_string(code.contents)})" if code is not None else self.NONE

    def gen_txt(self, s: Optional[str]) -> str:
        return f"txt({self._typst_string(s)})" if s is not None else self.NONE

    def gen_message(self, message: RichMessage) -> str:
        return f"message({self.gen_txt(message.contents)})"

    def gen_hyp(self, hyp: RichHypothesis) -> str:
        names = self.gen_names(hyp.names)
        return f"hyp({names}, {self.gen_code(hyp.body)}, {self.gen_code(hyp.type)})"

    def gen_goal(self, goal: RichGoal) -> str:
        hyps = " + ".join(self.gen_hyp(h) for h in goal.hypotheses) or self.NONE
        return f"goal({self.gen_txt(goal.name)}, {hyps}, {self.gen_code(goal.conclusion)})"

    def _gen_outputs(self, outputs: Iterable[Union[Goals, Messages]]) -> Iterable[str]:
        for fr in outputs:
            if isinstance(fr, Goals):
                yield from (self.gen_goal(g) for g in fr.goals)
            elif isinstance(fr, Messages):
                yield from (self.gen_message(m) for m in fr.messages)

    def gen_sentence(self, s: RichSentence) -> str:
        output = " + ".join(self._gen_outputs(s.outputs)) or self.NONE
        return f"sentence({self.gen_code(s.input)}, {output})"

    def gen_fragment(self, fr) -> str:
        if isinstance(fr, Text):
            return self.gen_code(fr)
        assert isinstance(fr, RichSentence)
        return self.gen_sentence(fr)

    def gen_fragments(self, fragments, ids=(), classes=()) -> str:
        from . import transforms
        fragments = transforms.apply_transforms(fragments, [
            transforms.group_whitespace_with_code,
            transforms.commit_affixes,
            transforms.commit_io_annotations
        ], delay_errors=False)
        body = "; ".join(self.gen_fragment(fr) for fr in fragments)
        return f"io({self._typst_string(self.lang)}, {{ {body} }})"

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
        if raw.get("lang") in ALL_LANGUAGES:
            yield raw
