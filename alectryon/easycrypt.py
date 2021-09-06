# Copyright © 2021 Clément Pit-Claudel
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

"""EasyCrypt frontend for Alectryon.

This is trickier than it should be for two reasons:

* Communicating with a plain-text REPL is a pain.
* The output of -tasts doesn't include final periods in sentences, so the
  segmentation code needs to reparse comments and move periods around (see
  ``reattach_periods``).
"""

import re
import subprocess
import tempfile
from collections import deque
from pathlib import Path

from . import literate
from .coq import CoqIdents
from .core import DriverInfo, TextREPLDriver, Document, EncodedDocument, \
    Positioned, Position, Goal, Hypothesis, Message, Sentence, Text

class EasyCrypt(TextREPLDriver):
    BIN = "easycrypt"
    NAME = "EasyCrypt"

    REPL_ARGS = ("cli", '-pragmas', 'Proofs:weak', "-emacs", "-pp-width", "55",)
    CLI_ARGS = ("compile", "-no-eco", '-pragmas', 'Proofs:weak',)
    VERSION_ARGS = ("config",)

    ID = "easycrypt_repl"
    LANGUAGE = "easycrypt"

    CLI_ENCODING = REPL_ENCODING = "utf-8"
    VERSION_RE = re.compile(rb"^git-hash:\s+(.*)$", re.MULTILINE)
    TSTATS_RE = re.compile(r"^([0-9]+):([0-9]+) ([0-9]+):([0-9]+) [^ ]+$", re.MULTILINE)

    @classmethod
    def version_info(cls, binpath=None):
        cmd = [cls.resolve_driver(binpath), *cls.VERSION_ARGS]
        bs = subprocess.check_output(cmd, stderr=subprocess.STDOUT)
        version = next(iter(cls.VERSION_RE.findall(bs)), b"??").decode('ascii', 'ignore')
        return DriverInfo(cls.NAME, version)

    @property
    def topfile(self):
        return CoqIdents.topfile_of_fpath(self.fpath, "top", exts=(".ec", ".eca"))

    def _find_sentences(self, doc):
        with tempfile.TemporaryDirectory(prefix="alectryon_easycrypt") as wd:
            source = Path(wd) / self.topfile
            dest = source.with_suffix(".tstats")
            source.write_bytes(doc.contents)
            self.run_cli(more_args=("-tstats", str(dest), str(source)))
            tstats = dest.read_text()
        last_end = 0
        for m in self.TSTATS_RE.finditer(tstats):
            begl, begc, endl, endc = map(int, m.groups())
            beg, end = doc.pos2offset(begl, begc), doc.pos2offset(endl, endc)
            beg = max(beg, last_end) # https://github.com/EasyCrypt/easycrypt/issues/73
            yield Positioned(beg, end, Sentence(doc[beg:end], [], []))
            last_end = end

    @staticmethod
    def find_period(txt):
        """Find first period in `txt`, skipping over comments (raise if none)."""
        beg = 0
        for part in literate.coq_partition(txt):
            if isinstance(part, literate.Code) and part.v.find(".") >= 0:
                return beg + part.v.find(".") # LATER: Deduplicate call to .find()
            beg += len(part.v)
        raise ValueError("Unterminated sentence before `{}`.".format(txt))

    @classmethod
    def reattach_periods(cls, frs):
        """Move first '.' of each fragment to preceding ``Sentence``, if any.

        >>> EasyCrypt.reattach_periods([Sentence("print ", [], []), Text("(*.a.*). (*.b.*)")])
        [Sentence(contents='print (*.a.*).', messages=[], goals=[]), Text(contents=' (*.b.*)')]
        """
        for idx, fr in enumerate(frs):
            if idx > 0 and isinstance(frs[idx - 1], Sentence):
                period = cls.find_period(fr.contents)
                before, after = fr.contents[:period + 1], fr.contents[period + 1:]
                frs[idx - 1] = frs[idx - 1]._replace(contents=frs[idx - 1].contents + before)
                frs[idx] = fr._replace(contents=after)
        return [fr for fr in frs if not (isinstance(fr, Text) and not fr.contents)]

    BLANKS = re.compile(r"\s+", re.DOTALL)

    @classmethod
    def isolate_comments(cls, fr):
        """Move comments from beginning of sentences into their own ``Text``.

        Needed due to https://github.com/EasyCrypt/easycrypt/issues/73.

        >>> list(EasyCrypt.isolate_comments(Sentence("(* a *) print ", [], [])))
        [Text(contents='(* a *) '), Sentence(contents='print ', messages=[], goals=[])]
        """
        parts = deque(literate.coq_partition(fr.contents))
        txt = ""
        while parts and (parts[0].v.isspace() or isinstance(parts[0], literate.Comment)):
            txt += str(parts.popleft().v)
        if parts:
            m = parts[0].v.match(cls.BLANKS)
            if m:
                pos = m.end() - m.start()
                txt += str(parts[0].v[:pos])
                parts[0] = parts[0]._replace(v = parts[0].v[pos:])
        if txt:
            yield Text(txt)
        contents = "".join(str(p.v) for p in parts)
        if contents:
            yield fr._replace(contents=contents)

    def partition(self, doc: Document):
        frs = list(doc.intersperse_text_fragments(doc, self._find_sentences(doc)))
        frs = self.reattach_periods(frs)
        frs = [f for fr in frs for f in self.isolate_comments(fr)]
        # from pprint import pprint; pprint(frs)
        return frs

    GOAL_RE = re.compile(r"""
        Current[ ]goal.*?\n\n
        Type[ ]variables:[ ](?P<type_vars>.*?)\n\n
        (?:(?P<hyps>.*?)\n)?
        --------------------------------*\n
        (?P<ccl>.*)
    """, re.VERBOSE | re.DOTALL)

    HYP_RE = re.compile(r"""
        (?P<hyp>
         (?P<name>[^ ]+)\s*:\s*
         (?P<type>.+(?:\n[ ].+)*)\n)
    """, re.VERBOSE)

    @staticmethod
    def _parse_hyps(hyps):
        hyps = hyps.strip()
        if not hyps:
            return
        for hyp in re.split(r"\n(?! )", hyps.strip()):
            name, sep, typ = re.split(r"(\s*:\s*)", hyp, 1)
            indentation = " " * (len(name) + len(sep))
            yield Hypothesis([name], None, re.sub("^" + indentation, "", typ))

    @staticmethod
    def _parse_type_vars(type_vars):
        if type_vars == "<none>":
            return
        names = re.split(r"\s*,\s*", type_vars)
        yield Hypothesis(names, None, "<type variable>")

    @classmethod
    def _parse_response(cls, response):
        response = re.sub(r"[ \t]+$", "", response, flags=re.MULTILINE).strip()
        end, goals, messages = 0, [], []
        for gl in cls.GOAL_RE.finditer(response):
            if gl.start() > end:
                messages.append(Message(response[end:gl.start()].strip()))
            type_vars, hyps, ccl = gl.group("type_vars", "hyps", "ccl")
            hyps = [*cls._parse_type_vars(type_vars), *cls._parse_hyps(hyps or "")]
            goals.append(Goal(None, ccl, hyps))
            end = gl.end()
        if end < len(response):
            messages.append(Message(response[end:].strip()))
        return goals, messages

    def _read_until_prompt(self):
        response = ""
        while True:
            line = self._read()
            if "]>" in line: # FIXME
                return response
            response += line

    def _annotate_one(self, fr):
        if isinstance(fr, Sentence):
            self._write(fr.contents, "\n")
            response = self._read_until_prompt()
            if response:
                goals, messages = self._parse_response(response)
                fr = fr._replace(goals=goals, messages=messages)
        return fr

    def _annotate_fragments(self, fragments):
        with self:
            self._read_until_prompt()
            for fr in fragments:
                yield self._annotate_one(fr)

    def annotate(self, chunks):
        r"""Use ``easycrypt -tstats`` to fragment annotate EasyCrypt code.

        >>> EasyCrypt().annotate(["print type int (* ... *). (* … *) ", "lemma t: true."])
        [[Sentence(contents='print type int (* ... *).',
                   messages=[Message(contents='type int.')], goals=[]),
         Text(contents=' (* … *) ')],
        [Sentence(contents='lemma t: true.', messages=[],
                  goals=[Goal(name=None, conclusion='true', hypotheses=[])])]]
        >>> EasyCrypt().annotate(["print type int. require import Int. (* … *)"])
        [[Sentence(contents='print type int.',
                   messages=[Message(contents='type int.')], goals=[]),
          Text(contents=' '),
          Sentence(contents='require import Int.', messages=[], goals=[]),
          Text(contents=' (* … *)')]]
        """
        # import sys
        # from . import core
        # core.DEBUG = True
        document = EncodedDocument(chunks, "\n", encoding=self.CLI_ENCODING)
        # document = Document(chunks, "\n")
        try:
            # from pprint import pprint; pprint(chunks, stream=sys.stderr)
            fragments = list(self.partition(document))
            # from pprint import pprint; pprint(fragments, stream=sys.stderr)
            # from pprint import pprint; sys.stderr.flush()
            annotated = list(self._annotate_fragments(fragments))
            return list(document.recover_chunks(annotated))
        except ValueError as e:
            self.observer.notify(None, str(e), Position(self.fpath, 0, 1), level=3)
            return [[Text(c)] for c in chunks]
