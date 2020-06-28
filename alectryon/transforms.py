# Copyright © 2019 Clément Pit-Claudel
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

"""Post-process annotated fragments of Coq code."""
import re
import textwrap
from copy import copy
from collections import namedtuple
from .core import CoqText, CoqSentence, HTMLSentence

class IOAnnots:
    def __init__(self, *annots):
        self.filters = None
        self.unfold = None
        self.fails = None
        for annot in annots:
            self.update(annot)

    NO = re.compile("no-")
    FILTER_ALL = { 'in': True, 'goals': True, 'messages': True }
    FILTER_NONE = { 'in': False, 'goals': False, 'messages': False }
    RE = re.compile("[.]([-a-z]+)")

    def update(self, annot):
        if annot == 'fails':
            self.fails = True
        elif annot == 'succeeds':
            self.fails = False

        elif annot == 'fold':
            self.unfold = False
        elif annot == 'unfold':
            self.unfold = True

        elif annot == 'all':
            self.filters = self.FILTER_ALL
        elif annot == 'none':
            self.filters = self.FILTER_NONE

        else:
            negated, annot = self.NO.match(annot), self.NO.sub("", annot)
            if self.filters is None:
                self.filters = copy(self.FILTER_ALL if negated else self.FILTER_NONE)
            flags = ('messages', 'goals') if annot == 'out' else (annot,)
            for flag in flags:
                if flag not in self.filters:
                    raise ValueError("Unknown flag {}".format(flag))
                self.filters[flag] = not negated

    @property
    def hide(self):
        return self.filters == self.FILTER_NONE

    def inherit(self, other):
        for field, value in self.__dict__.items():
            if value is None:
                setattr(self, field, copy(getattr(other, field)))

    def __getitem__(self, key):
        return self.filters[key] if self.filters else True

    def __repr__(self):
        return "IOAnnots(unfold={}, fails={}, filters={})".format(
            self.unfold, self.fails, self.filters)

def htmlify_sentences(fragments):
    for fr in fragments:
        if isinstance(fr, CoqSentence):
            yield HTMLSentence(prefixes=[], suffixes=[], annots=IOAnnots(),
                           **fr._asdict())
        else:
            yield fr

IO_COMMENT_RE = re.compile(r"[ \t]*[(][*]\s+(?:{}\s+)+[*][)]".format(IOAnnots.RE.pattern))

def process_io_annotations(fragments):
    annotated = []
    for fr in htmlify_sentences(fragments):
        if isinstance(fr, CoqText):
            target = annotated[-1] if annotated else None
        else:
            target = fr
        if target:
            for m in IO_COMMENT_RE.finditer(fr.contents):
                for mannot in IOAnnots.RE.finditer(m.group(0)):
                    target.annots.update(mannot.group(1))
            fr = fr._replace(contents=IO_COMMENT_RE.sub("", fr.contents))
        annotated.append(fr)
    return annotated

LEADING_BLANKS_RE = re.compile(r'\A([ \t]*(?:\n|\Z))?(.*?)([ \t]*)\Z',
                               flags=re.DOTALL)

def isolate_blanks(txt):
    return LEADING_BLANKS_RE.match(txt).groups()

def group_whitespace_with_code(fragments):
    # Attach all spaces following a code fragment, up to the first newline, to
    # the code fragment itself.  This makes sure that (1) we can hide the
    # newline when we display the goals as a block, and (2) that we don't hide
    # the goals when the user hovers on spaces between two tactics.
    grouped = list(htmlify_sentences(fragments))
    for idx, fr in enumerate(grouped):
        if isinstance(fr, CoqText):
            before, rest, after = isolate_blanks(fr.contents)

            if before:
                if idx > 0:
                    grouped[idx - 1].suffixes.append(before)
                else:
                    rest = before + rest

            if after:
                if idx + 1 < len(grouped):
                    grouped[idx + 1].prefixes.append(after)
                else:
                    rest = rest + after

            grouped[idx] = CoqText(rest) if rest else None
    return [g for g in grouped if g is not None]

def group_hypotheses(fragments):
    for fr in fragments:
        if isinstance(fr, (HTMLSentence, CoqSentence)):
            for g in fr.goals:
                hyps = []
                for hyp in g.hypotheses:
                    if (hyps
                        and hyp.body is None and hyps[-1].body is None
                        and hyps[-1].type == hyp.type):
                        hyps[-1].names.extend(hyp.names)
                    else:
                        hyps.append(hyp)
                g.hypotheses[:] = hyps
    return fragments

FAIL_RE = re.compile(r"^Fail\s+")
FAIL_MSG_RE = re.compile(r"^The command has indeed failed with message:\s+")

def strip_failures(fragments):
    for fr in fragments:
        if hasattr(fr, 'annots') and fr.annots.fails and FAIL_RE.match(fr.contents):
            for idx, r in enumerate(fr.responses):
                fr.responses[idx] = FAIL_MSG_RE.sub("", r)
            fr = fr._replace(contents=FAIL_RE.sub("", fr.contents))
        yield fr

def dedent(fragments):
    for fr in fragments:
        if hasattr(fr, 'responses'):
            for idx, r in enumerate(fr.responses):
                fr.responses[idx] = textwrap.dedent(r)
        yield fr

def find_long_lines(fragments, threshold):
    prefix = ""
    for fr in fragments:
        prefix += "".join(getattr(fr, "prefixes", ()))
        suffix = "".join(getattr(fr, "suffixes", ()))
        lines = (prefix + fr.contents + suffix).split("\n")
        for line in lines:
            if len(line) > threshold:
                yield line
        prefix = lines[-1]

COQ_CHUNK_DELIMITER = re.compile(r"(?:[ \t]*\n){2,}")

def partition_fragments(fragments, delim=COQ_CHUNK_DELIMITER):
    """Partition a list of `fragments` into chunks.

    The result is a list of chunks, each containing multiple fragments.  This
    can be useful as a post-processing step for .v files.  `delim` is a regular
    expression matching the delimiter (by default, two blank lines).
    """
    partitioned = [[]]
    for fr in fragments:
        if isinstance(fr, CoqText):
            m = delim.match(fr.contents)
            if m:
                if partitioned[-1]:
                    partitioned.append([])
                fr = fr._replace(contents=fr.contents[m.end():])
                if not fr.contents:
                    continue
        partitioned[-1].append(fr)
    return partitioned

LBLANKS = re.compile(r"\A([ \t]*\n)+")
RBLANKS = re.compile(r"(\n[ \t]*)+\Z")

def strip_text(fragments):
    for idx, fr in enumerate(fragments):
        if isinstance(fr, CoqText):
            fragments[idx] = fr = CoqText(contents=LBLANKS.sub("", fr.contents))
            if not fr.contents:
                continue
        break
    for idx, fr in reversed(list(enumerate(fragments))):
        if isinstance(fr, CoqText):
            fragments[idx] = fr = CoqText(contents=RBLANKS.sub("", fr.contents))
            if not fr.contents:
                continue
        break
    return fragments

CoqdocFragment = namedtuple("CoqdocFragment", "contents")
AlectryonFragments = namedtuple("AlectryonFragments", "fragments")
def isolate_coqdoc(fragments):
    from .literate import coq_partition_literate, Comment, COQDOC_OPEN
    refined = []
    for fr in fragments:
        if isinstance(fr, CoqText):
            for span in coq_partition_literate(fr.contents, opener=COQDOC_OPEN):
                wrapper = CoqdocFragment if isinstance(span, Comment) else CoqText
                refined.append(wrapper(str(span.v)))
        else:
            refined.append(fr)
    partitioned = []
    for fr in refined:
        if isinstance(fr, CoqdocFragment):
            partitioned.append(fr)
        else:
            if not partitioned or not isinstance(partitioned[-1], AlectryonFragments):
                partitioned.append(AlectryonFragments([]))
            partitioned[-1].fragments.append(fr)
    for part in partitioned:
        if isinstance(part, AlectryonFragments):
            strip_text(part.fragments)
    return partitioned

def default_transform(fragments):
    fragments = list(htmlify_sentences(fragments))
    fragments = group_hypotheses(fragments)
    fragments = process_io_annotations(fragments)
    fragments = strip_failures(fragments)
    fragments = dedent(fragments)
    return list(fragments)
