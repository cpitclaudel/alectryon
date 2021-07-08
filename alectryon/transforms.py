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

"""Post-process annotated fragments of source code."""
import re
import textwrap
from copy import copy
from collections import namedtuple
from itertools import chain
from .core import Text, Sentence, RichSentence, Goals, Messages

class IOAnnots:
    def __init__(self, *annots):
        self.filters = None
        self.unfold = None
        self.fails = None
        for annot in annots:
            self.update(annot)

    NO = re.compile("no-")
    RE = re.compile("[.]([-a-z]+)")
    FILTER_ALL = {'in': True, 'hyps': True, 'ccls': True, 'messages': True}
    FILTER_NONE = {'in': False, 'hyps': False, 'ccls': False, 'messages': False}
    META_FLAGS = {
        'out': ('messages', 'hyps', 'ccls'),
        'goals': ('hyps', 'ccls')
    }

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
            flags = self.META_FLAGS.get(annot, (annot,))
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

def enrich_sentences(fragments):
    """Change each ``Sentence`` in `fragments` into an ``RichSentence``."""
    for fr in fragments:
        if isinstance(fr, Sentence):
            # Always add goals & messages; empty lists are filtered out later
            outputs = [Messages(fr.messages), Goals(fr.goals)]
            yield RichSentence(contents=fr.contents, outputs=outputs,
                               prefixes=[], suffixes=[], annots=IOAnnots())
        else:
            yield fr

IO_COMMENT_RE = re.compile(r"[ \t]*[(][*]\s+(?:{}\s+)+[*][)]".format(IOAnnots.RE.pattern))

def process_io_annotations(fragments):
    """Strip IO comments and update ``.annots`` fields accordingly.

    This pass assumes that consecutive ``Text`` fragments have been
    coalesced.
    """
    annotated = []
    for fr in enrich_sentences(fragments):
        if isinstance(fr, Text):
            target = annotated[-1] if annotated else None
            assert not isinstance(target, Text)
        else:
            target = fr
        if target:
            for m in IO_COMMENT_RE.finditer(fr.contents):
                for mannot in IOAnnots.RE.finditer(m.group(0)):
                    target.annots.update(mannot.group(1))
            fr = fr._replace(contents=IO_COMMENT_RE.sub("", fr.contents))
        annotated.append(fr)
    return annotated

# pylint: disable=inconsistent-return-statements
def should_keep_output(output, annots):
    if isinstance(output, Messages):
        return annots["messages"] and output.messages
    if isinstance(output, Goals):
        return (annots["hyps"] or annots["ccls"]) and output.goals
    assert False

def commit_io_annotations(fragments, discard_folded=False):
    """Use I/O annotations to filter `fragments`.

    Hidden outputs of each `RichSentence` in `fragments` are discarded.
    Sentences with hidden inputs are set to ``contents=None``.  If
    `discard_folded` is ``True``, folded outputs are also discarded.
    """
    for fr in fragments:
        if isinstance(fr, RichSentence):
            if fr.annots.hide:
                continue

            contents = fr.contents if fr.annots["in"] else None
            if discard_folded and not fr.annots.unfold:
                outputs = []
            else:
                outputs = [o for o in fr.outputs if should_keep_output(o, fr.annots)]

            if not fr.annots["hyps"]:
                for o in outputs:
                    if isinstance(o, Goals):
                        for g in o.goals:
                            g.hypotheses.clear()

            if contents is None and outputs and not fr.annots.unfold:
                MSG = "Cannot show output of {!r} without .in or .unfold."
                raise ValueError(MSG.format(fr.contents))
            fr = fr._replace(contents=contents, outputs=outputs)
        yield fr

LEADING_BLANKS_RE = re.compile(r'\A([ \t]*(?:\n|\Z))?(.*?)([ \t]*)\Z',
                               flags=re.DOTALL)

def isolate_blanks(txt):
    """Split `txt` into blanks and an optional newline, text, and blanks."""
    return LEADING_BLANKS_RE.match(txt).groups()

def group_whitespace_with_code(fragments):
    """Attach spaces to neighboring sentences.

    This pass gathers all spaces following a sentence, up to the first
    (included) newline, and embeds them in the sentence itself (this ensures
    that we can hide the newline when we display the goals as a block).  It also
    collects spaces found at the beginning of a line (not including the
    preceding newline) and attaches them to the following sentence.

    This pass assumes that consecutive ``Text`` fragments have been
    coalesced.
    """
    grouped = list(enrich_sentences(fragments))
    for idx, fr in enumerate(grouped):
        if isinstance(fr, Text):
            before, rest, after = isolate_blanks(fr.contents)

            if before:
                if idx > 0:
                    assert not isinstance(grouped[idx - 1], Text)
                    grouped[idx - 1].suffixes.append(before)
                else:
                    rest = before + rest

            if after:
                if idx + 1 < len(grouped):
                    assert not isinstance(grouped[idx + 1], Text)
                    grouped[idx + 1].prefixes.append(after)
                else:
                    rest = rest + after

            grouped[idx] = Text(rest) if rest else None
    return [g for g in grouped if g is not None]

BULLET = re.compile(r"\A\s*[-+*]+\s*\Z")
def is_bullet(fr):
    return BULLET.match(fr.contents)

def attach_comments_to_code(fragments, predicate=lambda _: True):
    """Attach comments immediately following a sentence to the sentence itself.

    This is to support this common pattern::

       induction.
       - (* n = 0 *)
         …
       - (* n = S _ *) (* the hard case *) cbn.
         …

    A small complication is that we want to absorb only up to the end of a
    comment, not including subsequent spaces (for example, above, we want to
    capture ‘(* n = S _ *) (* the hard case *)’, without the final space).

    Only sentences for which `predicate` returns ``True`` are considered (to
    restrict the behavior to just bullets, pass ``is_bullet``.
    """
    from .literate import coq_partition, StringView, Code, Comment
    grouped = list(enrich_sentences(fragments))
    for idx, fr in enumerate(grouped):
        prev = idx > 0 and grouped[idx - 1]
        prev_is_sentence = isinstance(prev, (Sentence, RichSentence))
        if prev_is_sentence and predicate(prev) and isinstance(fr, Text):
            best = prefix = StringView(fr.contents, 0, 0)
            for part in coq_partition(fr.contents):
                if "\n" in part.v:
                    break
                if isinstance(part, Code) and not part.v.isspace():
                    break
                prefix += part.v
                if isinstance(part, Comment):
                    best = prefix
            if best:
                rest = fr.contents[len(best):]
                grouped[idx - 1] = prev._replace(contents=prev.contents + str(best))
                grouped[idx] = Text(rest) if rest else None
    return [g for g in grouped if g is not None]

def fragment_goal_sets(fr):
    if isinstance(fr, RichSentence):
        yield from (gs.goals for gs in fr.outputs if isinstance(gs, Goals))
    if isinstance(fr, Sentence):
        yield fr.goals

def fragment_message_sets(fr):
    if isinstance(fr, RichSentence):
        yield from (ms.messages for ms in fr.outputs if isinstance(ms, Messages))
    if isinstance(fr, Sentence):
        yield fr.messages

def group_hypotheses(fragments):
    for fr in fragments:
        for g in chain(*fragment_goal_sets(fr)):
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
        if isinstance(fr, RichSentence) and fr.annots.fails and FAIL_RE.match(fr.contents):
            for msgs in fragment_message_sets(fr):
                for idx, r in enumerate(msgs):
                    msgs[idx] = r._replace(contents=FAIL_MSG_RE.sub("", r.contents))
            fr = fr._replace(contents=FAIL_RE.sub("", fr.contents))
        yield fr

def dedent(fragments):
    for fr in fragments:
        for msgs in fragment_message_sets(fr):
            for idx, r in enumerate(msgs):
                msgs[idx] = r._replace(contents=textwrap.dedent(r.contents))
        yield fr

def _check_line_lengths(lines, first_linum, threshold, upto):
    for ln, line in enumerate(lines):
        if ln < upto and len(line) > threshold:
            yield first_linum + ln, line

def find_long_lines(fragments, threshold):
    linum, prefix = 0, ""
    for fr in fragments:
        prefix += "".join(getattr(fr, "prefixes", ()))
        suffix = "".join(getattr(fr, "suffixes", ()))
        lines = (prefix + fr.contents + suffix).split("\n")
        yield from _check_line_lengths(lines, linum, threshold, len(lines) - 1)
        linum += len(lines) - 1
        prefix = lines[-1]
    yield from _check_line_lengths(prefix.split("\n"), linum, threshold, len(lines))

COQ_CHUNK_DELIMITER = re.compile(r"(?:[ \t]*\n){2,}")

def partition_fragments(fragments, delim=COQ_CHUNK_DELIMITER):
    """Partition a list of `fragments` into chunks.

    The result is a list of chunks, each containing multiple fragments.  This
    can be useful as a post-processing step for .v files.  `delim` is a regular
    expression matching the delimiter (by default, two blank lines).
    """
    partitioned = [[]]
    for fr in fragments:
        if isinstance(fr, Text):
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
        if isinstance(fr, Text):
            fragments[idx] = fr = Text(contents=LBLANKS.sub("", fr.contents))
            if not fr.contents:
                continue
        break
    for idx, fr in reversed(list(enumerate(fragments))):
        if isinstance(fr, Text):
            fragments[idx] = fr = Text(contents=RBLANKS.sub("", fr.contents))
            if not fr.contents:
                continue
        break
    return fragments

def coalesce_text(fragments):
    """Coalesce consecutive ``Text`` objects in `fragments`."""
    last = None
    for fr in fragments:
        if isinstance(last, Text) and isinstance(fr, Text):
            last._replace(contents=last.contents + fr.contents)
        else:
            yield last
            last = fr
    if last:
        yield last

class CoqdocFragment(namedtuple("CoqdocFragment", "contents")):
    COQDOC_SPECIAL = re.compile(r"[(][*][*] +(remove +)?printing ")
    @property
    def special(self):
        return bool(self.COQDOC_SPECIAL.match(self.contents))

AlectryonFragments = namedtuple("AlectryonFragments", "fragments")
def isolate_coqdoc(fragments):
    from .literate import coq_partition_literate, Comment, COQDOC_OPEN
    refined = []
    for fr in fragments:
        if isinstance(fr, Text):
            for span in coq_partition_literate(fr.contents, opener=COQDOC_OPEN):
                wrapper = CoqdocFragment if isinstance(span, Comment) else Text
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

DEFAULT_TRANSFORMS = [
    enrich_sentences,
    attach_comments_to_code,
    group_hypotheses,
    process_io_annotations,
    strip_failures,
    dedent
]

def default_transform(fragments):
    for transform in DEFAULT_TRANSFORMS:
        fragments = transform(fragments)
    return list(fragments)
