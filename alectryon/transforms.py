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

from typing import Optional

import re
import textwrap
from copy import copy
from collections import namedtuple

from . import markers
from .core import Sentence, Text, Names, Enriched, \
    RichHypothesis, RichGoal, RichMessage, RichCode, \
    Goals, Messages, RichSentence

PathAnnot = namedtuple("PathAnnot", "enabled path")

class IOAnnots:
    def __init__(self):
        self.filters = None
        self.unfold = None
        self.fails = None
        self.paths = []

    NO = re.compile("no-")
    RE = re.compile("(?P<io>[-a-z]+)")
    DOTTED_RE = re.compile("[.]" + RE.pattern)
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
                    raise ValueError("Unknown flag `{}`.".format(flag))
                self.filters[flag] = not negated

    def update_paths(self, polarity, path):
        self.paths.append(PathAnnot(polarity != "-", path))

    @property
    def hidden(self):
        return self.filters == self.FILTER_NONE

    def inherit(self, other):
        for field, value in self.__dict__.items():
            if not value:
                setattr(self, field, copy(getattr(other, field)))

    def __getitem__(self, key):
        return self.filters[key] if self.filters else True

    def __repr__(self):
        return "IOAnnots(unfold={}, fails={}, filters={}, paths={})".format(
            self.unfold, self.fails, self.filters, self.paths)

def _enrich_goal(g):
    return RichGoal(g.name,
                    RichCode(g.conclusion),
                    [RichHypothesis(Names(h.names), h.body and RichCode(h.body), RichCode(h.type))
                     for h in g.hypotheses])

def enrich_sentences(fragments):
    """Change each ``Sentence`` in `fragments` into an ``RichSentence``."""
    for fr in fragments:
        if isinstance(fr, Sentence):
            # Always add goals & messages; empty lists are filtered out later
            outputs = [Messages([RichMessage(m.contents) for m in fr.messages]),
                       Goals([_enrich_goal(g) for g in fr.goals])]
            yield RichSentence(input=RichCode(fr.contents), outputs=outputs,
                               prefixes=[], suffixes=[], annots=IOAnnots())
        else:
            yield fr

ISOLATED = r"(?:\s|\A){}(?=\s|\Z)"
POLARIZED_PATH_SEGMENT = r"(?P<polarity>[-+]?)(?P<path>(?:{})+)".format(
    markers.MARKER_PATH_SEGMENT.pattern)

ONE_IO_FLAG = r"(?:{}|{})".format(
    IOAnnots.RE.pattern, POLARIZED_PATH_SEGMENT)
ONE_IO_FLAG_RE = re.compile(
    ISOLATED.format(ONE_IO_FLAG), re.VERBOSE)

ONE_IO_ANNOT = r"(?:{}|{})".format(
    IOAnnots.DOTTED_RE.pattern, POLARIZED_PATH_SEGMENT)
ONE_IO_ANNOT_RE = re.compile(
    ISOLATED.format(ONE_IO_ANNOT), re.VERBOSE)
IO_COMMENT_RE = re.compile(
    r"[ \t]*[(][*]\s+(?:{}\s+)+[*][)]".format(ONE_IO_ANNOT),
    re.VERBOSE)

def _parse_path(path):
    path = markers.parse_path(path)

    if path.get("io") is not None:
        raise ValueError("``.io`` not supported in visibility annotations")

    path.setdefault("io", None)
    path.setdefault("s", markers.TopMatcher())
    if "h" in path:
        path.setdefault("g", markers.TopMatcher())

    leaf = markers.set_leaf(path)
    if leaf in {"type", "body", "name"}:
        MSG = "``{}`` not supported in visibility annotations."
        raise ValueError(MSG.format(path["leaf"]))

    return path

def _update_io_flags(annots, flags_str, regex):
    for mannot in regex.finditer(flags_str):
        io, path, polarity = mannot.group("io", "path", "polarity")
        if io:
            annots.update(io)
        else:
            annots.update_paths(polarity, _parse_path(path))

def read_io_flags(annots, flags_str):
    _update_io_flags(annots, flags_str, ONE_IO_FLAG_RE)
    return ONE_IO_FLAG_RE.sub("", flags_str)

def _read_io_comments(annots, contents):
    for m in IO_COMMENT_RE.finditer(contents):
        _update_io_flags(annots, m.group(0), ONE_IO_ANNOT_RE)
    return IO_COMMENT_RE.sub("", contents)

def _contents(obj):
    if isinstance(obj, RichSentence):
        return obj.input.contents
    return obj.contents

def _replace_contents(fr, contents):
    if isinstance(fr, RichSentence):
        return fr._replace(input=fr.input._replace(contents=contents))
    return fr._replace(contents=contents)

def read_io_comments(fragments):
    """Strip IO comments and update ``.annots`` fields accordingly.

    This pass assumes that consecutive ``Text`` fragments have been
    coalesced.
    """
    last_sentence = None
    for fr in enrich_sentences(fragments):
        sentence: Optional[RichSentence] = last_sentence if isinstance(fr, Text) else fr
        if sentence:
            assert isinstance(sentence, RichSentence)
            try:
                contents = _read_io_comments(sentence.annots, _contents(fr)) # type: ignore
                fr = _replace_contents(fr, contents)
            except ValueError as e:
                yield e
        last_sentence = fr
        yield fr

def _find_marked(sentence, path):
    assert isinstance(sentence, RichSentence)

    if "s" in path and not path["s"].match(sentence.input.contents):
        return

    if "msg" in path:
        for m in markers.find_contents(list(fragment_messages(sentence)), path["msg"]):
            yield m
    elif "g" in path:
        for g in markers.find_goals(list(fragment_goals(sentence)), path["g"]):
            if "h" in path:
                for h in markers.find_hyps(g.hypotheses, path["h"]):
                    yield h
            elif "ccl" in path:
                yield g.conclusion
            else:
                yield g
    elif "in" in path:
        yield sentence.input
    else:
        yield sentence

def _find_flagged(sentence):
    annots = sentence.annots
    if not annots["in"]:
        yield sentence.input
    if not annots["hyps"]:
        for g in fragment_goals(sentence):
            yield from g.hypotheses
    if not annots["ccls"]:
        for g in fragment_goals(sentence):
            yield g.conclusion
    if not annots["messages"]:
        for m in fragment_messages(sentence):
            yield m

def process_io_annots(fragments):
    """Convert IO annotations to "enabled" flags."""
    for fr in fragments:
        if isinstance(fr, RichSentence):
            for (enabled, path) in fr.annots.paths:
                for obj in _find_marked(fr, path):
                    obj.flags["enabled"] = enabled
            for obj in _find_flagged(fr):
                obj.flags["enabled"] = False

            for g in fragment_goals(fr):
                if not any(_enabled(h) for h in g.hypotheses) and not _enabled(g.conclusion):
                    g.flags["enabled"] = False

            any_output = any(_enabled(o) for os in fr.outputs for o in _output_objects(os))

            if not _enabled(fr.input) and not any_output:
                fr.flags["enabled"] = False

            if not fr.annots.unfold and not _enabled(fr.input) and any_output:
                MSG = "Cannot show output of {!r} without .in or .unfold."
                yield ValueError(MSG.format(fr.input.contents))
        yield fr

def _enabled(o):
    return o.flags.get("enabled", True)

def _commit_enabled(objs):
    objs[:] = [o for o in objs if _enabled(o)]

def all_hidden(fragments, annots):
    """Check whether all `fragments` are hidden.
    ``RichSentence`` objects are hidden if their ``"enabled"` flag is set to
    false; ``Text`` objects are hidden if the default `annots` say so.
    """
    for fr in fragments:
        if isinstance(fr, RichSentence) and _enabled(fr):
            return False
        if isinstance(fr, Text) and not annots.hidden:
            return False
    return True

def _output_objects(o):
    if isinstance(o, Goals):
        return o.goals
    if isinstance(o, Messages):
        return o.messages
    assert False

def commit_io_annotations(fragments, discard_folded=False):
    """Use I/O annotations to filter `fragments`.

    Hidden outputs of each `RichSentence` in `fragments` are discarded.
    Sentences with hidden inputs are set to ``input=None``.  If
    `discard_folded` is ``True``, folded outputs are also discarded.
    """
    for fr in fragments:
        if isinstance(fr, RichSentence):
            if not _enabled(fr):
                continue

            for gs in fragment_goal_sets(fr):
                for idx, g in enumerate(gs):
                    _commit_enabled(g.hypotheses)
                    if not _enabled(g.conclusion):
                        gs[idx] = g._replace(conclusion=None)

            for o in fr.outputs:
                _commit_enabled(_output_objects(o))

            if not _enabled(fr.input):
                fr = fr._replace(input=None)

            if discard_folded and not fr.annots.unfold:
                fr.outputs.clear()
            else:
                fr.outputs[:] = [o for o in fr.outputs if _output_objects(o)]
        yield fr

def _sub_objects(obj):
    if isinstance(obj, RichSentence):
        return obj.outputs
    if isinstance(obj, RichGoal):
        return (obj.conclusion, *obj.hypotheses)
    if isinstance(obj, RichHypothesis):
        return obj.body, obj.type
    if isinstance(obj, (RichMessage, RichCode)):
        return ()
    assert False

def strip_ids_and_flags(obj):
    if isinstance(obj, Enriched):
        obj.ids.clear() # type: ignore
        obj.flags.clear() # type: ignore
        for obj_ in _sub_objects(obj):
            strip_ids_and_flags(obj_)
    return obj

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
    return BULLET.match(fr.input.contents)

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
        prev = grouped[idx - 1] if idx > 0 else None
        prev_is_sentence = isinstance(prev, RichSentence)
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
                grouped[idx - 1] = _replace_contents(prev, prev.input.contents + str(best))
                grouped[idx] = Text(rest) if rest else None
    return [g for g in grouped if g is not None]

def fragment_goal_sets(fr):
    if isinstance(fr, RichSentence):
        yield from (gs.goals for gs in fr.outputs if isinstance(gs, Goals))
    if isinstance(fr, Sentence):
        yield fr.goals

def fragment_goals(fr):
    for gs in fragment_goal_sets(fr):
        yield from gs

def fragment_message_sets(fr):
    if isinstance(fr, RichSentence):
        yield from (ms.messages for ms in fr.outputs if isinstance(ms, Messages))
    if isinstance(fr, Sentence):
        yield fr.messages

def fragment_messages(fr):
    for gs in fragment_message_sets(fr):
        yield from gs

def group_hypotheses(fragments):
    for fr in fragments:
        for g in fragment_goals(fr):
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
        if isinstance(fr, RichSentence) and fr.annots.fails and FAIL_RE.match(fr.input.contents):
            for msgs in fragment_message_sets(fr):
                for idx, r in enumerate(msgs):
                    msgs[idx] = r._replace(contents=FAIL_MSG_RE.sub("", r.contents))
            fr = _replace_contents(fr, FAIL_RE.sub("", fr.input.contents))
        yield fr

def dedent(fragments):
    for fr in fragments:
        for msgs in fragment_message_sets(fr):
            for idx, r in enumerate(msgs):
                msgs[idx] = r._replace(contents=textwrap.dedent(r.contents))
        yield fr

def _check_line_lengths(lines, first_linum, threshold, upto):
    # WISH: Only complain about long code lines, not long literate comments
    for ln, line in enumerate(lines):
        if ln < upto and len(line) > threshold:
            yield first_linum + ln, line

def find_long_lines(fragments, threshold):
    linum, prefix = 0, ""
    for fr in fragments:
        prefix += "".join(getattr(fr, "prefixes", ()))
        suffix = "".join(getattr(fr, "suffixes", ()))
        lines = (prefix + (_contents(fr) or "") + suffix).split("\n")
        yield from _check_line_lengths(lines, linum, threshold, len(lines) - 1)
        linum += len(lines) - 1
        prefix = lines[-1]
    lines = prefix.split("\n")
    yield from _check_line_lengths(lines, linum, threshold, len(lines))

COQ_CHUNK_DELIMITER = re.compile(r"(?:[ \t]*\n){2,}")

def partition_fragments(fragments, delim=COQ_CHUNK_DELIMITER):
    """Partition a list of `fragments` into chunks.

    The result is a list of chunks, each containing multiple fragments.  This
    can be useful as a pre-processing step for .v files.  `delim` is a regular
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
    read_io_comments,
    process_io_annots,
    strip_failures,
    dedent,
    # Not included:
    #   group_whitespace_with_code (not semantically relevant except)
    #   commit_io_annotations (breaks mref resolution by removing elements)
]

def filter_errors(outputs, delay_errors=False):
    transformed, errors = [], []
    for output in outputs:
        if isinstance(output, Exception):
            if not delay_errors:
                raise output
            errors.append(output)
        else:
            transformed.append(output)
    return transformed, errors

class CollectedErrors(ValueError):
    pass

def apply_transforms(fragments, transforms, delay_errors):
    errors = []
    for transform in transforms:
        fragments, errors[len(errors):] = filter_errors(transform(fragments), delay_errors)
    if errors:
        raise CollectedErrors(*errors)
    return fragments

def default_transform(fragments, delay_errors=False):
    return apply_transforms(fragments, DEFAULT_TRANSFORMS, delay_errors)
