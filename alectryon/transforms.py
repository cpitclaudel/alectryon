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

from typing import Optional, Tuple

import re
import textwrap
from copy import copy
from collections import namedtuple

from . import markers
from .core import Sentence, Text, Names, Enriched, \
    RichHypothesis, RichGoal, RichMessage, RichCode, \
    Goals, Messages, RichSentence, ALL_LANGUAGES

PathAnnot = namedtuple("PathAnnot", "raw path key val must_match")

class IOAnnots:
    def __init__(self, unfold=None, fails=None, filters=None, props=()):
        self.filters = filters
        self.unfold = unfold
        self.fails = fails
        self.props = list(props)

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

    def update_props(self, raw, path, key, val, must_match):
        self.props.append(PathAnnot(raw, path, key, val, must_match))

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
        return "IOAnnots(unfold={}, fails={}, filters={}, props={})".format(
            self.unfold, self.fails, self.filters, self.props)

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
POLARIZED_PATH_SEGMENT = r"""
  (?P<polarity>[-+]?)
  (?P<path>(?:{})+)
  (?:\[(?P<key>[a-z]+)\]=(?P<value>[A-Za-z0-9_]+))?
""".format(
    markers.MARKER_PATH_SEGMENT.pattern)

ONE_IO_FLAG = r"(?:{}|{})".format(
    IOAnnots.RE.pattern, POLARIZED_PATH_SEGMENT)
ONE_IO_FLAG_RE = re.compile(
    ISOLATED.format(ONE_IO_FLAG), re.VERBOSE)

ONE_IO_ANNOT = r"(?:{}|{})".format(
    IOAnnots.DOTTED_RE.pattern, POLARIZED_PATH_SEGMENT)
ONE_IO_ANNOT_RE = re.compile(
    ISOLATED.format(ONE_IO_ANNOT), re.VERBOSE)

_IO_ANNOTS_IN_COMMENT = r"\s+(?:{}\s+)+".format(ONE_IO_ANNOT)
_IO_COMMENT_RE = {
    "coq": r"[ \t]*[(][*]{}[*][)]",
    "dafny": r"[ \t]*[/][*]{}[*][/]",
    "lean3": r"[ \t]*[/][-]{}[-][/]",
    "lean4": r"[ \t]*[/][-]{}[-][/]"
}
IO_COMMENT_RE = {
    lang: re.compile(r.format(_IO_ANNOTS_IN_COMMENT), re.VERBOSE)
    for lang, r in _IO_COMMENT_RE.items()
}
assert _IO_COMMENT_RE.keys() == ALL_LANGUAGES

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

def _update_io_annots(annots, annots_str, regex, must_match):
    for mannot in regex.finditer(annots_str):
        io, path, polarity, key, val = mannot.group("io", "path", "polarity", "key", "value")
        if io:
            annots.update(io)
        else:
            if not key:
                key, val = "enabled", polarity != "-"
            annots.update_props(path, _parse_path(path), key, val, must_match)

def read_io_flags(annots, flags_str, must_match=False):
    _update_io_annots(annots, flags_str, ONE_IO_FLAG_RE, must_match)
    return ONE_IO_FLAG_RE.sub("", flags_str)

def read_all_io_flags(s, must_match=False):
    """Like ``read_io_flags``, but raise if `s` has other contents.

    `must_match` indicates whether an error should be raised for marker-placement
    paths that don't match.  Typically the flags in the arguments line of a
    ``.. coq::`` directive don't match all sentences, whereas IO annotations in
    comments *are* expected to match part the sentence that they apply to
    (otherwise they're useless).
    """
    annots = IOAnnots()
    leftover = read_io_flags(annots, s, must_match).strip()
    if leftover:
        raise ValueError("Unrecognized directive flags: {}".format(leftover))
    return annots

def inherit_io_annots(fragments, annots):
    """Apply `annots` to each fragment in `fragments`."""
    for fr in enrich_sentences(fragments):
        if hasattr(fr, 'annots'):
            fr.annots.inherit(annots)
        yield fr

def __read_io_comments(annots, contents, lang, must_match=True):
    for m in IO_COMMENT_RE[lang].finditer(contents):
        _update_io_annots(annots, m.group(0), ONE_IO_ANNOT_RE, must_match=must_match)
    return IO_COMMENT_RE[lang].sub("", contents)

def _contents(obj):
    if isinstance(obj, RichSentence):
        return obj.input.contents
    return obj.contents

def _replace_contents(fr, contents):
    if isinstance(fr, RichSentence):
        return fr._replace(input=fr.input._replace(contents=contents))
    return fr._replace(contents=contents)

def _read_io_comments(fragments, lang):
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
                contents = __read_io_comments(sentence.annots, _contents(fr), lang) # type: ignore
                fr = _replace_contents(fr, contents)
            except ValueError as e:
                yield e
        last_sentence = fr
        yield fr

def read_io_comments(lang):
    return lambda fragments: _read_io_comments(fragments, lang=lang)

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

def _find_hidden_by_annots(sentence):
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
    """Convert IO annotations to pre-object properties."""
    for fr in fragments:
        if isinstance(fr, RichSentence):
            for (raw, path, key, val, reqd) in fr.annots.props:
                for obj in _find_marked(fr, path):
                    obj.props[key] = val
                    reqd = False
                if reqd:
                    MSG = "No match found for `{}` in `{}`"
                    yield ValueError(MSG.format(raw, fr.input.contents))

            for obj in _find_hidden_by_annots(fr):
                obj.props["enabled"] = False

            for g in fragment_goals(fr):
                if not any(_enabled(h) for h in g.hypotheses) and not _enabled(g.conclusion):
                    g.props["enabled"] = False

            any_output = any(_enabled(o) for os in fr.outputs for o in _output_objects(os))

            if not _enabled(fr.input) and not any_output:
                fr.props["enabled"] = False

            if not fr.annots.unfold and not _enabled(fr.input) and any_output:
                MSG = "Cannot show output of {!r} without .in or .unfold."
                yield ValueError(MSG.format(fr.input.contents))
        yield fr

def _enabled(o):
    return o.props.get("enabled", True)

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

def commit_io_annotations(fragments):
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

            fr.outputs[:] = [o for o in fr.outputs if _output_objects(o)]
        yield fr

def _sub_objects(obj):
    """Return an iterable of objects contained within obj."""
    if isinstance(obj, RichSentence):
        yield from obj.outputs
    elif isinstance(obj, RichGoal):
        yield obj.conclusion
        yield from obj.hypotheses
    elif isinstance(obj, RichHypothesis):
        yield obj.body
        yield obj.type
    elif isinstance(obj, Messages):
        yield from obj.messages
    elif isinstance(obj, Goals):
        yield from obj.goals

def _all_sub_objects(obj):
    """Return an iterable of objects contained within obj.

    >>> from . import core as c
    >>> s = c.Sentence("s",
    ...   [c.Message("m")],
    ...   [c.Goal("n", "c", [c.Hypothesis(["h"], None, "t")])])
    >>> list(_all_sub_objects(next(enrich_sentences([s])))) # doctest: +ELLIPSIS
    [RichSentence...,
       Messages..., RichMessage...,
       Goals..., RichGoal...,
         RichCode..., RichHypothesis..., RichCode...]
    """
    yield obj
    for obj_ in _sub_objects(obj):
        yield from _all_sub_objects(obj_)

def strip_ids_and_props(obj, props):
    for so in _all_sub_objects(obj):
        if isinstance(so, Enriched):
            so.ids.clear() # type: ignore
            for p in props:
                so.props.pop(p, None) # type: ignore
    return obj

LEADING_BLANKS_RE = re.compile(r'\A([ \t]*(?:\n|\Z))?(.*?)([ \t]*)\Z',
                               flags=re.DOTALL)

def isolate_blanks(txt) -> Tuple[int, int]:
    """Split `txt` into blanks and an optional newline, text, and blanks.
    Returns the positions of the two splits.
    """
    return LEADING_BLANKS_RE.match(txt).span(2)

def group_whitespace_with_code(fragments):
    r"""Attach spaces to neighboring sentences.

    This pass gathers all spaces following a sentence, up to the first
    (included) newline, and embeds them in the sentence itself (this ensures
    that we can hide the newline when we display the goals as a block).  It also
    collects spaces found at the beginning of a line (not including the
    preceding newline) and attaches them to the following sentence.

    This pass assumes that consecutive ``Text`` fragments have been
    coalesced.

    >>> from .core import Sentence as S, Text as T
    >>> group_whitespace_with_code([T(" \n 1 "), S("S", [], []), T(" \n 2 ")])
    ... # doctest: +ELLIPSIS
    [Text(contents=' \n 1'),
     RichSentence(...contents='S'..., ...prefixes=[' '], suffixes=[' \n']...),
     Text(contents=' 2 ')]
    """
    grouped = list(enrich_sentences(fragments))
    for idx, fr in enumerate(grouped):
        if isinstance(fr, Text):
            txt = fr.contents
            beg, end = isolate_blanks(txt)

            if 0 < beg:
                if idx > 0:
                    assert not isinstance(grouped[idx - 1], Text)
                    grouped[idx - 1].suffixes.append(txt[:beg])
                elif beg == end: # blank text at very beginning
                    beg = end = 0
                else:
                    beg = 0

            if end < len(txt):
                if idx + 1 < len(grouped):
                    assert not isinstance(grouped[idx + 1], Text)
                    grouped[idx + 1].prefixes.append(txt[end:])
                else:
                    end = len(txt)

            grouped[idx] = Text(txt[beg:end]) if end > beg else None
    return [g for g in grouped if g is not None]

COQ_BULLET = re.compile(r"\A\s*[-+*]+\s*\Z")
def is_coq_bullet(fr):
    return COQ_BULLET.match(fr.input.contents)

def _attach_comments_to_code(lang, fragments, predicate=lambda _: True):
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
    restrict the behavior to just bullets, pass ``is_coq_bullet``.

    >>> from .core import Sentence as S, Text as T
    >>> frs = [S("-", [], []), T(" (* … *) "), S("cbn.", [], []), T("(* … *)")]
    >>> attach_comments_to_code("coq")(frs) # doctest: +ELLIPSIS
    [RichSentence(...contents='- (* … *)'...), Text(contents=' '),
     RichSentence(...contents='cbn.(* … *)'...)]
    >>> attach_comments_to_code("coq")(frs, predicate=is_coq_bullet) # doctest: +ELLIPSIS
    [RichSentence(...contents='- (* … *)'...), Text(contents=' '),
     RichSentence(...contents='cbn.'...), Text(contents='(* … *)')]
    """
    from .literate import partition, StringView, Code, Comment
    grouped = list(enrich_sentences(fragments))
    for idx, fr in enumerate(grouped):
        prev = grouped[idx - 1] if idx > 0 else None
        prev_is_sentence = isinstance(prev, RichSentence)
        if prev_is_sentence and predicate(prev) and isinstance(fr, Text):
            best = prefix = StringView(fr.contents, 0, 0)
            for part in partition(lang, fr.contents):
                if "\n" in part.v:
                    break
                if isinstance(part, Code):
                    assert part.v.isspace()
                prefix += part.v
                if isinstance(part, Comment):
                    best = prefix
            if best:
                rest = fr.contents[len(best):]
                grouped[idx - 1] = _replace_contents(prev, _contents(prev) + str(best))
                grouped[idx] = Text(rest) if rest else None
    return [g for g in grouped if g is not None]

def attach_comments_to_code(lang_name):
    """Attach comments to preceding code (see ``attach_comments_to_code``)."""
    def attach_comments_to_code_wrapper(*args, **kwargs):
        from .literate import LANGUAGES
        return _attach_comments_to_code(LANGUAGES[lang_name], *args, **kwargs)
    return attach_comments_to_code_wrapper

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
    """Merge consecutive hypotheses with the same name.

    >>> from .core import Sentence as S, Goal as G, Hypothesis as H
    >>> group_hypotheses([S("", [], [G("", "", [H([n], None, 'nat') for n in 'abc'])])])
    ... # doctest: +ELLIPSIS
    [...hypotheses=[Hypothesis(names=['a', 'b', 'c'], body=None, type='nat')]...]
    """
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

COQ_FAIL_RE = re.compile(r"^Fail\s+")
COQ_FAIL_MSG_RE = re.compile(r"^The command has indeed failed with message:\s+")

def is_coq_fail(fr):
    return (isinstance(fr, RichSentence) and fr.annots.fails
            and COQ_FAIL_RE.match(fr.input.contents))

def strip_coq_failures(fragments):
    for fr in fragments:
        if is_coq_fail(fr):
            for msgs in fragment_message_sets(fr):
                for idx, r in enumerate(msgs):
                    msgs[idx] = r._replace(contents=COQ_FAIL_MSG_RE.sub("", r.contents))
            fr = _replace_contents(fr, COQ_FAIL_RE.sub("", fr.input.contents))
        yield fr

def dedent(fragments):
    r"""Dedent messages.

    >>> from .core import Sentence as S, Message as M
    >>> list(dedent([S("", [M("  1\n    : nat")], [])])) # doctest: +ELLIPSIS
    [...messages=[Message(contents='1\n  : nat')]...]
    """
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
        if hasattr(fr, "props") and not _enabled(fr):
            continue
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
    r"""Partition a list of `fragments` into chunks.

    The result is a list of chunks, each containing multiple fragments.  This
    can be useful as a pre-processing step for .v files.  `delim` is a regular
    expression matching the delimiter (by default, two blank lines).

    >>> partition_fragments([Text("Goal True."), Text("  \n\n"), Text("split.")])
    [[Text(contents='Goal True.')], [Text(contents='split.')]]
    >>> partition_fragments([Text("Goal True."), Text(" (*x*) \n\n "), Text("split.")])
    [[Text(contents='Goal True.'), Text(contents=' (*x*)')],
     [Text(contents=' '), Text(contents='split.')]]
    """
    partitioned = [[]]
    for fr in fragments:
        if isinstance(fr, Text):
            m = delim.search(fr.contents)
            if m:
                before, after = fr.contents[:m.start()], fr.contents[m.end():]
                if before:
                    partitioned[-1].append(Text(before))
                if partitioned[-1]:
                    partitioned.append([])
                if not after:
                    continue
                fr = fr._replace(contents=after)
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
    r"""Coalesce consecutive ``Text`` objects in `fragments`.

    >>> list(coalesce_text([
    ...    Sentence(contents='apply Lt.le_lt_trans.', messages=[], goals=[]),
    ...    Text(contents=' \n       (* ... *) '),
    ...    Text(contents=' \n '),
    ...    Sentence(contents='Qed.', messages=[], goals=[]),
    ...    Text(contents=' \n ')
    ... ]))
    [Sentence(contents='apply Lt.le_lt_trans.', messages=[], goals=[]),
     Text(contents=' \n       (* ... *)  \n '),
     Sentence(contents='Qed.', messages=[], goals=[]),
     Text(contents=' \n ')]
    """
    last = None
    for fr in fragments:
        if isinstance(last, Text) and isinstance(fr, Text):
            last = last._replace(contents=last.contents + fr.contents)
        else:
            if last:
                yield last
            last = fr
    if last:
        yield last

class CoqdocFragment(namedtuple("CoqdocFragment", "contents")):
    COQDOC_SPECIAL = re.compile(r"[(][*][*] +(remove +)?printing ")
    @property
    def special(self):
        return bool(self.COQDOC_SPECIAL.match(self.contents))

COQDOC_OPEN = re.compile(r"[(][*][*]\s[ \t]*")
AlectryonFragments = namedtuple("AlectryonFragments", "fragments")
def isolate_coqdoc(fragments):
    from .literate import partition_literate, Comment, COQ
    refined = []
    for fr in fragments:
        if isinstance(fr, Text):
            for span in partition_literate(COQ, fr.contents, opener=COQDOC_OPEN):
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

SURROUNDING_BLANKS_RE = re.compile(r"\A(\s*)(.*?)(\s*)\Z", re.DOTALL)


def split_surrounding_space(fr):
    before, txt, after = SURROUNDING_BLANKS_RE.match(_contents(fr)).groups()
    if before: yield Text(before)
    if txt: yield _replace_contents(fr, txt)
    if after: yield Text(after)

def lean3_split_comments(fragments):
    r"""Make sure that ``Text`` objects in `fragments` only contain whitespace and comments.

    >>> from .core import Sentence as S, Text as T
    >>> list(lean3_split_comments([T(" A \n /- x -/ B \n"), S("\n S", [], [])]))
    [Text(contents=' '), Sentence(contents='A', messages=[], goals=[]),
     Text(contents=' \n '), Text(contents='/- x -/'), Text(contents=' '),
     Sentence(contents='B', messages=[], goals=[]), Text(contents=' \n'),
     Sentence(contents='\n S', messages=[], goals=[])]
    """
    from .literate import LEAN3, partition, Code, Comment
    for fr in fragments:
        if isinstance(fr, Text):
            for part in partition(LEAN3, fr.contents):
                if isinstance(part, Code):
                    yield from split_surrounding_space(Sentence(str(part.v), [], []))
                if isinstance(part, Comment):
                    yield from split_surrounding_space(Text(str(part.v)))
        else:
            yield fr

LEAN_VERNAC_RE = re.compile("^#[^ ]+")
LEAN_TRAILING_BLANKS_RE = re.compile(r"\s+\Z")

def lean3_truncate_vernacs(fragments):
    r"""Strip trailing whitespace in vernacs like ``#check``.

    >>> from .core import Message as M
    >>> list(lean3_truncate_vernacs([Sentence("#check (1 \n+ 1)\n\n", [M("…")], [])]))
    [Sentence(contents='#check (1 \n+ 1)', messages=[Message(contents='…')], goals=[]),
     Text(contents='\n\n')]

    This is only needed in Lean 3: in Lean4 the region for #check statements is
    precisely known (in Lean3 it expands too far).
    """
    for fr in fragments:
        # Check that `fr` is a ‘#xyz’ vernac starting at the beginning of a line
        contents = _contents(fr)
        if isinstance(fr, (Sentence, RichSentence)) and LEAN_VERNAC_RE.match(contents):
            m = LEAN_TRAILING_BLANKS_RE.search(contents)
            if m:
                yield _replace_contents(fr, contents[:m.start()])
                fr = Text(contents[m.start():])
        yield fr

LEAN_COMMA_RE = re.compile(r'\A\s*,')

def lean3_attach_commas(fragments):
    """Attach commas to preceding sentences.

    This pass gathers all commas and spaces following a sentence up to the first
    newline, and embeds them in the sentence itself. This improves the location
    of the hover bubbles.
    """
    grouped = list(fragments)
    for idx, fr in enumerate(grouped):
        if isinstance(fr, Text) and idx > 0:
            m = LEAN_COMMA_RE.match(fr.contents)
            if m and not isinstance(grouped[idx - 1], Text):
                prev = grouped[idx-1]
                comma, rest = fr.contents[:m.end()], fr.contents[m.end():]
                grouped[idx-1] = _replace_contents(prev, _contents(prev) + comma)
                grouped[idx] = Text(rest) if rest else None
    return [g for g in grouped if g is not None]

LEAN_TRIM_PREFIX = re.compile(r"^\s+")
LEAN_TRIM_POSTFIX = re.compile(r"(\s|;)+$")

def lean4_trim_sentences(fragments):
    """This pass removes all prefixes and postfixes of whitespaces, newlines, or semicolons
    of a sentences and transforms these pre- and postfixes into separate Text fragments.
    """
    transformed = []
    for fr in fragments:
        if isinstance(fr, RichSentence):
            prefix = ""
            center = fr.input.contents
            postfix = ""
            prefix_match = LEAN_TRIM_PREFIX.search(center)
            if prefix_match is not None:
                prefix = center[:prefix_match.start()]
                center = center[prefix_match.start():]
            postifx_match = LEAN_TRIM_POSTFIX.search(center)
            if postifx_match is not None:
                postfix = center[postifx_match.start():]
                center = center[:postifx_match.start()]
            transformed.append(Text(prefix))
            new_input = fr.input._replace(contents=center)
            transformed.append(fr._replace(input=new_input))
            transformed.append(Text(postfix))
        else:
            transformed.append(fr)
    return transformed

LEAN4_WHITESPACE_ONLY = re.compile(r"^\s*$")

def lean4_transform_whitespace_to_text(fragments):
    "Transforms each sentence that only contains whitespaces to a Text fragment."
    transformed = []
    for fr in fragments:
        if isinstance(fr, RichSentence):
            if LEAN4_WHITESPACE_ONLY.match(str(fr.input.contents)):
                transformed.append(Text(fr.input.contents))
            else:
                transformed.append(fr)
        else:
            transformed.append(fr)
    return transformed

DEFAULT_TRANSFORMS = {
    "coq": [
        enrich_sentences,
        attach_comments_to_code("coq"),
        group_hypotheses,
        read_io_comments("coq"),
        process_io_annots,
        strip_coq_failures,
        dedent,
    ],
    "dafny": [
        coalesce_text,
        read_io_comments("dafny"),
        process_io_annots,
    ],
    "lean3": [
        lean3_attach_commas,
        lean3_split_comments,
        coalesce_text,
        enrich_sentences,
        lean3_truncate_vernacs,
        coalesce_text,
        # attach_comments_to_code("lean3"),
        read_io_comments("lean3"),
        process_io_annots
    ],
    "lean4": [
        lean4_trim_sentences,
        lean4_transform_whitespace_to_text,
        coalesce_text,
        enrich_sentences,
        group_hypotheses,
        read_io_comments("lean4"),
        process_io_annots
    ],
    # Not included:
    #   group_whitespace_with_code (HTML-specific)
    #   commit_io_annotations (breaks mref resolution by removing elements)
}
assert DEFAULT_TRANSFORMS.keys() == ALL_LANGUAGES

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

def default_transform(fragments, lang, delay_errors=False):
    return apply_transforms(fragments, DEFAULT_TRANSFORMS[lang], delay_errors)
