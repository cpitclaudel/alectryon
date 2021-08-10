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

"""Place markers on subparts of code fragments."""

import re
from fnmatch import fnmatchcase

from .core import RichSentence

class MarkerError(ValueError):
    pass

class Matcher():
    def match(self, other):
        raise NotImplementedError()

class ExactMatcher(str, Matcher):
    def match(self, other):
        return self == other

class PlainMatcher(str, Matcher):
    def match(self, other):
        return self in other

class FnMatcher(str, Matcher):
    def match(self, other):
        return fnmatchcase(other, self)

class NameMatcher(FnMatcher):
    pass

class TopMatcher(Matcher):
    def match(self, _):
        return True

def find_sentences(fragments, needle):
    for fr in fragments:
        # LATER: Add a way to name sentences to make them easier to select
        if isinstance(fr, RichSentence) and needle.match(fr.contents):
            yield fr

def find_named(items, needle):
    for item in items:
        names = getattr(item, "names", []) or (getattr(item, "name", None) or "@unnamed",)
        if any(needle.match(nm) for nm in names):
            yield item

def find_goals(goals, needle):
    if isinstance(needle, NameMatcher):
        try:
            yield goals[int(needle) - 1]
        except (IndexError, ValueError):
            yield from find_named(goals, needle)
        return
    for g in goals:
        if needle.match(g.conclusion.contents):
            yield g

def find_hyps(hyps, needle):
    if isinstance(needle, NameMatcher):
        yield from find_named(hyps, needle)
        return
    for h in hyps:
        if needle.match(h.type.contents) or (h.body and needle.match(h.body.contents)):
            yield h

def find_one(kind, lookup_fn, haystack, needle):
    for s in lookup_fn(haystack, needle):
        return s
    raise MarkerError("No {} matches '{}'".format(kind, needle))

QUERY_KINDS = {
    "io":   ("io", ("name",)),
    "s":    ("sentence", ("plain", "fnmatch")),
    "g":    ("goal", ("plain", "fnmatch", "name")),
    "h":    ("hyp", ("plain", "fnmatch", "name")),
    "type": ("type", ("nil",)),
    "body": ("body", ("nil",)),
    "name":  ("name", ("nil",)),
    "ccl":  ("ccl", ("nil",))
}

MARKER_PATH_SEGMENT = re.compile(
    r"""[.](?P<kind>${KINDS})
         (?:(?P<nil>(?![#({]))
           |[#](?P<name>[^. ]+)
           |[(](?P<plain>.+?)[)]
           |[{](?P<fnmatch>.+?)[}])""".replace(
               "${KINDS}", "|".join(sorted(QUERY_KINDS.keys()))),
    re.VERBOSE)

QUERY_MATCHERS = {
    'nil': ExactMatcher,
    'name': NameMatcher,
    'plain': PlainMatcher,
    'fnmatch': FnMatcher
}

def parse_path(path, start=0, endpos=None):
    parsed = {"str": path}
    endpos = len(path) if endpos is None else endpos
    while start < endpos:
        m = MARKER_PATH_SEGMENT.match(path, start, endpos=endpos)
        if not m:
            raise MarkerError(path[start:])
        for matcher_name, matcher in QUERY_MATCHERS.items():
            needle = m.group(matcher_name)
            if needle is not None:
                kind, allowed_matchers = QUERY_KINDS[m.group("kind")]
                if matcher_name not in allowed_matchers:
                    raise MarkerError(path[start:])
                parsed[kind] = matcher(needle)
        start = m.end()
    return parsed

def merge_paths(*pths):
    out, full_str = {}, ""
    for pth in pths:
        if pth:
            full_str += pth["str"]
            out.update(pth)
    out["str"] = full_str
    return out
