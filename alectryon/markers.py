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

class MarkerError(ValueError):
    MSG = "{}"
    def __str__(self):
        return self.MSG.format(*self.args)
class ParseError(MarkerError):
    MSG = "Cannot parse marker-placement expression ``{}``."
class MissingPattern(MarkerError):
    MSG = ("Missing search pattern for key ``.{}`` in expression ``{}``. " +
           "(maybe an invalid pattern?)")
class UnsupportedPattern(MarkerError):
    MSG = "Unsupported search pattern {} for key ``.{}`` in expression ``{}``."

class Matcher():
    def match(self, other):
        raise NotImplementedError()

class PlainMatcher(str, Matcher):
    def match(self, other):
        return self in other

class FnMatcher(str, Matcher):
    def match(self, other):
        return fnmatchcase(other, self)

class NameMatcher(FnMatcher):
    pass

class TopMatcher(str, Matcher):
    def match(self, _):
        assert self == ""
        return True

def find_contents(objs, needle):
    for obj in objs:
        if needle.match(obj.contents):
            yield obj

def find_named(items, needle):
    for item in items:
        names = getattr(item, "names", []) or (getattr(item, "name", None) or "@unnamed",)
        if any(needle.match(nm) for nm in names):
            yield item

def find_sentences(objs, needle):
    for fr in objs:
        # LATER: Add a way to name sentences to make them easier to select
        if needle.match(fr.input.contents):
            yield fr

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
    raise MarkerError("No {} matches '{}'.".format(kind, needle))

QUERY_SHAPE = \
    {"io": {
        "s": {
            "in": {},
            "g": {"name": {},
                  "h": {"type": {},
                        "body": {},
                        "name": {}},
                  "ccl": {}},
            "msg": {}}}}

def _invalid_sets(path, leaf, allowed):
    for leaf_, allowed_ in allowed.items():
        if leaf_ in path:
            pth = {k: v for k, v in path.items() if k != leaf_}
            yield from _invalid_sets(pth, leaf_, allowed_)
    yield (leaf, path)

def path_leaf(path):
    components = {k: v for k, v in path.items() if k != "str"}
    (leaf, least_bad) = min(_invalid_sets(components, None, QUERY_SHAPE),
                            key=lambda p: len(p[1]))
    if least_bad:
        MSG = "Incompatible components in path ``{}``: not sure what to do with ``{}``."
        raise MarkerError(MSG.format(path["str"], ", ".join(least_bad)))
    return leaf

def set_leaf(path):
    leaf = path["leaf"] = path_leaf(path)
    return leaf

QUERY_KINDS = {
    "io":   ("name",),
    "s":    ("plain", "fnmatch"),
    "msg":  ("nil", "plain", "fnmatch"),
    "g":    ("plain", "fnmatch", "name"),
    "h":    ("plain", "fnmatch", "name"),
    "in":   ("nil",),
    "type": ("nil",),
    "body": ("nil",),
    "name": ("nil",),
    "ccl":  ("nil",)
}

FULL_NAMES = {
    "io":   "block",
    "s":    "sentence",
    "msg":  "message",
    "g":    "goal",
    "h":    "hypothesis",
    "in":   "input",
    "type": "type",
    "body": "body",
    "name": "name",
    "ccl":  "conclusion"
}

MARKER_PATH_SEGMENT = re.compile(
    r"""[.](?P<kind>${KINDS})
         (?P<search>(?P<nil>(?![#({]))
                   |[#](?P<name>[^. ]+)
                   |[(](?P<plain>.+?)[)]
                   |[{](?P<fnmatch>.+?)[}])"""
        .replace("${KINDS}", "|".join(sorted(QUERY_KINDS.keys()))),
    re.VERBOSE)

QUERY_MATCHERS = {
    'nil': TopMatcher,
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
            raise ParseError(path[start:])
        for matcher_name, matcher in QUERY_MATCHERS.items():
            needle = m.group(matcher_name)
            if needle is not None:
                kind = m.group("kind")
                allowed_matchers = QUERY_KINDS[kind]
                if matcher_name not in allowed_matchers:
                    if matcher_name == "nil":
                        raise MissingPattern(kind, path[start:])
                    raise UnsupportedPattern(m.group("search"), kind, path[start:])
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
