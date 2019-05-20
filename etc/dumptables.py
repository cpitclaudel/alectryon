#!/usr/bin/env python3

"""Write out regular expressions matching Coq's syntax classes."""

from enum import Enum
import textwrap
from unicodedata import category
from sys import maxunicode

class LetterKind(Enum):
    Symbol = 1
    Letter = 2
    IdentPart = 3
    IdentSep = 4

def single(c):
    return [(c, c)]

def populate_unicodetable(tbl):
    for c in range(maxunicode):
        tbl.setdefault(category(chr(c)).lower(), []).append((c, c))
    return tbl

UNICODETABLE = populate_unicodetable({})

TABLES = [
    (LetterKind.Symbol,
     [
         UNICODETABLE['sm'],           # Symbol, maths.
         UNICODETABLE['sc'],           # Symbol, currency.
         UNICODETABLE['so'],           # Symbol, modifier.
         UNICODETABLE['pd'],           # Punctuation, dash.
         UNICODETABLE['pc'],           # Punctuation, connector.
         UNICODETABLE['pe'],           # Punctuation, open.
         UNICODETABLE['ps'],           # Punctution, close.
         UNICODETABLE['pi'],           # Punctuation, initial quote.
         UNICODETABLE['pf'],           # Punctuation, final quote.
         UNICODETABLE['po'],           # Punctuation, other.
     ]),
    (LetterKind.Letter,
     [
         UNICODETABLE['lu'],           # Letter, uppercase.
         UNICODETABLE['ll'],           # Letter, lowercase.
         UNICODETABLE['lt'],           # Letter, titlecase.
         UNICODETABLE['lo'],           # Letter, others.
         UNICODETABLE['lm'],           # Letter, modifier.
     ]),
    (LetterKind.IdentPart,
     [
         UNICODETABLE['nd'],           # Number, decimal digits.
         UNICODETABLE['nl'],           # Number, letter.
         UNICODETABLE['no'],           # Number, other.
     ]),

    (LetterKind.Letter,
     [
         [(0x01D00, 0x01D7F)],      # Phonetic Extensions.
         [(0x01D80, 0x01DBF)],      # Phonetic Extensions Suppl.
         [(0x01DC0, 0x01DFF)],      # Combining Diacritical Marks Suppl.
     ]),

    (LetterKind.Symbol,
     [
         [(0x000B2, 0x000B3)],      # Superscript 2-3.
         single(0x000B9),           # Superscript 1.
         single(0x02070),           # Superscript 0.
         [(0x02074, 0x02079)],      # Superscript 4-9.
         single(0x0002E),           # Dot.
     ]),

    (LetterKind.IdentSep,
     [
         single(0x005F),           # Underscore.
         single(0x00A0),           # Non breaking space.
     ]),

    (LetterKind.IdentPart,
     [
         single(0x0027),          # Single quote.
     ])
]

def classify(table, kind, ranges):
    for (low, high) in ranges:
        for charcode in range(low, high + 1):
            table[charcode] = kind

RANGE_SPECIAL = "^-]\\"

def char_to_re(n):
    c = chr(n)
    if c in RANGE_SPECIAL:
        return "\\" + c
    return c

def range_to_re(r):
    lo, hi = r
    if lo == hi:
        return char_to_re(lo)
    return char_to_re(lo) + "-" + char_to_re(hi)

def ranges_to_re(ranges):
    return "".join(range_to_re(r) for r in ranges)

def list_to_ranges(nums):
    nums = iter(sorted(nums))
    high = low = next(nums, None)
    for n in nums:
        if n == high + 1:
            high = n
        else:
            yield (low, high)
            low = high = n
    yield (low, high)

def list_to_re(chrs):
    return ranges_to_re(list_to_ranges(chrs))

def wrap_with_prefix(prefix, s, suffix):
    w = 72 - len(prefix)
    lines = [repr(s[start:start + w]) for start in range(0, len(s), w)]
    return (prefix + lines[0] + "\n" +
       textwrap.indent("\n".join(lines[1:]), ' ' * len(prefix)) + suffix)

def main():
    coq_letters = {}
    for kind, rangess in TABLES:
        for ranges in rangess:
            classify(coq_letters, kind, ranges)
    by_kind = {}
    for letter, kind in coq_letters.items():
        by_kind.setdefault(kind, []).append(letter)

    identstart = by_kind[LetterKind.Letter] + by_kind[LetterKind.IdentSep]
    identpart = by_kind[LetterKind.IdentPart]
    symbol = by_kind[LetterKind.Symbol]

    print(wrap_with_prefix("identstart = (", list_to_re(identstart), ")"))
    print("identpart = (identstart +\n" +
          wrap_with_prefix("             ", list_to_re(identpart), ")"))
    print(wrap_with_prefix("symbol = (", list_to_re(symbol), ")"))

if __name__ == '__main__':
    main()
