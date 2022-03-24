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

import typing
from typing import Iterable, Tuple, Union, cast

import re
import unicodedata
from pathlib import Path

Pattern = type(re.compile("")) # LATER (3.7+): re.Pattern

class CoqIdents:
    COQ_IDENT_START = (
        'lu', # Letter, uppercase
        'll', # Letter, lowercase
        'lt', # Letter, titlecase
        'lo', # Letter, others
        'lm', # Letter, modifier
        re.compile(r"""[
           \u1D00-\u1D7F # Phonetic Extensions
           \u1D80-\u1DBF # Phonetic Extensions Suppl
           \u1DC0-\u1DFF # Combining Diacritical Marks Suppl
           \u005F # Underscore
           \u00A0 # Non breaking space
         ]""", re.VERBOSE | re.UNICODE)
    )

    COQ_IDENT_PART = (
        *COQ_IDENT_START,
        'nd', # Number, decimal digits
        'nl', # Number, letter
        'no', # Number, other
        re.compile("[']")
    )

    @staticmethod
    def valid_char(c: str, allowed: Iterable[Union[str, typing.Pattern[str]]]):
        for pattern in allowed:
            if isinstance(pattern, str) and unicodedata.category(c).lower() == pattern:
                return True
            if isinstance(pattern, Pattern) and cast(typing.Pattern[str], pattern).match(c):
                return True
        return False

    @classmethod
    def sub_chars(cls, chars, allowed):
        return "".join(c if cls.valid_char(c, allowed) else "_" for c in chars)

    @classmethod
    def make_ident(cls, name):
        """Transform `name` into a valid Coq identifier.

        >>> CoqIdents.make_ident("f:𝖴🄽𝓘ⓒ𝕆Ⓓ𝙴")
        'f_𝖴_𝓘_𝕆_𝙴'
        """
        return (cls.sub_chars(name[0], cls.COQ_IDENT_START) +
                cls.sub_chars(name[1:], cls.COQ_IDENT_PART))

    COQ_EXTS = (".v",)
    STRIP = (".rst", ".md")

    @classmethod
    def split_fpath(cls, fpath: Path, exts=COQ_EXTS, strip=STRIP) -> Tuple[str, str]:
        """Normalize `fpath` into a valid Coq identifier.
        If `fpath` is ``"-"``, return an empty filename.

        >>> CoqIdents.split_fpath(Path("dir/abc.def.v.xyz"), strip=(".xyz",))
        ('abc_def', '.v')
        >>> CoqIdents.split_fpath(Path("dir/abc.rst.def"))
        ('abc_def', '')
        >>> CoqIdents.split_fpath(Path("-"))
        ('', '')
        """
        if fpath.name in ("-", ""):
            return "", ""
        stem, *suffixes = fpath.name.split(".")
        suffixes = ["." + s for s in suffixes]
        name = stem + "".join(s for s in suffixes if s not in exts + strip)
        return cls.make_ident(name), "".join(s for s in suffixes if s in exts)

    @classmethod
    def topfile_of_fpath(cls, fpath: Path, default="Top", exts=COQ_EXTS, strip=STRIP) -> str:
        """Normalize `fpath` into a valid Coq file name.

        Extensions found in `exts` are preserved, and `exts[0]` is appended if
        none is found.  Extensions found in `strip` are removed.  If `fpath` is
        ``-`` or empty, `default` is used instead.
        """
        stem, ext = cls.split_fpath(fpath, exts, strip)
        return (cls.make_ident(stem) if stem else default) + (ext or exts[0])
