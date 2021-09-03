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
    def valid_char(c, allowed):
        for pattern in allowed:
            if isinstance(pattern, str) and unicodedata.category(c).lower() == pattern:
                return True
            if isinstance(pattern, Pattern) and pattern.match(c):
                return True
        return False

    @classmethod
    def sub_chars(cls, chars, allowed):
        return "".join(c if cls.valid_char(c, allowed) else "_" for c in chars)

    SUFFIXES = re.compile(r"(?:[.](?:v|rst))+\Z")

    @classmethod
    def topfile_of_fpath(cls, fpath: Path) -> str:
        """Normalize `fpath` to make its ``name`` a valid Coq identifier.

        >>> str(CoqIdents.topfile_of_fpath(Path("dir+ex/f:𝖴🄽𝓘ⓒ𝕆Ⓓ𝙴.v")))
        'f_𝖴_𝓘_𝕆_𝙴.v'
        >>> str(CoqIdents.topfile_of_fpath(Path("/tmp/abc.def.v.rst")))
        'abc_def.v'
        >>> str(CoqIdents.topfile_of_fpath(Path("/tmp/abc.def.rst.v")))
        'abc_def.v'
        >>> str(CoqIdents.topfile_of_fpath(Path("-")))
        'Top.v'
        """
        if fpath.name in ("-", ""):
            return "Top.v"
        stem = cls.SUFFIXES.sub("", fpath.name)
        stem = (cls.sub_chars(stem[0], cls.COQ_IDENT_START) +
                cls.sub_chars(stem[1:], cls.COQ_IDENT_PART))
        return stem + ".v"
