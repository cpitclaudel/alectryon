r"""
Run Alectryon's doctests.

   $ python doctests.py | sed 's/\(tests\) in [0-9.]\+s$/\1/g' > doctests.out
         # Run doctests; produces ‘doctests.out’

(but make sure that the ROOT of this repo is in PYTHONPATH)
"""

import doctest
import re
import sys
import unittest

from fnmatch import fnmatchcase
from pathlib import Path

DIR = Path(__file__).parent
ROOT = (DIR / "../../").resolve()

EXCLUDED = "__main__.py"
FLAGS = doctest.NORMALIZE_WHITESPACE

class Checker(doctest.OutputChecker):
    COMMENTS = re.compile(r"#.*(?:\n\s*)?")

    def check_output(self, want, got, optionflags):
        """Like ``OutputChecker.check_output``, but strip comments."""
        want = self.COMMENTS.sub("", want)
        return super().check_output(want, got, optionflags)

class DocFileCase(doctest.DocFileCase):
    """Like ``doctest.DocFileCase``, but don't print absolute paths."""
    def __repr__(self):
        return Path(self._dt_test.filename).name
doctest.DocFileCase = DocFileCase

def suite(loader):
    s = unittest.TestSuite()

    files = [(ROOT / "README.rst"),
             *sorted((ROOT / "alectryon").glob("*.py"))]

    for f in files:
        if f.name in EXCLUDED:
            continue
        if loader.testNamePatterns is not None:
            if not any(fnmatchcase(f.name, pat) for pat in loader.testNamePatterns):
                continue
        if f.name.endswith(".rst"):
            s.addTests(doctest.DocFileSuite(
                str(f.resolve()), module_relative=False,
                checker=Checker(), optionflags=FLAGS))
        else:
            s.addTests(doctest.DocTestSuite(f"alectryon.{f.stem}", optionflags=FLAGS))

    return s

def load_tests(loader, _standard_tests, _pattern): # pylint: disable=unused-argument
    # s.addTests(tests) # There are no tests in this file
    return suite(loader)

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
