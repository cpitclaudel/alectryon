import unittest
import sys
from doctest import DocTestSuite, NORMALIZE_WHITESPACE
from pathlib import Path

# To run the tests:
#   $ python doctests.py | sed 's/\(tests\) in [0-9.]\+s$/\1/g' > doctests.out
#       Run doctests; produces ‘doctests.out’
# (but make sure that the root of this repo is in PYTHONPATH)

root = (Path(__file__).parent / "../../").resolve()

def suite():
    s = unittest.TestSuite()
    for f in sorted((root / "alectryon").glob("*.py")):
        s.addTests(DocTestSuite(f"alectryon.{f.stem}", optionflags=NORMALIZE_WHITESPACE))
    return s

def load_tests(loader, tests, ignore):
    s = suite()
    s.addTests(tests)
    return s

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
