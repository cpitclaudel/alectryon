r"""
This file tests errors raised on paths that are not easily reachable from
the command line.

To run::

  $ python errors.py | sed 's/\(tests\) in [0-9.]\+s$/\1/g' > errors.py.out
      # Errors and warnings; produces ‘errors.py.out’
"""

import contextlib
import io
import sys
import unittest
import tempfile

import warnings
warnings.simplefilter("always")

@contextlib.contextmanager
def redirected_std():
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        yield (out, err)

class json(unittest.TestCase):
    def test_warnings(self):
        from alectryon.json import json_of_annotated, annotated_of_json
        with self.assertWarns(DeprecationWarning):
            _ = json_of_annotated([])
        with self.assertWarns(DeprecationWarning):
            _ = annotated_of_json([])

    def test_errors(self):
        from alectryon.json import FileCache
        with self.assertRaisesRegex(ValueError, "Unsupported"):
            _ = FileCache("/", "/", {}, "!!")

class cli(unittest.TestCase):
    def test_errors(self):
        from alectryon.cli import _gen_coqdoc_html_assert, copy_assets

        with self.assertRaises(AssertionError):
            with redirected_std() as (out, _):
                _gen_coqdoc_html_assert(["(** a **)", "(** b **)"], ["a"])
                self.assertRegex(out.getvalue(), "Coqdoc mismatch")

        from os.path import split
        from shutil import copyfile
        with tempfile.NamedTemporaryFile(prefix="alectryon_unit") as f:
            fdir, fname = split(f.name)
            copy_assets(None, [(fdir, fname)], copyfile, fdir)

class docutils(unittest.TestCase):
    def test_errors(self):
        from alectryon.docutils import CounterStyle, get_pipeline

        with self.assertRaisesRegex(ValueError, "Invalid"):
            _ = CounterStyle.of_str("0")

        with self.assertRaisesRegex(ValueError, "frontend"):
            _ = get_pipeline("!frontend", "latex", "xelatex")

        with self.assertRaisesRegex(ValueError, "backend"):
            _ = get_pipeline("coq+rst", "!backend", "xelatex")

        with self.assertRaisesRegex(ValueError, "dialect"):
            _ = get_pipeline("coq+rst", "latex", "!dialect")

class core(unittest.TestCase):
    def test_errors(self):
        from alectryon.core import Backend

        with self.assertRaisesRegex(TypeError, "Unexpected"):
            Backend(None)._gen_any(object())

class serapi(unittest.TestCase):
    def test_warnings(self):
        from alectryon.core import SerAPI, View, PrettyPrinted

        api = SerAPI()
        with redirected_std() as (_, err):
            api._warn_orphaned(View(b"chunk"), PrettyPrinted(0, "pp"))
            self.assertEqual(api.observer.exit_code, 2)
            self.assertRegex(err.getvalue(), "Orphaned message")

class sexp(unittest.TestCase):
    def test_errors(self):
        from alectryon.sexp import load, ParseError

        with self.assertRaisesRegex(ParseError, "Unbalanced"):
            _ = load(b"(")

        with self.assertRaisesRegex(ParseError, "Unterminated"):
            _ = load(b'("s)')

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
