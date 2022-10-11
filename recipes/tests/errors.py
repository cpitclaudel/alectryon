r"""Errors unit tests

This file tests errors raised on paths that are not easily reachable from
the command line.

To run::

  $ python errors.py | sed 's/\(tests\?\) in [0-9.]\+s$/\1/g' > errors.py.out
      # Errors and warnings; produces ‘errors.py.out’
"""

import contextlib
import io
import sys
import unittest
import unittest.mock
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
        from alectryon.json import CacheSet
        with self.assertRaisesRegex(ValueError, "Unsupported cache compression"):
            _ = CacheSet("/", "/", "!!")

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
        from alectryon.docutils import CounterStyle, get_pipeline, \
            get_parser, set_default_role
        from docutils.utils import new_document, SystemMessage

        with self.assertRaisesRegex(ValueError, "Invalid"):
            _ = CounterStyle.of_str("0")

        with self.assertRaisesRegex(ValueError, "frontend"):
            _ = get_pipeline("!frontend", "latex", "xelatex")

        with self.assertRaisesRegex(ValueError, "backend"):
            _ = get_pipeline("coq+rst", "!backend", "xelatex")

        with self.assertRaisesRegex(ValueError, "dialect"):
            _ = get_pipeline("coq+rst", "latex", "!dialect")

        with self.assertRaisesRegex(ValueError, "Unsupported language"):
            set_default_role("\0")

        with redirected_std():
            coq_parser = get_parser("coq+rst")()
            with self.assertRaisesRegex(SystemMessage, "SEVERE"):
                coq_parser.parse("(*", new_document("<string>"))

class coqc_time(unittest.TestCase):
    def test_warnings_and_errors(self):
        from alectryon.core import Text
        from alectryon.coqc_time import CoqcTime

        with self.assertRaisesRegex(ValueError, "not found"):
            CoqcTime(binpath="\0").resolve_driver()

        api = CoqcTime()
        with redirected_std() as (_, err):
            annot = api.annotate(["Goal True."])
            self.assertEqual(annot, [[Text(contents='Goal True.')]])
            self.assertEqual(api.observer.exit_code, 3)
            self.assertRegex(err.getvalue(), "There are pending proofs")

class core(unittest.TestCase):
    def test_errors(self):
        from alectryon.core import Backend, resolve_driver

        with self.assertRaisesRegex(TypeError, r"\AUnexpected object type"):
            Backend(None)._gen_any(object())

        with self.assertRaisesRegex(ValueError, r"\AUnknown language"):
            resolve_driver("\0", "\0")

        with self.assertRaisesRegex(ValueError, r"\AUnknown driver"):
            resolve_driver("coq", "\0")


class serapi(unittest.TestCase):
    def test_warnings_and_errors(self):
        from alectryon.core import View
        from alectryon.serapi import SerAPI, PrettyPrinted

        with self.assertRaisesRegex(ValueError, "not found"):
            SerAPI(binpath="\0").resolve_driver()

        api = SerAPI()
        with redirected_std() as (_, err):
            api._warn_orphaned(View(b"chunk"), PrettyPrinted(0, "pp"))
            self.assertEqual(api.observer.exit_code, 2)
            self.assertRegex(err.getvalue(), "Orphaned message")

class pygments(unittest.TestCase):
    def test_warnings(self):
        from pygments import token
        from alectryon.pygments import WarnOnErrorTokenFilter

        with self.assertWarnsRegex(Warning, "Unexpected token"):
            _ = list(WarnOnErrorTokenFilter().filter(None, [(token.Error, "err")]))

    def test_errors(self):
        from alectryon.pygments import validate_style, get_formatter

        with self.assertRaisesRegex(ValueError, "Unknown.*style"):
            _ = validate_style("\0")
        with self.assertRaisesRegex(ValueError, "Unknown.*format"):
            _ = get_formatter("\0")


class sexp(unittest.TestCase):
    def test_errors(self):
        from alectryon.sexp import load, ParseError

        with self.assertRaisesRegex(ParseError, "Unbalanced"):
            _ = load(b"(")

        with self.assertRaisesRegex(ParseError, "Unterminated"):
            _ = load(b'("s)')

class literate(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        from alectryon.literate import StringView, Line
        self.ln = Line(num=12, parts = ["    ", "line"])
        self.sa, self.sx = StringView("aaabbbccc"), StringView("xyz")

    def test_errors(self):
        with self.assertRaisesRegex(ValueError, "concatenate"):
            _ = self.sa + self.sx

        with self.assertRaisesRegex(ValueError, "concatenate"):
            _ = self.sa + self.sa

    def test_features(self):
        self.assertEqual(self.sa[3:6][0], "b")
        self.assertEqual(str(self.ln.dedent(2)), "  line")

class myst(unittest.TestCase):
    def test_failed_import(self):
        __import = __import__
        def fake_import(arg, *args):
            if isinstance(arg, str) and "myst_parser" in arg:
                raise ImportError
            return __import(arg, *args)

        with unittest.mock.patch("builtins.__import__", new=fake_import):
            from alectryon.myst import Parser, FallbackParser
            from docutils.utils import new_document, SystemMessage

            self.assertEqual(Parser, FallbackParser)

            with redirected_std():
                with self.assertRaisesRegex(SystemMessage, "SEVERE"):
                    Parser().parse("*xyz*", new_document("<string>"))

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
