r"""Misc unit tests

To run::

   $ python unit.py | sed 's/\(tests\?\) in [0-9.]\+s$/\1/g' > unit.py.out
       # Unit tests; produces ‘unit.py.out’
"""

import contextlib
import io
import unittest
import sys
from tempfile import TemporaryDirectory
from pathlib import Path

import warnings
warnings.simplefilter("always")

@contextlib.contextmanager
def redirected_std():
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        yield (out, err)

class core(unittest.TestCase):
    def test_backend_gen(self):
        from alectryon.core import Backend, Text, RichGoal, RichSentence

        class PrintingBackend(Backend): # pylint: disable=abstract-method
            def __init__(self, *args):
                super().__init__(*args)
                self.out = None
            def gen_fragment(self, _):
                self.out = "fr!"
            def gen_goal(self, _):
                self.out = "goal!"

        backend = PrintingBackend(None)
        backend._gen_any(Text("txt"))
        self.assertEqual(backend.out, "fr!")
        backend._gen_any(RichGoal("nm", "goal", []))
        self.assertEqual(backend.out, "goal!")
        backend._gen_any(RichSentence("i", "o", None, [], []))
        self.assertEqual(backend.out, "fr!")

class json(unittest.TestCase):
    @staticmethod
    def cache(chunks, driver, root, docpath, lang, compression):
        from alectryon.json import CacheSet
        with CacheSet(root, docpath, compression) as caches:
            return caches[lang].update(chunks, driver)

    def test_validation(self):
        from alectryon.serapi import SerAPI
        with TemporaryDirectory() as cache_root:
            cache_root = Path(cache_root)
            docpath = cache_root / "test.v"

            driver = SerAPI(fpath=docpath)

            chunks = ["Goal True."]
            self.cache(chunks, driver, cache_root, docpath, "coq", "none")

            with redirected_std() as (out, _):
                driver.user_args = ("--disallow-sprop",)
                self.cache(chunks, driver, cache_root, docpath, "coq", "none")
                self.assertRegex(out.getvalue().strip(), r"\AOutdated metadata.*\Z")

            with redirected_std() as (out, _):
                chunks = ["Goal False."]
                self.cache(chunks, driver, cache_root, docpath, "coq", "none")
                self.assertRegex(out.getvalue().strip(), r"\AOutdated contents.*\Z")

            with redirected_std() as (out, _):
                self.cache(chunks, driver, cache_root, docpath, "coq", "xz")
                self.assertRegex(out.getvalue().strip(), r"\ARecompression requested.*\Z")

class lsp(unittest.TestCase):
    def test_styles(self):
        from alectryon.dafny import DafnyLSP
        from alectryon.pygments_style import AlectryonStyle
        from alectryon.pygments_lexer import TokenizedStrLexer

        toks_by_style = {}
        for tokstr in set(DafnyLSP.LSP_TYPE_MAP.values()):
            tok = TokenizedStrLexer.resolve_pygments_token(tokstr)
            style = AlectryonStyle.styles[tok]
            toks_by_style.setdefault(style, []).append(tokstr)

        collisions = {style: types for (style, types) in toks_by_style.items()
                      if len(types) > 1}
        self.assertEqual(collisions, {})

if __name__ == '__main__':
    sys.stderr = sys.stdout
    unittest.main(verbosity=2)
