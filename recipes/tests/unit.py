r"""Misc unit tests

To run::

   $ python unit.py > unit.py.out 2>&1
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
        from alectryon.vsrocq import VsRocq
        with TemporaryDirectory() as cache_root:
            cache_root = Path(cache_root)
            docpath = cache_root / "test.v"

            driver = VsRocq(fpath=docpath)

            chunks = ["Goal True."]
            self.cache(chunks, driver, cache_root, docpath, "coq", "none")

            with redirected_std() as (out, _):
                driver.user_args = ("-disallow-sprop",)
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
        from alectryon.dafny import DafnyClient
        from alectryon.pygments_style import AlectryonStyle
        from alectryon.pygments_lexer import TokenizedStrLexer

        toks_by_style = {}
        for tokstr in set(DafnyClient.TOKEN_MAP.values()):
            tok = TokenizedStrLexer.resolve_pygments_token(tokstr)
            style = AlectryonStyle.styles[tok]
            toks_by_style.setdefault(style, []).append(tokstr)

        collisions = {style: types for (style, types) in toks_by_style.items()
                      if len(types) > 1}
        self.assertEqual(collisions, {})

class io_annots(unittest.TestCase):
    @classmethod
    def inherit(cls, directive_flags, sentence_flags):
        from alectryon.transforms import IOAnnots
        s = IOAnnots()
        s.inherit(IOAnnots(*directive_flags))
        for f in sentence_flags:
            s.update(f)
        return s

    def test_defaults(self):
        from alectryon.transforms import IOAnnots
        a = IOAnnots()
        self.assertEqual(a.filters, IOAnnots.FILTER_ALL)
        self.assertIsNone(a.unfold)
        self.assertIsNone(a.fails)
        self.assertEqual(a.props, [])

    def test_all_and_none(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(IOAnnots('all'), IOAnnots())
        self.assertEqual(IOAnnots('none').filters, IOAnnots.FILTER_NONE)
        self.assertEqual(IOAnnots('all', 'none').filters, IOAnnots.FILTER_NONE)
        self.assertEqual(IOAnnots('none', 'all').filters, IOAnnots.FILTER_ALL)

    def test_implicit_base(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(IOAnnots('no-in'), IOAnnots('all', 'no-in'))
        self.assertEqual(IOAnnots('in'), IOAnnots('none', 'in'))

    def test_meta_flag_equivalences(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(IOAnnots('out'), IOAnnots('hyps', 'ccls', 'messages'))
        self.assertEqual(IOAnnots('goals'), IOAnnots('hyps', 'ccls'))
        self.assertEqual(IOAnnots('no-out'), IOAnnots('no-hyps', 'no-ccls', 'no-messages'))
        self.assertEqual(IOAnnots('no-goals'), IOAnnots('no-hyps', 'no-ccls'))

    def test_toggles(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(IOAnnots('no-in', 'in'), IOAnnots())
        self.assertEqual(IOAnnots('in', 'no-in').filters, IOAnnots.FILTER_NONE)

    def test_unfold_fold(self):
        from alectryon.transforms import IOAnnots
        self.assertTrue(IOAnnots('unfold').unfold)
        self.assertFalse(IOAnnots('fold').unfold)
        self.assertFalse(IOAnnots('unfold', 'fold').unfold)
        self.assertTrue(IOAnnots('fold', 'unfold').unfold)

    def test_fails_succeeds(self):
        from alectryon.transforms import IOAnnots
        self.assertTrue(IOAnnots('fails').fails)
        self.assertFalse(IOAnnots('succeeds').fails)

    def test_fields_are_independent(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(IOAnnots('no-in', 'unfold', 'fails'),
                         IOAnnots('unfold', 'fails', 'no-in'))

    def test_unknown_flag(self):
        from alectryon.transforms import IOAnnots
        with self.assertRaises(ValueError):
            IOAnnots('no-banana')

    def test_child_overrides_scalar_fields(self):
        self.assertFalse(self.inherit(['unfold'], ['fold']).unfold)
        self.assertFalse(self.inherit(['fails'], ['succeeds']).fails)

    def test_props_merge(self):
        from alectryon.transforms import IOAnnots, PathAnnot
        p1, p2 = PathAnnot("r1", "p1", "k1", "v1", False), PathAnnot("r2", "p2", "k2", "v2", False)
        child = IOAnnots(props=[p2])
        child.inherit(IOAnnots(props=[p1]))
        self.assertEqual(child, IOAnnots(props=[p1, p2]))

    def test_filter_composition(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(self.inherit(['no-in'], ['no-goals']), IOAnnots('no-in', 'no-goals'))
        self.assertEqual(self.inherit(['no-out'], ['no-in']).filters, IOAnnots.FILTER_NONE)
        self.assertEqual(self.inherit(['in', 'hyps'], ['ccls', 'messages']).filters, IOAnnots.FILTER_ALL)

    def test_composition_is_symmetric(self):
        """inherit-then-update gives the same result as update-then-inherit."""
        from alectryon.transforms import IOAnnots
        cases = [
            (['no-in'], ['no-goals']),
            (['no-out'], ['no-in']),
            (['no-in'], ['in']),
            (['no-hyps'], ['no-ccls', 'no-messages']),
            (['none', 'in'], ['messages']),
            (['no-in', 'unfold'], ['no-goals', 'fold']),
        ]
        for parent, child in cases:
            with self.subTest(parent=parent, child=child):
                a = self.inherit(parent, child)
                b = IOAnnots(*child); b.inherit(IOAnnots(*parent))
                self.assertEqual(a, b)

    def test_three_levels(self):
        from alectryon.transforms import IOAnnots
        gp = IOAnnots('no-in')
        p = IOAnnots('no-goals'); p.inherit(gp)
        c = IOAnnots(); c.inherit(p)
        self.assertEqual(c, IOAnnots('no-in', 'no-goals'))

    def test_sentence_resets(self):
        from alectryon.transforms import IOAnnots
        self.assertEqual(self.inherit(['no-in'], ['all']).filters, IOAnnots.FILTER_ALL)
        self.assertEqual(self.inherit(['all'], ['none']).filters, IOAnnots.FILTER_NONE)

    def test_multiple_sentences_independent(self):
        from alectryon.transforms import IOAnnots
        d = IOAnnots('no-in')
        s1 = IOAnnots(); s1.inherit(d); s1.update('no-goals')
        s2 = IOAnnots(); s2.inherit(d)
        self.assertEqual(s1, IOAnnots('no-in', 'no-goals'))
        self.assertEqual(s2, IOAnnots('no-in'))

    def test_full_combination(self):
        from alectryon.transforms import IOAnnots, PathAnnot
        prop = PathAnnot("r", "p", "k", "v", False)
        s = self.inherit(['no-in', 'unfold', 'fails'], ['no-goals', 'fold'])
        s.props = [prop]
        self.assertEqual(s, IOAnnots('no-in', 'no-goals', 'fold', 'fails', props=[prop]))

    def test_hidden(self):
        from alectryon.transforms import IOAnnots
        self.assertTrue(self.inherit(['all'], ['none']).hidden)
        self.assertFalse(self.inherit(['none'], ['in']).hidden)
        self.assertFalse(IOAnnots().hidden)

class literate(unittest.TestCase):
    MARKER = "\uFFFC"

    def _roundtrip_point(self, md, source, point, fwd, bwd):
        out = fwd(md, source, point, self.MARKER)
        self.assertIn(self.MARKER, out, f"forward marker missing at point={point}")
        q = out.index(self.MARKER)
        rt = bwd(md, out.replace(self.MARKER, ""), q, self.MARKER)
        self.assertIn(self.MARKER, rt, f"reverse marker missing at point={point}")
        return rt

    def _check_roundtrip(self, markup, lang, source, fwd, bwd, expected_drifts):
        """Roundtrip `source` via `fwd`/`bwd` at every offset; check drifts."""
        from alectryon.literate import get_markup
        md = get_markup(markup, lang)
        drifts: dict = {}
        for p in range(len(source) + 1):
            rt = self._roundtrip_point(md, source, p, fwd, bwd)
            self.assertEqual(source, rt.replace(self.MARKER, ""))
            drifts.setdefault(rt.index(self.MARKER) - p, []).append(p)
        self.assertEqual(drifts, expected_drifts)

    def _check_code_roundtrip(self, markup, lang, code, expected_drifts):
        """Code → markup → code drift check."""
        from alectryon.literate import code2markup_marked, markup2code_marked
        self._check_roundtrip(markup, lang, code,
                              code2markup_marked, markup2code_marked, expected_drifts)

    def _check_markup_roundtrip(self, markup, lang, text, expected_drifts):
        """Markup → code → markup drift check."""
        from alectryon.literate import code2markup_marked, markup2code_marked
        self._check_roundtrip(markup, lang, text,
                              markup2code_marked, code2markup_marked, expected_drifts)

    def _check_coq_roundtrip(self, coq, expected_drifts):
        self._check_code_roundtrip("rst", "coq", coq, expected_drifts)

    def test_mark_point_coq_all_positions(self):
        self._check_code_roundtrip("rst", "coq", "(*|\nHello\n|*)\n\nLemma foo : True.\n", {
            0: [*range(4, 11),      # comment content + ``|`` of ``|*)``
                *range(15, 34)],    # code block + EOF
            1: [3, 14],             # newline after ``(*|``; blank line before code
            2: [2, 13],             # ``|`` of ``(*|``; newline after ``|*)``
            3: [1, 12],             # ``*`` of ``(*|``; ``)`` of ``|*)``
            4: [0, 11],             # ``(`` of ``(*|``; ``*`` of ``|*)``
        })

    def test_mark_point_rst_all_positions(self):
        self._check_markup_roundtrip("rst", "coq", "Hello\n\n.. coq::\n\n   Lemma foo : True.\n", {
            0: [*range(0, 6),         # prose content (``Hello\n``)
                *range(6, 7),         # blank line before directive
                *range(20, 39)],      # code content + EOF
            1: [19],                  # last indent space
            2: [18],                  # indent space
            3: [17],                  # indent space
            4: [16],                  # newline before indented code
            5: [15],                  # newline after ``.. coq::``
            6: [14],                  # ``:`` of ``.. coq::``
            7: [13],                  # ``:`` of ``.. coq::``
            8: [12],                  # ``q`` of ``.. coq::``
            9: [11],                  # ``o`` of ``.. coq::``
            10: [10],                 # ``c`` of ``.. coq::``
            11: [9],                  # `` `` of ``.. coq::``
            12: [8],                  # ``.`` of ``.. coq::``
            13: [7],                  # ``.`` of ``.. coq::``
        })

    def test_mark_point_blank_line(self):
        self._check_coq_roundtrip("\n", {0: [0], -1: [1]})

    def test_mark_point_code_only(self):
        self._check_coq_roundtrip("Check True.\n", {
            0: [*range(0, 13)],
        })

    def test_mark_point_lean3(self):
        self._check_code_roundtrip("rst", "lean3",
                                   "/-|\nHello\n|-/\n\ndef x := 1\n", {
            0: [*range(4, 11),      # comment content + ``|`` of ``|-/``
                *range(15, 27)],    # code block + EOF
            1: [3, 14],
            2: [2, 13],
            3: [1, 12],
            4: [0, 11],
        })

    def test_mark_point_dafny(self):
        self._check_code_roundtrip("rst", "dafny",
                                   "/// Hello\n\nmethod Foo() {}\n", {
            0: [*range(4, 28)],     # comment content + code + EOF
            1: [3],
            2: [2],
            3: [1],
            4: [0],
        })

    def split_lines_identity(self):
        from alectryon.literate import split_lines, StringView
        source = "hello\nworld\n"
        sv = StringView(source, 0, len(source))
        for p in split_lines(sv):
            self.assertIs(p.s, source)

    def wrap_literate_blank_line(self):
        from alectryon.literate import get_language, EmptyLine
        for l in get_language("dafny").wrap_literate([EmptyLine()]):
            self.assertNotIn(" \n", str(l), "must not have trailing spaces")

    def _assert_roundtrips(self, lang, codes):
        """Assert that each code string roundtrips through both RST and MD."""
        from alectryon.literate import code2markup, markup2code, get_markup
        for markup in ("rst", "md"):
            md = get_markup(markup, lang)
            for code in codes:
                self.assertEqual(markup2code(md, code2markup(md, code)), code,
                    f"{lang}+{markup} roundtrip failed for {code!r}")

    def test_dafny_roundtrips(self):
        """Dafny roundtrips through both RST and Markdown."""
        self._assert_roundtrips("dafny", [
            "/// Hello\n\nmethod Foo() {}\n",
            "method Foo() {}\n",
            "/// A\n\nX()\n\n/// B\n\nY()\n",
        ])

    def test_lean3_roundtrips(self):
        """Lean3 roundtrips through both RST and Markdown."""
        self._assert_roundtrips("lean3", [
            "/-|\nHello\n|-/\n\ndef x := 1\n",
            "def x := 1\n",
            "/-|\nJust prose.\n|-/\n",
        ])

if __name__ == '__main__':
    r = unittest.main(testRunner=unittest.TextTestRunner(stream=io.StringIO()), exit=False).result
    for t, tb in [*r.failures, *r.errors]:
        print(f"FAIL: {t}\n{tb}")
    print("OK" if r.wasSuccessful() else "FAILED")
    sys.exit(not r.wasSuccessful())
