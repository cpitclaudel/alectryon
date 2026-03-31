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
    COQ = "(*|\nHello\n|*)\n\nLemma foo : True.\n"

    from alectryon.literate import get_markup
    MD = get_markup("rst", "coq")

    def roundtrip(self, coq, point):
        from alectryon.literate import code2markup_marked, markup2code_marked
        rst = code2markup_marked(self.MD, coq, point, self.MARKER)
        self.assertIn(self.MARKER, rst, f"forward marker missing at point={point}")
        q = rst.index(self.MARKER)
        rst_clean = rst.replace(self.MARKER, "")
        coq_rt = markup2code_marked(self.MD, rst_clean, q, self.MARKER)
        self.assertIn(self.MARKER, coq_rt, f"reverse marker missing at point={point}")
        return coq_rt

    def test_mark_point_end_of_file(self):
        coq_rt = self.roundtrip(self.COQ, len(self.COQ))
        self.assertEqual(self.COQ, coq_rt.replace(self.MARKER, ""))

    def test_mark_point_all_positions(self):
        """For every point 0..len, the marker survives the roundtrip and
        content is preserved.  Drift is bounded by comment delimiter width."""
        from collections import defaultdict
        drifts = defaultdict(list)
        for p in range(len(self.COQ) + 1):
            coq_rt = self.roundtrip(self.COQ, p)
            self.assertEqual(self.COQ, coq_rt.replace(self.MARKER, ""))
            drifts[coq_rt.index(self.MARKER) - p].append(p)
        #   (*|\nHello\n|*)\n\nLemma foo : True.\n
        #   0123456789...
        self.assertEqual(dict(drifts), {
            -4: [4, 5, 6, 7],       # inside ``(*|`` opener + first content char
            -3: [3],                 # newline after ``(*|``
            -2: [2],                 # ``|`` of ``(*|``
            -1: [1, 33],             # ``*`` of ``(*|``; EOF
             0: [*range(0, 1),       # ``(`` of ``(*|``
                 *range(8, 10),      # last content char + newline before ``|*)``
                 *range(15, 33)],    # code block
            +1: [14],                # blank line before code
            +2: [13],               # newline after ``|*)``
            +3: [12],                # ``)`` of ``|*)``
            +4: [11],                # ``*`` of ``|*)``
            +5: [10],               # ``|`` of ``|*)``
        })

if __name__ == '__main__':
    r = unittest.main(testRunner=unittest.TextTestRunner(stream=io.StringIO()), exit=False).result
    for t, tb in [*r.failures, *r.errors]:
        print(f"FAIL: {t}\n{tb}")
    print("OK" if r.wasSuccessful() else "FAILED")
    sys.exit(not r.wasSuccessful())
