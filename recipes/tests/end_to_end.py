r"""End-to-end pipeline tests that include their own output.

To run::

   $ python end_to_end.py 2>&1 | sed 's/\(tests\?\) in [0-9.]\+s$/\1/g' > end_to_end.py.out
       # CI tests; produces ‘end_to_end.py.out’
"""

import re
import sys
import unittest

from pathlib import Path
from tempfile import TemporaryDirectory

from alectryon import cli

class PipelineTest:
    """Mixin: run ``cli.main()`` and compare output against ``OUT``."""

    IN_FNAME: str
    OUT_FNAME: str
    ARGS: tuple[str]

    IN: str
    OUT: str

    def _main(self):
        """Write ``IN``, run alectryon, and return the output file contents."""
        with TemporaryDirectory() as d:
            inp, outp = Path(d) / self.IN_FNAME, Path(d) / self.OUT_FNAME
            inp.write_text(self.IN)
            sys.argv = ["alectryon", str(inp), "-o", str(outp), *self.ARGS]
            with self.assertRaises(SystemExit) as cm:
                cli.main()
            self.assertEqual(cm.exception.code, 0)
            return outp.read_text()

    def _postprocess(self, output):
        return output

    def test_pipeline(self):
        output = self._postprocess(self._main())
        self.assertEqual(output, self._postprocess(self.OUT))

class Rocq2HTML(PipelineTest, unittest.TestCase):
    """Plain Rocq → HTML snippets."""

    IN_FNAME, OUT_FNAME = "t.v", "t.snippets.html"
    ARGS = ("--frontend", "coq")

    IN = "Check nat."
    OUT = (
        '<pre class="alectryon-io highlight">'
        '<!-- Generator: Alectryon -->'
        '<span class="alectryon-sentence">'
        '<input class="alectryon-toggle" id="t-v-chk0"'
        ' style="display: none" type="checkbox">'
        '<label class="alectryon-input" for="t-v-chk0">'
        '<span class="kn">Check</span> nat.</label>'
        '<small class="alectryon-output"><div>'
        '<div class="alectryon-messages">'
        '<blockquote class="alectryon-message">'
        'nat\n'
        '     : <span class="kt">Set</span>'
        '</blockquote></div></div></small>'
        '</span></pre><!-- alectryon-block-end -->\n'
    )

class RST2LaTeX(PipelineTest, unittest.TestCase):
    """RST with Rocq → LaTeX."""

    IN_FNAME, OUT_FNAME = "t.rst", "t.tex"
    ARGS = ()

    IN = """
A test:

.. coq::

   Check nat.
"""
    OUT = r"""
\begin{document}
A test:

\begin{alectryon}
  \begin{\al{sentence}}
    \begin{\al{input}}
      \PY{k+kn}{Check}~\PY{n}{nat}\PY{o}{.}
    \end{\al{input}}
    \Al{sep}
    \begin{\al{output}}
      \begin{\al{messages}}
        \begin{\al{message}}
          \PY{n}{nat}\Al{nl}
          ~~~~~\PY{o}{:}~\PY{k+kt}{Set}
        \end{\al{message}}
      \end{\al{messages}}
    \end{\al{output}}
  \end{\al{sentence}}
\end{alectryon}
\end{document}
"""
    BODY_RE = re.compile(r"\\begin\{document\}\n(?P<contents>.*?)\n\\end\{document\}", re.DOTALL)

    def _postprocess(self, output):
        return self.BODY_RE.search(output).group("contents").strip()

if __name__ == '__main__':
    from io import StringIO
    r = unittest.main(testRunner=unittest.TextTestRunner(stream=StringIO()), exit=False).result
    for t, tb in [*r.failures, *r.errors]:
        print(f"FAIL: {t}\n{tb}")
    print("OK" if r.wasSuccessful() else "FAILED")
    sys.exit(not r.wasSuccessful())
