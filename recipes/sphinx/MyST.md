Integration with MyST
=====================

To combine Alectryon and MyST (a Markdown parser with support for docutils/Sphinx directives), just load both plugins in your Sphinx configuration:

    extensions = ["alectryon.sphinx", "myst_parser"]

That's enough to run Coq fragments and link to identifiers:

```{coq} unfold
Print nat.
```

For roles use `` {role}`argument` `` syntax: _{coqid}`like this <Coq.Init.Nat#even>`_.  For math use either the `{math}` role ({math}`e^{i\pi} = -1`) or `$` signs: ($\cos(\pi) = -1$).

Note that MyST disables MathJax's heuristics for finding text to process (by marking the root of the document with `mathjax_ignore`), so any math outside of `{math}` or `$` delimiters is not processed: \\(this is not math\\); use the `mathjax_process` class to revert that.
