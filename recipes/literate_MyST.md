Writing Alectryon documents in Markdown with MyST
=================================================

To compile this file, use the following command:

    $ alectryon literate_MyST.md # MyST → HTML, produces ‘literate_MyST.html’

Alectryon supports input files written in MyST (a Markdown variant) in addition to Coq and reStructuredText.

```{raw} html
<style type="text/css"> .border { border: solid } </style>
```

In MyST Coq fragments are spelled as ```` ```{coq} ````, with arguments on the same line and options below:

```{coq} unfold
:class: border

Goal exists x, x * x = 49 /\ x < 10.
  let rec t n := (exists n; split; [reflexivity |]) || t (S n) in t 0.
  unfold lt.
  repeat constructor.
```

Math is written either in Docutils math roles ({math}`e^{i\pi} = -1`) or in `$` signs ($\cos(\pi) = -1$).  And unlike in reST, *built-in inline markup **nests**, including `code` and other roles like `coqid` {coqid}`references <Coq.Init.Nat#even>` or [links](https://myst-parser.readthedocs.io/en/latest/syntax/reference.html#extended-block-tokens)*.
