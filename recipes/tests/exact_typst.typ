/*
  Typst half of a LaTeX/Typst comparison; paired with exact_latex.tex.

  $ alectryon exact_typst.typ
      # Typst → JSON; produces ‘exact_typst.alectryon.json’
  $ typst compile --root . exact_typst.typ exact_typst.pdf
      # Typst → PDF; produces ‘exact_typst.pdf’
*/

// Match LaTeX's configuration so PDFs can be compared
#set par(first-line-indent: 0pt, spacing: 0.7em)

// LaTeX's `pt` is 1/72.27 inch; Typst's `pt` is 1/72 inch.
#let latex-pt = 72 / 72.27 * 1pt
#set text(size: 10 * latex-pt, font: "Latin Modern Roman")
#show raw: set text(font: "Latin Modern Mono")

// LaTeX's `article` sets `\topskip = 10pt`, so the first baseline lands
// 10pt below the top margin.  Typst places the first baseline at the font's
// cap-height (~6.84pt for Latin Modern Roman at 10pt).  Widening the top margin
// by that difference aligns the two first baselines.
#set page(paper: "a4", margin: (x: 1in, y: 1in + 3.16pt))

// `show` doesn't apply to eval-d blocks, so use `set` inside of `show`
#show raw.where(lang: "coq"): set raw(syntaxes: "/_output/tests/coq.tm-syntax")

#import "/_output/tests/alectryon.typ"
#show: alectryon.setup.with("/_output/tests/exact_typst.alectryon.json")

A small proof for LaTeX/Typst comparison:

```coq
Goal True /\ True.
Proof.
  split.
  idtac "test".
  -
      exact I.

  - exact I.


Qed.
```

End of test.
