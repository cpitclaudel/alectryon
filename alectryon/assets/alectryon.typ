/// Alectryon Typst support library

/// Theme

#let tango-light-aluminium = rgb("#EEEEEC")
#let tango-medium-aluminium = rgb("#D3D7CF")
#let tango-medium-gray = rgb("#555753")
#let tango-scarletred = rgb("#EF2929")

#let alectryon-fill-color = tango-light-aluminium
#let alectryon-stroke-color = tango-medium-aluminium
#let alectryon-goal-line-color = tango-medium-gray
#let alectryon-stale-warning-color = tango-scarletred

#let alectryon-margin = 0.3em
#let alectryon-vsep = 0.15em
#let alectryon-rule-skip = 0.3em
#let alectryon-hyp-h = 2em
#let alectryon-hyp-v = 0.6em
#let alectryon-hyp-indent = 0.3em

/// Utilities

// Render plain text as a raw element
#let txt(text) = raw(text)

// Current language, set by io() and read by code()
#let _alectryon-lang = state("alectryon-lang", "coq")

// Render code as a raw element
#let code(text) = context {
  let lang = _alectryon-lang.get()
  // -output avoids re-triggering the `show` rule
  raw(text, lang: lang + "-output")
}

// Top-aligned inline box (\parbox[t])
// https://github.com/typst/typst/issues/493
#let top-box(body) = context {
  let total = measure(body)
  let ascender = measure(text(top-edge: "ascender", bottom-edge: "baseline", txt("X"))).height
  box(baseline: total.height - ascender, body)
}

// https://github.com/typst/typst/issues/5741
#let output-block(body) = block(
  fill: alectryon-fill-color,
  stroke: alectryon-margin + alectryon-stroke-color,
  inset: alectryon-margin * 2,
  outset: -alectryon-margin / 2,
  width: 100%,
  breakable: true,
  spacing: alectryon-vsep,
  body,
)

/// Rendering primitives

// Wrap an annotated block (one or more sentences with goals/messages)
#let io(lang, body) = {
  _alectryon-lang.update(lang)
  set par(justify: false)
  set text(hyphenate: false)
  body
}

// Render a type or body preceded by its operator (`:`/`:=`)
#let hyp-bt(op, term) = {
  if term != none {
    top-box({
      h(math.thin.amount) + op + h(math.thin.amount)
      top-box(term)
    })
  }
}

// Render a single hypothesis
#let hyp(names, body, type) = {
  h(alectryon-hyp-h, weak: true)
  top-box(
    par(hanging-indent: alectryon-hyp-indent, {
      strong(names)
      hyp-bt(txt(":="), body)
      hyp-bt(txt(":"), type)
    })
  )
}

#let goal(name, hyps, concl) = output-block({
  if hyps != none {
    context par(leading: par.leading + alectryon-hyp-v, hyps)
  }
  block(above: alectryon-rule-skip, below: alectryon-rule-skip, {
    grid(
      columns: (1fr, auto),
      column-gutter: 0em,
      align: horizon,
      line(length: 100%, stroke: 0.4pt + alectryon-goal-line-color),
      if name != none { text(size: 0.75em, raw(" ") + name) }
    )
  })
  concl
})

// Render a message
#let message(body) = output-block(body)

// Render a sentence
#let sentence(input, outputs) = {
  input
  if outputs != none {
    set text(size: 0.85em)
    outputs
  }
}

// Scope passed to eval
#let render-scope = (
  io: io, sentence: sentence, goal: goal, hyp: hyp, message: message,
  code: code, txt: txt,
)

// Warning box for stale snippets
#let stale-warning(original) = block(
  fill: alectryon-stale-warning-color, inset: alectryon-margin, width: 100%,
  [*Stale snippet*: re-run `alectryon`. \ #original]
)

/// Main entry point

#let setup(json-path, body) = {
  if sys.inputs.at("alectryon-mode", default: none) == "query" {
    // Skip processing when running in query mode
    return body
  }

  if json-path == none {
    return body
  }

  let snippets = json(json-path).at("snippets", default: ())
  let langs = snippets.map(s => s.lang).dedup()
  let alectryon-counter = counter("alectryon-block-index")

  show raw.where(block: true): it => {
    if it.at("lang", default: none) not in langs {
      return it
    }

    context {
      let idx = alectryon-counter.get().first()
      let entry = snippets.at(idx, default: (src: "", rendered: none))
      if entry.src != it.text {
        stale-warning(it)
      } else {
        eval(entry.rendered, mode: "code", scope: render-scope)
      }
    }

    alectryon-counter.step()
  }

  body
}
