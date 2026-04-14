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

// LaTeX dimensions are set once and not rescaled within the output boxes
#let alectryon-output-scale = 0.9
#let alectryon-io-vsep = 1em // Match LaTeX
#let alectryon-margin = 0.3em / alectryon-output-scale
#let alectryon-vsep = 0.15em / alectryon-output-scale
#let alectryon-rule-skip = 0.3em / alectryon-output-scale
#let alectryon-hyp-h = 2em / alectryon-output-scale
#let alectryon-hyp-v = 0.6em / alectryon-output-scale
#let alectryon-hyp-indent = 0.3em / alectryon-output-scale

/// Utilities

// Typst hardcodes `size: 0.8em` on `raw` elements
#let raw-correction = 1em / 0.8

// Render plain text as a raw element
#let txt = raw

// Current language, set by io() and read by code()
#let _alectryon-lang = state("alectryon-lang", "coq")

// Render code as a raw element
#let code(contents) = context {
  let lang = _alectryon-lang.get()
  // <alectryon-processed> prevents the `show` rule added by `setup` from
  // triggering recursively.  Per the docs “labels can only be attached to
  // elements in markup mode, not in code mode”, so we must use [] syntax.
  [#raw(contents, lang: lang)<alectryon-processed>]
}

// Top-aligned inline box (\parbox[t])
// https://github.com/typst/typst/issues/493
#let top-box(body) = context {
  let total = measure(body)
  let ascender = measure(text(top-edge: "ascender", bottom-edge: "baseline", txt("X"))).height
  box(baseline: total.height - ascender, body)
}

// https://github.com/typst/typst/issues/5741
#let outputs(body) = block(
  fill: alectryon-stroke-color,
  inset: alectryon-margin,
  width: 100%,
  breakable: true,
  spacing: alectryon-vsep,
  body,
)

#let output(body) = block(
  fill: alectryon-fill-color,
  inset: alectryon-margin,
  width: 100%,
  breakable: true,
  spacing: alectryon-margin,
  body,
)

/// Rendering primitives

// Wrap an annotated block (one or more sentences with goals/messages)
#let io(lang, body) = {
  v(alectryon-io-vsep)
  block(spacing: alectryon-io-vsep, {
    _alectryon-lang.update(lang)
    set par(justify: false)
    // Adjust font size of plain text items
    set text(size: raw-correction)
    // Adjust font size of code
    show raw: set text(size: raw-correction)
    body
  })
  v(alectryon-io-vsep)
}

// Render a type or body preceded by its operator (`:`/`:=`)
#let _hyp-bt(op, term) = {
  if term != none {
    top-box({
      h(math.thin.amount) + op + h(math.thin.amount)
      top-box(term)
    })
  }
}

#let hyp(names, body, type) = {
  h(alectryon-hyp-h, weak: true)
  top-box(
    par(hanging-indent: alectryon-hyp-indent, {
      strong(names)
      _hyp-bt(txt(":="), body)
      _hyp-bt(txt(":"), type)
    })
  )
}

#let _goal-separator(name) = {
  v(alectryon-rule-skip)
  block(spacing: alectryon-rule-skip, {
    grid(
      columns: (1fr, auto),
      column-gutter: 0em,
      align: horizon,
      line(length: 100%, stroke: 0.4pt + alectryon-goal-line-color),
      if name != none { text(size: 0.75em, txt(" ") + name) }
    )
  })
  v(alectryon-rule-skip)
}

#let goal(name, hyps, concl) = {
  output({
    if hyps != none {
      context par(leading: par.leading + alectryon-hyp-v, hyps)
    }
    _goal-separator(name)
    concl
  })
}

#let message = output

#let goals = outputs
#let messages = outputs

#let sentence(input, outputs) = block({
  block(input)
  if outputs != none {
    set text(size: alectryon-output-scale * 1em)
    // LaTeX adds space relative to the bottom of the previous box; Typst uses
    // the baseline.  Compromise by adding half of a strut depth to vsep.
    block(above: 0.3em / 2 + alectryon-vsep, {
      outputs
    })
  }
})

// Scope passed to eval
#let render-scope = (
  io: io, sentence: sentence,
  goals: goals, goal: goal, hyp: hyp,
  messages: messages, message: message,
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
    // Skip already-processed raw elements
    if it.at("label", default: none) == <alectryon-processed> {
      return it
    }

    // Skip unknown languages
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
