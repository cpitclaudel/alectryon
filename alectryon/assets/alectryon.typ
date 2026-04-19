/// Alectryon Typst support library

#let alectryon-json-version = 1

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

// Math unit from LaTeX
#let mu = 1em / 18

#let txt = raw

// Current language, set by the show rule in `setup` and read by code()
#let _alectryon-lang = state("alectryon-lang", "coq")

#let code(contents) = context {
  let lang = _alectryon-lang.get()
  raw(contents, lang: lang)
}

// Top-aligned inline box (\parbox[t])
// https://github.com/typst/typst/issues/493
#let top-box(body) = context {
  let total = measure(body).height
  let single-line = measure(code("X")).height
  box(baseline: total - single-line, body)
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
#let io(body) = {
  v(alectryon-io-vsep)
  block(spacing: alectryon-io-vsep, {
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
      h(3 * mu) + op + h(4 * mu)
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

#let sentence(input, outputs) = {
  input
  if outputs != none {
    set text(size: alectryon-output-scale * 1em)
    // LaTeX adds space relative to the bottom of the previous box; Typst uses
    // the baseline.  Compromise by adding half of a strut depth to vsep.
    block(spacing: 0.3em / 2 + alectryon-vsep, {
      outputs
    })
  }
}

#let concat(..args) = {
  args.pos().sum(default: none)
}

#let nodes = (
  io: io, sentence: sentence,
  goals: goals, goal: goal, hyp: hyp,
  messages: messages, message: message,
  code: code, txt: txt, "+": concat,
)

#let render(node) = {
  if node == none or type(node) == str {
    node
  } else {
    let fn = nodes.at(node.first())
    let args = node.slice(1).map(render)
    fn(..args)
  }
}

// Warning box for stale snippets
#let stale-warning(original) = block(
  fill: alectryon-stale-warning-color, inset: alectryon-margin, width: 100%,
  [*Stale snippet*: re-run `alectryon`. \ #original]
)

/// Main entry point

#let first-line-re = regex("^(.*?)(?:\n|\\z)")
#let fence-re = regex("^[{]([a-z0-9]+)[}]$")

// Typst <= 0.14.2 doesn't recognize {coq}, so we look for a {...} language tag
// at the beginning of the body if the real language tag is missing.
#let read-lang-tag(it) = {
  let lang = it.at("lang", default: none)
  let text = it.text

  if lang == none {
    // LATER: Discard this branch
    let line0 = text.match(first-line-re)
    if line0 == none { return (none, none) }
    (lang, text) = (line0.captures.at(0), text.slice(line0.end))
  }

  let fence = lang.match(fence-re)
  if fence == none { return (none, none) }
  (fence.captures.at(0), text)
}

#let setup(json-path, body) = {
  if sys.inputs.at("alectryon-mode", default: none) == "query" {
    // Skip processing when running in query mode
    return body
  }

  if json-path == none {
    return body
  }

  let data = json(json-path)
  if data.at("version") != alectryon-json-version {
    panic([`alectryon.typ` version #str(alectryon-json-version) does not match
      #json-path version #repr(data.at("version")); re-run `alectryon`.])
  }

  let snippets = data.at("snippets", default: ())
  let alectryon-counter = counter("alectryon-block-index")

  show raw.where(block: true): it => {
    let (lang, text) = read-lang-tag(it)
    if lang == none { return it }
    context {
      let idx = alectryon-counter.get().first()
      let entry = snippets.at(idx, default: (src: "", lang: "", rendered: none))
      if entry.src != text or entry.lang != lang {
        stale-warning(it)
      } else {
        _alectryon-lang.update(entry.lang)
        render(entry.rendered)
      }
    }

    alectryon-counter.step()
  }

  body
}
