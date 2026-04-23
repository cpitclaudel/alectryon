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
#let alectryon-marker-sep = 0.35em
#let alectryon-marker-stroke = 0.4pt

/// Utilities

// Typst hardcodes `size: 0.8em` on `raw` elements
#let raw-correction = 1em / 0.8

// Math unit from LaTeX
#let mu = 1em / 18

#let txt = raw

// Current language, set by the show rule in `setup` and read by code()
#let _lang = state("alectryon-lang", "coq")

// kind → list of entries (indexed by call position)
#let _marker-info = state("alectryon-marker-info", ("mrefs": (), "mquotes": ()))

#let mref-marker(marker) = {
  h(alectryon-marker-sep)
  box(
    stroke: alectryon-marker-stroke,
    inset: alectryon-marker-stroke / 2 + 0.1em,
    baseline: alectryon-marker-stroke / 2 + 0.1em,
    text(size: 0.8em, weight: "bold", marker)
  )
}

#let mref-markers(markers) = {
  for m in markers { mref-marker(m) }
}

#let with-ids(contents, ..ids) = {
  contents
  for id in ids.pos() [#metadata(none)#label(id)]
}

#let with-markers(contents, ..markers) = {
  contents
  mref-markers(markers.pos())
}

#let code(contents) = context {
  let lang = _lang.get()
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

// https://github.com/typst/typst/issues/8162
#let smash(contents) = context {
  let h = measure(contents).height
  box(height: 0pt, clip: false, box(height: h, contents))
}

#let _goal-separator(name, markers) = {
  v(alectryon-rule-skip)
  block(spacing: alectryon-rule-skip, {
    grid(
      columns: (1fr, auto, auto),
      column-gutter: 0pt,
      align: horizon,
      line(length: 100%, stroke: 0.4pt + alectryon-goal-line-color),
      if name != none { text(size: 0.75em, txt(" ") + name) },
      // For goals, markers appear next to the rule
      if markers != () { smash(mref-markers(markers)) }
    )
  })
  v(alectryon-rule-skip)
}

#let goal(name, hyps, concl, ..markers) = {
  output({
    if hyps != none {
      context par(leading: par.leading + alectryon-hyp-v, hyps)
    }
    _goal-separator(name, markers.pos())
    concl
  })
}

#let message = output

#let goals = outputs
#let messages = outputs

#let sentence(input, outputs, ..markers) = {
  input + mref-markers(markers.pos())
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
  id: with-ids, marker: with-markers,
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

/// Marker references, quotes, and assertions

#let _is-query-mode = {
  sys.inputs.at("alectryon-mode", default: none) == "query"
}

// Counters used to step through JSON data
#let _mref-counter = counter("alectryon-mref-idx")
#let _mquote-counter = counter("alectryon-mquote-idx")
#let _block-counter = counter("alectryon-block-index")

#let _resolve-marker(kind, fn, counter, path, ..values) = {
  if _is-query-mode {
    [#metadata((path: path, ..values.named()))#label("alectryon-" + kind)]
    return
  }
  if fn == none { return }

  context {
    let idx = counter.get().first()
    let entry = _marker-info.get().at(kind).at(idx, default: none)
    if entry == none or entry.path != path { // Stale Alectryon data
      text(fill: alectryon-stale-warning-color, [?#raw(path)?])
    } else {
      fn(entry)
    }
  }
  counter.step()
}

#let _mref(entry) = {
  link(label(entry.id), entry.marker)
}

// Link to `path` (a value in the marker positioning mini-language)
#let mref(path, title: none, prefix: none, counter-style: none) = {
  _resolve-marker("mrefs", _mref, _mref-counter,
    path, title: title, prefix: prefix, counter-style: counter-style
  )
}

#let _mquote(entry, language: none, block: false) = {
  let lang = if language != none { language } else { entry.lang }
  _lang.update(lang)
  if block { render(entry.rendered) } else { box(render(entry.rendered)) }
}

#let mquote(path, prefix: none, language: none, block: false) = {
  _resolve-marker("mquotes", _mquote.with(language: language, block: block),
    _mquote-counter,
    path, prefix: prefix
  )
}

#let massert(path, prefix: none) = {
  _resolve-marker("masserts", none, none, path, prefix: prefix)
}

#let setup(json-path, body) = {
  if sys.inputs.at("alectryon-mode", default: none) == "query" {
    // Skip processing when running in query mode
    return body
  }

  if json-path == none {
    return body
  }

  let js = json(json-path)
  if js.at("version") != alectryon-json-version {
    panic([`alectryon.typ` version #str(alectryon-json-version) does not match
      #json-path version #repr(js.at("version")); re-run `alectryon`.])
  }

  _marker-info.update(js.at("marker-info"))
  let snippets = js.at("snippets")

  show raw.where(block: true): it => {
    let (lang, text) = read-lang-tag(it)
    if lang == none { return it }
    context {
      let idx = _block-counter.get().first()
      let entry = snippets.at(idx, default: (src: "", lang: "", rendered: none))
      if entry.src != text or entry.lang != lang {
        stale-warning(it)
      } else {
        _lang.update(entry.lang)
        render(entry.rendered)
      }
    }

    _block-counter.step()
  }

  body
}
