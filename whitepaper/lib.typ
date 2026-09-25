// whitepaper/lib.typ — the macro library of the whitepaper (task #323).
//
// ONE SOURCE, TWO RENDERINGS.  `build.sh` compiles `main.typ` twice, to
// PDF and to HTML, both with `--features html`; every macro below asks
// `target()` and emits either paged Typst layout or `html.elem`s styled
// by `style.css` (inlined into the page).  Writers never branch on the
// target themselves: they use the macros.
//
// USAGE.  Every section file starts with `#import "../lib.typ": *`;
// `main.typ` additionally applies `#show: template.with(...)`.
//
//   #ann[...]          THE annotation colour (blue-violet `ann-color`,
//                      #5b3fd6 — chosen to stay a legible dark grey on a
//                      greyscale printer; the HTML lightens it in dark
//                      mode).  Works in prose (`#ann[a proposition]`),
//                      inside math (`$lambda x : ann(p w). b$`), in rule
//                      premises and in grammars.  Colour is the ONLY
//                      change: a reader who ignores it sees Lean as it is.
//
//   #rule(name: "β", $premise 1$, $premise 2$, $conclusion$)
//                      an inference rule.  The LAST positional argument is
//                      the conclusion, everything before it a premise; no
//                      premise = an axiom.  Renders inline (put several in
//                      one paragraph for a row); `#rules(..)` centres a
//                      wrapping row of them with spacing.
//
//   #theorem[...] <lbl>          numbered blocks, ONE shared counter:
//   #lemma(name: "Preservation")[...]   theorem, lemma, corollary,
//   #definition[...] #remark[...] #example[...]   definition, remark,
//   #proof[...]                  example; `proof` is unnumbered and ends
//                                with a tombstone.  `@lbl` renders
//                                "Theorem 3", "Lemma 4", ….
//
//   #src("ConLeche/Kernel/PropWhen.lean", 12, 40)[PropWhen]
//                      a source link.  The label (optional) is plain
//                      text; it is followed by a small grey ↗ that links
//                      to github …/blob/master/<path>#L12-L40 (the third
//                      argument is optional: one line).  Paths under
//                      `ConLeche/` and `whitepaper/Fragment/` use the
//                      same shape.  Path and line numbers MUST be
//                      literals — `links-gate.sh` reads `src("…", a, b)`
//                      calls off the source text and snapshots the cited
//                      lines.
//
//   #lean[PropWhen]    a Lean code name, inline code (also `#lean("…")`).
//
//   #left-out[Projections][one sentence]
//                      an item of the "what we left out" list.
//
// ADDING A MACRO: give it both branches (paged and html), a CSS class in
// `style.css` for the html one, and a line up here.

#let ann-color = rgb("#5b3fd6")
#let repo = "https://github.com/leanprover/con-leche/blob/master/"

// --- is this macro being expanded inside math? ---------------------------
// Typst has no "am I in math" query; the template's show rule on
// `math.equation` flips this state on entering and leaving every equation,
// so `in-math.get()` is true exactly inside one.  It decides whether `ann`
// emits an `<mstyle>` (valid inside `<math>`) or a `<span>`.
#let in-math = state("in-math", false)

#let is-html() = target() == "html"

// --- the annotation ---------------------------------------------------------
#let ann(body) = context {
  if is-html() {
    if in-math.get() {
      html.elem("mstyle", attrs: (class: "ann", mathcolor: ann-color.to-hex()), body)
    } else {
      html.elem("span", attrs: (class: "ann"), body)
    }
  } else {
    text(fill: ann-color, body)
  }
}

// --- inference rules --------------------------------------------------------
#let rule(name: none, ..args) = {
  let a = args.pos()
  assert(a.len() >= 1, message: "rule: needs at least a conclusion")
  let prem = a.slice(0, a.len() - 1)
  let conc = a.last()
  context if is-html() {
    html.elem("span", attrs: (class: "rule"),
      html.elem("span", attrs: (class: "rule-body"),
        html.elem("span", attrs: (class: "premises"),
          prem.map(p => html.elem("span", attrs: (class: "premise"), p)).join())
        + html.elem("span", attrs: (class: "conclusion"), conc))
      + if name != none { html.elem("span", attrs: (class: "rule-name"), name) })
  } else {
    let prem-row = prem.join(h(1.5em))
    let w = calc.max(measure(prem-row).width, measure(conc).width) + 0.6em.to-absolute()
    let bar = stack(dir: ttb, spacing: 0.35em,
      align(center, block(width: w, prem-row)),
      line(length: w, stroke: 0.5pt),
      align(center, block(width: w, conc)))
    box(baseline: 35%, inset: (x: 0.4em, y: 0.3em),
      if name == none { bar } else {
        grid(columns: 2, column-gutter: 0.4em, align: horizon,
          bar, smallcaps(text(size: 0.9em, name)))
      })
  }
}

// A centred, wrapping row of rules.
#let rules(..rs) = context if is-html() {
  html.elem("div", attrs: (class: "rules"), rs.pos().join())
} else {
  align(center, block(width: 100%, rs.pos().join(h(1em))))
}

// --- numbered blocks --------------------------------------------------------
// All kinds share the figure counter of kind "theorem"; the supplement
// carries the kind, so `@lbl` prints "Lemma 4" and the numbers run in one
// sequence through the paper.
#let thm-block(supplement, name, body) = figure(
  kind: "theorem", supplement: supplement, numbering: "1",
  if name == none { body } else { metadata(name) + body })

#let theorem(name: none, body) = thm-block("Theorem", name, body)
#let lemma(name: none, body) = thm-block("Lemma", name, body)
#let corollary(name: none, body) = thm-block("Corollary", name, body)
#let definition(name: none, body) = thm-block("Definition", name, body)
#let remark(name: none, body) = thm-block("Remark", name, body)
#let example(name: none, body) = thm-block("Example", name, body)

#let proof(body) = context if is-html() {
  html.elem("div", attrs: (class: "proof"),
    html.elem("span", attrs: (class: "proof-head"), [Proof.]) + [ ] + body
    + html.elem("span", attrs: (class: "qed"), sym.square.stroked))
} else {
  block(width: 100%, inset: (y: 0.2em))[_Proof._ #body #h(1fr) $square.stroked$]
}

// --- source links ----------------------------------------------------------
// `src(path, a)`, `src(path, a, b)`, each optionally followed by `[label]`.
#let src(path, a, ..rest) = {
  let pos = rest.pos()
  let b = if pos.len() > 0 and type(pos.at(0)) == int { pos.at(0) } else { a }
  let label = if pos.len() > 0 and type(pos.last()) != int { pos.last() } else { none }
  assert(type(a) == int and type(b) == int and b >= a,
    message: "src: line numbers must be integer literals with b >= a")
  let anchor = if a == b { "#L" + str(a) } else { "#L" + str(a) + "-L" + str(b) }
  let url = repo + path + anchor
  let where = path + anchor
  context if is-html() {
    if label != none { html.elem("span", attrs: (class: "src-label"), label) }
    html.elem("a", attrs: (class: "src", href: url, title: where), sym.arrow.tr)
  } else {
    if label != none { label }
    link(url, text(size: 0.7em, fill: luma(110), baseline: -0.5em, sym.arrow.tr))
  }
}

// --- code names ---------------------------------------------------------------
#let content-text(c) = {
  if type(c) == str { c }
  else if c.has("text") { c.text }
  else if c.has("children") { c.children.map(content-text).join() }
  else if c.func() == [ ].func() { " " }
  else { "" }
}
#let lean(s) = raw(content-text(s), lang: "lean")

// --- the "what we left out" list ---------------------------------------------
#let left-out(what, why) = context if is-html() {
  html.elem("p", attrs: (class: "left-out"),
    html.elem("strong", what) + [ — ] + why)
} else {
  block(width: 100%, inset: (y: 0.15em))[*#what* — #why]
}

// --- the template -------------------------------------------------------------
// `#show: template.with(title: .., authors: .., note: ..)` in main.typ.
#let template(title: "", authors: "", note: none, doc) = {
  set document(title: title, author: authors)
  set heading(numbering: "1.")

  // Flip `in-math` around every equation (see above).
  show math.equation: it => { in-math.update(true); it; in-math.update(false) }

  // The numbered blocks: one rendering per target, the header built from
  // the figure's own supplement, counter and optional `metadata(name)`.
  show figure.where(kind: "theorem"): it => {
    let name = none
    let body = it.body
    if (body.has("children") and body.children.len() > 0
        and body.children.first().func() == metadata) {
      name = body.children.first().value
      body = body.children.slice(1).join()
    }
    let head = [#it.supplement #it.counter.display(it.numbering)]
    let head = if name == none { [#head.] } else { [#head (#name).] }
    context if is-html() {
      let attrs = (class: "thm")
      html.elem("div", attrs: attrs,
        html.elem("span", attrs: (class: "thm-head"), head) + [ ] + body)
    } else {
      set align(left)
      block(width: 100%, inset: (left: 0.8em, y: 0.4em),
        stroke: (left: 1.5pt + luma(170)), breakable: true,
        [*#head* #body])
    }
  }
  show ref: it => {
    // `@lbl` on a numbered block prints "Lemma 4", the kind from the
    // supplement of the target rather than the figure's generic one.
    let el = it.element
    if el != none and el.func() == figure and el.kind == "theorem" {
      let n = numbering(el.numbering, ..el.counter.at(el.location()))
      link(it.target, [#el.supplement #n])
    } else { it }
  }

  context if is-html() {
    html.elem("style", read("style.css"))
    html.elem("header", attrs: (class: "title"),
      html.elem("h1", title)
      + html.elem("p", attrs: (class: "authors"), authors)
      + if note != none { html.elem("p", attrs: (class: "note"), note) })
    doc
  } else {
    set page(paper: "a4", margin: (x: 2.6cm, y: 2.4cm), numbering: "1")
    set text(font: "Libertinus Serif", size: 10.5pt)
    set par(justify: true, leading: 0.65em)
    show heading: set text(font: "Libertinus Sans")
    show heading: it => { v(0.6em); it; v(0.3em) }
    show raw: set text(font: "DejaVu Sans Mono", size: 0.88em)
    show link: set text(fill: rgb("#2a4d8f"))
    align(center, {
      text(font: "Libertinus Sans", size: 20pt, weight: "bold", title)
      v(0.6em)
      text(size: 11pt, authors)
      v(0.4em)
    })
    if note != none {
      block(width: 100%, inset: (x: 1.5em, y: 0.6em), fill: luma(245),
        text(size: 9.5pt, note))
    }
    doc
  }
}
