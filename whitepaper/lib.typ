// whitepaper/lib.typ — the macro library of the whitepaper (task #324).
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
//                      premises and in grammars, and with a nested
//                      equation as the body (`ann(PW)` for `PW = $…$`).
//                      Colour is the ONLY change: a reader who ignores it
//                      sees Lean as it is.
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
//   #src("ConLeche/Kernel/PropWhen.lean", 12, 40)[the datum]
//                      a source link.  The LABEL IS THE LINK (required,
//                      non-empty: the natural phrase of the sentence, or
//                      the definition's name), marked by a muted dotted
//                      underline and nothing else — no arrow — pointing
//                      at github …/blob/master/<path>#L12-L40 (the third
//                      argument is optional: one line).  In HTML the
//                      label shows the cited lines on hover/focus (at
//                      most 40, then an ellipsis); the lines are read off
//                      the tree at compile time, so an anchor past the
//                      end of the file fails the build.  Paths under
//                      `ConLeche/` and `whitepaper/Fragment/` use the
//                      same shape.  Path and line numbers MUST be
//                      literals — `links-gate.sh` reads `src("…", a, b)`
//                      calls off the source text and snapshots the cited
//                      lines.
//
//   #overview(7)[label]
//                      a link to section `## 7. …` of OVERVIEW.md on
//                      GitHub, anchor computed from the heading at
//                      compile time (no such section = compile error).
//                      Default label: `OVERVIEW.md` §7.
//
//   #lean[PropWhen]    a Lean code name, inline code (also `#lean("…")`).
//
//   #left-out[Projections][one sentence]
//                      an item of the "what we left out" list.
//
//   #real[...]         a set-off remark about the REAL proof/checker
//                      (PLAN.md, 2026-10-02): a paragraph the reader can
//                      skip at a glance — thin rule on the left, the
//                      label in small caps, body slightly smaller, all in
//                      the muted colour (never the annotation colour), no
//                      background.  `#real(label: "In the real checker")[...]`
//                      overrides the default label "In the real proof".
//
// ADDING A MACRO: give it both branches (paged and html), a CSS class in
// `style.css` for the html one, and a line up here.
//
// TYPST NOTES — traps met while building (2026-09-25).  None of them
// produces a compile warning; all were found by reading the output.
//
//   * Typst 0.15's HTML export silently DROPS `text(fill: …)`, in prose
//     and in math, while emitting native MathML for everything else.
//     Hence `ann` emits a <span class="ann"> in prose and an <mstyle
//     mathcolor> inside <math>, told apart by the `in-math` depth
//     counter below.
//   * The same export drops a rule name typeset with `h(…)`/`stack`;
//     hence `rule` is a flex box in HTML and a measured stack in the PDF.
//   * A nested equation as `ann`'s body inside math (`ann(PW)` with
//     `PW = $…$`) must be unwrapped: <math> inside <math> is invalid
//     MathML, and the extra equation element made the export's
//     introspection loop fail to converge ("number of equation
//     elements did not stabilize").  `ann` unwraps it.
//   * In markup, a `;` directly after a `#src(...)` call is swallowed
//     as the call's terminator; write `\;`.

#let ann-color = rgb("#5b3fd6")
#let repo = "https://github.com/leanprover/con-leche/blob/master/"

// --- is this macro being expanded inside math? ---------------------------
// Typst has no "am I in math" query; the template's show rule on
// `math.equation` increments this DEPTH on entering and decrements it on
// leaving every equation — a counter, not a flag, because a nested
// equation (a `$…$` bound to a name and used inside another) would
// otherwise reset it to "outside" when it ends.  `in-math.get() > 0` is
// true exactly inside math; it decides whether `ann` emits an `<mstyle>`
// (valid inside `<math>`) or a `<span>`.
#let in-math = state("in-math", 0)

#let is-html() = target() == "html"

// --- the annotation ---------------------------------------------------------
#let ann(body) = context {
  if is-html() {
    if in-math.get() > 0 {
      // A nested equation as the body (`ann(PW)` with `PW = $…$`) is
      // unwrapped: a <math> inside <math> is invalid MathML, and the
      // extra equation element is what kept the export from converging.
      let inner = if body.func() == math.equation { body.body } else { body }
      html.elem("mstyle", attrs: (class: "ann", mathcolor: ann-color.to-hex()), inner)
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
  assert(label != none and label != [] and label != "",
    message: "src(" + path + "): a source link needs a label — `#src(\"…\", a, b)[the phrase]`")
  let anchor = if a == b { "#L" + str(a) } else { "#L" + str(a) + "-L" + str(b) }
  let url = repo + path + anchor
  let where = path + ":L" + str(a) + if b != a { "-L" + str(b) } else { "" }
  // The cited lines, read off the tree at compile time (build.sh passes
  // `--root <repo root>`, so "/" + path is the file).  An anchor outside
  // the file is a compile error — the second half of the link gate.
  let lines = read("/" + path).split("\n")
  if lines.len() > 0 and lines.last() == "" { lines.pop() }
  assert(a >= 1 and b <= lines.len(),
    message: "src: " + where + " is outside the file (" + str(lines.len()) + " lines)")
  context if is-html() {
    // The hover tip: at most `cap` lines, numbered, as a raw block.
    // INLINE elements only (spans, inline raw): the tip sits inside a
    // paragraph, and a <p> or <pre> there would make the HTML parser
    // close the enclosing paragraph.  CSS gives the spans their blocks.
    let cap = 40
    let last = calc.min(b, a + cap - 1)
    let width = str(last).len()
    let lang = if path.ends-with(".lean") { "lean" } else { none }
    let numbered = range(a, last + 1).map(n =>
      html.elem("span", attrs: (class: "ln"), " " * (width - str(n).len()) + str(n))
      + raw(lines.at(n - 1), block: false, lang: lang) + "\n").join()
    if last < b {
      numbered += (html.elem("span", attrs: (class: "ln"), " " * width)
        + html.elem("span", attrs: (class: "more"), "… " + str(b - last) + " more lines"))
    }
    html.elem("span", attrs: (class: "src-wrap"),
      html.elem("a", attrs: (class: "src", href: url, title: where), label)
      + html.elem("span", attrs: (class: "src-tip"),
          html.elem("span", attrs: (class: "src-tip-head"), where)
          + html.elem("span", attrs: (class: "src-tip-code"), numbered)))
  } else {
    // The label itself is the link, in the running text's colour (the
    // template's `show link` blue is overridden by the fill in force
    // outside the link — black in prose, muted inside a `real` block),
    // marked by a muted dotted underline.
    link(url, text(fill: text.fill,
      underline(stroke: (paint: luma(150), thickness: 0.7pt, dash: "dotted"),
        offset: 2.2pt, label)))
  }
}

// --- OVERVIEW.md sections -------------------------------------------------------
// `overview(7)` or `overview(7)[label]`: a link to the `## 7. …` section
// of OVERVIEW.md on GitHub.  The anchor is GitHub's slug of the heading
// (lowercase, punctuation dropped, spaces to hyphens), computed here by
// reading /OVERVIEW.md, so a renumbered section fails the compile
// instead of rotting into a dead anchor.  links-gate.sh checks the same.
#let github-slug(title) = {
  let t = lower(title.trim())
  t = t.replace(regex("[^\\p{L}\\p{N} -]"), "")
  t.replace(" ", "-")
}

#let overview(n, ..rest) = {
  let label = if rest.pos().len() > 0 { rest.pos().first() } else { [§#n of `OVERVIEW.md`] }
  let prefix = "## " + str(n) + "."
  let heads = read("/OVERVIEW.md").split("\n").filter(l => l.starts-with(prefix))
  assert(heads.len() == 1,
    message: "overview: OVERVIEW.md has no (unique) heading `" + prefix + " …`")
  let title = heads.first().slice(3)
  let url = repo + "OVERVIEW.md#" + github-slug(title)
  context if is-html() {
    html.elem("a", attrs: (class: "overview", href: url, title: "OVERVIEW.md, " + title), label)
  } else {
    link(url, label)
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

// --- remarks about the real proof ------------------------------------------
// `real[...]`, `real(label: "In the real checker")[...]`: the set-off,
// skippable paragraph of PLAN.md (2026-10-02) about the REAL proof or
// checker.  Muted throughout — rule, label and body — so the eye passes
// over it; the HTML export drops `text(fill: …)`, so there `style.css`
// (`.real`) carries the colour, size and small caps.
#let muted = luma(106)   // = the CSS --muted, #6a6a6a
#let real(label: "In con-leche", body) = context if is-html() {
  html.elem("div", attrs: (class: "real"),
    html.elem("span", attrs: (class: "real-label"), label) + [ ] + body)
} else {
  block(width: 100%, inset: (left: 0.9em, y: 0.3em),
    stroke: (left: 0.7pt + muted), breakable: true,
    text(size: 0.92em, fill: muted, [#smallcaps(label)#h(0.7em)#body]))
}

// --- the template -------------------------------------------------------------
// `#show: template.with(title: .., authors: .., note: ..)` in main.typ.
#let template(title: "", authors: "", note: none, doc) = {
  set document(title: title, author: authors)
  set heading(numbering: "1.")

  // Count equation depth (see `in-math` above).
  show math.equation: it => { in-math.update(d => d + 1); it; in-math.update(d => d - 1) }

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
    // Keep a source tip inside the viewport: CSS shows it, this nudges it
    // left when it would overflow the right edge.  (No `<`, `>` or `&`
    // in the script: the export escapes them.)
    html.elem("script", read("src-tip.js"))
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
