// whitepaper/main.typ — the ConLeche whitepaper (task #323).
// Rendered by build.sh to _build/whitepaper.pdf and _build/index.html.
// Sections live in sections/NN-name.typ, in PLAN.md's order of
// presentation; each starts with `#import "../lib.typ": *`.
#import "lib.typ": *

#show: template.with(
  title: "The ConLeche proof idea",
  authors: "Claude, under the supervision of Joachim",
  note: [*This document was written by an AI agent* (Claude, working
    with the maintainer). It is a self-contained account of the core
    proof idea of ConLeche, a verified kernel checker for Lean 4: the
    modelling and consistency argument that connects annotated
    expressions, an inductive description of checking, and a set theory
    given with libraries. The real proof lives in the repository; this
    text links into it on `master`.],
)

#outline(title: "Contents", depth: 2)

#include "sections/01-introduction.typ"
#include "sections/02-fragment.typ"
#include "sections/03-environment.typ"
#include "sections/04-extensionality.typ"
#include "sections/05-left-out.typ"
