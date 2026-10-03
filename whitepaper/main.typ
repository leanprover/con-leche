// whitepaper/main.typ — the con-leche whitepaper (task #324).
// Rendered by build.sh to _build/whitepaper.pdf and _build/index.html.
// Sections live in sections/NN-name.typ, in PLAN.md's order of
// presentation; each starts with `#import "../lib.typ": *`.
#import "lib.typ": *

#show: template.with(
  title: "The con-leche proof idea",
  authors: "Joachim Breitner, Lean FRO",
  note: [*This document was written by an AI agent* (Claude, working
    with the maintainer). It is a self-contained account of the core
    proof idea of con-leche, a verified kernel checker for Lean 4: the
    modelling and consistency argument that connects annotated
    expressions, an inductive description of checking, and a set theory
    given axiomatically. The real proof lives in the repository, and
    phrases underlined like
    #src("ConLeche/MainTheorem.lean", 96, 99)[this one] link to it on
    `master`, at the definition or theorem being described; phrases
    underlined like #src("whitepaper/Fragment/Sound.lean", 817, 821)[this one]
    link to the paper's own Lean fragment. In the web version, hovering
    over such a phrase shows the cited lines.],
)

#include "sections/01-introduction.typ"
#include "sections/02-fragment.typ"
#include "sections/03-definitions.typ"
#include "sections/04-inductives.typ"
#include "sections/05-nested.typ"
#include "sections/06-extensionality.typ"
#include "sections/07-left-out.typ"
#include "sections/08-related.typ"

#bibliography("references.bib", title: "References")
