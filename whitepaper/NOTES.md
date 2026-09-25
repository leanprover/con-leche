# Notes from the whitepaper lanes

Places where, thinking at this level of abstraction, the con-leche proof
or the process could be simpler. Dated, one paragraph each.

**2026-09-25 (tooling).** Typst 0.15's HTML export silently DROPS
`text(fill: …)` — both in prose and in math — while emitting native
MathML for everything else. For a paper whose one device is a colour
that is a trap worth naming: `lib.typ`'s `ann` therefore emits a
`<span class="ann">` in prose and an `<mstyle mathcolor>` inside `<math>`,
told apart by a state flipped around every equation by a show rule. A
second trap: a rule name typeset with `h(…)`/`stack` is dropped too, so
the inference rules are flex boxes in HTML and measured stacks in the
PDF. Neither is a reason to leave Typst; both were found by the spike,
not by a compile warning.
