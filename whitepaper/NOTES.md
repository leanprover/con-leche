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

**2026-09-25 (writer lane, §1 and §5).** Writing §5 meant listing every
layer the fragment does without, and three of them look removable from
the real proof too. (1) The reading has three notations for one idea:
`denoteMeta` (checker term → erased `AnnotTerm`, partial), `interp`
(`AnnotTerm` → set) and `Denotes` (checker term → set, the statement's
relation), plus the theorem that identifies the first two with the
third. The paper has one denotation that reads the coloured datum at the
level valuation directly, and nothing in §2's argument needs the numeral
layer; if `interp` were defined on `Expr` under `φ` — as `Denotes` is,
but as a function — the erased layer and `Denotes_of_denoteMeta` would
go, and `WellDenoted` would be stated once, on the checker's terms.
(2) `Certs`, `DefEqList` and `EtaProjCerts` are relations only because a
rule with a list premise is awkward in a mutual inductive; a
`List.Forall₂`-shaped premise (or a nested occurrence, at the cost of a
hand-written induction principle) folds all three into the rules that
use them, which is what the paper does and what a reader expects. (3) The
run-to-derivation story is told twice — the bridge from the pure fuelled
core to the relations, and the simulation from the cached core to the
pure one. If the cached core were the only core (the pure one exists for
the proof alone), the bridge could be stated on it directly and the
simulation layer, its `CSOK` invariant and the twin-effect kit would
disappear; the price is that the bridge induction would then carry the
memo-table invariant, which is the one thing the simulation currently
isolates. Also worth recording: a `;` directly after `#src(...)` is
swallowed by Typst as the expression terminator; write `)\;`.
