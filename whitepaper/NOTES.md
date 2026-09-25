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
**2026-09-25 (section 2, terms and rules).**  Two places where the
fragment is simpler than the real proof and the real proof could
follow.  (1) The level oracle: the fragment's `LevelOracle` class
assumes `≤` and `=` sound *and complete* for `eval`, but the real
proof only ever proves soundness (`leq_sound`, `isEquiv_sound` in
`ConLeche/Verify/Level.lean`) and the env-free rules consume only the
`= true` direction.  If the inductive installs do not need
completeness either, the fragment's class can drop the reverse
implications and the paper can stop claiming an assumption it does
not use.  (2) `Infer.lam`: `Rel.lean`'s rule validates the datum once
per λ-chain (`body.lamPw`), which costs three conditional premises
and junk witnesses; the fragment validates at every λ with one
unconditional premise pair.  The checker's economy is a fact about
runs, not about the relation: with the per-λ rule as the primitive,
"inner data agree with the neighbour and the innermost is validated"
would be a derived lemma feeding the bridge, and the soundness case
for `lam` would shrink to the fragment's.

**2026-09-25 (fragment lane, stage 1–3).** Five things the fragment's
proof shows about the real one. (1) *No frame.* The three claims of
`Model/Rules/Motive.lean` carry `Frame d e` (scoping, loose-bvar bounds,
leaf bounds) and conclude it of every reduct and inferred type, and the
environment laws need closedness lemmas. In the fragment nothing of the
kind exists: `interp` is total on de Bruijn terms, the environment laws
are stated for every `ρ` (`type_ok`, `unfold`, `RecRuleLaw` in
`EnvModel.lean`), and the β-substitution lemma is an identity about
environments — so `Frame` is entirely an artefact of `fvar`s and of the
closing operation between the checker's opened bodies and the relation's
de Bruijn reading. (2) *The ι comparisons are redundant.* `Red.iota` in
`Rel.lean` compares the constructor's levels with the recursor's
(`Level.isEquivList usj …`) and, for some rules, the parameters
(`DefEqList`). The fragment's `Red.iota` carries neither: the recursor
certificate puts the major in the family at the recursor's parameters,
and a fixpoint's inversion (the obligation `RecRuleLaw`'s docstring hands
part 2) gives the fields' membership at those parameters. Lean's kernel
does not compare either; whether con-leche's comparisons pay for
something the modeled/nested routes need, or are simply inherited, is
worth a look. (3) *`trans` cannot be refuted here.* The task #309
counterexample lives on `DefEq.fvar` ignoring an annotation that
`DefEq.proofFast` reads; with contexts instead of annotated `fvar`s the
fragment has neither rule, and I found no fragment counterexample. The
paper's argument against `trans` should therefore be the structural one
(the middle term's invariant has no supplier: `DefEq.redL_sound` is the
sound chaining precisely because `RedSem` concludes the reduct's
invariant), with the real checker's unsoundness as the reason the
question is not academic. (4) *The domain-sort premise of `Infer.lam` is
not used by soundness* (`Infer.lam_sound`'s `_hu`): it is the checker's
"the domain is a type" check, and the model does not need it because a
λ's domain only ever enters as the set its denotation is a graph over.
(5) *One `Sat` clause instead of a context predicate.* Defining `Sat`
recursively on the context (`WellDenoted.lean`) makes `Sat_cons` hold by
`Iff.rfl`, so every binder case opens the context definitionally — the
`CtxOk`/`Sat`/`CtxOk.of_subset` machinery of the real proof exists to
track annotations on `fvar`s, not contexts.

**2026-09-25 (section 2, model and proof).**  Three things the
fragment's soundness makes visible, seen from the paper's altitude.  (1) The λ rule's domain-sort premise is unused by soundness (the
fragment lane's note (4) above); the real proof already drops it at the
io grade, so the full grade could too if Lean conformance were checked
elsewhere — the ∀ rule does read its sort premise, since the product's
level depends on it.  (2) The invariant is one predicate: the fragment's
`WellDenoted` folds the annotation's truthfulness into the two binder
clauses, and every case of the soundness proof reads it from there;
the real proof carries `AnnotValid` as a separate conjunct of
`WellDenotedV`, which the per-rule lemmas then split and rejoin.  A
single predicate with the annotation clause inside is what the pen-
and-paper argument wants, and nothing in §2 needed the separation.
(3) The env-free soundness uses no set-forming operation beyond
graphs, function spaces, truth values and the universe chain — no
pairing, union or power set — so `Model/Rules/*` could be stated over
a `SetLib`-sized interface derived from `SetTheory`, which would
document exactly what the soundness of the rules needs and what only
the constructions need.  A Typst trap of this lane: the coloured datum
inside a *display* equation (`ann(PW)` where `PW` is itself an
equation) makes the HTML export fail to converge ("number of equation
elements did not stabilize"); writing the datum inline, `ann(italic("pw"))`,
fixes it.  Related and unfixed: `lib.typ`'s `ann` emits `<mstyle>` only
while its in-math state is true, and a nested equation (such as `PW`
or `Sort`) inside the outer one resets the state to false when it ends,
so most coloured data inside `<math>` come out as `<span class="ann">`
— one `<mstyle>` in the whole page against 74 spans.  The show rule
should save and restore the state rather than set it to false.
