# Notes from the whitepaper lanes

What this is: places where, thinking at the whitepaper's altitude —
one denotation on annotated terms, a semantic invariant instead of a
typing judgement, a set theory given as a class — the con-leche proof
could be simpler or more elegant. One numbered list, one observation
per item, each naming the fragment files and the real-proof files it
compares and the lane that made it (task #324, all of 2026-09-25).
Typst and tooling traps are not here: they are the "Typst notes"
comment block at the top of `lib.typ`.

1. **One denotation instead of three.** The real proof reads a
   checker term into an erased `AnnotTerm` (`denoteMeta`, partial),
   interprets that (`interp`), and states the main theorem over a
   third notion, the relation `Denotes` on checker terms, plus the
   theorem identifying the first two with the third
   (`Model/Denotes.lean`). The fragment has one denotation
   (`Fragment/Interp.lean`) that reads the coloured datum at the
   level valuation directly, and nothing in §2's argument needs the
   numeral layer. If `interp` were defined on `Expr` under `φ` — as
   `Denotes` is, but as a function — the erased layer and
   `Denotes_of_denoteMeta` would go, and `WellDenoted` would be stated
   once, on the checker's terms. Item 14 says what else this unlocks.
   (§1/§5 writer lane; §3 lane.)

2. **Fold the list relations into the rules.** `Certs`, `DefEqList`
   and `EtaProjCerts` (`Rules/Rel.lean`) are relations only because a
   rule with a list premise is awkward in a mutual inductive. A
   `List.Forall₂`-shaped premise (or a nested occurrence, at the cost
   of a hand-written induction principle) folds all three into the
   rules that use them, which is what the paper does
   (`Fragment/Rules.lean`, `Red.iota`) and what a reader expects.
   (§1/§5 writer lane.)

3. **One core, not two.** The run-to-derivation story is told twice:
   the bridge from the pure fuelled core to the relations
   (`Verify/Rules/Bridge.lean`) and the simulation from the cached
   core to the pure one (`Verify/Cached/SimC.lean`). If the cached
   core were the only core — the pure one exists for the proof alone —
   the bridge could be stated on it directly, and the simulation
   layer, its `CSOK` invariant and the twin-effect kit would
   disappear; the price is that the bridge induction would then carry
   the memo-table invariant, which is the one thing the simulation
   currently isolates. (§1/§5 writer lane.)

4. **The level oracle's completeness is assumed and never used.** The
   fragment's `LevelOracle` class (`Fragment/Level.lean`) assumes `≤`
   and `=` sound *and complete* for `eval`, but the real proof only
   ever proves soundness (`leq_sound`, `isEquiv_sound` in
   `Verify/Level.lean`), and every fragment theorem — the env-free
   rules and the inductive installs alike — consumes only the
   `= true` direction. The class can drop the reverse implications,
   and the paper can stop claiming an assumption it does not use.
   (§2a lane.)

5. **Validate the datum at every λ, not once per chain.** `Infer.lam`
   in `Rules/Rel.lean` validates the codomain datum once per λ-chain
   (`body.lamPw`), which costs three conditional premises and junk
   witnesses; the fragment validates at every λ with one unconditional
   premise pair (`Fragment/Rules.lean`). The checker's economy is a
   fact about runs, not about the relation: with the per-λ rule as the
   primitive, "inner data agree with the neighbour and the innermost is
   validated" would be a derived lemma feeding the bridge, and the
   soundness case for `lam` would shrink to the fragment's. (§2a lane.)

6. **`Frame` is an artefact of `fvar`s.** The three claims of
   `Model/Rules/Motive.lean` carry `Frame d e` (scoping, loose-bvar
   bounds, leaf bounds), conclude it of every reduct and inferred
   type, and the environment laws need closedness lemmas. In the
   fragment nothing of the kind exists: `interp` is total on de Bruijn
   terms, the environment laws are stated for every `ρ` (`type_ok`,
   `unfold`, `RecRuleLaw` in `Fragment/EnvModel.lean`), and the
   β-substitution lemma is an identity about environments. `Frame` is
   entirely the cost of `fvar`s and of the closing operation between
   the checker's opened bodies and the relation's de Bruijn reading.
   (Fragment lane, stages 1–3.)

7. **The ι comparisons are load-bearing exactly in the Prop regime.**
   `Red.iota` (`Rules/Rel.lean:206-231`) compares the constructor's
   levels with the recursor's (`Level.isEquivList`), its parameters
   (`DefEqList`) and its residual's index expressions with the
   recursor's index arguments. Where the family is a *type* they are
   redundant: the certificate puts the major — a tagged tuple of the
   fields — in the family at the recursor's parameters and indices,
   and the fixpoint's inversion reads everything off it. Where the
   family is a *proposition* the major denotes the point and the
   certificates say only that the fibre is inhabited: with
   `P : Nat → Prop`, one constructor `mk : ∀ n, P n` and a large
   eliminator (the subsingleton criterion admits it — `n` is an
   index), a rule without the comparisons would let
   `P.rec motive minor 7 (mk 5)` reduce to `minor 5`, while the
   recursor's set, a function of its arguments alone, has one value at
   index `7`. The fragment's `Red.iota` carries all three and its ι
   law (`RecRuleLaw`) takes their semantic forms as premises; in the
   proof (`Fragment/InstallIota.lean`) the levels make the block's
   valuation the same through both instantiations, the parameters
   make the constructor's fit a fit at the recursor's parameters, and
   the indices make the recursor's index values the constructor's
   index expressions read under the fields. Lean's kernel gets the
   same facts by type-checking the major's type against the
   recursor's, which a semantic proof cannot read off a `DefEq`
   verdict between two propositions — worth one sentence in
   con-leche's ι docstring. (Fragment lane, stages 1–3; fragment lane,
   part 2 — ι; fragment lane, stages 3–4.)

8. **Retracted: the three ι comparisons follow from the telescope
   certificates and could be dropped from the rule.** The fragment's
   first `Red.iota` carried the two telescope certificates only, on
   that reasoning. Refuted by the Prop-regime counterexample of item 7:
   the comparisons are redundant where the family is a type and
   indispensable where it is a proposition with a large eliminator.
   (Fragment lane, part 2 — ι.)

9. **`trans` cannot be refuted in the fragment; argue structurally.**
   The task #309 counterexample lives on `DefEq.fvar` ignoring an
   annotation that `DefEq.proofFast` reads; with contexts instead of
   annotated `fvar`s the fragment has neither rule, and no fragment
   counterexample was found. The paper's argument against `trans` is
   therefore the structural one — the middle term's invariant has no
   supplier; `DefEq.redL_sound` is the sound chaining precisely
   because `RedSem` concludes the reduct's invariant — with the real
   checker's unsoundness as the reason the question is not academic.
   (Fragment lane, stages 1–3.)

10. **The λ rule's domain-sort premise is unused by soundness.**
    `Infer.lam_sound`'s `_hu` (`Fragment/Sound.lean`) is the checker's
    "the domain is a type" check; the model does not need it, because
    a λ's domain only ever enters as the set its denotation is a graph
    over. The real proof already drops the premise at the io grade,
    so the full grade could too if Lean conformance were checked
    elsewhere. The ∀ rule does read its sort premise: the product's
    level depends on it. (Fragment lane, stages 1–3; §2b lane.)

11. **One `Sat` clause instead of a context predicate.** Defining
    `Sat` recursively on the context (`Fragment/WellDenoted.lean`)
    makes `Sat_cons` hold by `Iff.rfl`, so every binder case opens the
    context definitionally. The real proof's `CtxOk`/`Sat`/
    `CtxOk.of_subset` machinery exists to track annotations on
    `fvar`s, not contexts. (Fragment lane, stages 1–3.)

12. **One invariant predicate, with the annotation clause inside.**
    The fragment's `WellDenoted` folds the annotation's truthfulness
    into the two binder clauses, and every case of the soundness proof
    reads it from there. The real proof carries `AnnotValid` as a
    separate conjunct of `WellDenotedV`, which the per-rule lemmas
    then split and rejoin; nothing in §2 needed the separation.
    (§2b lane.)

13. **The env-free soundness needs a `SetLib`-sized interface.** It
    uses no set-forming operation beyond graphs, function spaces,
    truth values and the universe chain — no pairing, union or power
    set (`Fragment/Lib.lean` is the whole list). `Model/Rules/*` could
    be stated over such an interface derived from `SetTheory`, which
    would document what the soundness of the rules needs and what
    only the constructions need. (§2b lane.)

14. **The ι law on values.** Stated on values (`appList`, `TeleFitV`,
    `piBodyV`, `SpineOk` in `Fragment/EnvModel.lean`) the law mentions
    the model only at the stored terms and survives an extension of
    the environment by congruence, where con-leche's term-indexed
    `RecRuleLaw` needs its carried readings and the `EnvExtend`
    transport. The one price is a syntactic premise on the rule — the
    stored types have the spine's length of binders (`Expr.hasPis`),
    because a substitution can create a telescope (`(x : Type) → x` at
    a function type) that a walk on values never sees. The residual's
    index comparison, con-leche's "index pin", is one line on values
    (`piBodyV`'s body under the fields' values), and the term-to-value
    bridge (`piResidual_of_piBodyV`) is the whole of what
    `Fragment/Tele.lean` has to say about substitution. Con-leche's
    `RecRuleLaw` docstring records that a value-level draft "died on
    the transport conjunct" because `WellDenotedV` is
    `AnnotTerm`-indexed; the fragment's law carries the same conjunct
    on values (`SpineOk`, turned back into the reduct's invariant by
    `WellDenoted_mkAppN_of_spineOk`) as a two-line predicate. The
    obstacle was the reading layer, not the value form: with one
    denotation on the checker's terms (item 1) the value-level law
    would go through in the real proof too. (Fragment lane, part 2 —
    ι; §3 lane.)

15. **Least fixed points cost nothing; the fibre bound is the one
    set-theoretic input.** The ambient logic's `Prop` is
    impredicative, so the least fixed point of a monotone operator on
    predicates is a definition (`Lfp` in `Fragment/IndLib.lean`, the
    intersection of the closed predicates) with its fixed-point
    equation and induction principle as ten-line theorems, and
    separation turns a fibre into a set. Con-leche builds
    `lfpSet`/`lfpFamSet` inside the set theory (a separation over a
    classically chosen closed member) and then needs a closed member
    of the universe to exist — the ω-iterate for finitary blocks
    (`SetModel/Iter.lean`), the container theorem for reflexive ones
    (`SetModel/Container.lean`, 600 lines). With the predicate form
    the closed member is asked for once: the fibre must be a *member*
    of `univ u`, and a separation of `univ u` lands in `univ (u+1)`,
    so the fragment states `inductive_closure` in its class (for any
    list of constructor telescopes some family of members is closed
    under every bounded instance) and separates the family from that
    member. `container_closed_exists` is exactly that law proved from
    Grothendieck universes, the ω-iterate its finitary special case:
    `Container.lean` is the whole of what the inductive model takes
    from the strength of the universes and could be presented as one
    theorem with the closure law as its statement, consumed nowhere
    else. (Fragment lane, part 2 — least fixed points; §3 lane.)

16. **One recursion theorem for both regimes.** The real proof builds
    the recursor of a type-valued block as a fixed point of its
    unfolding chosen by `Classical.choice`
    (`Semantics/Tower/FixRec.lean`) and, separately, `recGraph`
    (`SetModel/RecGraph.lean`) for the squash regime — a Prop family
    with a large eliminator. The fragment (`Fragment/IndSem.lean`) has
    one construction: the recursor's graph as a least fixed point,
    single-valued by induction over the graph (tags and tuples are
    injective), total by induction over the family, and `graph` of
    the resulting function is the recursor's set — no `recGraph`
    family space, no choice of a fixed point of an unfolding. The
    squash regime is then not a second construction but a *choice of
    witness* at the point (`pick`/`wit`), whose irrelevance IS the
    subsingleton criterion: `Uniq.lean` proves "two members at one
    index are the same tagged tuple" from the syntactic criterion,
    and exactly one place needs it, the recursion equation at a
    constructor value (`recSem_eq`); the recursor's typing
    (`recSem_mem`) and the motive's inhabitation at a proposition
    (`motive_inhabited`) need no uniqueness. This also makes the
    criterion's semantic meaning explicit, which con-leche's
    `checkStructFieldSortsI` docstring only attributes to official.
    (Fragment lane, stages 3–4; §3 lane.)

17. **Readers instead of `EnvExtend` transport.** The block's
    generated syntax is read in the model as it grows — the former
    added (`M₁`), then the constructors (`M₂`), then the recursor
    (`M₃`) — and every reading is the same reading: a *reader*
    (`Fragment/Read.lean`) is any assignment agreeing with the old
    model on the stored constants and mapping the former to the
    family, and the block's own expressions, closed over the stored
    constants at the block's level parameters, denote the same under
    every reader (`interp_spec`). The recursor's context is read under
    two readers at once — the block's own valuation and the recursor's
    instantiated one — and the two readings agree entry by entry
    (`CtxAgree`, `agree_recCtx`); that congruence replaces con-leche's
    `EnvExtend` transport of the carried readings. (Fragment lane,
    stages 3–4.)

18. **The consistency corollary needs no pin and no construction.**
    The fragment reads "no closed term inhabits an empty inductive
    type" off law 1 for the block's *recursor* in an arbitrary model of
    an accepted environment (`no_empty_inductive_inhabitant`,
    `Fragment/Consistency.lean`): at the all-zero valuation the
    recursor's type is the elimination principle
    `∀ (C : I → Prop) (t : I), C t`, a true proposition in the model,
    and the motive constantly `False` does the rest — at any sort, so
    `Empty` and `False` are one corollary, and nothing about the
    model's construction has to be carried across later installations,
    only that some model exists (`accepted_model`). The real proof
    states its capstones only for the pinned `False` and `Empty`
    (`Capstone.lean`'s `no_constant_of_emptyPin`), because the pin
    fixes the leaf; the pins are there so the *statement* can name
    `False` and `Eq`, not because the proof needs them. The same
    one-line argument from `EnvModelM.mem_type` at the stream's own
    recursor would give the corollary for every zero-constructor block
    the stream declares. (§3 lane; fragment lane, stages 3–4.)

19. **Structure η and unit-likeness from one model-side lemma, not
    from stream artefacts.** Against the library laws the three rules
    the fragment drops are small: K is `eq_pt_of_mem_truthVal` twice;
    structure η is the fixed-point equation read left to right
    (`Lfp.unfold`: a member IS a tagged tuple) plus
    `tuple_inj`/`tag_inj`; unit-likeness is η at zero fields, or the
    truth value at a `Prop` instance. The real proof has the same
    argument on the native route (`FixEntryLaw.lean`'s clause (C),
    `fixEntryEtaCore`; `FixZeroField.lean`'s `fixFibreUnitLaw`,
    `fixFibreEtaLaw0`) but obtains the same two laws on the modeled
    route from stream artefacts — a `T._model.eta` and a
    `T._model.unitlike` theorem the checker checks and the model tier
    *fires* (`IndEtaLaw.lean`, `IndUnitLaw.lean`, `IndProjEta.lean`:
    three files of `EtaLaw`/`UnitLaw` producers, each built around
    `Eq`-slot rigidity and a valuation bridge through
    `BlockAcvalInstalled`). Those artefacts carry no information the
    model does not already have: the modeled block's family is a
    tagged union over the generated tag type, and a member of it is a
    tagged tuple by the same inversion. One model-side lemma per
    representation ("every member of the carrier is the constructor
    at its own projections", which is `towerSet_elim` for the tower
    already) would replace the two generated theorems, their
    pinned-shape checks (`checkEtaThm`, `checkUnitThm`) and the three
    firing files, and would make the η capability a property of the
    block's shape (as `nativeCapsAt` already computes it) instead of
    what the stream happened to include. Likewise the two `PUnit`
    rules (`unitLike` on the pinned `PUnit`, `structUnit` on a stored
    unit-like family) are one rule in the model: "the family has at
    most one member". (§4 lane.)

20. **Two block conditions that carry semantic weight.** The
    fragment's `Ok` (`Fragment/Decl.lean`) asks two things of a block
    that con-leche checks too but the first fragment left implicit:
    no field reads an earlier recursive field (`fieldNoRecDep`,
    con-leche's `structUsedLater`), which is what lets the domains be
    read at a frame whose recursive slots hold an arbitrary value
    (`junkRec`); and the block's level parameters are distinct with
    the elimination parameter fresh, which is what makes the two
    instantiations of item 7 comparable. Both deserve their semantic
    reason in the checker's docstrings. (Fragment lane, stages 3–4.)

21. **"Every fibre is {pt}" versus "every fibre is inhabited".** The
    real proof's `piR` (`ConLeche/SetModel/Ops.lean`) reads the
    propositional `∀` as the truth value of "every fibre is
    inhabited"; the fragment now reads it as "every fibre equals
    {pt}" (`Fragment/Lib.lean`). Under the semantic invariant the two
    agree, and in the env-free fragment the change only moves the one
    use of "the fibres are truth values": elimination (`app_mem_piR`,
    the app case of `Fragment/Sound.lean`) loses that premise,
    introduction (`lamR_mem`, the λ case) gains it. The cost shows in
    the inductive section (`Fragment/IndSem.lean`,
    `Fragment/InstallRead1.lean`, `Fragment/InstallInd.lean`): a
    Prop-valued motive's fibres must be truth values at every
    member's indices, so the recursor's typing needs the
    constructors' index expressions to fit (`idx_fits_of_mem_Fam`) —
    a well-formedness fact the "inhabited" reading never consulted at
    that level. Net +62 lines over the fragment; whichever way the
    real proof reads it, that is the trade. (Regime lane.)

22. **The semantic invariant as an inductive judgement.** The real
    proof's `WellDenoted` (`ConLeche/Semantics/WellDenoted.lean`) is a
    structurally recursive `def` on `AnnotTerm`, the application clause
    and each binder clause carrying its regime as a Boolean (`piR p`,
    `pw.holds φ = true → …`). In the fragment it is now an inductive
    predicate with nine rules: `bvar`, `sort`, `const`, and the
    application, the λ and the ∀ each split into a function-regime and
    a propositional-regime rule (`appFun`/`appProp`,
    `lamFun`/`lamProp`, `piFun`/`piProp`) — the annotation's readout is
    a premise of the binder rules, and no `p → …` premise remains.
    What the refactor cost in the fragment: the merged clauses survive
    as inversion lemmas under the old names (`WellDenoted_app`,
    `_lam`, `_pi`, some 45 lines), and every other file reads the
    judgement through them — of the 16 files that use `WellDenoted`,
    only `Sound.lean` changed, at five leaf sites that closed a
    variable's or a sort's judgement with `trivial` and now name the
    rule; `Hygiene.lean`, `Ctx.lean`, `Tele.lean`, `Read.lean` and the
    install files compiled unchanged. The substitution transport
    (`WellDenoted_inst`) was re-proved by induction on the derivation,
    one half on the derivation for `e[a]` and one on the derivation for
    `e`: about 200 lines where the term induction through the
    inversion lemmas was 45, because the derivation for `e[a]` has to
    recover the shape of `e` (or meet the substituted variable) in
    every rule and an `↔` needs both inductions. `WellDenoted_liftN`,
    `_instL` and the β lemmas stayed as they were, via inversion. For
    the real proof: splitting the regimes is a presentation choice with
    no cost downstream as long as the inversion lemmas exist, and the
    transport lemmas are cheaper as term inductions. (Invariant lane.)
