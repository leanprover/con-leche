# Notes from the whitepaper lanes

What this is: places where, thinking at the whitepaper's altitude —
one denotation on annotated terms, a semantic invariant instead of a
typing judgement, a set theory given as a class — the con-leche proof
could be simpler or more elegant. One numbered list, one observation
per item, each naming the fragment files and the real-proof files it
compares and the lane that made it (task #324; 2026-09-25 unless the
item says otherwise — the items marked 2026-10-01 were written after
the uniform installer landed upstream).
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

7. **The ι comparisons: the index comparison is load-bearing, the
   level comparison is assumed, the parameter comparison is dead.**
   `Red.iota` (`Rules/Rel.lean`) compares the constructor's levels
   with the recursor's (`Level.isEquivList`), its parameters
   (`DefEqList`, only when `RecRule.compareParams`) and its residual's
   index expressions with the recursor's index arguments. Where the
   family is a *type* all three are redundant: the certificate puts
   the major — a tagged tuple of the fields — in the family at the
   recursor's parameters and indices, and the fixed point's inversion
   reads everything off it. Where the family is a *proposition* with
   a large eliminator the major denotes the point and the certificates
   say only that the fibre is inhabited, and the INDEX comparison is
   indispensable: with `P : Nat → Prop` and one constructor
   `mk : ∀ n, P n` (the subsingleton criterion admits it — `n` is an
   index), a rule without it would let `P.rec motive minor 7 (mk 5)`
   reduce to `minor 5`, while the recursor's set, a function of its
   arguments alone, has one value at index `7`. The LEVEL comparison
   is what the fragment's law for a rule on the block's own
   constructors assumes (`RecRuleLaw`, `Fragment/EnvModel.lean`: the
   constructor's levels evaluate as the recursor's last ones) and what
   `Fragment/InstallIota.lean` uses first (`block_valuation_eq`): it
   makes the block's valuation the same through both instantiations,
   so a field that is a proposition on the recursor's side is one on
   the constructor's. The PARAMETER comparison cannot matter: the
   reduct takes its parameters from the recursor's spine and only the
   fields from the major, and in the `Prop` regime every field is a
   proof — the point at any parameters — or an index, fixed by the
   index comparison. The real checker fires the rules it generates
   without it (`paramsBlind`, `Kernel/Inductives/SumInstall.lean`;
   `RecRule.compareParams`, `Kernel/Env.lean`) and
   `blockRecRuleLaw_gen` (`Model/Inductives/BlockRecLaw.lean`) notes
   it unused; the fragment's `RecRuleLaw` still carries the premise
   and `InstallIota.lean` uses it to move the constructor's fit to
   the recursor's parameters — dropping it would align the fragment
   with the checker and shorten the law by one conjunct. The official
   kernel compares nothing at an ι step (`inductive_reduce_rec` fires
   by constructor name and `nfields`; typing justifies it), which a
   semantic proof cannot do: a `DefEq` verdict between two
   propositions is an equality of truth values. (Fragment lane,
   stages 1–3; fragment lane, part 2 — ι; §4 lane, 2026-10-01.)

8. **Retracted: the three ι comparisons follow from the telescope
   certificates and could be dropped from the rule.** The fragment's
   first `Red.iota` carried the two telescope certificates only, on
   that reasoning. Refuted by the Prop-regime counterexample of item 7:
   the comparisons are redundant where the family is a type, and
   where it is a proposition with a large eliminator the index
   comparison is indispensable and the level comparison is what the
   law assumes — only the parameter comparison could go.
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
    *After the uniform installer* (2026-10-01, §4 lane): the container
    theorem is gone, and the closed family of a block's operator comes
    from `closed_of_acc` (`SetModel/Access.lean`) — an operator whose
    every output element depends on a bounded set of input elements,
    for one bound in the universe, has a closed tuple, by iteration
    along well-founded trees with the union kept small by coding a
    tree as its paths. That is the fragment's `inductive_closure`
    proved once, as this item asked. But the positivity run is still
    read twice: `blockCtorPos_of_run`
    (`Model/Inductives/BlockPosRunCont.lean`) for monotonicity and
    `blockAcc_of_run` (`BlockAccRunCont.lean`) for accessibility,
    while `AccTuple.monoTuple` (`Access.lean`) says an accessible
    operator is monotone. One reading of the run would give
    `LfpClause.functor`'s three conjuncts, with the `Prop`-valued case
    (`closedTuple_zero`, no bound needed) as its degenerate case.

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
    (Fragment lane, stages 3–4; §3 lane.) *After the uniform
    installer* (2026-10-01): the real proof has the one construction
    too — the graph as the least relation closed under the rules
    (`SetModel/GraphRec.lean`), `FixRec.lean` and `RecGraph.lean` are
    gone — and takes the sort-dependent fact as one premise, "two
    decodings are equal or the motive's value is a subsingleton",
    discharged three ways (`Model/Inductives/ClassGenUniq.lean`); the
    witness device is the fragment's way of discharging the third.

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
    (`Model/Capstone.lean`'s `no_constant_of_emptyPin`), because the pin
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
    most one member". (§4 lane.) *After the uniform installer*
    (2026-10-01): the stream artefacts and the three firing files are
    gone; whether a block has η or is unit-like is decided at its
    install from its shape (`blockCapsAt`,
    `Kernel/Inductives/BlockInstall.lean`) and both laws are
    established from the fixed point (`fixEntryEtaCore`,
    `Model/Inductives/FixKit.lean`), as this item proposed.

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

23. **The recursor record's pre-pass is only needed for nesting.** The
    generated-recursor stage reads the stream's recursor types in an
    unverified pre-pass (`Kernel/Inductives/ClassRead.lean`) for the
    classes a family eliminates and the layout of its motives and minor
    premises, then checks the classes as majors and generates the
    family. For a block with one type former and no container field
    the classes and the layout are determined by the constructors
    alone — the fragment generates the recursor from the specification
    and reads nothing (`Fragment/Decl.lean`'s generators). The real
    checker could generate the layout from the block in that case and
    read the stream's record for its type only, leaving the pre-pass,
    the class checks and node agreement to the nested case where the
    stream genuinely supplies information (which containers get an
    auxiliary recursor). (§4 lane.)

24. **The elimination criterion's two halves, and the `Sort u`
    superset's reason.** The real checker asks the per-field
    subsingleton criterion only of a family whose sort is provably zero
    (`checkStructFieldSortsI`, `Kernel/Inductives/SumInstall.lean`) and
    the count guard when the sort is not never-zero
    (`blockLargeElimAllowed`, `Kernel/Inductives/BlockRec.lean`); the
    fragment asks the criterion whenever the sort may be zero
    (`Fragment/Decl.lean`). The checker's superset — a `Sort u` family
    with one constructor eliminating into any sort — is sound for a
    reason that neither docstring states: the universe bound on a
    non-`Prop` family holds at every valuation, so at a valuation
    sending `u` to zero every field is a proposition and the criterion
    holds vacuously. The model side sees this as `genUniq`'s width-zero
    case (`Model/Inductives/ClassGenUniq.lean`) discharged by the fit's
    values being the point. One sentence in `checkStructFieldSortsI`'s
    docstring would record it; a fragment that tested "provably zero"
    instead of "may be zero" would need exactly that lemma. (§4 lane.)

25. **A nested rule's stored instantiation is never load-bearing.**
    The real checker certifies an auxiliary recursor's rule against
    the constructor's expected levels and parameters (`.nested`
    certification, `tests/e2e/src/nested_rec.lean`); the fragment's
    `Red.iotaNested` (`Fragment/Rules.lean`) compares them too, but
    its law `RecRuleLawN` (`Fragment/EnvModel.lean`) does not consume
    the comparisons: large elimination is refused for a nested block
    whose sort may be `Prop` (`blockLargeElimAllowed`), so the
    recursion equation is only ever needed above a proposition, where
    the major is itself the tagged tuple and its membership in the
    class pins the fields (`ClassLaws.inv`, `Fragment/NestRec.lean`).
    Item 7's observation on the parameter comparison holds for the
    nested one without even the `Prop` exception, and the level
    comparison is not assumed there either. (Nested lane,
    2026-10-01.)

26. **The container's constructors join the block's closure; no new
    law.** The real proof's "existence of the fixed point by
    accessibility, not by a container theorem" is, at this altitude,
    the one closure law of `IndLib` applied ONCE to the block's
    constructors and the container's at the instantiation, over a
    joint index — the family's fibres and the class
    (`IndSpec.ctorsX`, `JIdx`, `Fragment/IndSem.lean`); the block's
    constructors are tagged after the container's (`tagOf`) so that
    the closure's tags are the model's. The bound for the class is
    then closed under the container's constructors with the member
    at the family's bound, which is all `contInBound_of`
    (`Fragment/NestSem.lean`) needs. Whether the real proof's
    accessibility route could be replaced by listing the container's
    constructor telescopes in the existing container theorem is worth
    a look. (Nested lane, 2026-10-01.)

27. **The guard is established before the constructors are read.**
    Monotonicity of the class in the member (`ContGood`,
    `Fragment/IndSem.lean`) is what a container field's clause is read
    under; it is proved from the class having a sort at the block's
    parameters — a check read in a model of the environment holding
    the former only, which needs nothing of the class
    (`InstallNest.lean`, `argsFit_of`: the former's set is a graph
    tower, so `appList_of_wd` puts the class's arguments in the
    container's parameters, and positivity lets the member be any set
    of the universe). The reader structure had to be split for this
    (`Reader` / `ReaderG`, `Fragment/Read.lean`). The real proof's
    `EnvModelM` carries the installed blocks' data (`lfpBlocks`); the
    fragment's `BlockModel` (`Fragment/BlockModel.lean`) carries one
    law per plain block — scope, the former's and constructors' sets
    as the fixed point's graphs, the domains bounded at fitting
    parameters — and that is exactly what a later nesting consumes
    (`NestFacts`). (Nested lane, 2026-10-01.)

28. **What the fragment's positivity leaves out, and why.** Beyond
    the rulings (depth one, no indices, no reflexive container field)
    the fragment asks that the class's arguments and the member's
    index expressions be closed under the block's parameters, and that
    no field of the container after a member field read it
    (`NestInfo.Positive`, `Fragment/Spec.lean`). Both are prices of
    the closure device of item 26. The container's telescope joins the
    closure with the member field as a recursive position, whose value
    is junked (`toTeleXK`), so nothing may read it. And the class's
    arguments must fit the container's parameters at EVERY member set
    of the universe (`NestFacts.argsFit`), which a field-dependent
    argument could not do without a fitting instance at the final
    family. The real checker's `nestPos` admits both
    (`Kernel/Inductives/Positivity.lean`). (Nested lane, 2026-10-01.)

29. **One generator for the block's and the class's minors.** The
    container's constructors translated into the block's own field
    kinds — the member field a recursive field at the member's index
    expressions, the container's recursive fields container fields,
    its ordinary fields with the container's parameters substituted
    (`IndSpec.classCtor`, `Fragment/Decl.lean`) — are in the block's
    scope (`classCtor_fieldScoped`, `Fragment/NestRead.lean`), so the
    block's readers read the class's minor premises verbatim; only the
    conclusion's head (the container's constructor at the class's
    arguments) and its motive differ. The real proof's `ClassGen`
    (`Kernel/Inductives/GenRec.lean`) reads the container's
    constructors separately (`classCtorOf`, node agreement); a
    translation to the block's field kinds would let one generator
    and one reading serve both. (Nested lane, 2026-10-01.)


30. **Two of a definition's three scope conditions are not checks.**
    A definition's type and value are typed in the empty context, so
    they are closed and mention only stored constants by the typing
    derivations themselves (`Infer.closedAt`, `Infer.consts`,
    `Fragment/ScopeOfInfer.lean`, structural inductions over `Infer`
    alone); only "uses the declared level parameters" is a condition
    beyond typing, and the fragment's `DefOk` (`Fragment/Decl.lean`)
    now states that one alone, the environment section recovering the
    full scope (`DefOk.type_scoped`, `DefOk.value_scoped`). The real
    checker runs `looseBVarsBounded` and `constsResolve` as separate
    checks on a definition (`Kernel/CheckerBase.lean`); the model
    proof could take them from the derivations the same way. (Scope
    lane, 2026-10-02.)


31. **A recursive field is a reflexive field with an empty telescope.**
    The fragment's `Field` had both kinds (`recursive es` and
    `reflexive tele es`), as the real checker's `RecFieldKind` has
    (`Kernel/Inductives/FieldTele.lean`); but every generator
    (`fieldDom`, `ihTy`, `ihVal`, `ihValN`, `Fragment/Decl.lean`) and
    every semantic clause (`fieldSet`, `IhOk`, `ihSem`, `IhTyped`,
    `Fragment/IndSem.lean`; their nested twins in `NestRec.lean`)
    produced, at `tele = []`, exactly the recursive clause's term or
    set — `mkPis pw [] b = b`, `piCtx … [] F = F ρ`, `lamCtx … [] g =
    g ρ` are all `rfl`. Merging the kinds (`reflexive [] es` for the
    old `recursive es`) removed 88 `recursive` match arms over 18
    files — about twenty definitional clauses, the rest duplicated
    proof cases, each a special case of the reflexive one — for a net
    −303 lines, and one law of the class (`ClassLaws.noRefl`, "no
    translated constructor has a reflexive field") became a two-line
    lemma (`classField_reflexive`, `Fragment/NestRec.lean`: the only
    reflexive field a translation produces is the member's, with the
    empty telescope). The positivity clause for a container's own
    recursive field is now `tele = [] ∧ es = []`
    (`NestInfo.Positive`, `Fragment/Spec.lean`). The real checker
    could do the same: its `recursive` kind is `reflexive` with an
    empty telescope, and its generators and the model's field
    readings would lose their duplicated case. (Field-merge lane,
    2026-10-02.)
