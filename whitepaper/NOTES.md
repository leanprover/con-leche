# Notes from the whitepaper lanes

What this is: places where, thinking at the whitepaper's altitude —
one denotation on annotated terms, a semantic invariant instead of a
typing judgement, a set theory given as a class — the con-leche proof
could be simpler or more elegant. One numbered list, one observation
per item, each naming the fragment files and the real-proof files it
compares and the lane that made it (task #324; 2026-09-25 unless the
item says otherwise — the items marked 2026-10-01 were written after
the uniform block check landed upstream, those marked 2026-10-03
after the inductive model was rebuilt on Grothendieck universes and
accessibility). Items made obsolete by those changes are removed or
marked *superseded* / *done upstream*; "member" is set membership
throughout, the type being defined inside a container is "the nested
occurrence".
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

15. **The least fixed point inside the set theory, and one reading
    of the positivity run.** *Superseded* (2026-10-03): this item once
    proposed the fragment's predicate-level least fixed point with an
    `inductive_closure` law in the class as the simpler presentation; the
    ruling that the fragment follows con-leche's proof replaced it. The
    fragment now has con-leche's construction — Grothendieck universes
    (`Fragment/Univ.lean`), `closed_of_acc` proved along well-founded
    trees (`Fragment/Access.lean`), the least fixed point as a separation
    inside the set theory (`lfpFamSet`, `Fragment/LfpSet.lean`) — and the
    law is gone. What remains of the item is one suggestion for the real
    proof: the positivity run is read twice, by `blockCtorPos_of_run`
    (`Model/Inductives/BlockPosRunCont.lean`) for monotonicity and by
    `blockAcc_of_run` (`BlockAccRunCont.lean`) for accessibility, while
    `AccTuple.monoTuple` (`SetModel/Access.lean`) says an accessible
    operator is monotone. One reading of the run would give
    `LfpClause.functor`'s three conjuncts, with the proposition-valued
    case (`closedTuple_zero`, no bound needed) as its degenerate case.
    (Fragment lane, part 2; §3 lane; §4 lane, 2026-10-01; revised
    2026-10-03.)

16. **One recursion theorem for both regimes, keyed on decodings.**
    The recursor's set is the graph of one function, read off the least
    relation closed under the rules: single-valued by induction over the
    graph, total by induction over the family (`RecGraph`, `RecGraph_fun`,
    `recSem_eq`, `Fragment/IndRec.lean`; con-leche's `GraphRecKit`,
    `SetModel/GraphRec.lean`). The graph is keyed on the major itself —
    `pt` at a proposition — with the major's *decodings* (a constructor
    and fields fitting it that reach the indices) as the rule's data, and
    the sort-dependent fact is one premise: two decodings of one major
    agree (`decode_unique`: tags and tuples are injective in the
    type-valued regime, the subsingleton criterion in the
    proposition-valued one, `Fragment/Uniq.lean`) — con-leche's `huniq`,
    "two decodings are equal or the motive's value is a subsingleton",
    discharged three ways (`Model/Inductives/ClassGenUniq.lean`). An
    earlier fragment read a propositional major through a chosen
    witness (`pick`/`wit`) and needed uniqueness of witnesses; that
    detour is gone, and so are the real proof's former two constructions
    (`FixRec.lean`, `RecGraph.lean`). What the fragment adds is the
    criterion's semantic meaning, stated (`Subsingleton`, `Uniq.lean`),
    which con-leche's `checkStructFieldSortsI` docstring only attributes
    to the official kernel. (Fragment lane, stages 3–4; §3 lane; lane 2,
    2026-10-03.)

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

19. **Structure η and unit-likeness from the fixed point — done
    upstream.** Against the axioms the three rules the fragment drops
    are small: K is `eq_pt_of_mem_truthVal` twice; structure η is the
    fixed-point equation read left to right (an element of the family IS
    a tagged tuple) plus `tuple_inj`/`tag_inj`; unit-likeness is η at
    zero fields, or the truth value at a `Prop` instance. This item once
    proposed replacing the stream artefacts (`T._model.eta`,
    `T._model.unitlike`) and their three firing files by that argument;
    the real checker now decides at the install, from the block's shape,
    whether a type has η or is unit-like (`blockCapsAt`,
    `Kernel/Inductives/BlockInstall.lean`), and both laws are
    established from the fixed point (`fixEntryEtaCore`,
    `Model/Inductives/FixKit.lean`). Still open: the two `PUnit` rules
    (`unitLike` on the pinned `PUnit`, `structUnit` on a stored unit-like
    family) are one rule in the model, "the family has at most one
    element". (§4 lane; revised 2026-10-01.)

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
    Prop-valued motive's fibres must be truth values at the indices
    of every element, so the recursor's typing needs the
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

26. **What the fragment's positivity asks beyond the rulings, and
    why.** Beyond depth one, no indices and no reflexive container field,
    the fragment asks that the class's arguments and the nested
    occurrence's index expressions be closed under the block's
    parameters, and that no field of the container after a parameter
    field read its value (`NestInfo.Positive`, `Fragment/Spec.lean`). The
    second is what the replacement lemma (item 34) needs: the class is
    read at every approximant, so a parameter field's value must be free
    to move. The first is what lets the class's arguments fit the
    container's parameters at EVERY parameter set of the universe
    (`NestFacts.argsFit`, proved in `InstallNest.lean` from the class
    having a sort in the environment holding the type former only), which
    a field-dependent argument could not do. The real checker's `nestPos`
    admits both (`Kernel/Inductives/Positivity.lean`). (Nested lane,
    2026-10-01; revised 2026-10-03.)

27. **One generator for the block's and the class's minors.** The
    container's constructors translated into the block's own field
    kinds — the parameter field a recursive field at the nested
    occurrence's index expressions, the container's recursive fields
    container fields,
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

28. **Two of a definition's three scope conditions are not checks.**
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

29. **A recursive field is a reflexive field with an empty telescope.**
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
    reflexive field a translation produces is the parameter field,
    with the empty telescope). The positivity clause for a container's own
    recursive field is now `tele = [] ∧ es = []`
    (`NestInfo.Positive`, `Fragment/Spec.lean`). The real checker
    could do the same: its `recursive` kind is `reflexive` with an
    empty telescope, and its generators and the model's field
    readings would lose their duplicated case. (Field-merge lane,
    2026-10-02.)

30. **The fixed point and accessibility need no graphs.** The real
    proof's family layer (`SetTheory/Derive/LfpTuple.lean`,
    `SetModel/Access.lean`) works on tuples of *graphs*: a family is
    `graph (i ↦ …) (Is m)`, membership is `x ∈ app (X m) i`, and
    `famSpace`, `graph_mem_famSpace`, `famSpace_app`, `app_graph`
    and `famSpace_ext` thread through every statement and proof
    (`lfpTuple_eq` is `famSpace_ext` over `app_lfpTuple_eq`;
    `stage_eq_of_code` needs `image_congr` under `app`). The
    fragment states the same definitions and proves the same
    theorems — `lfpFamSet`, `closed_of_acc`, line by line the same
    proof — on Lean-level families `ι → V` with "every fibre a member
    of `univ n`" (`Fragment/LfpSet.lean`, `Fragment/Access.lean`),
    and the graph laws are simply absent: `lfpFamSet_eq` is
    `Sub.antisymm` of the two inclusions, the limit family is a
    `famUnion` per fibre. The real proof denotes the carrier as a
    set, so it needs a graph *once*, at the end — `graph (lfpFamSet …)
    I` — not in the fixed-point and accessibility layer; the
    `AccRead` closure lemmas, `lfpP_acc` and the Bekić lemma would
    lose their `app`/`famSpace` premises the same way. (Accessibility
    lane, 2026-10-03.)

31. **The universal field bound needs no holes-in-context check.**
    `closed_of_acc` needs the block's operator to map families of
    the universe to families of the universe, i.e. the constructors'
    fields bounded along instances of EVERY family of the universe,
    not just the block's own (`DomsBounded`, `Fragment/IndSem.lean`;
    con-leche's `LfpClause.fieldsOk`).  The real proof obtains that
    from a proof-only check — the constructor type-checked with the
    holes in context (`nestCtors`, OVERVIEW §5, "Checks made for the
    proof alone") — recorded as `FieldsOkB` at every hole frame.  The
    fragment obtains it from the ORDINARY typing of the constructor
    in the environment holding the former (`Ok`, `Decl.lean`): the
    former's type `∀ params indices, Sort u` is inhabited by the
    graph of any family of members of `univ u`, so the environment
    has a model for each such family (`mIndF`, `readerF`,
    `Fragment/InstallInd.lean`), and soundness read there gives the
    bound at that family (`domsBounded_of`).  The real proof could
    drop the holes-in-context check and `fieldsOk` the same way:
    `EnvModelM`'s constant clause holds of any assignment that sends
    each type former of the block to a family of its tuple space.  (Lane 2, 2026-10-03.)

32. **The accessibility bound is one set because no field reads a
    recursive one.**  The fragment's bound (`bound`, `IndSem.lean`) is,
    per constructor and per reflexive field, the tuples of the field's
    telescope at every prefix fitting the ONE-FIBRE family (every fibre
    `{pt}`), coded by the field's position; an instance of any family
    has its support inside it because the telescope reads the same at
    the instance's earlier values once the recursive values are
    replaced by the one-fibre family's canonical member — the point
    abstracted over the telescope (`toOne`, `ctxSet_toOne`), which is
    `NoRecDep` (con-leche's `structUsedLater` guard) and nothing else.
    The real proof carries the bound as a function of the frame and
    makes it uniform with `InvOn`/`TeleAcc`; the fragment suggests the
    uniform bound can be stated directly off the positivity guard.
    Also: at a proposition the operator's fibres are subsets of `{pt}`,
    so `MapsFam` is immediate there and no bound is consulted
    (`closedFam_zero`).  (Lane 2, 2026-10-03.)

33. **The container's clause is one more case of the operator, and
    two facts about the container are all it needs.**  The nested
    block's operator reads a container field as the class at the
    approximant's fibre at the nested occurrence (`fieldSet`'s
    container clause, `Fragment/IndSem.lean`, through `classSet`: the
    container's set in the model at the class's arguments with that
    fibre in the nested position).  Monotonicity and accessibility
    of the operator then ask of that clause exactly what they ask of a
    reflexive field's product: it grows with the fibre, and a value
    in it has a support in the fibre coded inside one set
    (`ContClause`: `mono`, `acc`; plus `mem_univ` for the operator to
    stay in the universe, and `inhab_one`, item 35).  The installation
    proves the four from the container's positivity and the leastness
    of its fixed point (`Fragment/NestSem.lean`, `contClause_of`) —
    the real proof's container case of `Model/Annot/BlockLfpMono.lean`
    (monotone through the container's lfp clause,
    `SetModel/HoleClose.lean`) and `Model/Inductives/ContAcc.lean`,
    with the container's frames and the walk of its constructors
    replaced by one lemma about its fields (item 34).  Nothing is asked
    of a plain block (`contOk_of_plain`).  (Lane 3, 2026-10-03.)

34. **One replacement lemma carries monotonicity, accessibility and
    the one-fibre counterpart.**  Positivity of the container in the
    nested position says a constructor reads the parameter set only
    through its parameter fields and its own family only through its
    recursive fields, and an ordinary field reads neither; so a
    fitting list stays fitting when the parameter-field values are
    replaced by members of another parameter set, the recursive values by members of
    another family's fibre, and the ordinary values kept
    (`FitsFields_psK_repl`, `Fragment/NestSem.lean`; the real proof's
    `spineFit_mono` along the instantiation's relation, `CtorPos`).
    From it: the family at a larger parameter set is closed under the
    operator at a smaller one, so by leastness the family grows with
    the parameter set (`Fam_psK_mono`); the operator is accessible
    jointly in the parameter set and its own family with one code per
    field position (`jointOp_acc`), so by the nested case of
    accessibility (`lfpP_acc`, `Fragment/Access.lean`, a port of
    `SetModel/Access.lean`'s `lfpP_acc` over Lean-level families with a
    sum type of indices) the family is accessible in the parameter set
    with the bound `accPaths` of the positions (`Fam_psK_acc`) — a set
    computed from the specification alone (`classBound`, item 35).
    (Lane 3, 2026-10-03.)

35. **The one-fibre reading of the fields needs the class inhabited at
    `{pt}`, and the class's bound is spec-computed.**  Lane 2's bound
    is one set because the telescopes are read at the one-fibre
    family with every recursive value replaced by the point
    abstracted over the telescope (item 32).  A container value has
    no such canonical stand-in: the class at `{pt}` may be empty while
    the class at a larger fibre is not (`K α := wrap (a : α)`), and the
    universe bound on the fields (`DomsBounded`) is only recorded at
    fitting prefixes.  So the container's clause includes
    `inhab_one`: the class at `{pt}` is inhabited whenever the class is
    inhabited at any parameter set of the universe — by induction over
    the container's family, every constructor instance has a
    counterpart at `{pt}` (`Fam_psK_inhab_one`, the replacement lemma
    once more) — and `toOne` replaces a container value by a chosen
    member of the class at `{pt}` (`contOne`).  The class's bound is
    `accPaths` of the numerals below the container's longest field
    list (`classBound`), so the block's bound stays a definition and
    `famOp_acc` keeps lane 2's shape; the real proof carries the
    container's bound as a function of the frame (`ContAccFrame.lean`,
    `frameAccOut_of`).  (Lane 3, 2026-10-03.)

36. **One reader for plain and nested blocks, and a model that
    remembers its blocks.**  The first nested lane read a container
    field's domain under a guard (`ReaderG.good`, a split of the reader
    structure); the rebuilt `Reader` (`Fragment/Read.lean`) has no plainness field and
    reads the domain by β through the container's set, a stored
    constant the reader agrees on (`classTy_fit`), as the fibre of the
    reader's family at the nested occurrence; `IdxFitAt`'s container
    clause is that the nested occurrence's index values fit the indices, read off
    the semantic invariant (`fieldDom_wd`).  Only the lemmas about the PLAIN
    recursor's hypotheses' context (`read_ihTy`, `fits_ihCtxAux`,
    `Reader₂.minorOk`, and `IndRec`'s totality and typing) take
    `S.nest = none` explicitly; `ctorSet_mem` takes the container's
    clause at fitting parameters, which is how a nested block's
    constructors get their type law without a "class in the bound"
    condition (`InstallNest.lean`, `type_ok_ctorN`).  The frozen
    copies of the first nested lane, with the old closure law, are
    gone.  The real proof's `EnvModelM` carries the installed blocks'
    data (`lfpBlocks`); the fragment's `BlockModel`
    (`Fragment/BlockModel.lean`) carries one law per plain block —
    scope, the type former's and constructors' sets as the fixed
    point's graphs, the fields' universe bound at fitting parameters —
    which is exactly what a later nesting consumes (`NestFacts`), and
    pushes agreement through the operator (`Agree.famOp_eq`,
    `Agree.Fam_eq`).  (Lane 3, 2026-10-03.)

37. **Monotonicity is a corollary of accessibility, in both regimes.**
    The fixed-point equation and induction need a monotone operator
    (`lfpFamSet_eq`, `lfpFamSet_induction`), and accessibility gives
    it on families in the universe: the support in `W` is in the
    larger `W'` (`AccFam.mono`, the real proof's
    `AccTuple.monoTuple`).  The block's operator is accessible in
    BOTH regimes — only the bound's membership of the universe needs
    a type — so the fragment derives `famOp_mono` from `famOp_acc`
    and has no separate monotonicity proof (`fieldSet_mono`,
    `piCtx_sub`, `piR_mono`, `piSet_mono` are gone; `FitsFields_mono`,
    which the recursor's induction uses, re-types through
    `FitsFields_retype`).  For a container the same holds once the
    nested case of accessibility is stated at a proposition too:
    `lfpP_acc` needs the bound in the universe only above one, and
    at a proposition the section's closed family is `{pt}`
    (`closedFam_zero`) — so `Fam_psK_acc` holds in both regimes, the
    container's clause drops its `mono` field (`ContClause.mono` is a
    theorem), and `Fam_psK_mono` is derived; the leastness proof of
    item 34 is gone.  The real proof proves monotonicity separately
    (`HoleMono.lean`, `BlockPosRunCont.lean`, the container case of
    `BlockLfpMono.lean` through `HoleClose.lean`'s `lfpTuple_le_on`)
    and states `lfpP_acc` above a proposition only; deriving
    `LfpClause.functor`'s monotone conjunct from `blockAcc_of_run`
    (extended to `w = 0`) could retire those modules.  (2026-10-03.)
