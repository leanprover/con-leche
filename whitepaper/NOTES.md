# Notes from the whitepaper lanes

What this is: places where, thinking at the whitepaper's altitude —
one denotation on the terms, a semantic invariant instead of a
typing judgement, a set theory given as a class — the con-leche proof
could be simpler or more elegant. One numbered list, one observation
per item, each naming the fragment files and the real-proof files it
compares and the lane that made it (task #324), with its date
(2026-09-25 unless the item says otherwise). Every item describes the
proof and the fragment as they are; items the real proof has taken up
are marked *done upstream*. "Member" is set membership throughout,
and the type being defined inside a container is "the nested
occurrence".
Typst and tooling traps are not here: they are the "Typst notes"
comment block at the top of `lib.typ`.

1. **One denotation instead of three.** The real proof reads a
   checker term into a `Term` (`denote`, partial),
   interprets that (`interp`), and states the main theorem over a
   third notion, the relation `Denotes` on checker terms, plus the
   theorem identifying the first two with the third
   (`Model/Denotes.lean`). The fragment has one denotation
   (`Fragment/Interp.lean`) that reads the terms at the level
   valuation directly, and nothing in §2's argument needs the
   numeral layer. If `interp` were defined on `Expr` under `φ` — as
   `Denotes` is, but as a function — the intermediate `Term` layer and
   `Denotes_of_denote` would go, and `WellDenoted` would be stated
   once, on the checker's terms. Item 11 says what else this unlocks.
   (§1/§5 writer lane; §3 lane.)

2. **Fold the list relations into the rules.** `CertsF` and
   `DefEqList` (`Rules/Rel.lean`) are relations only because a rule
   with a list premise is awkward in a mutual inductive. A
   `List.Forall₂`-shaped premise (or a nested occurrence, at the cost
   of a hand-written induction principle) folds both into the rules
   that use them, which is what the paper does
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

5. **`Frame` is an artefact of `fvar`s.** The three claims of
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

6. **The ι comparisons are needed in the certified case only.**
   `Red.iota` (`Rules/Rel.lean`) compares the constructor's levels with
   the rule's comparands (`Level.isEquivList`), its parameters
   (`DefEqList`) and its residual's index expressions with the
   recursor's index arguments. Where the family is never a
   proposition all three are redundant: the major is a tagged tuple
   of the fields in the family at the recursor's parameters and
   indices, and the fixed point's inversion reads everything off it;
   at a K rule the law holds at any major. Where the family may be a
   proposition the major may denote the point, and then nothing else
   ties the two spines: the INDEX comparison is indispensable (with
   `P : Nat → Prop` and one constructor `mk : ∀ n, P n`, a rule
   without it would let `P.rec motive minor 7 (mk 5)` reduce to
   `minor 5`, while the recursor's set has one value at index `7`),
   the LEVEL comparison makes the block's valuation the same through
   both instantiations (`block_valuation_eq`,
   `Fragment/InstallIota.lean`), and the PARAMETER comparison is
   needed too (at `T {α : Sort u} : α → Prop` with `u` sent to `1`,
   a fitting spine is unconstrained in `α`). *Done upstream*: the
   checker makes the comparisons, with the constructor's telescope
   certificate, in that case only (`iotaCase3`, `Kernel/CoreDefs.lean`)
   and compares nothing elsewhere, as the official kernel does
   (`inductive_reduce_rec` fires by constructor name and `nfields`).
   The fragment's ι rules compare in every case but K, and its law
   `RecRuleLaw` could drop the comparisons outside the certified case. (Fragment
   lane, stages 1–3; fragment lane, part 2 — ι; §4 lane, 2026-10-01;
   revised 2026-10-13.)

7. **`trans` cannot be refuted in the fragment; argue structurally.**
   The task #309 counterexample lives on `DefEq.fvar` ignoring the
   type a free variable carries, which `DefEq.proofFast` reads; with
   contexts instead of typed `fvar`s the fragment has neither rule,
   and no fragment counterexample was found. The paper's argument
   against `trans` is therefore the structural one — the middle term's
   invariant has no supplier; `DefEq.redL_sound` is the sound chaining
   precisely because `RedSem` concludes the reduct's invariant — with
   the real checker's two rules as the reason the question is not
   academic. (Fragment lane, stages 1–3.)

8. **The lambda rule's domain-sort premise is unused by soundness.**
    `Infer.lam_sound`'s `_hu` (`Fragment/Sound.lean`) is the checker's
    "the domain is a type" check; the model does not need it, because
    a lambda's domain only ever enters as the set its denotation is a graph
    over. The real proof already drops the premise at the io grade,
    so the full grade could too if Lean conformance were checked
    elsewhere. The ∀ rule does read its sort premise: the Π-type's
    level depends on it. (Fragment lane, stages 1–3; §2b lane.)

9. **One `Sat` clause instead of a context predicate.** Defining
    `Sat` recursively on the context (`Fragment/WellDenoted.lean`)
    makes `Sat_cons` hold by `Iff.rfl`, so every binder case opens the
    context definitionally. The real proof's `CtxOk`/`Sat`/
    `CtxOk.of_subset` machinery exists to track the types carried by
    `fvar`s, not contexts. (Fragment lane, stages 1–3.)

10. **The env-free soundness needs a `SetLib`-sized interface.** It
    uses no set-forming operation beyond graphs, function spaces,
    truth values and the universe chain — no pairing, union or power
    set (`Fragment/Lib.lean` is the whole list). `Model/Rules/*` could
    be stated over such an interface derived from `SetTheory`, which
    would document what the soundness of the rules needs and what
    only the constructions need. (§2b lane.)

11. **The ι law on values.** Stated on values (`appList`, `TeleFitV`,
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
    `Fragment/Tele.lean` has to say about substitution. The fragment's
    law carries the reduct's invariant on values too (`SpineOk`, turned
    back into the reduct's invariant by `WellDenoted_mkAppN_of_spineOk`)
    as a two-line predicate. What keeps con-leche's law on terms is the
    reading layer, not the value form: with one denotation on the
    checker's terms (item 1) the value-level law would go through in
    the real proof too. (Fragment lane, part 2 — ι; §3 lane.)

12. **One recursion theorem for both regimes, keyed on decodings.**
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
    discharged three ways (`Model/Inductives/ClassGenUniq.lean`).
    Reading a propositional major through a chosen witness would need
    uniqueness of witnesses; the decodings make that unnecessary, in
    the fragment and in the real proof. What the fragment adds is the
    criterion's semantic meaning, stated (`Subsingleton`, `Uniq.lean`),
    which con-leche's `checkStructFieldSortsI` docstring only attributes
    to the official kernel. (Fragment lane, stages 3–4; §3 lane; lane 2,
    2026-10-03.)

13. **Readers instead of `EnvExtend` transport.** The block's
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

14. **The consistency corollary needs no pin and no construction.**
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

15. **Structure η and unit-likeness from the fixed point — done
    upstream.** Against the axioms the three rules the fragment drops
    are small: K is `eq_pt_of_mem_truthVal` twice; structure η is the
    fixed-point equation read left to right (an element of the family IS
    a tagged tuple) plus `tuple_inj`/`tag_inj`; unit-likeness is η at
    zero fields, or the truth value at a `Prop` instance. The real
    checker decides at the install, from the block's shape, whether a
    type has η or is unit-like (`blockCapsAt`,
    `Kernel/Inductives/BlockInstall.lean`), and both laws are
    established from the fixed point by that argument
    (`fixEntryEtaCore`, `Model/Inductives/FixKit.lean`). (§4 lane;
    revised 2026-10-01 and 2026-10-13.)

16. **Two block conditions that carry semantic weight.** The
    fragment's `Ok` (`Fragment/Decl.lean`) asks two things of a block
    that con-leche checks too, and that are easy to overlook:
    no field reads an earlier recursive field (`fieldNoRecDep`,
    con-leche's `structUsedLater`), which is what lets the domains be
    read at a frame whose recursive slots hold an arbitrary value
    (`junkRec`); and the block's level parameters are distinct with
    the elimination parameter fresh, which is what makes the two
    instantiations of item 6 comparable. Both deserve their semantic
    reason in the checker's docstrings. (Fragment lane, stages 3–4.)

17. **"Every fibre is {pt}" versus "every fibre is inhabited".** The
    real proof's propositional function space (`piR` at `0`,
    `ConLeche/SetModel/Ops.lean`) is the truth value of "every fibre
    is inhabited"; the fragment's is "every fibre equals {pt}"
    (`piProp`, `Fragment/Lib.lean`). Under the semantic invariant the
    two agree, and in the env-free fragment the choice only moves the
    one use of "the fibres are truth values": elimination
    (`app_mem_piR`, the app case of `Fragment/Sound.lean`) needs no
    such premise, introduction (`lamR_mem`, the lambda case) does. The cost
    shows in the inductive section (`Fragment/IndSem.lean`,
    `Fragment/InstallRead1.lean`, `Fragment/InstallInd.lean`): a
    Prop-valued motive's fibres must be truth values at the indices
    of every element, so the recursor's typing needs the
    constructors' index expressions to fit (`idx_fits_of_mem_Fam`) —
    a well-formedness fact the "inhabited" reading never consults at
    that level; whichever way the real proof reads it, that is the
    trade. (Regime lane.)

18. **The recursor record's pre-pass is only needed for nesting.** The
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

19. **The elimination criterion's two halves, and the `Sort u`
    superset's reason.** The real checker asks the per-field
    subsingleton criterion only of a family whose sort is provably zero
    (`checkStructFieldSortsI`, `Kernel/Inductives/BlockRec.lean`) and
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

20. **A nested rule's comparison is never consumed.** The real
    checker compares a `.nested` rule's stored instantiation — the
    class's levels and parameters (`auxRuleFire`) — with the major's
    constructor only in the certified case of ι (`iotaCase3`), and the
    fragment's `Red.iotaNested` (`Fragment/Rules.lean`) in every case;
    the fragment's law `RecRuleLawN` (`Fragment/EnvModel.lean`) does
    not consume the comparisons: large elimination is refused for a
    nested block whose sort may be `Prop` (`blockLargeElimAllowed`),
    so the recursion equation is only ever needed above a proposition,
    where the major is itself the tagged tuple and its membership in
    the class pins the fields (`ClassLaws.inv`, `Fragment/NestRec.lean`).
    So the certified case of a nested rule could skip the comparisons
    as the other cases do. (Nested lane, 2026-10-01; revised
    2026-10-13.)

21. **What the fragment's positivity asks beyond the rulings, and
    why.** Beyond depth one, no indices and no reflexive container field,
    the fragment asks that the class's arguments and the nested
    occurrence's index expressions be closed under the block's
    parameters, and that no field of the container after a parameter
    field read its value (`NestInfo.Positive`, `Fragment/Spec.lean`). The
    second is what the replacement lemma (item 29) needs: the class is
    read at every approximant, so a parameter field's value must be free
    to move. The first is what lets the class's arguments fit the
    container's parameters at EVERY parameter set of the universe
    (`NestFacts.argsFit`, proved in `InstallNest.lean` from the class
    having a sort in the environment holding the type former only), which
    a field-dependent argument could not do. The real checker's `nestPos`
    admits both (`Kernel/Inductives/Positivity.lean`). (Nested lane,
    2026-10-01; revised 2026-10-03.)

22. **One generator for the block's and the class's minors.** The
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

23. **Two of a definition's three scope conditions are not checks.**
    A definition's type and value are typed in the empty context, so
    they are closed and mention only stored constants by the typing
    derivations themselves (`Infer.closedAt`, `Infer.consts`,
    `Fragment/ScopeOfInfer.lean`, structural inductions over `Infer`
    alone); only "uses the declared level parameters" is a condition
    beyond typing, and the fragment's `DefOk` (`Fragment/Decl.lean`)
    states that one alone, the environment section recovering the
    full scope (`DefOk.type_scoped`, `DefOk.value_scoped`). The real
    checker runs `looseBVarsBounded` and `constsResolve` as separate
    checks on a definition (`Kernel/CheckerBase.lean`); the model
    proof could take them from the derivations the same way. (Scope
    lane, 2026-10-02.)

24. **A recursive field is a reflexive field with an empty telescope.**
    The fragment's `Field` has one kind for both (`reflexive tele es`,
    recursive at `tele = []`): every generator (`fieldDom`, `ihTy`,
    `ihVal`, `ihValN`, `Fragment/Decl.lean`) and every semantic clause
    (`fieldSet`, `IhOk`, `ihSem`, `IhTyped`, `Fragment/IndSem.lean`;
    their nested twins in `NestRec.lean`) produces, at `tele = []`,
    exactly the recursive clause's term or set — `mkPis [] b = b`,
    `piCtx … [] F = F ρ`, `lamCtx … [] g = g ρ` are all `rfl`. So no
    clause and no proof case is written twice, and "no translated
    constructor has a reflexive field" is a two-line lemma
    (`classField_reflexive`, `Fragment/NestRec.lean`: the only
    reflexive field a translation produces is the parameter field,
    with the empty telescope); the positivity clause for a container's
    own recursive field is `tele = [] ∧ es = []` (`NestInfo.Positive`,
    `Fragment/Spec.lean`). The real checker's `RecFieldKind`
    (`Kernel/Inductives/FieldTele.lean`) has both kinds, and its
    generators and the model's field readings carry a case each that
    the reflexive one subsumes. (Field-merge lane, 2026-10-02.)

25. **The fixed point and accessibility need no graphs.** The real
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

26. **The universal field bound needs no holes-in-context check.**
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

27. **The accessibility bound is one set because no field reads a
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

28. **The container's clause is one more case of the operator, and
    two facts about the container are all it needs.**  The nested
    block's operator reads a container field as the class at the
    approximant's fibre at the nested occurrence (`fieldSet`'s
    container clause, `Fragment/IndSem.lean`, through `classSet`: the
    container's set in the model at the class's arguments with that
    fibre in the nested position).  Monotonicity and accessibility
    of the operator then ask of that clause exactly what they ask of a
    reflexive field's function space: it grows with the fibre, and a value
    in it has a support in the fibre coded inside one set
    (`ContClause`: `mono`, `acc`; plus `mem_univ` for the operator to
    stay in the universe, and `inhab_one`, item 30).  The installation
    proves the four from the container's positivity and the leastness
    of its fixed point (`Fragment/NestSem.lean`, `contClause_of`) —
    the real proof's container case of `Model/Env/BlockLfpMono.lean`
    (monotone through the container's lfp clause,
    `SetModel/HoleClose.lean`) and `Model/Inductives/ContAcc.lean`,
    with the container's frames and the walk of its constructors
    replaced by one lemma about its fields (item 29).  Nothing is asked
    of a plain block (`contOk_of_plain`).  (Lane 3, 2026-10-03.)

29. **One replacement lemma carries monotonicity, accessibility and
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
    computed from the specification alone (`classBound`, item 30).
    (Lane 3, 2026-10-03.)

30. **The one-fibre reading of the fields needs the class inhabited at
    `{pt}`, and the class's bound is spec-computed.**  Lane 2's bound
    is one set because the telescopes are read at the one-fibre
    family with every recursive value replaced by the point
    abstracted over the telescope (item 27).  A container value has
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

31. **One reader for plain and nested blocks, and a model that
    remembers its blocks.**  The fragment's `Reader`
    (`Fragment/Read.lean`) has no plainness field: it reads a container
    field's domain by β through the container's set, a stored constant
    the reader agrees on (`classTy_fit`), as the fibre of the reader's
    family at the nested occurrence; `IdxFitAt`'s container clause is
    that the nested occurrence's index values fit the indices, read off
    the semantic invariant (`fieldDom_wd`).  Only the lemmas about the
    PLAIN recursor's hypotheses' context (`read_ihTy`, `fits_ihCtxAux`,
    `Reader₂.minorOk`, and `IndRec`'s totality and typing) take
    `S.nest = none` explicitly; `ctorSet_mem` takes the container's
    clause at fitting parameters, which is how a nested block's
    constructors get their type law without a "class in the bound"
    condition (`InstallNest.lean`, `type_ok_ctorN`).  The real proof's
    `EnvModelM` carries the installed blocks' data (`lfpBlocks`); the
    fragment's `BlockModel` (`Fragment/BlockModel.lean`) carries one
    law per plain block — scope, the type former's and constructors'
    sets as the fixed point's graphs, the fields' universe bound at
    fitting parameters — which is exactly what a later nesting consumes
    (`NestFacts`), and pushes agreement through the operator
    (`Agree.famOp_eq`, `Agree.Fam_eq`).  (Lane 3, 2026-10-03.)

32. **Monotonicity is a corollary of accessibility, in both regimes.**
    The fixed-point equation and induction need a monotone operator
    (`lfpFamSet_eq`, `lfpFamSet_induction`), and accessibility gives
    it on families in the universe: the support in `W` is in the
    larger `W'` (`AccFam.mono`, the real proof's
    `AccTuple.monoTuple`).  The block's operator is accessible in
    BOTH regimes — only the bound's membership of the universe needs
    a type — so the fragment derives `famOp_mono` from `famOp_acc`
    and has no separate monotonicity proof (`FitsFields_mono`, which
    the recursor's induction uses, re-types through
    `FitsFields_retype`).  For a container the same holds with the
    nested case of accessibility stated at a proposition too:
    `lfpP_acc` needs the bound in the universe only above one, and
    at a proposition the section's closed family is `{pt}`
    (`closedFam_zero`) — so `Fam_psK_acc` holds in both regimes,
    `ContClause.mono` is a theorem, and `Fam_psK_mono` is derived.
    *Done upstream*: accessibility is stated with a bound that need be
    in the universe only above a proposition, holds at every level,
    and the operator's monotonicity is derived from it; the recursor's
    frame monotonicity (`HoleMono.lean`, `posD_mono`, `frameIter`)
    serves the recursor.  (2026-10-03, updated 2026-10-04.)

33. **ι's soundness as three laws of the environment, not a
    certificate walk — done upstream.**  In the fragment the recursor's
    spine needs no certificate at all: a redex that is not the point
    fits the recursor's telescope by the semantic invariant's
    application slots and domain uniqueness (`Sound.lean`,
    `teleFit_of_ne_pt`).  What is left is stated once, as fields of the
    environment's model, and proved where the constants are created:
    the fibre law (`EnvModel.ind_fib`, a stored family's fibres are
    truth values or strict sets as its stored sort says), the slot law
    (`rec_rules_slot`) and the K law (`rec_rules_k`).  The real proof
    has the same shape: its carrier invariant states what the ι step
    consumes as the rule's extra facts (`RecRuleExtra`,
    `Model/Env/Laws.lean`), the certificate is the constructor's
    arguments in one case (`CertsF`), and the per-redex case split is a
    level test on the stored sort (`iotaCase3`).  (2026-10-12, updated
    2026-10-13.)

34. **The K law needs neither `Prop` nor the elimination level.**  The
    installer's proof of the K law (`InstallIota.lean`,
    `rec_rule_lawK`) is inversion of the least fixed point at the
    recursor's own parameters, and holds for every block with one
    constructor and no fields.  The real proof can state K's law for
    that shape and keep "is `Prop`" as the checker's flag only, for
    fidelity with Lean; the K rule's soundness then reads no sort.
    And for a structure without fields the step through the
    projections and K's step have the same reduct
    (`EtaIota.lean`, `iotaEta_noFields`, `recRuleLawK_of_eta`), so
    one law can serve both.  (2026-10-12.)

35. **Lambda telescopes as their own relation — done upstream.**
    `DefEqLams` (`Rules.lean`) compares two lambda telescopes level by level
    and types only the innermost bodies; its claim is unconditional
    (`LamsSem`), which is why the outer levels need no type
    (`Sound.lean`, `DefEqLams.outer_sound`).  The real relation has the
    same rule (`DefEqLams`, `Rules/Rel.lean`), so the checker's "descend
    while both bodies are lambdas" is a rule, not a bridge lemma.
    (2026-10-12, updated 2026-10-13.)

36. **`let` by substitution: the value's checks are verdicts, not
    proof obligations — done upstream.**  With the body inferred at the
    value itself (`Infer.letE`), the soundness of `let` is the
    substituted body's claim plus `interp_zeta`; the checks of the value
    against its type are not consumed (`Infer.letE_sound`), and the
    cheaper grade skips them (`InferIO.letE`).  The real proof's `let`
    rule has the same shape (`Infer.letE`, `Rules/Rel.lean`: the value's
    checks at the full grade only, the body at the value), and the
    checker keeps no variables bound to values.  (2026-10-12, updated
    2026-10-13.)

37. **The cheaper grade as a separate relation.**  The fragment states
    the cheaper grade as its own relation `InferIO` with its own claim
    (`IOGrade.lean`: the hereditary `IORel`, keyed on the type's
    syntax), and its consumers as separate theorems.  The real proof
    carries a grade index on one inference relation, so every
    soundness case is stated for both grades.  Splitting the grades
    would let the full grade's claim stay the plain membership of
    `InferSem` and keep the hereditary claim to the rules that use it.
    (2026-10-12.)

38. **Comparing less than the bodies' types is not enough.**  The
    ill-typed redex of the lambda congruence witness (`ValueReading.lean`)
    can be moved into a stored definition
    `d := fun x => (fun (h : E x) => h) n` of type `∀ x : Prop, F x`;
    then `fun x => d x` and `fun x => n` are typed in the empty
    context, their bodies' types `F x` and `Prop` both have sort
    `Type`, and a comparison of the bodies' sorts, or of their
    zero-ness, passes; only the comparison `F x ≡ Prop` fails
    (`Probe.lean`, `lam_congr_sorts_unsound`).  That environment has a
    model, but `d`'s value is not typed, so it is not accepted.  No
    counterexample with an accepted environment is known; it would need
    a typed term whose reduct holds a redex with an argument outside
    its lambda's domain.  The semantic proof does not need to know whether
    one exists: the check replaces the argument.  The fragment also
    proves weaker forms of the rule sound (`DefEq.lamProp`,
    `DefEq.lamConst`, `DefEq.etaProp`, `DefEq.appIn`,
    `Fragment/Rules.lean`): no type comparison over a domain that is a
    proposition, or between two bodies that do not use the variable,
    or between two arguments compared at the domain of a known head
    type.  The checker uses none of them.  (Lane R4, 2026-10-13.)

39. **Where the ι certificate goes.**  If large elimination from a
    family that may be a proposition is restricted to families with no
    constructor, to K-like families and to structures whose fields are
    propositions wherever the structure is, as Lean's planned kernel
    changes do, then the certified case of ι is empty: K and the step
    through the projections (`EtaIota.lean`) cover every remaining
    large eliminator, and no ι step checks a constructor application.
    (Lane R4, 2026-10-13.)

**2026-10-27 (task #370, modular checking).** The module-by-module
theorem needs no global name table and no weakening of derivations.
Qualified names (home module and name; a proof by its statement) make
every module's own environment a reading of one assignment, and the
proof goes by restriction and extension of models: the world's model,
read through a module's resolution, is a model of the module's context
(`context_model`), the ordinary installation theorems extend it over
the module's declarations (`Checks.blockModel`), and the module's own
ordinary constants extend the world's assignment (`modular_step`).
Con-leche's implementation should follow the same route: its soundness
consumes checker runs, not derivations, so restricting the world's
model to a module's context, applying the existing step theorem of the
fold there, and extending back is the argument that fits, and no
monotonicity of the checker in its environment is needed. Every module
can be type-checked in parallel against its context; the remaining
local checks compare constants and resolutions with the direct imports
and type-check nothing.

**2026-10-27 (task #370, comparison).** Comparator's contract fits the
modular theorem as a second way to validate a module: a module whose
whole own environment reads from earlier modules (every constant an
earlier module's, or an assumption of its type) needs no type checking,
and its model is the restriction of the world's, by the same lemma that
gives a checked module's context its model (`reads_model`). So
con-leche can subsume Comparator without a second soundness argument:
compare the challenge's private environment (definitions with their
values) constant by constant with the solution's, treat axioms and
`sorryAx`-valued constants as holes, and read the result off the
modular theorem.

