import Setlec.SetR.CtxOkR
import Setlec.Verify.Denote.Install
import Setlec.Verify.IotaWalkInv

/-!
# `DeclR`: the per-declaration relation (task #148, T2 — statements)

The transpose of `checkDecl`'s per-kind checks into relation-family
premises (design §1.5), following the TT lane's proven organization
(`Setlec/TTVerify/DeclStep.lean`): one named `Prop` per declaration
kind, assembled by kind dispatch (`DeclR`), with the bridge-facing
assembly lemma `checkDeclR_of` proved here (it is pure dispatch — its
per-kind hypotheses are T3's obligations, its `EnvS`-consumers T5's).

**Statement conventions.**

* Fuel and mode: the annotate pass contributes no relation — its
  outputs are quantified, its calls (`annotateCore μ env F d e = .ok e'`)
  are V-free side conditions, so the per-kind `Prop`s carry `(μ, F)`.
* Front doors are stated at `Δ = []`, `d = 0`, universally in
  `φ : Name → Nat` (declarations are level-polymorphic; the `EnvS`
  fields quantify `φ` the same way).
* Checker runs at positive depth (the `Nat`-op recurrences at `2`, the
  div/mod certificates at `4`, the iota-theorem walks at `rP + cnF`)
  are stated over **canonical contexts**: the denotations of the opened
  variables' annotations at their own depths (`OpenCtxR`), or the
  pinned `Nat` entries where the checker's variables are `Nat`-typed.
  An existentially quantified context would be vacuous-premise-unsound
  (an uninhabited entry empties `Sat`), so the entries are pinned.
* The `indDecl` kind mirrors `checkIndDecl`'s phase structure
  (`Setlec/Kernel/Modeled.lean:773-809`); the walk packs transpose
  `checkIotaThm`/`checkIotaThmN` (`Modeled.lean:62-311`).  The
  projection-function phase is stated at lookup/shape granularity with
  its `proj_i.iota` pack (`ProjIotaR`); `checkProjRule`'s rule
  synthesis enters as the annotate output it stores.  Refinement
  points are recorded in `Setlec/SetR/DESIGN.md` (§D6).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-! ## Canonical-context helpers -/

/-- Pointwise lifting of a relation to lists (arity-checking).  Core
has no `Forall2`; this is the standard definition. -/
def Forall2 {α β : Type _} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

/-- Pointwise denotation of an `Expr` spine at depth `d`. -/
def DenoteL (cval : TConstVal) (env : Env) (φ : Name → Nat) (d : Nat)
    (es : List Expr) (vs : List VExpr) : Prop :=
  Forall2 (fun e v => denote cval env φ d e = some v) es vs

/-- The canonical relation-side context of a checker run over an opened
telescope: `tys` are the opened variables' annotations, outermost
first (each already instantiated at the earlier variables, as
`openPisAtFvars` produces them); the context collects their
denotations at their own depths, innermost first. -/
def OpenCtxR (cval : TConstVal) (env : Env) (φ : Name → Nat) :
    Nat → List Expr → List VExpr → Prop
  | _, [], Δ => Δ = []
  | d, ty :: tys, Δ =>
    ∃ Tv Δ', denote cval env φ d ty = some Tv ∧
      OpenCtxR cval env φ (d + 1) tys Δ' ∧ Δ = Δ' ++ [Tv]

/-- One positive-depth certified comparison, in the bridge's own
quantified-context form (T5's D6 refinement — record in
`Setlec/SetR/DESIGN.md`): both sides denote at the run's depth, and at
**every** context correlating with the checker's frame per `CtxOkR`
the denotations are `DefEq`.  The bridge's defeq claim is exactly
`∀ Δ`-shaped, so one checker run yields every instance; the install
derivation consumes them at *padded* contexts (`.sort 0` at slots the
subjects do not touch — the [set] transpose of the TT lane's padding
trick, `pt ∈ˢ univ 0` making the padded slots `Sat`-free). -/
def DefEqAtW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (a b : Expr) : Prop :=
  ∃ Av Bv, denote cval env φ d a = some Av ∧
    denote cval env φ d b = some Bv ∧
    ∀ Δ : List VExpr, CtxOkR μ cval env φ d Δ a →
      CtxOkR μ cval env φ d Δ b →
      DefEq μ env cval φ Δ Av Bv

/-- One `checkDefEqList` walk at depth `d`: pointwise quantified
comparisons (D6 refinement — see `DefEqAtW`). -/
def DefEqListW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (as bs : List Expr) : Prop :=
  Forall2 (DefEqAtW μ env cval φ d) as bs

/-- One `checkTypedList` element: the spine element's inferred type is
`DefEq` to the domain's denotation, at every correlating context (the
inferred type is per-context — the bridge's slack). -/
def TypedAtW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (e dom : Expr) : Prop :=
  ∃ Ev Dv, denote cval env φ d e = some Ev ∧
    denote cval env φ d dom = some Dv ∧
    ∀ Δ : List VExpr, CtxOkR μ cval env φ d Δ e →
      CtxOkR μ cval env φ d Δ dom →
      ∃ t, Infer μ env cval φ Δ Ev t ∧ DefEq μ env cval φ Δ t Dv

/-- One `checkTypedList` walk (D6 refinement — see `TypedAtW`). -/
def TypedListW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (es doms : List Expr) : Prop :=
  Forall2 (TypedAtW μ env cval φ d) es doms

/-- The `checkIotaSidesTy` pack at `--set-model` (no #146 slot-sort
conjunct — tt-only): both equation sides infer types `DefEq` to the
equation's type slot, at every correlating context (D6 refinement). -/
def IotaSidesTyR (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (alphaS lhsS rhsS : Expr) : Prop :=
  ∃ Av Lv Rv,
    denote cval env φ d alphaS = some Av ∧
    denote cval env φ d lhsS = some Lv ∧
    denote cval env φ d rhsS = some Rv ∧
    ∀ Δ : List VExpr, CtxOkR μ cval env φ d Δ alphaS →
      CtxOkR μ cval env φ d Δ lhsS → CtxOkR μ cval env φ d Δ rhsS →
      (∃ tl, Infer μ env cval φ Δ Lv tl ∧ DefEq μ env cval φ Δ tl Av) ∧
      (∃ tr, Infer μ env cval φ Δ Rv tr ∧ DefEq μ env cval φ Δ tr Av)

/-- The stored `Nat` former's valuation (the level-monomorphic leaf
every `Nat`-typed canonical context entry uses). -/
def natVR (cval : TConstVal) (φ : Name → Nat) : VExpr :=
  cval natName (Level.substFn φ [] [])

/-! ## The shared front doors -/

/-- The `checkConstantVal` pack (`Setlec/Kernel/CheckerBase.lean:70-90`):
freshness/reservation/level guards, the annotated type's syntactic
guards, **the front door's own two-step run chain**, and the type
front door (`infer` + `ensureSort` at `Δ = []`, every `φ`).

The run-chain conjunct is the front door's *literal* output
(`CheckerBase.lean:88-89`): `inferType` names an intermediate `stype`
and `ensureSort` only whnfs it — the inferred type need not **be** a
sort.  Recording the fused `.ok (.sort u)` would be recording
something the checker does not produce (seal 48). -/
def ConstantValR (μ : CheckMode) (F : Nat) (env : Env)
    (cval : TConstVal) (cv : ConstantVal) (type' : Expr) : Prop :=
  (env.find? cv.name).isNone = true ∧
  reservedBasisNames.contains cv.name = false ∧
  cv.name.isProjFnShape = false ∧
  Name.nodup cv.levelParams = true ∧
  cv.type.looseBVarsBounded 0 = true ∧
  cv.type.hasFvar = false ∧
  annotateCore μ env F 0 cv.type = .ok type' ∧
  type'.allLevelParamsDefined cv.levelParams = true ∧
  type'.constsResolve env = true ∧
  (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
    ensureSortCore μ env F 0 stype = .ok u) ∧
  ∀ φ : Name → Nat,
    ∃ Tv tT u, denoteClosed cval env φ type' = some Tv ∧
      Infer μ env cval φ [] Tv tT ∧
      DefEq μ env cval φ [] tT (.sort u)

/-- The value front door shared by `defn`/`thm`/`opaque`
(`checkDefnVal`/`checkThmVal`/`checkOpaqueVal`'s common core): the
value's syntactic guards, its annotate output, **the branch's own
`inferType` + `isDefEq` run pair on the annotated value**, and its
inference against the annotated type at `Δ = []`, every `φ`.

The run conjunct is the twin of `ConstantValR`'s: the value side runs
`inferType` and then compares by `isDefEq` (seal 47).  Task #161 P4
H1 extends it from the bare `inferType` run to the **pair** — the
comparison is the branch's literal next call
(`Setlec/Kernel/Checker.lean:372-374`, and identically at `:395-396`,
`:420-421`): `isDefEq` at fuel `F`, depth `0`, the *inferred* type
first and the annotated declared type second.  No whnf sits between
them, and the entry point is the same `ops` record, so the recorded
form is the checker's literal output (seal 48). -/
def ValueFrontR (μ : CheckMode) (F : Nat) (env : Env)
    (cval : TConstVal) (cv : ConstantVal) (value : Expr)
    (type' value' : Expr) : Prop :=
  value.looseBVarsBounded 0 = true ∧
  value.hasFvar = false ∧
  annotateCore μ env F 0 value = .ok value' ∧
  value'.allLevelParamsDefined cv.levelParams = true ∧
  value'.constsResolve env = true ∧
  (∃ vtype, inferTypeCore μ env F 0 value' = .ok vtype ∧
    isDefEqCore μ env F 0 vtype type' = .ok true) ∧
  ∀ φ : Name → Nat,
    ∃ Tv Vv tv, denoteClosed cval env φ type' = some Tv ∧
      denoteClosed cval env φ value' = some Vv ∧
      Infer μ env cval φ [] Vv tv ∧
      DefEq μ env cval φ [] tv Tv

/-! ## The conditional pin packs (value kinds) -/

/-- The structural-`Nat` recurrence pack (`certifyNatEqs` at the
`checkDecl` defn site): each equation of `natOpEquations`, with the
op's self-references replaced by the stored value, holds as a `DefEq`
at depth `2` over the canonical `[Nat, Nat]` context. -/
def NatEqsR (μ : CheckMode) (env : Env) (cval : TConstVal)
    (eqs : List (Expr × Expr)) : Prop :=
  ∀ eq ∈ eqs, ∀ φ : Name → Nat,
    ∃ L R, denote cval env φ 2 eq.1 = some L ∧
      denote cval env φ 2 eq.2 = some R ∧
      DefEq μ env cval φ [natVR cval φ, natVR cval φ] L R

/-- The structural-`Nat` recurrences' **checker runs** (task #161 P4
H1, extended to the literal tier): `certifyNatEqs`'s verdict is the
conjunction of one `isDefEqCore` run per equation
(`Setlec/Kernel/Checker.lean:426-433` — `ops.isDefEq env 2 eq.1 eq.2`
under `fueledOps μ F`, i.e. `isDefEqCore` at fuel `F`, depth `2`), so
the recorded form is the checker's literal output, one run per
equation.  The P tier's establishment route consumes these runs
through `DefEqClaims2P` — the run-certificate move — because the
relational `NatEqsR` above concludes a `DefEq` whose soundness lives
at the collapse currency only (`Interp2/Step2/NatP.lean`'s wall
record). -/
def NatEqsRunR (μ : CheckMode) (F : Nat) (env : Env)
    (eqs : List (Expr × Expr)) : Prop :=
  ∀ eq ∈ eqs, isDefEqCore μ env F 2 eq.1 eq.2 = .ok true

/-- The `checkDivModPin` pack (`Setlec/Kernel/Checker.lean:638-658`):
environment/pin guards, the stored value pinned `DefEq` to the vendored
definition, and the certificate list. -/
def DivModPinR (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (_cval : TConstVal) (c : Name) (value' : Expr) : Prop :=
  divModEnvGuard env₂ c = true ∧
  divModPinGuard env c = true ∧
  divModCertsGuard env c value' = true ∧
  ∃ pinA, annotateCore μ env F 0 (divModDeclPin c) = .ok pinA ∧
    -- task #148 T6: the pin comparison is **not** recorded, for the
    -- reason `ReducePinR` does not record its own — it is the
    -- elaborator-drift gate, `DivModPinTT` does not record it either,
    -- and the pin's denotation has no supplier.  The certificates
    -- below carry the derivation-layer content.
    -- task #148 T6, **reversible design decision**: the certificate
    -- list enters as the checker's own verdict, not as a transposed
    -- relation.  `DivModCertR` (a depth-`4` `Infer`/`DefEq` pack) had
    -- **zero consumers** — D6's house rule forbids freezing a
    -- statement no consumer has exercised, and the trap family is
    -- five-for-five on unexercised statements getting their
    -- quantifiers wrong.  `DivModPinTT` (`TTVerify/DeclDefn.lean:64`)
    -- keeps the checker call for the same branch, and that lane
    -- finished it.
    --
    -- *Reopen condition*: if `DivModPinS`'s discharge shows the
    -- certificate content wants first-class relational form,
    -- reintroduce it **then**, shaped by that actual consumer.
    -- `CtxOkR.pinnedCtx` is already landed for it.
    checkDivModCerts (m := CheckM) (fueledOps μ F) env c value'
      (divModCertStmts c) (divModCertProofs c) = .ok true

/-- The `checkReducePin` pack (`Setlec/Kernel/Checker.lean:677-697`):
storage/element/pin guards, the witness pinned `DefEq` to the vendored
identity, and the identity certificate at depth `1` over the canonical
element context. -/
def ReducePinR (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (cval : TConstVal) (c : Name) (value : Expr) : Prop :=
  reduceStoredOk env₂ c = true ∧
  reduceElemOk env c = true ∧
  reducePinGuard env c = true ∧
  ∃ valA pinA,
    annotateCore μ env F 0 value = .ok valA ∧
    annotateCore μ env F 0 (reduceDeclPin c) = .ok pinA ∧
    -- task #148 T6: the pin comparison is **not** recorded.  It is
    -- the elaborator-drift gate (`TTVerify/ReducePin.lean`'s own
    -- reading: "a gate that protects the *checker's* other guarantees
    -- leaves the derivation layer alone"), the install destructured
    -- it and never used it, and the pin's own denotation has no
    -- supplier.  Consumer's vote, as with the `ErasedEq` granularity.
    --
    -- task #161 P4 H1: the *identity certificate*'s run, on the other
    -- hand, **is** recorded — it was absorbed into the `DefEq`
    -- conjunct below, which is the exact gap H1 closes elsewhere.
    -- Literal form (`Setlec/Kernel/Checker.lean:689`): `isDefEq` at
    -- depth `1`, applied side first, the certificate variable second.
    isDefEqCore μ env F 1 (.app valA (reduceCertVar c))
      (reduceCertVar c) = .ok true ∧
    (∀ φ : Name → Nat, ∃ E V,
      denoteClosed cval env φ (reduceElemTy c) = some E ∧
      denoteClosed cval env φ valA = some V ∧
      DefEq μ env cval φ [E] (.app V (.bvar 0)) (.bvar 0))

/-! ## The value kinds -/

/-- A checked `def` (design §1.5, `defn` row). -/
def DeclDefnR (μ : CheckMode) (F : Nat) (env : Env) (cval : TConstVal)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint)
    (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValR μ F env cval cv type' ∧
    ValueFrontR μ F env cval cv value type' value' ∧
    env₂ = ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
      env.consts⟩ ∧
    (natOpNames.contains cv.name = true →
      natOpGuard env₂ cv.name = true ∧
      (natOpDeps cv.name).all (natOpStoredOk env₂) = true ∧
      NatEqsR μ env cval
        ((natOpEquations 0 cv.name).map fun eq =>
          (Expr.substConst0 cv.name value' eq.1,
           Expr.substConst0 cv.name value' eq.2)) ∧
      NatEqsRunR μ F env
        ((natOpEquations 0 cv.name).map fun eq =>
          (Expr.substConst0 cv.name value' eq.1,
           Expr.substConst0 cv.name value' eq.2))) ∧
    (natDivModNames.contains cv.name = true →
      DivModPinR μ F env env₂ cval cv.name value')

/-- A checked `theorem`: the defn front doors plus the
is-a-proposition requirement on the type. -/
def DeclThmR (μ : CheckMode) (F : Nat) (env : Env) (cval : TConstVal)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValR μ F env cval cv type' ∧
    -- task #161 P4 H1: the is-a-proposition check's **own three runs**
    -- (`Setlec/Kernel/Checker.lean:382-385`), in the checker's literal
    -- order.  Note these are *not* `ConstantValR`'s pair: that pack
    -- records `checkConstantVal`'s chain, and `checkThmVal` re-runs
    -- `inferType`/`ensureSort` on the annotated type from scratch, so
    -- the intermediates are separately named here.  The level test is
    -- `Level.isEquiv` under `liftFueled`, i.e. literally `some true`.
    (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
      ensureSortCore μ env F 0 stype = .ok u ∧
      Level.isEquiv u .zero = some true) ∧
    -- the type is a proposition (`checkThmVal`'s `ensureSort` +
    -- `Level.isEquiv u .zero`, absorbed to the ground sort `0`)
    (∀ φ : Name → Nat,
      ∃ Tv sT, denoteClosed cval env φ type' = some Tv ∧
        Infer μ env cval φ [] Tv sT ∧
        DefEq μ env cval φ [] sT (.sort 0)) ∧
    ValueFrontR μ F env cval cv value type' value' ∧
    env₂ = ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value' ::
      env.consts⟩

/-- A checked `opaque`: the defn front doors, stored as an axiom
(realizability witness discarded), plus the conditional compiler-trust
pin. -/
def DeclOpaqueR (μ : CheckMode) (F : Nat) (env : Env)
    (cval : TConstVal) (cv : ConstantVal) (value : Expr) (env₂ : Env) :
    Prop :=
  ∃ type' value',
    ConstantValR μ F env cval cv type' ∧
    ValueFrontR μ F env cval cv value type' value' ∧
    env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ ∧
    (reduceOpNames.contains cv.name = true →
      ReducePinR μ F env env₂ cval cv.name value)

/-- An accepted `axiom` (`checkDecl`'s axiom branch,
`Setlec/Kernel/Checker.lean:756-799`): the type front door plus one of
the pinned families' shape gates, or a tolerated skip (installing
nothing). -/
def DeclAxiomR (μ : CheckMode) (F : Nat) (env : Env) (cval : TConstVal)
    (cv : ConstantVal) (env₂ : Env) : Prop :=
  ∃ type',
    ConstantValR μ F env cval cv type' ∧
    (let cvA : ConstantVal := ⟨cv.name, cv.levelParams, type'⟩
     (stdAxiomOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     (cvA.name = trustCompilerName ∧ trustCompilerOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     ((cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) ∧
        ofReduceAxOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     (stdAxiomOk env cvA = false ∧
        cvA.name ≠ trustCompilerName ∧
        cvA.name ≠ ofReduceNatName ∧ cvA.name ≠ ofReduceBoolName ∧
        cvA.name ≠ propextName ∧ cvA.name ≠ choiceName ∧
        toleratedAxiomNames.contains cvA.name = true ∧
        env₂ = env))

/-- The pinned basis-block install (`checkDecl`'s basis branch): the
quot-requires-`Eq` guard and the freshness-checked fold. -/
def BasisInstallR (env : Env) : List ConstantInfo → Env → Prop
  | [], env₂ => env₂ = env
  | ci :: rest, env₂ =>
    (env.find? ci.name).isNone = true ∧
    BasisInstallR ⟨ci :: env.consts⟩ rest env₂

/-- A pinned basis block (design §1.5, `basis` row): side conditions
only — the pinned declarations are pre-annotated, and their semantic
content is `EnvS`'s basis fields (T5), not per-install premises. -/
def DeclBasisR (env : Env) (kind : BasisKind) (env₂ : Env) : Prop :=
  (kind = .quotK → env.find? eqName = some eqA) ∧
  BasisInstallR env kind.declsA env₂

/-! ## The inductive block (design §1.5, `indDecl` row)

Phase-for-phase with `checkIndDecl` (`Modeled.lean:773-809`).  The
walk packs below transpose `checkIotaThm` (`:62-143`) and
`checkIotaThmN` (`:202-311`); the pure shape predicates
(`nestedRuleShape`, `checkEtaThm`-adjacent capability computation,
`ctorResidualOk`) are reused verbatim as Boolean side conditions —
they read only stored data. -/

/-- The `checkMemberVal` pack (`Modeled.lean:373-391`): the constant
check plus the model-counterpart pins. -/
def MemberValR (μ : CheckMode) (F : Nat) (env' : Env)
    (cval : TConstVal) (blockNames : List Name) (cv : ConstantVal)
    (cvA : ConstantVal) : Prop :=
  ∃ type',
    ConstantValR μ F env' cval cv type' ∧
    cvA = ⟨cv.name, cv.levelParams, type'⟩ ∧
    cvA.name.isModelSuffix = false ∧
    ∃ cvm mval hint,
      env'.find? (cvA.name.str "_model")
        = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams = cvA.levelParams ∧
      Expr.eqUpToNames
        (cvA.type.renameConsts fun n =>
          if blockNames.contains n then n.str "_model" else n)
        cvm.type = true

/-- The valuation a modeled block member takes at its install: the
model artifact's.  The block folds thread it (finding 5's resolution,
option 3 — see the `IndMembersR` docstring). -/
def cvalModeled (cval : TConstVal) (n : Name) : TConstVal :=
  cvalWith cval n (fun ψ => cval (n.str "_model") ψ)

/-- The non-recursor member fold (`checkIndMember` over `nonrecs`).

**The valuation runs with the environment** (finding 5, resolved
2026-08-28 in favour of option 3).  The checker threads a running
*environment* through the block, and each member's type may mention
the members installed before it — a constructor targets its family —
so a fold that fixed one `cval` would state member `k > 1`'s front
door about the valuation those members had *before* they existed.
Indexing by the running valuation makes the relation and the install
(`indMemberS`) agree **by construction**: the step's valuation is the
one the install builds, `cvalModeled`.  It also puts blocks on the
same discipline as the single-declaration kinds, whose `cval` *is*
the running valuation at their own check time; and it leaves no
unstated obligation on T6 (any running-vs-final agreement is a
freshness lemma proved where a consumer wants the final form). -/
def IndMembersR (μ : CheckMode) (F : Nat)
    (blockNames : List Name) (caps : IndCaps) :
    Env → TConstVal → List ConstantInfo → Env → TConstVal → Prop
  | env', cval, [], env₂, cval₂ => env₂ = env' ∧ cval₂ = cval
  | env', cval, ci :: rest, env₂, cval₂ =>
    ∃ cvA, MemberValR μ F env' cval blockNames ci.toConstantVal cvA ∧
      match ci with
      | .indInfo _ _ =>
        IndMembersR μ F blockNames caps
          ⟨.indInfo cvA caps :: env'.consts⟩ (cvalModeled cval cvA.name)
          rest env₂ cval₂
      | .ctorInfo _ nP nF =>
        IndMembersR μ F blockNames caps
          ⟨.ctorInfo cvA nP nF :: env'.consts⟩
          (cvalModeled cval cvA.name) rest env₂ cval₂
      | _ => False

/-- Recursor provisioning (`provisionRecs`): each recursor's constant
is member-checked and provisioned rule-less on top of the previous
ones. -/
def ProvisionRecsR (μ : CheckMode) (F : Nat)
    (blockNames : List Name) :
    Env → TConstVal → List ConstantInfo →
    Env → TConstVal → List (ConstantVal × Nat × Nat × List RecRule) →
    Prop
  | envAcc, cval, [], envSelf, cvalSelf, checked =>
    envSelf = envAcc ∧ cvalSelf = cval ∧ checked = []
  | envAcc, cval, ci :: rest, envSelf, cvalSelf, checked =>
    ∃ cvA mI rP rules rest',
      ci = .recInfo ci.toConstantVal mI rP rules ∧
      MemberValR μ F envAcc cval blockNames ci.toConstantVal cvA ∧
      ProvisionRecsR μ F blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩
        (cvalModeled cval cvA.name) rest envSelf cvalSelf rest' ∧
      checked = (cvA, mI, rP, rules) :: rest'

/-- The statement-side walks common to `checkIotaThm` and
`checkIotaThmN` after their structural pins: the index comparison, the
field-domain comparison, the prefix-domain comparison, the rule-λ
comparison, the rhs `DefEq`, and the sides-type pack — at every `φ`,
depth `rP + cnF` throughout, each in the quantified-context form (D6
refinement: the pinned open contexts are the consumer's to build,
padded as its `Sat`-construction needs). -/
def IotaWalksR (μ : CheckMode) (envSelf : Env) (cval : TConstVal)
    (depth : Nat)
    (idxL idxR domL domR preL preR lamL lamR : List Expr)
    (rhsS rhsApplied alphaS lhsS : Expr) : Prop :=
  ∀ φ : Name → Nat,
    DefEqListW μ envSelf cval φ depth idxL idxR ∧
    DefEqListW μ envSelf cval φ depth domL domR ∧
    DefEqListW μ envSelf cval φ depth preL preR ∧
    DefEqListW μ envSelf cval φ depth lamL lamR ∧
    DefEqAtW μ envSelf cval φ depth rhsS rhsApplied ∧
    IotaSidesTyR μ envSelf cval φ depth alphaS lhsS rhsS

/-- **The walks' recorded runs** (task #161 ind tier, the H1 exposure
at the last tier — the campaign's first move returned): the
checker-verdict forms the producer holds at the walk conversion
(`DefEqListOk` per comparison list, the raw `isDefEqCore` verdict at
the rhs comparison, and `checkIotaSidesTy`'s literal run pair,
`Modeled.lean:34-41`), recorded beside the derivation walks.  The P
tier's establishment consumes these through the claims
(`interp2_ne_interp_erase` refutes the currency transport, and
derivation → run is false for a fuel-bounded checker — the part-3
wall's two countermodels); the derivation walks stay for the v1
installs. -/
def IotaRunsR (μ : CheckMode) (F : Nat) (envSelf : Env) (depth : Nat)
    (idxL idxR domL domR preL preR lamL lamR : List Expr)
    (rhsS rhsApplied alphaS lhsS : Expr) : Prop :=
  DefEqListOk μ F envSelf depth idxL idxR ∧
  DefEqListOk μ F envSelf depth domL domR ∧
  DefEqListOk μ F envSelf depth preL preR ∧
  DefEqListOk μ F envSelf depth lamL lamR ∧
  isDefEqCore μ envSelf F depth rhsS rhsApplied = .ok true ∧
  (∃ tl, inferTypeCore μ envSelf F depth lhsS = .ok tl ∧
    isDefEqCore μ envSelf F depth tl alphaS = .ok true) ∧
  (∃ tr, inferTypeCore μ envSelf F depth rhsS = .ok tr ∧
    isDefEqCore μ envSelf F depth tr alphaS = .ok true)

/-- A *canonical* rule's `iota_j` theorem pack — the transpose of
`checkIotaThm` (`Modeled.lean:62-143`): the stored theorem's shape
pins (pure equations over stored data) plus the walks **and their
recorded runs** (task #161). -/
def IotaThmR (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (cval : TConstVal) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule)
    (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : Prop :=
  ∃ cvt fvs tbody,
    env'.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     (largs.getLastD (.bvar 0) == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs)) = true ∧
     (cvj.type.stripPis (cnP + cnF)).isSome = true ∧
     ∃ cdoms cres rdoms fvsP cdomsP crestP xFvsP crest2 ldoms lrest,
       Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f)
         = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       Expr.instPisAt (fvsP.take cnP) cvj.type = some (cdomsP, crestP) ∧
       openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         -- the public-side parameter-domain walk (`:130-131`)
         (∀ φ : Name → Nat,
           DefEqListW μ envSelf cval φ depth
             ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP) ∧
         IotaWalksR μ envSelf cval depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS ∧
         IotaRunsR μ F envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- A *nested-auxiliary* rule's `iota_j` theorem pack — the transpose
of `checkIotaThmN` (`Modeled.lean:202-311`): the stored shape data
(`nestedRuleShape`, pure) with the generalized major pin, the
constructor walks at the stored instantiations, the pin annotate/typed
walks, and the shared statement walks. -/
def IotaThmNR (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (cval : TConstVal) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule)
    (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr)
    (lvls : List Level) (pins : List Expr) : Prop :=
  nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
    = some (lvls, pins) ∧
  ∃ cvt fvs tbody,
    env'.findCV? ((cvName.str "_model").str s!"iota_{j}") = some cvt ∧
    cvt.levelParams = lps ∧
    openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody) ∧
    isEqHead tbody.getAppFn = true ∧
    tbody.getAppArgs.length = 3 ∧
    (let depth := rP + cnF
     let targs := tbody.getAppArgs
     let lhsS := targs.getD 1 (.bvar 0)
     let rhsS := targs.getD 2 (.bvar 0)
     let xFvs := fvs.drop rP
     let pinsF := pins.map fun p =>
       Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
     let largs := lhsS.getAppArgs
     (lhsS.getAppFn == Expr.const (f cvName) (lps.map .param)) = true ∧
     largs.length = mI + 1 ∧
     (largs.take rP == fvs.take rP) = true ∧
     -- task #148 T6: the *erasure* granularity, not `eqUpToNames`.
     -- The checker tests the stronger `eqUpToNames` and
     -- `checkIotaThmN_inv` weakens it (`ErasedEq.of_eqUpToNames`,
     -- which is sound only in that direction — `eqUpToNames` still
     -- compares `fvar` annotations, which `ErasedEq` drops), so
     -- `NestedChecked` cannot supply the stronger form.  Nor is it
     -- wanted: `IndBottomNestedS` takes this pin as `_hmaj` and the
     -- soundness argument reads the major through `denote_erasedEq`.
     Expr.ErasedEq (largs.getLastD (.bvar 0))
       (Expr.mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)) ∧
     (∃ cbinders cbody0, cvj.type.stripPis (cnP + cnF)
        = some (cbinders, cbody0) ∧
       (match cbody0.getAppFn with
        | .const _ _ => true | _ => false) = true) ∧
     ∃ cdoms cres rdoms lrest fvsP crest2 cdomsP crestP xFvsP ldoms,
       Expr.instPisAt (pinsF ++ xFvs)
         ((cvj.type.instantiateLevelParams cvj.levelParams
           lvls).renameConsts f) = some (cdoms, cres) ∧
       cres.getAppArgs.length = cnP + (mI - rP) ∧
       Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
         = some (rdoms, lrest) ∧
       openPisAtFvars rP tyA 0 = some (fvsP, crest2) ∧
       (let pinsP := pins.map fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p
        -- the pins are annotate fixed points (`checkAnnotList`)
        (∀ p ∈ pinsP, annotateCore μ envSelf F depth p = .ok p) ∧
        Expr.instPisAt pinsP
          (cvj.type.instantiateLevelParams cvj.levelParams lvls)
          = some (cdomsP, crestP) ∧
        openPisAtFvars cnF crestP rP = some (xFvsP, ldoms) ∧
        -- the residual *after* the field opening (`crest2P` in
        -- `checkIotaThmN:295-300`) carries the arity pin
        (ldoms.getAppArgs.length == cnP + (mI - rP)) = true) ∧
       ∃ ldomsL lrest2,
         Expr.instLamsAt
           (fvsP ++ xFvsP) rhsA = some (ldomsL, lrest2) ∧
         (∀ φ : Name → Nat,
           TypedListW μ envSelf cval φ depth
             (pins.map fun p =>
               Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP) ∧
         IotaWalksR μ envSelf cval depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS ∧
         IotaRunsR μ F envSelf depth
           ((largs.drop rP).take (mI - rP)) (cres.getAppArgs.drop cnP)
           (xFvs.map Expr.fvarTypeD) (cdoms.drop cnP)
           ((fvs.take rP).map Expr.fvarTypeD) rdoms
           ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL
           rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs)
           (targs.getD 0 (.bvar 0)) lhsS)

/-- One modeled recursor rule (`checkIotaRule`, `Modeled.lean:319-352`):
rhs well-formedness, the λ-telescope shape, and the fire-mode dispatch
into the canonical or nested pack. -/
def IotaRuleR (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (cval : TConstVal) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r r' : RecRule) :
    Prop :=
  ∃ cvj cnP cnF rhsA,
    env'.find? r.ctor = some (.ctorInfo cvj cnP cnF) ∧
    r.nfields = cnF ∧
    r.rhs.looseBVarsBounded 0 = true ∧
    r.rhs.hasFvar = false ∧
    annotateCore μ envSelf F 0 r.rhs = .ok rhsA ∧
    rhsA.allLevelParamsDefined lps = true ∧
    rhsA.constsResolve envSelf = true ∧
    (rhsA.stripLams (rP + cnF)).isSome = true ∧
    -- the rule's rhs infers (the fold derivation reads the λ-tower
    -- through this inference)
    (∀ φ : Name → Nat, ∃ Rv t,
      denoteClosed cval envSelf φ rhsA = some Rv ∧
      Infer μ envSelf cval φ [] Rv t) ∧
    ∃ fire,
      r' = { r with rhs := rhsA, ctorParams := cnP, fire := fire } ∧
      ((Expr.recRulePlain tyA mI rP cnP = true ∧ fire = .plain ∧
          IotaThmR μ F env' envSelf cval f cvName lps tyA mI rP j r
            cvj cnP cnF rhsA) ∨
       (Expr.recRulePlain tyA mI rP cnP = false ∧
          ((fire = .inert ∧
            nestedRuleShape env' envSelf cvName lps tyA mI rP cnP j
              = none) ∨
           (∃ lvls pins, fire = .nested lvls pins ∧
             IotaThmNR μ F env' envSelf cval f cvName lps tyA mI rP j r
               cvj cnP cnF rhsA lvls pins))))

/-- The per-recursor rule fold (`checkIotaRules`). -/
def IotaRulesR (μ : CheckMode) (F : Nat) (env' envSelf : Env)
    (cval : TConstVal) (f : Name → Name) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP : Nat) :
    Nat → List RecRule → List RecRule → Prop
  | _, [], out => out = []
  | j, r :: rest, out =>
    ∃ r' rest',
      IotaRuleR μ F env' envSelf cval f cvName lps tyA mI rP j r r' ∧
      IotaRulesR μ F env' envSelf cval f cvName lps tyA mI rP
        (j + 1) rest rest' ∧
      out = r' :: rest'

/-- The recursor-group phase (`checkIndRecs`): the pinned-`Eq` guard,
provisioning, and the per-recursor installs. -/
def IndRecsR (μ : CheckMode) (F : Nat)
    (blockNames : List Name) (env₂ : Env) (cval₂ : TConstVal)
    (recs : List ConstantInfo) (env₃ : Env) (cval₃ : TConstVal) :
    Prop :=
  (recs = [] ∧ env₃ = env₂ ∧ cval₃ = cval₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf cvalSelf checked,
     ProvisionRecsR μ F blockNames env₂ cval₂ recs envSelf cvalSelf
       checked ∧
     IndRecsFoldR μ F blockNames env₂ envSelf cvalSelf env₂ cval₂
       checked env₃ cval₃)
where
  /-- The install fold over the provisioned group.  The self
  environment and its valuation are the provisioning's output (the
  rules are checked against the whole group); the accumulator's
  valuation runs with the accumulator (finding 5, option 3). -/
  IndRecsFoldR (μ : CheckMode) (F : Nat) (blockNames : List Name)
      (envBase envSelf : Env) (cvalSelf : TConstVal) :
      Env → TConstVal → List (ConstantVal × Nat × Nat × List RecRule) →
      Env → TConstVal → Prop
    | acc, cval, [], out, cvalOut => out = acc ∧ cvalOut = cval
    | acc, cval, c :: rest, out, cvalOut =>
      ∃ rules',
        -- task #148 T6: the *base* environment, not the accumulator.
        -- `checkIndRecs` runs every `checkIotaRules` at `env₂`; the
        -- accumulator only collects the results.  Naming `acc` here
        -- asked for a strengthening the checker does not deliver,
        -- and the install consumes this only through `FoldUpS`,
        -- which the base satisfies a fortiori.
        IotaRulesR μ F envBase envSelf cvalSelf
          (fun n => if blockNames.contains n then n.str "_model" else n)
          c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          rules' ∧
        IndRecsFoldR μ F blockNames envBase envSelf cvalSelf
          ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩
          (cvalModeled cval c.1.name) rest out cvalOut

/-- The projection-function phase for one field (`checkProjFn`,
`Modeled.lean:560-575`): lookups, the public type's roundtrip pins,
the rule's annotate output and synthesis pins, and the `proj_i.iota`
theorem's shape pins and sides pack over the statement's opened
telescope.

**D6's reserved refinement, cashed (task #148, T5 c4).**  The
rule-synthesis internals now enter as the pins their *first consumer*
— `IndBottomProjS` — reads: `checkProjShape`'s constructor telescope
and residual arity/head, `checkProjRule`'s λ-tower shape
(`stripLams` to the field's bound variable) with its
`domsMatchAux`-pinned domains and its rhs front door, and
`checkProjIota`'s `domsMatchAux` domain pin (the statement's telescope
domains *are* the constructor's, renamed).  `checkProjRule`'s two
`checkDefEqList` frame walks and its `instPisAt`/`openPisAtFvars` runs
stay untransposed: the projection bottom reaches its λ-tower context
through the syntactic domain pins (`towerCtxEq`), so no consumer
exercises them, and the house rule forbids freezing a statement no
consumer has exercised. -/
def ProjFnR (μ : CheckMode) (F : Nat) (env' : Env) (cval : TConstVal)
    (T ctorName : Name) (lps : List Name) (nP nF i : Nat)
    (env'' : Env) : Prop :=
  ∃ cvj mcv mval mhint pty rhsA,
    env'.find? ctorName = some (.ctorInfo cvj nP nF) ∧
    env'.find? (projModelName T i) = some (.defnInfo mcv mval mhint) ∧
    mcv.levelParams = lps ∧
    (env'.find? (projFnName T i)).isNone = true ∧
    (env'.find? T).isSome = true ∧
    env'.find? eqName = some eqA ∧
    pty = mcv.type.renameConsts (projBack T ctorName nF) ∧
    (pty.renameConsts (projFwd T ctorName nF) == mcv.type) = true ∧
    pty.constsResolve env' = true ∧
    pty.looseBVarsBounded 0 = true ∧
    pty.hasFvar = false ∧
    pty.allLevelParamsDefined lps = true ∧
    (pty.stripPis (nP + 1)).isSome = true ∧
    i < nF ∧
    -- `checkProjShape` (`CheckerBase.lean:234-243`)
    (pty.stripPis nP).isSome = true ∧
    (∃ cbinders cbody,
      cvj.type.stripPis (nP + nF) = some (cbinders, cbody) ∧
      cbody.getAppArgs.length = nP ∧
      (∃ c cus, cbody.getAppFn = Expr.const c cus) ∧
      -- `checkProjRule` (`CheckerBase.lean:247-278`)
      rhsA.hasFvar = false ∧
      rhsA.looseBVarsBounded 0 = true ∧
      rhsA.allLevelParamsDefined lps = true ∧
      rhsA.constsResolve env' = true ∧
      (∃ rbinders,
        rhsA.stripLams (nP + nF) = some (rbinders, .bvar (nF - 1 - i)) ∧
        ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta), i0 < nP + nF →
          rbinders[i0]? = some b → cbinders[i0]? = some b' →
          b.2.1 = b'.2.1) ∧
      -- the rule's front door (`ops.inferType env' 0 rhsA`) — the
      -- derivation for the v1 install, AND its recorded run (task
      -- #161, the H1 exposure: the P tier consumes the run through
      -- the claims)
      (∀ φ : Name → Nat, ∃ Rv t,
        denoteClosed cval env' φ rhsA = some Rv ∧
        Infer μ env' cval φ [] Rv t) ∧
      (∃ t', inferTypeCore μ env' F 0 rhsA = .ok t') ∧
      -- the `proj_i.iota` theorem's shape pins and sides pack
      (∃ tcv tval,
        env'.find? ((projModelName T i).str "iota")
          = some (.thmInfo tcv tval) ∧
        tcv.levelParams = lps ∧
        -- `checkProjIota`'s body match (`Modeled.lean:535-543`): the
        -- statement's strip-form body is the pinned `Eq`-spine, with
        -- the model projection applied to the parameters and the
        -- model constructor's full spine, equated to the field's
        -- bound variable.  **D6 refinement, cashed at T5 stage 5b**:
        -- the projection bottom consumes the *opened* form, and
        -- `projStmtParts` computes it from exactly this pin — so the
        -- pin is the checker's own `match`, transposed verbatim.
        (∃ (sbinders : List (Name × Expr × BinderMeta)) (ℓA : Level)
            (tySlot : Expr),
          tcv.type.stripPis (nP + nF) = some (sbinders,
            .app (.app (.app (.const eqName [ℓA]) tySlot)
              (Expr.mkAppN (.const (projModelName T i)
                  (lps.map .param))
                (((List.range nP).map fun k =>
                    Expr.bvar (nP + nF - 1 - k)) ++
                 [Expr.mkAppN
                   (.const (ctorName.str "_model")
                     (cvj.levelParams.map .param))
                   (((List.range nP).map fun k =>
                       Expr.bvar (nP + nF - 1 - k)) ++
                    ((List.range nF).map fun k =>
                      Expr.bvar (nF - 1 - k)))])))
              (.bvar (nF - 1 - i))) ∧
          -- `checkProjIota`'s `domsMatchAux`: the statement's domains
          -- are the constructor's, renamed to the model side
          ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta), i0 < nP + nF →
            sbinders[i0]? = some b → cbinders[i0]? = some b' →
            b.2.1 = b'.2.1.renameConsts (projFwd T ctorName nF)) ∧
        ∃ fvsI sbodyO,
          openPisAtFvars (nP + nF) tcv.type 0 = some (fvsI, sbodyO) ∧
          (∀ φ : Name → Nat,
            IotaSidesTyR μ env' cval φ (nP + nF)
              (sbodyO.getAppArgs.getD 0 (.bvar 0))
              (sbodyO.getAppArgs.getD 1 (.bvar 0))
              (sbodyO.getAppArgs.getD 2 (.bvar 0))))) ∧
    env'' = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then .plain else .inert,
        rhsA⟩] :: env'.consts⟩

/-- The projection-function install fold over the field indices, then
the elimination-template pass (`installProjFnStep` /
`installProjTemplateStep`; both skip where the model's artifacts are
absent — the skip conditions are the stored-data lookups above, so the
fold is stated disjunctively per field). -/
def ProjInstallR (μ : CheckMode) (F : Nat)
    (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
    Env → TConstVal → List Nat → Env → TConstVal → Prop
  | env', cval, [], env₄, cval₄ => env₄ = env' ∧ cval₄ = cval
  | env', cval, i :: rest, env₄, cval₄ =>
    ∃ env'' cval'',
      ((ProjFnR μ F env' cval T ctorName lps nP nF i env'' ∧
          -- the projection function's valuation is the model
          -- projection's (finding 5, option 3; this is the
          -- identification `etaLawKeyS` consumes as `hvP`)
          cval'' = cvalWith cval (projFnName T i)
            (fun ψ => cval (projModelName T i) ψ)) ∨
       -- artifact absent: the step is a no-op (`installProjFnStep`'s
       -- skip; the exact skip conditions are D6's refinement point)
       ((env'.find? (projModelName T i)).isNone = true ∧ env'' = env' ∧
         cval'' = cval)) ∧
      ProjInstallR μ F T ctorName lps nP nF env'' cval'' rest env₄
        cval₄

/-- A modeled inductive block (design §1.5, `indDecl` row): the block
split pins, the member fold, the recursor group, and — for
single-constructor blocks — the capability record, the (mode-gated)
constructor-residual check, and the projection installs.  The
elimination-template second pass installs pure stored data
(`installProjTemplate`) and is folded into `TemplatesR`. -/
def DeclIndR (μ : CheckMode) (F : Nat) (env : Env) (cval : TConstVal)
    (block : List ConstantInfo) (env₂ : Env) : Prop :=
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  let blockNames := block.map (·.name)
  block = nonrecs ++ recs ∧
  ((∃ cvT capsT cvC nP nF,
      block.filter (fun ci => match ci with
        | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
      block.filter (fun ci => match ci with
        | .ctorInfo _ _ _ => true | _ => false)
        = [.ctorInfo cvC nP nF] ∧
      (let caps := indBlockCaps μ env cvT cvC nP nF
       ∃ envM cvalM envR cvalR,
         IndMembersR μ F blockNames caps env cval nonrecs envM cvalM ∧
         IndRecsR μ F blockNames envM cvalM recs envR cvalR ∧
         ctorResidualOk μ envR cvT.name cvC.name cvT.levelParams nP nF
           caps.eta = true ∧
         (List.range nF).all
           (fun j => (envR.find? (projFnName cvT.name j)).isNone)
           = true ∧
         ∃ envP cvalP,
           ProjInstallR μ F cvT.name cvC.name cvT.levelParams nP nF
             envR cvalR (List.range nF) envP cvalP ∧
           TemplatesR cvT.name cvC.name cvT.levelParams nP nF envP
             (List.range nF) env₂)) ∨
   (¬ (∃ cvT capsT cvC nP nF,
        block.filter (fun ci => match ci with
          | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
        block.filter (fun ci => match ci with
          | .ctorInfo _ _ _ => true | _ => false)
          = [.ctorInfo cvC nP nF]) ∧
    ∃ envM cvalM cval₂,
      IndMembersR μ F blockNames {} env cval nonrecs envM cvalM ∧
      IndRecsR μ F blockNames envM cvalM recs env₂ cval₂))
where
  /-- The elimination-template second pass: pure stored-data installs
  (`installProjTemplateStep`).

  **No valuation** (D6's refinement point, cashed at T5 stage 6).  The
  other block folds thread a `TConstVal` because their members *alias*
  their model artifacts — a checker-side fact (`cvalModeled` mirrors
  `checkIndMember`'s semantics).  A template entry exists precisely
  because the field has no artifact, so there is nothing to alias and
  the valuation is the *install's* free choice.  Threading one here
  would have forced the soundness side to model a valuation the
  relation picked arbitrarily; dropping it is both simpler and more
  faithful to `installProjTemplate`, which never touches a value. -/
  TemplatesR (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
      Env → List Nat → Env → Prop
    | env', [], env₂ => env₂ = env'
    | env', i :: rest, env₂ =>
      ∃ env'',
        (env'' = env' ∨
         ∃ entry : ProjEntry, entry.structName = T ∧ entry.idx = i ∧
           entry.native = false ∧
           -- the stored shape and the freshness `installProjTemplate`
           -- checks (`Modeled.lean:687-691`), both of which the cons
           -- needs
           entry.levelParams = lps ∧ entry.ty = .sort .zero ∧
           (env'.find? (projFnName T i)).isNone = true ∧
           env'' = ⟨.projInfo entry :: env'.consts⟩) ∧
        TemplatesR T ctorName lps nP nF env'' rest env₂

/-! ## The assembly -/

/-- The per-declaration relation: kind dispatch into the six per-kind
`Prop`s (the relation presentation of design §1.5; the per-kind names
are the working interface, exactly as in the TT lane). -/
def DeclR (μ : CheckMode) (F : Nat) (cval : TConstVal) (env : Env) :
    Declaration → Env → Prop
  | .defnDecl cv value hint, env₂ => DeclDefnR μ F env cval cv value hint env₂
  | .thmDecl cv value, env₂ => DeclThmR μ F env cval cv value env₂
  | .opaqueDecl cv value, env₂ => DeclOpaqueR μ F env cval cv value env₂
  | .axiomDecl cv, env₂ => DeclAxiomR μ F env cval cv env₂
  | .basisDecl kind, env₂ => DeclBasisR env kind env₂
  | .indDecl block, env₂ => DeclIndR μ F env cval block env₂

/-- **The assembly shape** (transpose of `checkDeclTT_of`'s dispatch):
the six per-kind bridge obligations assemble into the whole
`checkDecl → DeclR` claim.  The hypotheses are T3's obligations; the
dispatch itself is proved here because `checkDecl`'s body *is* the
dispatch. -/
theorem checkDeclR_of {μ : CheckMode} {F : Nat} {cval : TConstVal}
    {env env₂ : Env}
    -- task #148 T6: the branch obligations are at **this** `env`.
    -- Re-quantifying `env` inside them while `cval` stays fixed asks
    -- for a semantic relation at a valuation unattached to the
    -- environment it is about — the unattached-premise shape, which
    -- no caller can discharge (it holds only at `m.cval` for `m`'s
    -- own `env`).  The dispatch never needed the generality: it runs
    -- at one environment.
    (hdefn : ∀ {cv : ConstantVal} {value : Expr}
      {hint : ReducibilityHint},
      checkDecl μ (fueledOps μ F) env (.defnDecl cv value hint)
        = .ok env₂ → DeclDefnR μ F env cval cv value hint env₂)
    (hthm : ∀ {cv : ConstantVal} {value : Expr},
      checkDecl μ (fueledOps μ F) env (.thmDecl cv value) = .ok env₂ →
      DeclThmR μ F env cval cv value env₂)
    (hopaq : ∀ {cv : ConstantVal} {value : Expr},
      checkDecl μ (fueledOps μ F) env (.opaqueDecl cv value) = .ok env₂ →
      DeclOpaqueR μ F env cval cv value env₂)
    (hax : ∀ {cv : ConstantVal},
      checkDecl μ (fueledOps μ F) env (.axiomDecl cv) = .ok env₂ →
      DeclAxiomR μ F env cval cv env₂)
    (hbas : ∀ {kind : BasisKind},
      checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂ →
      DeclBasisR env kind env₂)
    (hind : ∀ {block : List ConstantInfo},
      checkDecl μ (fueledOps μ F) env (.indDecl block) = .ok env₂ →
      DeclIndR μ F env cval block env₂)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclR μ F cval env d env₂ := by
  cases d with
  | defnDecl cv value hint => exact hdefn h
  | thmDecl cv value => exact hthm h
  | opaqueDecl cv value => exact hopaq h
  | axiomDecl cv => exact hax h
  | basisDecl kind => exact hbas h
  | indDecl block => exact hind h

end Setlec.SetR
