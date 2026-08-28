import Setlec.SetR.CtxOkR

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

/-- One `checkDefEqList` walk at depth `d` over context `Δ`: both
spines denote and are pointwise `DefEq`. -/
def DefEqListW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (as bs : List Expr) :
    Prop :=
  ∃ As Bs, DenoteL cval env φ d as As ∧ DenoteL cval env φ d bs Bs ∧
    DefEqL μ env cval φ Δ As Bs

/-- One `checkTypedList` walk: each spine element's inferred type is
`DefEq` to the corresponding domain's denotation. -/
def TypedListW (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (Δ : List VExpr) (es doms : List Expr) :
    Prop :=
  Forall2 (fun e dom => ∃ Ev Dv t,
    denote cval env φ d e = some Ev ∧
    denote cval env φ d dom = some Dv ∧
    Infer μ env cval φ Δ Ev t ∧ DefEq μ env cval φ Δ t Dv) es doms

/-- The `checkIotaSidesTy` pack at `--set-model` (no #146 slot-sort
conjunct — tt-only): both equation sides infer types `DefEq` to the
equation's type slot. -/
def IotaSidesTyR (μ : CheckMode) (env : Env) (cval : TConstVal)
    (φ : Name → Nat) (d : Nat) (Δ : List VExpr)
    (alphaS lhsS rhsS : Expr) : Prop :=
  ∃ Av Lv Rv tl tr,
    denote cval env φ d alphaS = some Av ∧
    denote cval env φ d lhsS = some Lv ∧
    denote cval env φ d rhsS = some Rv ∧
    Infer μ env cval φ Δ Lv tl ∧ DefEq μ env cval φ Δ tl Av ∧
    Infer μ env cval φ Δ Rv tr ∧ DefEq μ env cval φ Δ tr Av

/-- The stored `Nat` former's valuation (the level-monomorphic leaf
every `Nat`-typed canonical context entry uses). -/
def natVR (cval : TConstVal) (φ : Name → Nat) : VExpr :=
  cval natName (Level.substFn φ [] [])

/-! ## The shared front doors -/

/-- The `checkConstantVal` pack (`Setlec/Kernel/CheckerBase.lean:70-90`):
freshness/reservation/level guards, the annotated type's syntactic
guards, and the type front door (`infer` + `ensureSort` at `Δ = []`,
every `φ`). -/
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
  ∀ φ : Name → Nat,
    ∃ Tv tT u, denoteClosed cval env φ type' = some Tv ∧
      Infer μ env cval φ [] Tv tT ∧
      DefEq μ env cval φ [] tT (.sort u)

/-- The value front door shared by `defn`/`thm`/`opaque`
(`checkDefnVal`/`checkThmVal`/`checkOpaqueVal`'s common core): the
value's syntactic guards, its annotate output, and its inference
against the annotated type at `Δ = []`, every `φ`. -/
def ValueFrontR (μ : CheckMode) (F : Nat) (env : Env)
    (cval : TConstVal) (cv : ConstantVal) (value : Expr)
    (type' value' : Expr) : Prop :=
  value.looseBVarsBounded 0 = true ∧
  value.hasFvar = false ∧
  annotateCore μ env F 0 value = .ok value' ∧
  value'.allLevelParamsDefined cv.levelParams = true ∧
  value'.constsResolve env = true ∧
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

/-- One div/mod certificate (`checkDivModCerts` step,
`Setlec/Kernel/Checker.lean:584-598`): the applied vendored proof
annotates, and at every `φ` it infers a type `DefEq` to the
substituted characteristic equation, at depth `4` over the canonical
context (`x y : Nat` and the substituted hypothesis slots at their own
depths; unused slots are padded with `Nat` — the checker's depth-`4`
convention is independent of the hypothesis count). -/
def DivModCertR (μ : CheckMode) (F : Nat) (env : Env)
    (cval : TConstVal) (c : Name) (value' : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Prop :=
  ∃ appliedA,
    annotateCore μ env F 4
      (divModCertApplied (Expr.substConstAll c value' proof)
        (hyps.map (Expr.substConst0 c value'))) = .ok appliedA ∧
    ∀ φ : Name → Nat,
      ∃ H1 H2 : VExpr,
        (∀ h1, (hyps.map (Expr.substConst0 c value'))[0]? = some h1 →
          denote cval env φ 2 h1 = some H1) ∧
        ((hyps.map (Expr.substConst0 c value'))[0]? = none →
          H1 = natVR cval φ) ∧
        (∀ h2, (hyps.map (Expr.substConst0 c value'))[1]? = some h2 →
          denote cval env φ 3 h2 = some H2) ∧
        ((hyps.map (Expr.substConst0 c value'))[1]? = none →
          H2 = natVR cval φ) ∧
        ∃ Av Tv Ev,
          denote cval env φ 4 appliedA = some Av ∧
          denote cval env φ 4 (Expr.substConst0 c value' eqE) = some Ev ∧
          Infer μ env cval φ [H2, H1, natVR cval φ, natVR cval φ] Av Tv ∧
          DefEq μ env cval φ [H2, H1, natVR cval φ, natVR cval φ] Tv Ev

/-- The `checkDivModPin` pack (`Setlec/Kernel/Checker.lean:638-658`):
environment/pin guards, the stored value pinned `DefEq` to the vendored
definition, and the certificate list. -/
def DivModPinR (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (cval : TConstVal) (c : Name) (value' : Expr) : Prop :=
  divModEnvGuard env₂ c = true ∧
  divModPinGuard env c = true ∧
  divModCertsGuard env c value' = true ∧
  ∃ pinA, annotateCore μ env F 0 (divModDeclPin c) = .ok pinA ∧
    (∀ φ : Name → Nat, ∃ V P,
      denoteClosed cval env φ value' = some V ∧
      denoteClosed cval env φ pinA = some P ∧
      DefEq μ env cval φ [] V P) ∧
    Forall2
      (fun (se : List Expr × Expr) (proof : Expr) =>
        DivModCertR μ F env cval c value' se.1 se.2 proof)
      (divModCertStmts c) (divModCertProofs c)

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
    (∀ φ : Name → Nat, ∃ V P,
      denoteClosed cval env φ valA = some V ∧
      denoteClosed cval env φ pinA = some P ∧
      DefEq μ env cval φ [] V P) ∧
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
           Expr.substConst0 cv.name value' eq.2))) ∧
    (natDivModNames.contains cv.name = true →
      DivModPinR μ F env env₂ cval cv.name value')

/-- A checked `theorem`: the defn front doors plus the
is-a-proposition requirement on the type. -/
def DeclThmR (μ : CheckMode) (F : Nat) (env : Env) (cval : TConstVal)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValR μ F env cval cv type' ∧
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

/-- The non-recursor member fold (`checkIndMember` over `nonrecs`). -/
def IndMembersR (μ : CheckMode) (F : Nat) (cval : TConstVal)
    (blockNames : List Name) (caps : IndCaps) :
    Env → List ConstantInfo → Env → Prop
  | env', [], env₂ => env₂ = env'
  | env', ci :: rest, env₂ =>
    ∃ cvA, MemberValR μ F env' cval blockNames ci.toConstantVal cvA ∧
      match ci with
      | .indInfo _ _ =>
        IndMembersR μ F cval blockNames caps
          ⟨.indInfo cvA caps :: env'.consts⟩ rest env₂
      | .ctorInfo _ nP nF =>
        IndMembersR μ F cval blockNames caps
          ⟨.ctorInfo cvA nP nF :: env'.consts⟩ rest env₂
      | _ => False

/-- Recursor provisioning (`provisionRecs`): each recursor's constant
is member-checked and provisioned rule-less on top of the previous
ones. -/
def ProvisionRecsR (μ : CheckMode) (F : Nat) (cval : TConstVal)
    (blockNames : List Name) :
    Env → List ConstantInfo →
    Env → List (ConstantVal × Nat × Nat × List RecRule) → Prop
  | envAcc, [], envSelf, checked => envSelf = envAcc ∧ checked = []
  | envAcc, ci :: rest, envSelf, checked =>
    ∃ cvA mI rP rules rest',
      ci = .recInfo ci.toConstantVal mI rP rules ∧
      MemberValR μ F envAcc cval blockNames ci.toConstantVal cvA ∧
      ProvisionRecsR μ F cval blockNames
        ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩ rest envSelf rest' ∧
      checked = (cvA, mI, rP, rules) :: rest'

/-- The statement-side walks common to `checkIotaThm` and
`checkIotaThmN` after their structural pins: the index comparison, the
field-domain comparison, the prefix-domain comparison, the rule-λ
comparison, the rhs `DefEq`, and the sides-type pack — at every `φ`,
over the canonical contexts of the model-side opening (`Δm`, from
`fvs`) and the public-side opening (`Δp`, from `fvsP ++ xFvsP`),
depth `rP + cnF` throughout. -/
def IotaWalksR (μ : CheckMode) (envSelf : Env) (cval : TConstVal)
    (depth : Nat) (fvs fvsP xFvsP : List Expr)
    (idxL idxR domL domR preL preR lamL lamR : List Expr)
    (rhsS rhsApplied alphaS lhsS : Expr) : Prop :=
  ∀ φ : Name → Nat,
    ∃ Δm Δp,
      OpenCtxR cval envSelf φ 0 (fvs.map Expr.fvarTypeD) Δm ∧
      OpenCtxR cval envSelf φ 0
        ((fvsP ++ xFvsP).map Expr.fvarTypeD) Δp ∧
      DefEqListW μ envSelf cval φ depth Δm idxL idxR ∧
      DefEqListW μ envSelf cval φ depth Δm domL domR ∧
      DefEqListW μ envSelf cval φ depth Δm preL preR ∧
      DefEqListW μ envSelf cval φ depth Δp lamL lamR ∧
      (∃ Rv Sv, denote cval envSelf φ depth rhsS = some Rv ∧
        denote cval envSelf φ depth rhsApplied = some Sv ∧
        DefEq μ envSelf cval φ Δm Rv Sv) ∧
      IotaSidesTyR μ envSelf cval φ depth Δm alphaS lhsS rhsS

/-- A *canonical* rule's `iota_j` theorem pack — the transpose of
`checkIotaThm` (`Modeled.lean:62-143`): the stored theorem's shape
pins (pure equations over stored data) plus the walks. -/
def IotaThmR (μ : CheckMode) (_F : Nat) (env' envSelf : Env)
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
         (∀ φ : Name → Nat, ∃ Δp,
           OpenCtxR cval envSelf φ 0
             ((fvsP ++ xFvsP).map Expr.fvarTypeD) Δp ∧
           DefEqListW μ envSelf cval φ depth Δp
             ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP) ∧
         IotaWalksR μ envSelf cval depth fvs fvsP xFvsP
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
     Expr.eqUpToNames (largs.getLastD (.bvar 0))
       (Expr.mkAppN (.const (f r.ctor) lvls) (pinsF ++ xFvs)) = true ∧
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
         (∀ φ : Name → Nat, ∃ Δp,
           OpenCtxR cval envSelf φ 0
             ((fvsP ++ xFvsP).map Expr.fvarTypeD) Δp ∧
           TypedListW μ envSelf cval φ depth Δp
             (pins.map fun p =>
               Expr.instSpine (fvsP.take rP) (rP - 1) p) cdomsP) ∧
         IotaWalksR μ envSelf cval depth fvs fvsP xFvsP
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
def IndRecsR (μ : CheckMode) (F : Nat) (cval : TConstVal)
    (blockNames : List Name) (env₂ : Env) (recs : List ConstantInfo)
    (env₃ : Env) : Prop :=
  (recs = [] ∧ env₃ = env₂) ∨
  (recs ≠ [] ∧
   env₂.find? eqName = some eqA ∧
   ∃ envSelf checked,
     ProvisionRecsR μ F cval blockNames env₂ recs envSelf checked ∧
     IndRecsFoldR μ F cval blockNames envSelf env₂ checked env₃)
where
  /-- The install fold over the provisioned group. -/
  IndRecsFoldR (μ : CheckMode) (F : Nat) (cval : TConstVal)
      (blockNames : List Name) (envSelf : Env) :
      Env → List (ConstantVal × Nat × Nat × List RecRule) → Env → Prop
    | acc, [], out => out = acc
    | acc, c :: rest, out =>
      ∃ rules',
        IotaRulesR μ F acc envSelf cval
          (fun n => if blockNames.contains n then n.str "_model" else n)
          c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          rules' ∧
        IndRecsFoldR μ F cval blockNames envSelf
          ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ rest out

/-- The projection-function phase for one field (`checkProjFn`,
`Modeled.lean:560-575`): lookups, the public type's roundtrip pins,
the rule's annotate output, and the `proj_i.iota` sides pack over the
statement's opened telescope.  The rule-synthesis internals
(`checkProjRule`, `checkProjShape`) enter through their stored outputs
(recorded refinement point D6). -/
def ProjFnR (μ : CheckMode) (_F : Nat) (env' : Env) (cval : TConstVal)
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
    -- the `proj_i.iota` theorem's shape pins and sides pack
    (∃ tcv tval,
      env'.find? ((projModelName T i).str "iota")
        = some (.thmInfo tcv tval) ∧
      tcv.levelParams = lps ∧
      ∃ fvsI sbodyO,
        openPisAtFvars (nP + nF) tcv.type 0 = some (fvsI, sbodyO) ∧
        (∀ φ : Name → Nat, ∃ ΔI,
          OpenCtxR cval env' φ 0 (fvsI.map Expr.fvarTypeD) ΔI ∧
          IotaSidesTyR μ env' cval φ (nP + nF) ΔI
            (sbodyO.getAppArgs.getD 0 (.bvar 0))
            (sbodyO.getAppArgs.getD 1 (.bvar 0))
            (sbodyO.getAppArgs.getD 2 (.bvar 0)))) ∧
    env'' = ⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [⟨ctorName, nF, nP,
        if Expr.recRulePlain pty nP nP nP then .plain else .inert,
        rhsA⟩] :: env'.consts⟩

/-- The projection-function install fold over the field indices, then
the elimination-template pass (`installProjFnStep` /
`installProjTemplateStep`; both skip where the model's artifacts are
absent — the skip conditions are the stored-data lookups above, so the
fold is stated disjunctively per field). -/
def ProjInstallR (μ : CheckMode) (F : Nat) (cval : TConstVal)
    (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
    Env → List Nat → Env → Prop
  | env', [], env₄ => env₄ = env'
  | env', i :: rest, env₄ =>
    ∃ env'',
      (ProjFnR μ F env' cval T ctorName lps nP nF i env'' ∨
       -- artifact absent: the step is a no-op (`installProjFnStep`'s
       -- skip; the exact skip conditions are D6's refinement point)
       ((env'.find? (projModelName T i)).isNone = true ∧ env'' = env')) ∧
      ProjInstallR μ F cval T ctorName lps nP nF env'' rest env₄

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
       ∃ envM envR,
         IndMembersR μ F cval blockNames caps env nonrecs envM ∧
         IndRecsR μ F cval blockNames envM recs envR ∧
         ctorResidualOk μ envR cvT.name cvC.name cvT.levelParams nP nF
           caps.eta = true ∧
         (List.range nF).all
           (fun j => (envR.find? (projFnName cvT.name j)).isNone)
           = true ∧
         ∃ envP,
           ProjInstallR μ F cval cvT.name cvC.name cvT.levelParams nP nF
             envR (List.range nF) envP ∧
           TemplatesR cvT.name cvC.name cvT.levelParams nP nF envP
             (List.range nF) env₂)) ∨
   (¬ (∃ cvT capsT cvC nP nF,
        block.filter (fun ci => match ci with
          | .indInfo _ _ => true | _ => false) = [.indInfo cvT capsT] ∧
        block.filter (fun ci => match ci with
          | .ctorInfo _ _ _ => true | _ => false)
          = [.ctorInfo cvC nP nF]) ∧
    ∃ envM,
      IndMembersR μ F cval blockNames {} env nonrecs envM ∧
      IndRecsR μ F cval blockNames envM recs env₂))
where
  /-- The elimination-template second pass: pure stored-data installs
  (`installProjTemplateStep`); the exact per-field skip/install shape
  is D6's refinement point — the fold records only that each step
  extends by at most the template entry. -/
  TemplatesR (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
      Env → List Nat → Env → Prop
    | env', [], env₂ => env₂ = env'
    | env', i :: rest, env₂ =>
      ∃ env'',
        (env'' = env' ∨
         ∃ entry : ProjEntry, entry.structName = T ∧ entry.idx = i ∧
           entry.native = false ∧
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
    (hdefn : ∀ {env env₂ : Env} {cv : ConstantVal} {value : Expr}
      {hint : ReducibilityHint},
      checkDecl μ (fueledOps μ F) env (.defnDecl cv value hint)
        = .ok env₂ → DeclDefnR μ F env cval cv value hint env₂)
    (hthm : ∀ {env env₂ : Env} {cv : ConstantVal} {value : Expr},
      checkDecl μ (fueledOps μ F) env (.thmDecl cv value) = .ok env₂ →
      DeclThmR μ F env cval cv value env₂)
    (hopaq : ∀ {env env₂ : Env} {cv : ConstantVal} {value : Expr},
      checkDecl μ (fueledOps μ F) env (.opaqueDecl cv value) = .ok env₂ →
      DeclOpaqueR μ F env cval cv value env₂)
    (hax : ∀ {env env₂ : Env} {cv : ConstantVal},
      checkDecl μ (fueledOps μ F) env (.axiomDecl cv) = .ok env₂ →
      DeclAxiomR μ F env cval cv env₂)
    (hbas : ∀ {env env₂ : Env} {kind : BasisKind},
      checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂ →
      DeclBasisR env kind env₂)
    (hind : ∀ {env env₂ : Env} {block : List ConstantInfo},
      checkDecl μ (fueledOps μ F) env (.indDecl block) = .ok env₂ →
      DeclIndR μ F env cval block env₂)
    {env env₂ : Env} {d : Declaration}
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
