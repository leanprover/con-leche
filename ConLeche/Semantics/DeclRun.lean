module

public import ConLeche.Semantics.Decl

@[expose] public section

/-!
# `DeclRun` — the per-declaration run/guard records (task #161 S4)

Each record carries **guards and runs** only — `Bool` side conditions
on stored data, `inferTypeCore`/`isDefEqCore`/`ensureSortCore`
verdicts, and the `env₂ = ⟨… :: env.consts, env.tables⟩` shapes.  It is
**valuation-free**: no `cval` parameter, no `denote`, no `Infer`, no
`DefEq`, no `V`.

**Which conjuncts each record carries, and its model consumer** (every
one is read off a consumer):

| record | kept, and its consumer |
|---|---|
| `ConstantValRun` | the six freshness/reservation/level/scoping guards (`hfresh` at every harvest and at `declEtaStepRun`), the stored term (`stored_syntax`), the two `allLevelParamsDefined`/`constsResolve` guards, and the run chain `∃ stype u, inferTypeCore … ∧ ensureSortCore …` (the type's reading, through `acceptedReads_of`) |
| `ValueFrontRun` | the value's two syntactic guards, the stored value (`value' = value`), its two resolution guards, and the run **pair** `∃ vtype, inferTypeCore … ∧ isDefEqCore …` (the leaf's reading, and the membership crossing) |
| `NatEqsRun` | one `isDefEqCore` run per recurrence, carried by `DeclDefnRun`; `natOps_install` consumes the runs |
| `DivModPinRun` | the guards and the certificate verdict; `divMod_install` consumes them |
| `ReducePinRun` | the three storage guards and the recorded identity-certificate run; `reduceOps_install` consumes exactly these |
| `DeclThmRun` | the prop-check run triple (`inferTypeCore` + `ensureSortCore` + `Level.isEquiv`) |
| `DeclAxiomRun` | the four-way branch disjunction verbatim — pure stored-data guards |
| `DeclBasisRun` | guards only |
| the inductive kind | the `Ind` parameter below |

**The inductive kind is a parameter.**  `DeclRun`
takes the inductive kind's payload as a **`Prop`-valued parameter**
`Ind`, as `declEtaStepRun` (`Semantics/DeclEta.lean`) takes the ind
kind's η-closure as its one premise.  The caller instantiates
`Ind := DeclIndRunDispatchK μ F env` (`Semantics/Bridge/Sound.lean`:
`DeclBlockRun` at a recognised block).
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## Shared syntactic plumbing

The stored term is the declared one (`e' = e`); the first thing every
consumer of a `*Run` record's storage conjunct calls. -/

/-- The stored terms' syntactic facts, packaged: no fvars, bounded,
from the input's own guards. -/
theorem stored_syntax {e e' : Expr} (hst : e' = e)
    (hef : e.hasFvar = false) (heb : e.looseBVarsBounded 0 = true) :
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true :=
  hst ▸ ⟨hef, heb⟩

/-! ## The shared front doors, run half -/

/-- The shared front door's guards and runs: the stored type's checks. -/
def ConstantValRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (type' : Expr) : Prop :=
  (env.find? cv.name).isNone = true ∧
  reservedBasisNames.contains cv.name = false ∧
  Name.nodup cv.levelParams = true ∧
  cv.type.looseBVarsBounded 0 = true ∧
  cv.type.hasFvar = false ∧
  type' = cv.type ∧
  type'.allLevelParamsDefined cv.levelParams = true ∧
  type'.constsResolve env = true ∧
  (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
    ensureSortCore μ env F 0 stype = .ok u)

/-- The value front door's guards and runs. -/
def ValueFrontRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (type' value' : Expr) : Prop :=
  value.looseBVarsBounded 0 = true ∧
  value.hasFvar = false ∧
  value' = value ∧
  value'.allLevelParamsDefined cv.levelParams = true ∧
  value'.constsResolve env = true ∧
  (∃ vtype, inferTypeCore μ env F 0 value' = .ok vtype ∧
    isDefEqCore μ env F 0 vtype type' = .ok true)

/-! ## The conditional pin packs, run half -/

/-- The `Nat.div`/`Nat.mod` pin pack: the pin comparison is not
transposed and the certificates enter as the checker's verdict.

**The matched variant is existential and unlisted** (task #304): the
install gate's pin list is a parameter of the fold, so naming the
shipped list here would tie the whole run tier to it.  Nothing downstream reads
the membership — the model's conversion (`divMod_install`,
`ConLeche/Model/DivModCert.lean`) is over an arbitrary
`ps : NatOpPinSet`, because what it consumes is the certificates'
verdict *in this environment* and not where the variant came from.  So
the pack says only that SOME variant's guards passed and certificates
checked, which is what an install at any pin list establishes. -/
def DivModPinRun (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (c : Name) (value' : Expr) : Prop :=
  divModEnvGuard env₂ c = true ∧
  -- the pin variant that matched (task #273): its guards, its
  -- certificates checked
  ∃ ps : NatOpPinSet,
    divModPinGuard ps env c = true ∧
    divModCertsGuard ps env c value' = true ∧
      checkDivModCerts (m := CheckM) (fueledOps μ F) env c value'
        (divModCertStmts c) (divModCertProofs ps c) = .ok true

/-- The reduce pin pack: the storage guards and the recorded
identity-certificate run. -/
def ReducePinRun (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (c : Name) (value : Expr) : Prop :=
  reduceStoredOk env₂ c = true ∧
  reduceElemOk env c = true ∧
  reducePinGuard env c = true ∧
    isDefEqCore μ env F 1 (.app value (reduceCertVar c))
      (reduceCertVar c) = .ok true

/-! ## The value kinds, run half -/

/-- A `defnDecl`'s guards and runs. -/
def DeclDefnRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint)
    (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    ValueFrontRun μ F env cv value type' value' ∧
    env₂ = ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
      env.consts, env.tables⟩ ∧
    (natOpNames.contains cv.name = true →
      natOpGuard env₂ cv.name = true ∧
      (natOpDeps cv.name).all (natOpStoredOk env₂) = true ∧
      NatEqsRun μ F env
        ((natOpEquations 0 cv.name).map fun eq =>
          (Expr.substConst0 cv.name value' eq.1,
           Expr.substConst0 cv.name value' eq.2))) ∧
    (natDivModNames.contains cv.name = true →
      DivModPinRun μ F env env₂ cv.name value')

/-- A `thmDecl`'s guards and runs. -/
def DeclThmRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
      ensureSortCore μ env F 0 stype = .ok u ∧
      Level.isEquiv u .zero = some true) ∧
    ValueFrontRun μ F env cv value type' value' ∧
    -- stored by statement only: the constant carries no value (the
    -- checked `value'` is the realizability witness, not stored)
    env₂ = ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts, env.tables⟩

/-- **A type the checker finds to be a proposition**: its inferred type
reduces to a sort whose level is zero — the prop row of `DeclThmRun`, at
some fuel.  A definition or opaque constant whose type passes it gets
the canonical proof as its leaf (`Model/Harvest.lean`), so that every
proof of one statement has one leaf. -/
def PropTypeRun (μ : CheckMode) (env : Env) (ty : Expr) : Prop :=
  ∃ F stype u, inferTypeCore μ env F 0 ty = .ok stype ∧
    ensureSortCore μ env F 0 stype = .ok u ∧ Level.isEquiv u .zero = some true

/-- An `opaqueDecl`'s guards and runs. -/
def DeclOpaqueRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    ValueFrontRun μ F env cv value type' value' ∧
    env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ ∧
    (reduceOpNames.contains cv.name = true →
      ReducePinRun μ F env env₂ cv.name value)

/-- An `axiomDecl`'s guards and runs: the branch disjunction is pure
stored-data guards and is carried verbatim. -/
def DeclAxiomRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (env₂ : Env) : Prop :=
  -- **`Quot.sound`** (task #293): the pinned quotient block's own
  -- record, compared with the pin BEFORE the common checks (its name is
  -- a reserved basis name) and installing nothing of its own — the
  -- block installs it.  No `ConstantValRun`: the record's type is not
  -- checked here.
  (cv.name = quotSoundName ∧ env₂ = env) ∨
  ∃ type',
    ConstantValRun μ F env cv type' ∧
    (let cv : ConstantVal := ⟨cv.name, cv.levelParams, type'⟩
     (stdAxiomOk env cv = true ∧
        env₂ = ⟨.axiomInfo cv :: env.consts, env.tables⟩) ∨
     (cv.name = trustCompilerName ∧ trustCompilerOk env cv = true ∧
        env₂ = ⟨.axiomInfo cv :: env.consts, env.tables⟩) ∨
     ((cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName) ∧
        ofReduceAxOk env cv = true ∧
        env₂ = ⟨.axiomInfo cv :: env.consts, env.tables⟩) ∨
     (stdAxiomOk env cv = false ∧
        cv.name ≠ trustCompilerName ∧
        cv.name ≠ ofReduceNatName ∧ cv.name ≠ ofReduceBoolName ∧
        cv.name ≠ propextName ∧ cv.name ≠ choiceName ∧
        cv.name = sorryAxName ∧
        env₂ = env))

/-! ## The assembly -/

/-- **The per-declaration run relation**: the kind dispatch, with the
inductive kind's payload taken as a parameter (see the module
docstring). -/
def DeclRun (μ : CheckMode) (F : Nat)
    (Ind : List ConstantInfo → Nat → Env → Prop) (env : Env) :
    Declaration → Env → Prop
  | .defnDecl cv value hint, env₂ => DeclDefnRun μ F env cv value hint env₂
  | .thmDecl cv value, env₂ => DeclThmRun μ F env cv value env₂
  | .opaqueDecl cv value, env₂ => DeclOpaqueRun μ F env cv value env₂
  | .axiomDecl cv, env₂ => DeclAxiomRun μ F env cv env₂
  | .basisDecl kind, env₂ => DeclBasisRun env kind env₂
  -- **The pinned blocks are recognised in the FOLD** (task #293): a
  -- stream block that IS one of the five pins installs the pin, and the
  -- quotient package's `type` record installs the sixth (its other
  -- records are members of the block that one installs).
  | .indDecl block nP, env₂ =>
    match basisPinHit block with
    | some kind => DeclBasisRun env kind env₂
    | none => Ind block nP env₂
  | .quotDecl k _, env₂ =>
    match k with
    | .type => DeclBasisRun env .quotK env₂
    | _ => env₂ = env

end ConLeche.Semantics
