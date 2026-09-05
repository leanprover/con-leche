import Setlec.Verify.Leaves
import Setlec.Verify.Denote.Install
import Setlec.Verify.IotaWalkInv

/-!
# The per-declaration RUN records (task #148 T2; the derivation half
removed 2026-09-05)

The V-free records `checkDecl`'s per-kind checks produce: the `Nat`
recurrences' runs, the pinned basis install, the iota walks' runs, the
elimination-template pass and the direct-structure stage runs.  Every
one is a statement about the CHECKER — `isDefEqCore … = .ok true`,
`checkDirectProj … = .ok env''` — and mentions no relation and no
valuation.

**What this file used to be.**  It was `DeclR`: the transpose of
`checkDecl`'s per-kind checks into *relation-family* premises (design
§1.5), one named `Prop` per declaration kind assembled by kind
dispatch, with the bridge-facing assembly lemma `checkDeclR_of`.  That
was the collapsed model's front door, and the SetR removal's Stage C
deleted it with the relation family (`Red`, `Infer`, `DefEq`, `Tele`)
it was stated over.  A proof-term probe had put every one of those
records outside both surviving capstones' closures **and** outside the
run route the graded fold calls; what is left here is exactly the part
that was inside it.

`DeclIndR` is gone, but `DeclIndR.TemplatesR` survives it — the
elimination-template pass never took a valuation and never built a
derivation (D6's refinement point, cashed at T5 stage 6), so it was
always a run record wearing a `where` clause.  It keeps its full name,
in a namespace block, because five live consumers spell it that way.

**Statement conventions** (unchanged): fuel and mode are carried as
`(μ, F)`; the annotate pass contributes no relation — its calls
(`annotateCore μ env F d e = .ok e'`) are V-free side conditions.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify


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

/-- The valuation a modeled block member takes at its install: the
model artifact's.  The block folds thread it (finding 5's resolution,
option 3 — see the `IndMembersR` docstring). -/
def cvalModeled (cval : TConstVal) (n : Name) : TConstVal :=
  cvalWith cval n (fun ψ => cval (n.str "_model") ψ)

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

/-! ## The elimination-template pass

`DeclIndR` is deleted; this pass is not.  It is kept under its old
qualified name (`DeclIndR.TemplatesR`) because that is how
`SetBase/{DeclIndRun,IndBlockR,IndBlockRun}.lean` and
`SetP/ProjInstallP.lean` spell it, and a rename would have edited four
modules to say the same thing. -/

namespace DeclIndR

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
def TemplatesR (T ctorName : Name) (lps : List Name) (nP nF : Nat) :
    Env → List Nat → Env → Prop
  | env', [], env₂ => env₂ = env'
  | env', i :: rest, env₂ =>
    ∃ env'',
      (env'' = env' ∨
       ∃ entry : ProjEntry, entry.structName = T ∧ entry.idx = i ∧
         entry.native = false ∧
         -- task #175 wiring W3: template entries are tower-free
         -- (what `ProjOkT`'s third conjunct consumes at the cons)
         entry.tower = false ∧
         -- the stored shape and the freshness `installProjTemplate`
         -- checks (`Modeled.lean:687-691`), both of which the cons
         -- needs
         entry.levelParams = lps ∧ entry.ty = .sort .zero ∧
         (env'.find? (projFnName T i)).isNone = true ∧
         env'' = ⟨.projInfo entry :: env'.consts⟩) ∧
      TemplatesR T ctorName lps nP nF env'' rest env₂

end DeclIndR

/-! ## The direct-structure arm (task #175 wiring, W4)

The direct arm of the `.indDecl` clause, recorded as a **run
relation** (the W4 freeze's threading decision): the direct block has
no model artifacts, so nothing V-free can pin its valuations here —
the tier's leaves are built by the install soundness from these rows'
readings, with the semantics coming from the claims interface.  The
per-stage anatomy is exposed by inversion lemmas on the stage
functions where the dischargers need it (`SetBase/DeclDirect.lean`
holds the `checkDirectStruct` inversion). -/

/-- The projection-slot fold (`checkDirectStruct`'s tail): each slot
is `checkDirectProj`'s own run at the accumulator — the entry decision
(`slots`, `directProjSlots`) and the guard levels (`guards`,
`directProjGuards`) are the fold's data. -/
def DirectProjFoldR (μ : CheckMode) (F : Nat) (T C : Name)
    (lps : List Name) (nP nF : Nat) (resSort : Level) (slots : List Bool)
    (guards : List Level) (cvTa cvCa : ConstantVal) :
    Env → List Nat → Env → Prop
  | env', [], env₂ => env₂ = env'
  | env', i :: rest, env₂ =>
    ∃ env'', checkDirectProj (m := Setlec.CheckM) (fueledOps μ F)
        T C lps nP nF resSort slots guards cvTa cvCa env' i = .ok env'' ∧
      DirectProjFoldR μ F T C lps nP nF resSort slots guards cvTa cvCa env''
        rest env₂

/-- **The direct-structure declaration, as checked**: the stage runs
of `checkDirectStruct`, with the intermediate environments and the
recursor install named.  `env` is the pre-block environment. -/
def DeclDirectR (μ : CheckMode) (F : Nat) (env : Env)
    (p : DirectParts) (env₂ : Env) : Prop :=
  ∃ (cvTa cvCa cvRa : ConstantVal) (sorts : List Level) (rhsA : Expr)
    (envI envC : Env),
    checkDirectInd (m := Setlec.CheckM) (fueledOps μ F) env p
      = .ok (envI, cvTa) ∧
    checkDirectCtor (m := Setlec.CheckM) (fueledOps μ F) env envI p cvTa
      = .ok (envC, cvCa, sorts) ∧
    checkConstantVal (m := Setlec.CheckM) (fueledOps μ F) envC p.cvR
      = .ok cvRa ∧
    checkDirectRecTy (m := Setlec.CheckM) (fueledOps μ F) envC p
      cvTa cvCa cvRa = .ok () ∧
    checkDirectRule (m := Setlec.CheckM) (fueledOps μ F) envC p
      cvCa cvRa = .ok rhsA ∧
    (let env₃ : Env :=
      ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
            .plain else .inert,
          rhsA⟩] :: envC.consts⟩
     (List.range p.nF).all
        (fun j => (env₃.find? (projFnName p.cvT.name j)).isNone)
        = true ∧
      DirectProjFoldR μ F p.cvT.name p.cvC.name p.cvT.levelParams
        p.nP p.nF p.resSort (directProjSlots p)
        (directProjGuards cvCa.type p.nP p.nF sorts) cvTa cvCa env₃
        (List.range p.nF) env₂)

end Setlec.SetR
