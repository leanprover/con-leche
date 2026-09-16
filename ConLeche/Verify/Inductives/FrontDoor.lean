module

public import ConLeche.Verify.BridgeWfImp
public import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.ExceptBind

public section

/-!
# The two front doors, one set of facts (task #315, M6 s6)

A constant enters the environment through one of two doors:
`checkConstantVal` (the ANNOTATION WALK — the stored type is the
walk's output) or `checkConstantValPre` (the PRE-ANNOTATED door of
task #279 K.10/K.12: every check runs, `inferType` included, and the
stored type is the input).  The nested route's scratch install runs
the mutual installer at the `auxRoute` grade, which takes the second
door for every member and constructor of the auxiliary block; the
mutual route takes the first.

The model tier's readers (`formerData_of`, `ctorDataI_ofShape`,
`formerLevels_of`, `MemberConsOk.ofCheck`) consume NOTHING of the walk
beyond what both doors establish: the freshness and name guards, the
stored type's four syntactic facts (closed, fvar-free, level-defined,
resolving) and the `inferTypeCore`/`ensureSortCore` run on it — the
reading itself comes from the `inferTypeCore` run (`acceptedReads_of`,
the `inferRow` claim).  `FrontDoorFacts` is that common interface, so
that the readers are stated ONCE over it and the mutual stage theorems
are generic in the grade (DESIGN §U.18 (a)).
-/

namespace ConLeche

variable {mode : CheckMode}

/-- **What both front doors establish** of a checked constant `cv`
stored as `cvA`: the name guards, the stored constant's name and level
parameters the input's, its type closed, fvar-free, level-defined and
resolving, and the `inferTypeCore`/`ensureSortCore` run on it. -/
structure FrontDoorFacts (mode : CheckMode) (F : Nat) (env : Env) (cv cvA : ConstantVal) :
    Prop where
  fresh : env.find? cv.name = none
  nres : reservedBasisNames.contains cv.name = false
  pshape : cv.name.isProjFnShape = false
  nodup : Name.nodup cv.levelParams = true
  name : cvA.name = cv.name
  lps : cvA.levelParams = cv.levelParams
  bounded : cvA.type.looseBVarsBounded 0 = true
  noFvar : cvA.type.hasFvar = false
  lpsOk : cvA.type.allLevelParamsDefined cvA.levelParams = true
  resolve : cvA.type.constsResolve env = true
  infer : ∃ stype u, inferTypeCore mode env F 0 cvA.type = .ok stype ∧
    ensureSortCore mode env F 0 stype = .ok u
  /-- every `.proj` node of the stored type sits at a stored table slot
  (the walk's `annotateCore_projSlotsOk`; the pre-annotated door's
  `projTablesOk` guard, K.13) -/
  slots : Expr.ProjSlotsOk env cvA.type

/-- **`projTablesOk` is `ProjSlotsOk`, as a Bool**: the pre-annotated
door's `.proj`-slot guard (K.13) says exactly what the annotation walk
establishes of its output. -/
theorem Expr.projSlotsOk_of_projTablesOk {env : Env} :
    ∀ e : Expr, e.projTablesOk env = true → Expr.ProjSlotsOk env e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | lit l => intro _; simp
  | const n us => intro _; simp
  | fvar idx ty ih =>
    intro h
    rw [Expr.projSlotsOk_fvar]
    exact ih (by simpa [Expr.projTablesOk] using h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.projTablesOk, Bool.and_eq_true] at h
    rw [Expr.projSlotsOk_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b mb ihty ihb =>
    intro h
    simp only [Expr.projTablesOk, Bool.and_eq_true] at h
    rw [Expr.projSlotsOk_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b mb ihty ihb =>
    intro h
    simp only [Expr.projTablesOk, Bool.and_eq_true] at h
    rw [Expr.projSlotsOk_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.projTablesOk, Bool.and_eq_true] at h
    rw [Expr.projSlotsOk_letE]
    exact ⟨ihty h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s j e ihe =>
    intro h
    simp only [Expr.projTablesOk, Bool.and_eq_true] at h
    rw [Expr.projSlotsOk_proj]
    exact ⟨Option.isSome_iff_exists.mp h.1, ihe h.2⟩

/-- The stored constant is the input with its type replaced. -/
theorem FrontDoorFacts.eq {F : Nat} {env : Env} {cv cvA : ConstantVal}
    (h : FrontDoorFacts mode F env cv cvA) : cvA = { cv with type := cvA.type } := by
  have h1 := h.name
  have h2 := h.lps
  cases cvA with
  | mk n l t =>
    cases cv with
    | mk n' l' t' =>
      simp only at h1 h2
      subst h1 h2
      rfl

/-- The annotation walk's door. -/
theorem FrontDoorFacts.ofCheck {F : Nat} {env : Env} {cv cvA : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    FrontDoorFacts mode F env cv cvA := by
  obtain ⟨hfind, hnres, hpshape, hnodup, -, hitf, type', stype, u, hann, -, -, hst, hens, rfl⟩ :=
    checkConstantVal_inv h
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF h
  exact ⟨hfind, hnres, hpshape, hnodup, rfl, rfl, htb, htf, htp, htr, ⟨stype, u, hst, hens⟩,
    annotateCore_projSlotsOk (mode := mode) _ _ hann (Expr.FvarTysOk.of_not_hasFvar _ hitf)⟩

/-- A thrown step never succeeds. -/
private theorem doorThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact doorThrow_ne_ok (by assumption))
        | (exfalso; exact doorThrow_ne_ok h)
        | (simp at h))

/-- The pre-annotated door: its guards are the facts, and the stored
constant is the input. -/
theorem FrontDoorFacts.ofPre {F : Nat} {env : Env} {cv cvA : ConstantVal}
    (h : checkConstantValPre (m := CheckM) (fueledOps mode F) env cv = .ok cvA) :
    FrontDoorFacts mode F env cv cvA := by
  unfold checkConstantValPre at h
  by_cases h1 : (env.find? cv.name).isSome = true
  case pos => rw [if_pos h1] at h; close_throw
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  case pos => rw [if_pos h2] at h; close_throw
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  case pos => rw [if_pos h3] at h; close_throw
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; close_throw
  rw [if_pos h4] at h
  by_cases h5 : cv.type.looseBVarsBounded 0 = true
  case neg => rw [if_neg h5] at h; close_throw
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  case pos => rw [if_pos h6] at h; close_throw
  rw [if_neg h6] at h
  by_cases h7 : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => rw [if_neg h7] at h; close_throw
  rw [if_pos h7] at h
  by_cases h8 : cv.type.constsResolve env = true
  case neg => rw [if_neg h8] at h; close_throw
  rw [if_pos h8] at h
  by_cases h9 : cv.type.projTablesOk env = true
  case neg => rw [if_neg h9] at h; close_throw
  rw [if_pos h9] at h
  try simp only [bind, Except.bind] at h
  obtain ⟨sty, hinf, h⟩ := exceptBind_ok h
  try simp only at h
  obtain ⟨u, hens, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  refine ⟨?_, Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3, h4, rfl, rfl, h5,
    Bool.eq_false_iff.mpr h6, h7, h8, ⟨sty, u, hinf, hens⟩, Expr.projSlotsOk_of_projTablesOk _ h9⟩
  cases hf : env.find? cv.name with
  | none => rfl
  | some ci => exact absurd (by rw [hf]; rfl) h1

/-- The door at a grade: `true` is the pre-annotated one. -/
theorem FrontDoorFacts.ofGrade {F : Nat} {env : Env} {cv cvA : ConstantVal} (g : Bool)
    (h : (if g then checkConstantValPre (m := CheckM) (fueledOps mode F) env cv
      else checkConstantVal (fueledOps mode F) env cv) = .ok cvA) :
    FrontDoorFacts mode F env cv cvA := by
  cases g with
  | true => exact .ofPre (by simpa using h)
  | false => exact .ofCheck (by simpa using h)

end ConLeche
