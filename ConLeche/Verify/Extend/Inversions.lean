module

public import ConLeche.Kernel.Checker

public section

/-!
# Inversions

Small syntactic inversion lemmas and name disequalities shared by
the extension lemmas.

Every statement here is over `Env`/`Expr` only — no valuation, no
`SetTheory` — so the semantics and model tiers import it as it stands.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! Projection equations for the pure checker operations: the
declaration-checker inversions unfold through these (never through
`fueledOps` itself, so record spellings in hypotheses keep matching). -/

theorem fueledOps_inferType (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).inferType env d e = inferTypeCore mode false env F d e := rfl
theorem fueledOps_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps mode F).isDefEq env d a b = isDefEqCore mode false env F d a b := rfl
theorem fueledOps_ensureSort (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).ensureSort env d e = ensureSortCore mode false env F d e := rfl
theorem fueledOps_whnf (F : Nat) (env : Env) (d : Nat) (e : Expr) :
    (fueledOps mode F).whnf env d e = ConLeche.whnf mode false env F d e := rfl

/-- Inversion for `checkConstantVal`. -/
theorem checkConstantVal_inv {env : Env} {cv : ConstantVal}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok ()) :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ stype u,
      cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧
      inferTypeCore mode false env F 0 cv.type = .ok stype ∧
      ensureSortCore mode false env F 0 stype = .ok u := by
  simp only [checkConstantVal, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos =>
    rw [ite_eq_left hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  by_cases htp : cv.type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : cv.type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  cases hst : inferTypeCore mode false env F 0 cv.type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSortCore mode false env F 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hnd, hlb,
    by simpa using hif,
    stype, u, htp, htr, by first | rfl | exact hst, by first | rfl | exact hsort⟩

/-- Reserved basis names are all `str`-shaped. -/
theorem reservedBasisNames_not_num (p : Name) (k : Nat) :
    reservedBasisNames.contains (Name.num p k) = false := rfl

/-- One pinned basis install, inverted (relocated from the TT lane,
task #148 T6: both lanes' basis-block bridges invert the same fold). -/
theorem installBasisDecl_inv {env env₁ : Env} {ci : ConstantInfo}
    (h : installBasisDecl (m := CheckM) env ci = .ok env₁) :
    env.find? ci.name = none ∧ env₁ = ⟨ci :: env.consts, env.tables⟩ := by
  unfold installBasisDecl at h
  revert h
  cases hf : env.find? ci.name with
  | none =>
    intro h
    simp only [Option.isNone_none, ite_true, pure, Except.pure,
      Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩
  | some ci' =>
    intro h
    simp only [Option.isNone_some, Bool.false_eq_true, ite_false,
      throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    exact nomatch h
end ConLeche
