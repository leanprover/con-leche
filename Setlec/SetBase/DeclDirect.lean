import Setlec.SetBase.DeclIndRun

/-!
# `DeclDirectR`: the direct-structure declaration relation (task #175 wiring, W4)

The direct arm of `checkDecl`'s `.indDecl` clause
(`checkDirectStruct`, `Setlec/Kernel/Checker.lean`), recorded as a
**run relation**: one row per stage of the check, each the stage
function's own `.ok` run at the fueled ops, plus the install spine.

**Why runs and not unfoldings** (the W4 freeze's threading decision):
the direct block has no model artifacts, so — unlike `DeclIndR`,
whose member rows pin valuations to stored `_model` leaves — nothing
V-free can pin the direct constants' valuations here.  The tier's
leaves (`directTyAV`/`directMkAV`/`directRecAV`) are *built by the
install soundness* from the recorded runs' readings, and the
semantic facts they need come from the claims interface
(`SetP/Claims2P.lean`) applied to these rows.  So the relation is
entirely V-free, the bridge inversion is a monad-shape argument, and
the per-stage anatomy (the `checkDirectRecTy` frame walks, the
`checkDirectProj` entry data) is exposed by inversion lemmas on the
stage functions where the dischargers need it.

Pre-flip (`directStructsEnabled = false`) the arm is dead:
`directParts?_none` reduces `DeclR`'s guarded `.indDecl` row to
`DeclIndR`, and every consumer discharges the direct case with it.
-/

namespace Setlec.SetR

open Setlec (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectParts RecRule fueledOps checkDirectInd checkDirectCtor
  checkConstantVal checkDirectRecTy checkDirectRule checkDirectProj
  checkDirectStruct projFnName directCaps)

/-! ## The bridge inversion

`checkDirectStruct`'s body is the stage chain; the inversion is the
monad-shape argument, one `cases` per bind. -/

theorem declDirectR_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectParts}
    (h : checkDirectStruct (m := Setlec.CheckM) (fueledOps μ F) env p
      = .ok env₂) :
    DeclDirectR μ F env p env₂ := by
  rw [checkDirectStruct] at h
  simp only [bind, Except.bind] at h
  cases hInd : checkDirectInd (m := Setlec.CheckM) (fueledOps μ F)
      env p with
  | error e => rw [hInd] at h; exact nomatch h
  | ok r₁ =>
  obtain ⟨envI, cvTa⟩ := r₁
  rw [hInd] at h
  dsimp only at h
  cases hCtor : checkDirectCtor (m := Setlec.CheckM) (fueledOps μ F)
      env envI p cvTa with
  | error e => rw [hCtor] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨envC, cvCa⟩ := r₂
  rw [hCtor] at h
  dsimp only at h
  cases hCV : checkConstantVal (m := Setlec.CheckM) (fueledOps μ F)
      envC p.cvR with
  | error e => rw [hCV] at h; exact nomatch h
  | ok cvRa =>
  rw [hCV] at h
  dsimp only at h
  cases hRecTy : checkDirectRecTy (m := Setlec.CheckM) (fueledOps μ F)
      envC p cvTa cvCa cvRa with
  | error e => rw [hRecTy] at h; exact nomatch h
  | ok u =>
  obtain rfl : u = () := rfl
  rw [hRecTy] at h
  dsimp only at h
  cases hRule : checkDirectRule (m := Setlec.CheckM) (fueledOps μ F)
      envC p cvCa cvRa with
  | error e => rw [hRule] at h; exact nomatch h
  | ok rhsA =>
  rw [hRule] at h
  dsimp only at h
  refine ⟨cvTa, cvCa, cvRa, rhsA, envI, envC, hInd, hCtor, hCV,
    hRecTy, hRule, ?_⟩
  dsimp only at h ⊢
  revert h
  -- name the fire ite once, so the guard's `if` is the only one left
  generalize (if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2)
      p.nP then Setlec.RecRuleFire.plain
    else Setlec.RecRuleFire.inert) = fire
  -- name the recursor-extended environment
  generalize (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩] :: envC.consts⟩ : Env)
    = env₃
  split
  · next hall =>
    intro h
    refine ⟨hall, ?_⟩
    clear hall
    revert h
    generalize List.range p.nF = idxs
    induction idxs generalizing env₃ with
    | nil =>
      intro h
      simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    | cons i rest ih =>
      intro h
      simp only [List.foldlM, bind, Except.bind] at h
      revert h
      cases hstep : checkDirectProj (m := Setlec.CheckM)
          (fueledOps μ F) p.cvT.name p.cvC.name p.cvT.levelParams
          p.nP p.nF p.resSort cvTa cvCa env₃ i with
      | error e => intro h; exact nomatch h
      | ok env₄ =>
        intro h
        exact ⟨env₄, hstep, ih env₄ h⟩
  · intro h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The run-level dispatch

`checkDeclRun_ofEnvRE`'s `Ind` slot, post-#175: the direct arm is
already a run relation, so the dispatch pairs it with `DeclIndRunR`. -/

/-- The `.indDecl` dispatch at the run level. -/
def DeclIndRunDispatchR (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (env₂ : Env) : Prop :=
  match Setlec.directParts? env block with
  | some p => DeclDirectR μ F env p env₂
  | none => DeclIndRunR μ F env block env₂

/-- Pre-flip the run dispatch **is** the modeled run record. -/
theorem declIndRunDispatchR_eq_ind {μ : CheckMode} {F : Nat}
    {env : Env} {block : List ConstantInfo} {env₂ : Env} :
    DeclIndRunDispatchR μ F env block env₂
      ↔ DeclIndRunR μ F env block env₂ := by
  rw [DeclIndRunDispatchR]
  have hnone : Setlec.directParts? env block = none := by
    unfold Setlec.directParts?
    cases Setlec.directPartsCore? block with
    | none => rfl
    | some p => simp [Setlec.directStructsEnabled]
  rw [hnone]

end Setlec.SetR
