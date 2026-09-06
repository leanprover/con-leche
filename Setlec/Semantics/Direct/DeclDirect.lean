import Setlec.Semantics.DeclIndRun

/-!
# `DeclDirectRun`: the direct-structure declaration relation (task #175 wiring, W4)

The direct arm of `checkDecl`'s `.indDecl` clause
(`checkDirectStruct`, `Setlec/Kernel/Checker.lean`), recorded as a
**run relation**: one row per stage of the check, each the stage
function's own `.ok` run at the fueled ops, plus the install spine.

**Why runs and not unfoldings** (the W4 freeze's threading decision):
the direct block has no model artifacts, so — unlike `DeclIndRun`,
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

Since task #175 W4c the direct route is the priority route: every
consumer of the dispatch cases on the kernel's own `directParts?`.
-/

namespace Setlec.Semantics

open Setlec (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  DirectParts RecRule fueledOps checkDirectInd checkDirectCtor
  checkConstantVal checkDirectRec checkDirectProjTable
  checkDirectStruct projTableName directCaps)

/-! ## The bridge inversion

`checkDirectStruct`'s body is the stage chain; the inversion is the
monad-shape argument, one `cases` per bind. -/

theorem declDirectRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectParts}
    (h : checkDirectStruct (m := Setlec.CheckM) (fueledOps μ F) env p
      = .ok env₂) :
    DeclDirectRun μ F env p env₂ := by
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
  obtain ⟨envC, cvCa, sorts⟩ := r₂
  rw [hCtor] at h
  dsimp only at h
  cases hRec : checkDirectRec (m := Setlec.CheckM) (fueledOps μ F)
      envC p cvTa cvCa with
  | error e => rw [hRec] at h; exact nomatch h
  | ok r₃ =>
  obtain ⟨cvRa, rhsA⟩ := r₃
  rw [hRec] at h
  dsimp only at h
  refine ⟨cvTa, cvCa, cvRa, sorts, rhsA, envI, envC, hInd, hCtor, hRec, ?_⟩
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
  intro h
  exact h

/-! ## The run-level dispatch

`checkDeclRun_ofEnvFactsE`'s `Ind` slot, post-#175: the direct arm is
already a run relation, so the dispatch pairs it with `DeclIndRun`.
Consumers case on the kernel's `directParts?` (the priority gate). -/

/-- The `.indDecl` dispatch at the run level. -/
def DeclIndRunDispatch (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (env₂ : Env) : Prop :=
  match Setlec.directParts? env block with
  | some p => DeclDirectRun μ F env p env₂
  | none => DeclIndRun μ F env block env₂

end Setlec.Semantics
