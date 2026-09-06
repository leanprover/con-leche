import Setlec.Semantics.DeclIndRun
import Setlec.Verify.Extend.Inversions

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
  checkConstantVal checkDirectRecTy checkDirectRule checkDirectProj
  checkDirectStruct projFnName directCaps)

/-! ## The bridge inversion

`checkDirectStruct`'s body is the stage chain; the inversion is the
monad-shape argument, one `cases` per bind. -/

/-- The projection-slot fold, inverted (each step enters the type's
context, then runs `checkDirectProj`). -/
theorem projFold_run {μ : CheckMode} {F : Nat} {T C : Name} {lps : List Name}
    {nP nF : Nat} {resSort : Level} {slots : List Bool} {guards : List Level}
    {cvTa cvCa : ConstantVal} {env₂ : Env} :
    ∀ (idxs : List Nat) (env₃ : Env),
      idxs.foldlM (fun env i => do
          let env ← Setlec.enterCtx (m := Setlec.CheckM) env lps
          checkDirectProj (m := Setlec.CheckM) (fueledOps μ F) T C lps nP nF resSort
            slots guards cvTa cvCa env i) env₃ = .ok env₂ →
      DirectProjFoldRun μ F T C lps nP nF resSort slots guards cvTa cvCa env₃ idxs env₂
  | [], env₃, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | i :: rest, env₃, h => by
    simp only [List.foldlM, bind, Except.bind] at h
    revert h
    cases hE : Setlec.enterCtx (m := Setlec.CheckM) env₃ lps with
    | error e => intro h; exact nomatch h
    | ok envP =>
    obtain ⟨c, hc, rfl⟩ := Setlec.enterCtx_inv hE
    intro h
    dsimp only at h
    revert h
    cases hstep : checkDirectProj (m := Setlec.CheckM)
        (fueledOps μ F) T C lps nP nF resSort slots guards cvTa cvCa (env₃.withLps c) i with
    | error e => intro h; exact nomatch h
    | ok env₄ =>
      intro h
      exact ⟨c, env₄, hc, hstep, projFold_run rest env₄ h⟩

theorem declDirectRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p : DirectParts}
    (h : checkDirectStruct (m := Setlec.CheckM) (fueledOps μ F) env p
      = .ok env₂) :
    DeclDirectRun μ F env p env₂ := by
  rw [checkDirectStruct] at h
  simp only [bind, Except.bind] at h
  cases hET : Setlec.enterCtx (m := Setlec.CheckM) env p.cvT.levelParams with
  | error e => rw [hET] at h; exact nomatch h
  | ok envT =>
  rw [hET] at h
  obtain ⟨cT, hcT, rfl⟩ := Setlec.enterCtx_inv hET
  dsimp only at h
  cases hInd : checkDirectInd (m := Setlec.CheckM) (fueledOps μ F)
      (env.withLps cT) p with
  | error e => rw [hInd] at h; exact nomatch h
  | ok r₁ =>
  obtain ⟨envI, cvTa⟩ := r₁
  rw [hInd] at h
  dsimp only at h
  cases hEC : Setlec.enterCtx (m := Setlec.CheckM) envI p.cvC.levelParams with
  | error e => rw [hEC] at h; exact nomatch h
  | ok envC' =>
  rw [hEC] at h
  obtain ⟨cC, hcC, rfl⟩ := Setlec.enterCtx_inv hEC
  dsimp only at h
  cases hCtor : checkDirectCtor (m := Setlec.CheckM) (fueledOps μ F)
      env (envI.withLps cC) p cvTa with
  | error e => rw [hCtor] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨envC, cvCa, sorts⟩ := r₂
  rw [hCtor] at h
  dsimp only at h
  cases hER : Setlec.enterCtx (m := Setlec.CheckM) envC p.cvR.levelParams with
  | error e => rw [hER] at h; exact nomatch h
  | ok envR' =>
  rw [hER] at h
  obtain ⟨cR, hcR, rfl⟩ := Setlec.enterCtx_inv hER
  dsimp only at h
  cases hCV : checkConstantVal (m := Setlec.CheckM) (fueledOps μ F)
      (envC.withLps cR) p.cvR with
  | error e => rw [hCV] at h; exact nomatch h
  | ok cvRa =>
  rw [hCV] at h
  dsimp only at h
  cases hRecTy : checkDirectRecTy (m := Setlec.CheckM) (fueledOps μ F)
      (envC.withLps cR) p cvTa cvCa cvRa with
  | error e => rw [hRecTy] at h; exact nomatch h
  | ok u =>
  obtain rfl : u = () := rfl
  rw [hRecTy] at h
  dsimp only at h
  cases hRule : checkDirectRule (m := Setlec.CheckM) (fueledOps μ F)
      (envC.withLps cR) p cvCa cvRa with
  | error e => rw [hRule] at h; exact nomatch h
  | ok rhsA =>
  rw [hRule] at h
  dsimp only at h
  refine ⟨cvTa, cvCa, cvRa, sorts, rhsA, envI, envC, cT, cC, cR, hcT, hInd, hcC,
    hCtor, hcR, hCV, hRecTy, hRule, ?_⟩
  simp only [Env.withLps_consts, Env.withLps_lps] at h ⊢
  revert h
  -- name the fire ite once, so the guard's `if` is the only one left
  generalize (if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2)
      p.nP then Setlec.RecRuleFire.plain
    else Setlec.RecRuleFire.inert) = fire
  intro h
  by_cases hall : ((List.range p.nF).all fun j =>
      (({ consts := (.recInfo cvRa (p.nP + 2) (p.nP + 2)
          [⟨p.cvC.name, p.nF, p.nP, fire, rhsA⟩]) :: envC.consts, lps := cR } : Env).find?
        (projFnName p.cvT.name j)).isNone) = true
  · simp only [hall, ↓reduceIte] at h
    exact ⟨hall, projFold_run _ _ h⟩
  · simp only [hall] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

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
