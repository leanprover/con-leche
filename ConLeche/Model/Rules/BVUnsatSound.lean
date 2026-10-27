module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit

/-!
# `Infer.bvUnsat` is sound (task #368)

`U E C a` (`U = unsat_of_verifyBVExpr_eq_true`) is the point, and
`⟦Unsat E⟧` holds it.  The semantic content is the environment law
`BVUnsatSemLaw` (`RulesInputs.bv_unsat`, proved from the fold's
invariant in `Model/BVUnsat.lean`); this file supplies its premises:
`E`'s reading lies in `⟦BVLogicalExpr⟧` (the inference of `E` and the
comparison of its type), and at every quoted assignment `x` the reading
of `eval (quoteAssign x) E` is `⟦false⟧` (the rule's reductions, whose
soundness the master induction passes in).  `a` is not inferred: it is
a stored constant, so it reads and is graded, and the point applied to
anything is the point.
-/

public section

namespace ConLeche.Model.Rules
open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w
variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- The canonical proof applied to anything graded is graded and is the
canonical proof (`Model/BasisQuot.lean`'s `WellDenoted_app_pt`, which
this tier cannot import). -/
theorem wd_app_pt {ρ : Nat → V} {f a : Term}
    (hf : WellDenoted V ρ f) (hfi : interp V ρ f = pt) (ha : WellDenoted V ρ a) :
    WellDenoted V ρ (.app f a) ∧ interp V ρ (.app f a) = pt := by
  refine ⟨?_, by rw [interp_app, hfi, app_pt]⟩
  rw [WellDenoted_app]
  refine ⟨hf, ha, 0, sing (interp V ρ a), fun _ => piR 0 (unitSet : V) (fun _ => unitSet),
    ?_, mem_sing.mpr rfl, fun _ _ _ => piR_zero_mem_univZero, fun h => absurd rfl h⟩
  rw [hfi]
  exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩⟩

theorem denote_const_nil {acval : Name → (Name → Nat) → Term}
    {d : Nat} {n : Name} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci) (hlp : ci.toConstantVal.levelParams = []) :
    denote acval env φ d (.const n []) = some (acval n (Level.substFn φ [] [])) := by
  have h := denote_const (acval := acval) (φ := φ) (d := d) (us := []) hf (by simp [hlp])
  rw [hlp] at h
  exact h

theorem Infer.bvUnsat_sound (hin : RulesInputs V m φ) {d : Nat} {E C a tf tE tC : Expr}
    (_hf : InferSemFull m φ d (.app (.app (.const ConLeche.unsatThmName []) E) C) tf)
    (hE : InferSemFull m φ d E tE) (hd : DefEqSem m φ d tE (.const bvLogicalExprName []))
    (hC : InferSemFull m φ d C tC)
    (hhit : ConLeche.bvUnsatHit env.find? env.findProj? (.app (.app (.const ConLeche.unsatThmName []) E) C) a
      = true)
    (hred : ∀ x : Std.Tactic.BVDecide.BVExpr.Assignment,
      RedSem m φ d (.app (.app (.const bvEvalName []) (quoteAssign x)) E)
        (.const ConLeche.boolFalseName []))
    (hpow : ∀ k : Nat, RedSem m φ d (pow2E (.lit (.natVal k))) (.lit (.natVal (2 ^ k)))) :
    InferSem m φ .full d (.app (.app (.app (.const ConLeche.unsatThmName []) E) C) a)
      (ConLeche.bvUnsatType E) := by
  intro hfr Δa ea hCtx hea
  obtain ⟨harg, hok⟩ := ConLeche.bvUnsatHit_parts hhit
  obtain ⟨n, ci, rfl, hfn, -⟩ := ConLeche.bvUnsatArgOk_const harg
  have hpins := ConLeche.bvUnsatOk_pins hok
  have hok' := hok
  simp only [ConLeche.bvUnsatOk, Bool.and_eq_true, Bool.not_eq_true'] at hok'
  obtain ⟨⟨⟨⟨hEc, hEf⟩, hCc⟩, -⟩, -⟩ := hok'
  have hΔ : Δa.length = d := hCtx.1
  obtain ⟨hFE, hCE⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa) hEf hEc hΔ
  -- the subject's reading, split
  obtain ⟨f2, aT, hf2, haT, rfl⟩ := denote_app_inv hea
  obtain ⟨f1, cT, hf1, hcT, rfl⟩ := denote_app_inv hf2
  obtain ⟨uT, eT, huT, heT, rfl⟩ := denote_app_inv hf1
  -- the frame of `C`
  obtain ⟨hws, hb, hLb⟩ := hfr
  simp only [Expr.WScoped, Expr.looseBVarsBounded, Bool.and_eq_true] at hws hb
  have hFC : Frame d C := ⟨hws.1.2, hCc, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])⟩
  -- `E` is in `⟦BVLogicalExpr⟧`, `C` and `a` are graded
  obtain ⟨hFtE, hsubE, tEa, htEa, hrowE⟩ := hE hFE hCE heT
  obtain ⟨_hFtC, _hsubC, tCa, _htCa, hrowC⟩ := hC hFC (hCtx.app_fn.app_arg) hcT
  -- the stored constants the claim reads
  obtain ⟨cvU, hfU, hlU⟩ := ConLeche.BVUnsat.pin_U hpins
  obtain ⟨cvS, vS, hS, hfS, hlS⟩ := ConLeche.BVUnsat.pin_Unsat hpins
  obtain ⟨cvB, vB, hB, hfB, hlB, htB⟩ := ConLeche.BVUnsat.pin_BVLE hpins
  have hdS := denote_const_nil (acval := m.acval) (φ := φ) (d := d) hfS hlS
  have hdB := denote_const_nil (acval := m.acval) (φ := φ) (d := d) hfB hlB
  have haT' : aT = m.acval n (Level.substFn φ ci.toConstantVal.levelParams []) := by
    have := denote_const_arityK hfn haT
    exact this.2
  -- the type: framed, no new leaf, and its reading
  have hTnf : (ConLeche.bvUnsatType E).hasFvar = false := by
    simp [ConLeche.bvUnsatType, Expr.hasFvar, hEf]
  have hTbd : (ConLeche.bvUnsatType E).looseBVarsBounded 0 = true := by
    simp [ConLeche.bvUnsatType, Expr.looseBVarsBounded, hEc]
  obtain ⟨hFT, -⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa) hTnf hTbd hΔ
  refine ⟨hFT, ?_, .app (m.acval ConLeche.bvUnsatName (Level.substFn φ [] [])) eT, ?_, ?_⟩
  · intro l hl
    rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hTnf] at hl; exact nomatch hl
  · simp [ConLeche.bvUnsatType, denote_app, hdS, heT]
  intro ρ hρ hL
  have hLE : LeavesGr m φ d E ρ := fun l hl => by
    rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hEf] at hl; exact nomatch hl
  obtain ⟨hwE, hwtE, hmemE⟩ := hrowE ρ hρ hLE
  obtain ⟨hwC, -, -⟩ := hrowC ρ hρ hL.app_fn.app_arg
  -- `E`'s reading lies in `⟦BVLogicalExpr⟧`
  have hmemB : ∀ BA, denote m.acval env φ d (.const bvLogicalExprName []) = some BA →
      interp V ρ eT ∈ˢ interp V ρ BA := by
    intro BA hBA
    rw [hdB] at hBA
    obtain rfl := Option.some.inj hBA
    obtain ⟨tyB, htyB, -, hmB⟩ := hin.const_ty d bvLogicalExprName _ [] hfB (by simp [ConLeche.ConstantInfo.toConstantVal, hlB])
    simp only [ConLeche.ConstantInfo.toConstantVal, htB, hlB] at htyB hmB
    rw [show (Expr.sort (.succ .zero)).instantiateLevelParams [] [] = .sort (.succ .zero) from rfl,
      denote_sort] at htyB
    obtain rfl := Option.some.inj htyB
    have hisB : IsTy (interp V ρ (m.acval bvLogicalExprName (Level.substFn φ [] []))) := by
      have := hmB ρ
      simp only [interp_sort] at this
      exact IsTy_of_mem_univ this
    obtain ⟨hFB, hCB⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa)
      (e := .const bvLogicalExprName []) rfl rfl hΔ
    have heq := hd hFtE hFB (hCE.of_subset hsubE) hCB htEa hdB ρ hρ
      (hLE.of_subset hsubE) (fun l hl => by simp [Expr.fvarLeaves] at hl)
      hwtE.1 (m.acval_wellDenoted _ _ ρ) hwtE.2.ne_pt hisB.ne_pt
    rw [← heq]
    exact hmemE
  -- the reductions, at every quoted assignment
  have hredx : ∀ (x : Std.Tactic.BVDecide.BVExpr.Assignment) (rx fa : Term),
      denote m.acval env φ d (.app (.app (.const bvEvalName []) (quoteAssign x)) E) = some rx →
      WellDenoted V ρ rx → interp V ρ rx ≠ pt →
      denote m.acval env φ d (.const ConLeche.boolFalseName []) = some fa →
      interp V ρ rx = interp V ρ fa := by
    intro x rx fa hrx hwx hnx hfa
    obtain ⟨hqb, hqf⟩ := quoteAssign_closed x
    have hnf : (Expr.app (.app (.const bvEvalName []) (quoteAssign x)) E).hasFvar = false := by
      simp [Expr.hasFvar, hqf, hEf]
    have hbd : (Expr.app (.app (.const bvEvalName []) (quoteAssign x)) E).looseBVarsBounded 0
        = true := by
      simp [Expr.looseBVarsBounded, hqb, hEc]
    obtain ⟨hFx, hCx⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa) hnf hbd hΔ
    obtain ⟨-, -, fa', hfa', hrow⟩ := hred x hFx hCx hrx
    rw [hfa] at hfa'
    obtain rfl := Option.some.inj hfa'
    exact (hrow ρ hρ (fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; exact nomatch hl)
      hwx hnx).2
  have hpowx : ∀ (k : Nat) (pk lk : Term),
      denote m.acval env φ d (pow2E (.lit (.natVal k))) = some pk →
      WellDenoted V ρ pk → interp V ρ pk ≠ pt →
      denote m.acval env φ d (.lit (.natVal (2 ^ k))) = some lk →
      interp V ρ pk = interp V ρ lk := by
    intro k pk lk hpk hwk hnk hlk
    have hnf : (pow2E (.lit (.natVal k))).hasFvar = false := by
      simp [pow2E, Expr.mkAppN, Expr.hasFvar]
    have hbd : (pow2E (.lit (.natVal k))).looseBVarsBounded 0 = true := by
      simp [pow2E, Expr.mkAppN, Expr.looseBVarsBounded]
    obtain ⟨hFk, hCk⟩ := frame_of_not_hasFvar (m := m) (φ := φ) (Δa := Δa) hnf hbd hΔ
    obtain ⟨-, -, lk', hlk', hrow⟩ := hpow k hFk hCk hpk
    rw [hlk] at hlk'
    obtain rfl := Option.some.inj hlk'
    exact (hrow ρ hρ (fun l hl => by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl; exact nomatch hl)
      hwk hnk).2
  obtain ⟨uT', unsT, huT', hunsT, hwU, hUpt, hwTy, hpt⟩ :=
    hin.bv_unsat hpins ρ hEc hEf heT hwE hmemB hredx hpowx
  rw [huT] at huT'
  obtain rfl := Option.some.inj huT'
  rw [hdS] at hunsT
  obtain rfl := Option.some.inj hunsT
  obtain ⟨hw1, hi1⟩ := wd_app_pt hwU hUpt hwE
  obtain ⟨hw2, hi2⟩ := wd_app_pt hw1 hi1 hwC
  obtain ⟨hw3, hi3⟩ := wd_app_pt (a := aT) hw2 hi2 (by rw [haT']; exact m.acval_wellDenoted _ _ ρ)
  exact ⟨hw3, hwTy, by rw [hi3]; exact hpt⟩

/-- The rule's conclusion at its skip form: the skip's type equation
makes the Π-type body at `a` the formula's `Unsat`. -/
theorem Infer.bvUnsat_soundSkip (hin : RulesInputs V m φ) {d : Nat} {E C a tf tE tC body : Expr}
    (hf : InferSemFull m φ d (.app (.app (.const ConLeche.unsatThmName []) E) C) tf)
    (hE : InferSemFull m φ d E tE) (hd : DefEqSem m φ d tE (.const bvLogicalExprName []))
    (hC : InferSemFull m φ d C tC)
    (hskip : ConLeche.bvUnsatSkip env.find? env.findProj? (.app (.app (.const ConLeche.unsatThmName []) E) C) a
      body = true)
    (hred : ∀ x : Std.Tactic.BVDecide.BVExpr.Assignment,
      RedSem m φ d (.app (.app (.const bvEvalName []) (quoteAssign x)) E)
        (.const ConLeche.boolFalseName []))
    (hpow : ∀ k : Nat, RedSem m φ d (pow2E (.lit (.natVal k))) (.lit (.natVal (2 ^ k)))) :
    InferSem m φ .full d (.app (.app (.app (.const ConLeche.unsatThmName []) E) C) a)
      (body.instantiate1 a) := by
  rw [ConLeche.bvUnsatSkip_type hskip]
  exact Infer.bvUnsat_sound hin hf hE hd hC (ConLeche.bvUnsatSkip_hit hskip) hred hpow

end ConLeche.Model.Rules
