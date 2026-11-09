module

public import InLeanProof.WalksInferBody
import ConLeche.Verify.LooseBVar
import ConLeche.Verify.ProjGuard
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.IndWalksC
/- `Expr.hasLooseBVars` is read through `looseBVarRange` (as in `Ops.lean`). -/
import all Lean.Expr

/-!
# The projection guard's field loop against master's (task #451, lane follow-master)

InLean's guard (`InLean.checkProjGuardI`) is the twin of master's
`checkProjGuard`: the structure's sort (`projGuardSortI`), the constructor's
type at the use's levels with its parameters opened (`constTyAtM`,
`openPisAtFvarsM`), its fields stepped as official `infer_proj` does
(`projGuardRowsGoM`, twin of `projGuardRowsGo`), and the rows' sorts
(`checkGuardRowsI`).  This file has the parameters' opener
(`openPisAtFvarsI_run`, master's pure `openPisAtFvars` at the translation,
read at the final state) and the loop: `projGuardRowsGoI_run`, an answer's
rows read at the final state as master's on the translated telescope.  A field the rest of the telescope does not use is stepped over in
both (`hasLooseBVarI_TrS`: InLean's occurrence test is master's on the
reading), unopened.  Then the rows' sorts (`checkGuardRowsI_run`), the sort
they answer to (`projGuardSortI_run`), the rows at a sort
(`checkProjRowsI_run`, master's `projGuardRows` on the translated entry, whose
rows' scoping is master's `projGuardRows_ws`), and the guard:
**`projGuardSpecI_of`**, `ProjGuardSpecI` from the knot's specs and what the
bodies read of the environment (`EnvWF`, `EnvRelI`, `EnvViewI`), so the knot's
bodies discharge it themselves (`bodiesI_of`).

The proofs are functional (`bind_run`, `pure_run`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## The window query (`hasLooseBVarInC`'s twin) -/

/-- `EO.hasLooseBVarIn`'s test. -/
@[expose] def hlbInF (d w : Nat) (x : Lean.Expr) (k : Nat) : Option Bool :=
  if x.looseBVarRange ≤ d + k then some false else
  match x with
  | .bvar j => some (decide (d + k ≤ j) && decide (j < d + k + w))
  | _ => none

theorem hasLooseBVarIn_eq (e : Lean.Expr) (d w : Nat) (hw : w ≠ 0) :
    EO.hasLooseBVarIn e d w = anySpec (hlbInF d w) e 0 := by
  unfold EO.hasLooseBVarIn
  simp only [beq_iff_eq, hw, ↓reduceIte]
  exact anyNode_spec _ e 0

theorem cl_hasLooseBVarInP_cut {c : ConLeche.Expr} {w n : Nat} (h : c.bvarBound ≤ n) :
    ConLeche.Expr.hasLooseBVarInP w c n = false :=
  ConLeche.Expr.hasLooseBVarInP_cut (by rw [ConLeche.Expr.bvarB_eq]; exact h)

theorem cl_hasLooseBVarInP_unfold {c : ConLeche.Expr} {w n : Nat} (h : ¬ c.bvarBound ≤ n) :
    ConLeche.Expr.hasLooseBVarInP w c n =
      match c with
      | .bvar j => decide (n ≤ j) && decide (j < n + w)
      | .fvar .. | .sort _ | .const .. | .lit _ => false
      | .app f a => ConLeche.Expr.hasLooseBVarInP w f n || ConLeche.Expr.hasLooseBVarInP w a n
      | .lam ty b => ConLeche.Expr.hasLooseBVarInP w ty n || ConLeche.Expr.hasLooseBVarInP w b (n + 1)
      | .forallE ty b =>
        ConLeche.Expr.hasLooseBVarInP w ty n || ConLeche.Expr.hasLooseBVarInP w b (n + 1)
      | .letE t v b =>
        ConLeche.Expr.hasLooseBVarInP w t n || ConLeche.Expr.hasLooseBVarInP w v n ||
          ConLeche.Expr.hasLooseBVarInP w b (n + 1)
      | .proj _ _ s => ConLeche.Expr.hasLooseBVarInP w s n := by
  rw [ConLeche.Expr.hasLooseBVarInP.eq_def]
  simp only [ConLeche.Expr.bvarB_eq, h, ↓reduceIte]
  cases c <;> rfl

/-- **InLean's window query reads as con-leche's** on a term in range (at
binder offset `k`). -/
theorem hasLooseBVarIn_toExpr {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv) (d w : Nat) :
    ∀ (e : Lean.Expr), Expr.RangeOk e → ∀ (k : Nat) (c : ConLeche.Expr), toExpr fv e = some c →
      anySpec (hlbInF d w) e k = ConLeche.Expr.hasLooseBVarInP w c (d + k) := by
  intro e
  induction e with
  | app g a ihg iha =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.app g a).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.app g a) k = none := by simp [hlbInF, hcut]
      have hc' := hcut
      rw [looseBVarRange_toExpr hfv hr h] at hc'
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨cg, hg, ca, ha, rfl⟩ := h
      rw [cl_hasLooseBVarInP_unfold hc']
      simp [anySpec, hn, ihg hr.1 k cg hg, iha hr.2 k ca ha]
  | lam n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.lam n t b bi).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.lam n t b bi) k = none := by simp [hlbInF, hcut]
      have hc' := hcut
      rw [looseBVarRange_toExpr hfv hr h] at hc'
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      rw [cl_hasLooseBVarInP_unfold hc']
      simp [anySpec, hn, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, Nat.add_assoc]
  | forallE n t b bi iht ihb =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.forallE n t b bi).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.forallE n t b bi) k = none := by simp [hlbInF, hcut]
      have hc' := hcut
      rw [looseBVarRange_toExpr hfv hr h] at hc'
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cb, hb, rfl⟩ := h
      rw [cl_hasLooseBVarInP_unfold hc']
      simp [anySpec, hn, iht hr.1 k ct ht, ihb hr.2 (k + 1) cb hb, Nat.add_assoc]
  | letE n t v b nd iht ihv ihb =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.letE n t v b nd).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.letE n t v b nd) k = none := by simp [hlbInF, hcut]
      have hc' := hcut
      rw [looseBVarRange_toExpr hfv hr h] at hc'
      simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ct, ht, cv, hv, cb, hb, rfl⟩ := h
      rw [cl_hasLooseBVarInP_unfold hc']
      simp [anySpec, hn, iht hr.1 k ct ht, ihv hr.2.1 k cv hv, ihb hr.2.2 (k + 1) cb hb,
        Nat.add_assoc, Bool.or_assoc]
  | mdata m x ih =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.mdata m x).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.mdata m x) k = none := by simp [hlbInF, hcut]
      simp only [toExpr] at h
      simp [anySpec, hn, ih hr k c h]
  | proj s j x ih =>
    intro hr k c h
    by_cases hcut : (Lean.Expr.proj s j x).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      rw [looseBVarRange_toExpr hfv hr h] at hcut
      exact (cl_hasLooseBVarInP_cut hcut).symm
    · have hn : hlbInF d w (.proj s j x) k = none := by simp [hlbInF, hcut]
      have hc' := hcut
      rw [looseBVarRange_toExpr hfv hr h] at hc'
      simp only [toExpr, Option.map_eq_some_iff] at h
      obtain ⟨cx, hx, rfl⟩ := h
      rw [cl_hasLooseBVarInP_unfold hc']
      simp [anySpec, hn, ih hr k cx hx]
  | bvar j =>
    intro hr k c h
    simp only [toExpr, Option.some.injEq] at h; subst h
    by_cases hcut : (Lean.Expr.bvar j).looseBVarRange ≤ d + k
    · rw [anySpec_some (show hlbInF d w _ k = some false by simp [hlbInF, hcut])]
      have hc' := hcut
      rw [Expr.looseBVarRange_eq hr] at hc'
      simp only [rangeS] at hc'
      exact (cl_hasLooseBVarInP_cut (by simp [ConLeche.Expr.bvarBound]; omega)).symm
    · rw [anySpec_some (show hlbInF d w _ k =
        some (decide (d + k ≤ j) && decide (j < d + k + w)) by simp [hlbInF, hcut])]
      have hc' := hcut
      rw [Expr.looseBVarRange_eq hr] at hc'
      simp only [rangeS] at hc'
      rw [cl_hasLooseBVarInP_unfold (by simp [ConLeche.Expr.bvarBound]; omega)]
  | mvar m => intro _ k c h; simp [toExpr] at h
  | fvar id =>
    intro hr k c h
    obtain ⟨_, _, rfl⟩ := hfv id c h
    rw [anySpec_some (show hlbInF d w _ k = some false by
      simp [hlbInF, Expr.looseBVarRange_eq hr, rangeS])]
    exact (cl_hasLooseBVarInP_cut (by simp [ConLeche.Expr.bvarBound])).symm
  | sort u =>
    intro hr k c h
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    rw [anySpec_some (show hlbInF d w _ k = some false by
      simp [hlbInF, Expr.looseBVarRange_eq hr, rangeS])]
    exact (cl_hasLooseBVarInP_cut (by simp [ConLeche.Expr.bvarBound])).symm
  | const n us =>
    intro hr k c h
    simp only [toExpr, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
    rw [anySpec_some (show hlbInF d w _ k = some false by
      simp [hlbInF, Expr.looseBVarRange_eq hr, rangeS])]
    exact (cl_hasLooseBVarInP_cut (by simp [ConLeche.Expr.bvarBound])).symm
  | lit l =>
    intro hr k c h
    simp only [toExpr, Option.some.injEq] at h; subst h
    rw [anySpec_some (show hlbInF d w _ k = some false by
      simp [hlbInF, Expr.looseBVarRange_eq hr, rangeS])]
    exact (cl_hasLooseBVarInP_cut (by simp [ConLeche.Expr.bvarBound])).symm

/-- **`EO.hasLooseBVarIn` reads as master's `hasLooseBVarInC`.** -/
theorem toExpr_hasLooseBVarIn {fv : FVarId → Option ConLeche.Expr} (hfv : FVarsOnly fv)
    {e : Lean.Expr} {c : ConLeche.Expr} (hr : Expr.RangeOk e) (h : toExpr fv e = some c) (d w : Nat) :
    EO.hasLooseBVarIn e d w = ConLeche.Expr.hasLooseBVarInC d w c := by
  rw [ConLeche.Cached.Expr.hasLooseBVarInC_spec]
  by_cases hw : w = 0
  · subst hw
    rw [ConLeche.Cached.Expr.hasLooseBVarInP_zero]
    unfold EO.hasLooseBVarIn; rfl
  · rw [hasLooseBVarIn_eq e d w hw, hasLooseBVarIn_toExpr hfv d w e hr 0 c h]; rfl

/-! ## The telescope opener -/

/-- **Opening a telescope at interned variables** (master's `openPisAtFvars` at
the translation): an answer reads, at the final state, as master's on the
translated term. -/
theorem openPisAtFvarsI_run :
    ∀ (n i : Nat) {e : Lean.Expr} {s₀ : InLean.CState} {r : Option (List Lean.Expr × Lean.Expr)}
      {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.openPisAtFvarsM n e i s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ fvs b, r = some (fvs, b) → OkSL s' fvs = true ∧ OkS s' b = true ∧
          ConLeche.openPisAtFvars n (TrS s₀ e) i = some (TrSL s' fvs, TrS s' b)
  | 0, i, e, s₀, r, s', hs, hok, _, h => by
    rw [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro fvs b ⟨⟩
    exact ⟨rfl, hok, rfl⟩
  | n + 1, i, .mdata _ e, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hc ⊢
    exact openPisAtFvarsI_run (n + 1) i hs hok hc h
  | n + 1, i, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.openPisAtFvarsM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    obtain ⟨x, s₂, hx, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs i hok.1 hc.1) x s₂ hx
    obtain ⟨r', s₃, hr, h⟩ := bind_run h
    have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
    have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
    have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
    have hTI : TrS s₂ (body.inst1I x) =
        (TrS s₀ body).instantiate1 (.fvar i (TrS s₀ dom)) 0 := by
      rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht₂ hok.2]
    obtain ⟨hs₃, ht₃, hR⟩ := openPisAtFvarsI_run n (i + 1) hs₂ hokI
      (by rw [hTI]; exact lbb_instantiate1 rfl hc.2) hr
    have ht23 : TabLe s₀ s₃ := ht₂.trans ht₃
    cases r' with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₃, ht23, by rintro _ _ ⟨⟩⟩
    | some q =>
      obtain ⟨fvs', b'⟩ := q
      obtain ⟨rfl, rfl⟩ := pure_run h
      refine ⟨hs₃, ht23, ?_⟩
      rintro fvs b ⟨⟩
      obtain ⟨hokf, hokb, hm⟩ := hR fvs' b' rfl
      refine ⟨?_, hokb, ?_⟩
      · simp only [OkSL, List.all_cons, Bool.and_eq_true]
        exact ⟨okS_of_tabLe ht₃ hokx, hokf⟩
      · rw [TrS_forallE]
        simp only [ConLeche.openPisAtFvars]
        rw [← hTI, hm]
        simp only [TrSL, List.map_cons, TrS_of_tabLe ht₃ hokx, htx]
  | _ + 1, _, .bvar _, _, _, _, hs, _, _, h | _ + 1, _, .fvar _, _, _, _, hs, _, _, h
  | _ + 1, _, .mvar _, _, _, _, hs, _, _, h | _ + 1, _, .sort _, _, _, _, hs, _, _, h
  | _ + 1, _, .const _ _, _, _, _, hs, _, _, h | _ + 1, _, .app _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lam _ _ _ _, _, _, _, hs, _, _, h | _ + 1, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lit _, _, _, _, hs, _, _, h | _ + 1, _, .proj _ _ _, _, _, _, hs, _, _, h => by
    simp only [InLean.openPisAtFvarsM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by rintro _ _ ⟨⟩⟩

/-- InLean's occurrence test on a term with a reading is master's on the
reading. -/
theorem hasLooseBVarI_TrS {s : InLean.CState} {e : Lean.Expr} (h : OkS s e = true) (i : Nat) :
    e.hasLooseBVarI i = (TrS s e).hasLooseBVarB i := by
  rw [ConLeche.Expr.hasLooseBVarB_eq]
  exact toExpr_hasLooseBVar (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS h) (TransS_of_ok h) i

/-- **The guard's field loop at interned variables** (master's
`projGuardRowsGo` at the translation): an answer's rows read, at the final
state, as master's on the translated telescope. -/
theorem projGuardRowsGoI_run :
    ∀ (k d : Nat) {e : Lean.Expr} {s₀ : InLean.CState}
      {r : Option (List (Nat × Lean.Expr))} {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → (TrS s₀ e).looseBVarsBounded 0 = true →
      InLean.projGuardRowsGoM k d e s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ rows, r = some rows →
          (∀ p ∈ rows, OkS s' p.2 = true ∧ (TrS s' p.2).looseBVarsBounded 0 = true) ∧
          ConLeche.projGuardRowsGo k d (TrS s₀ e) = some (rows.map fun p => (p.1, TrS s' p.2))
  | k, d, .mdata _ e, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hc ⊢
    exact projGuardRowsGoI_run k d hs hok hc h
  | 0, d, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro rows ⟨⟩
    refine ⟨by simp [hok.1, hc.1], ?_⟩
    rw [TrS_forallE]
    rfl
  | k + 1, d, .forallE nm dom body bi, s₀, r, s', hs, hok, hc, h => by
    rw [InLean.projGuardRowsGoM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, lbb_forallE, Bool.and_eq_true] at hc
    have hlb := hasLooseBVarI_TrS hok.2 0
    rw [TrS_forallE]
    cases hb : body.hasLooseBVarI 0
    · -- stepped over, unopened
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      have hc0 : (TrS s₀ body).looseBVarsBounded 0 = true :=
        ConLeche.Expr.looseBVarsBounded_of_not_hasLooseBVar _ hc.2
          (by rw [← ConLeche.Expr.hasLooseBVarB_eq, ← hlb, hb])
      obtain ⟨hs', ht', hR⟩ := projGuardRowsGoI_run k (d + 1) hs hok.2 hc0 h
      refine ⟨hs', ht', fun rows hr => ?_⟩
      obtain ⟨hokr, hm⟩ := hR rows hr
      refine ⟨hokr, ?_⟩
      simp only [ConLeche.projGuardRowsGo, ← hlb, hb, Bool.false_eq_true, ↓reduceIte]
      exact hm
    · -- a row, opened at its variable
      simp only [hb, ↓reduceIte] at h
      obtain ⟨x, s₂, hx, h⟩ := bind_run h
      obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs d hok.1 hc.1) x s₂ hx
      obtain ⟨r', s₃, hr, h⟩ := bind_run h
      have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
      have hcx : (TrS s₂ x).looseBVarsBounded 0 = true := by rw [htx]; rfl
      have hokI : OkS s₂ (body.inst1I x) = true := OkS_inst1 hb₂ hokx hcx
      have hTI : TrS s₂ (body.inst1I x) =
          (TrS s₀ body).instantiate1 (.fvar d (TrS s₀ dom)) 0 := by
        rw [inst1I_eq, TrS_inst1_eq hb₂ hokx hcx, htx, TrS_of_tabLe ht₂ hok.2]
      obtain ⟨hs₃, ht₃, hR⟩ := projGuardRowsGoI_run k (d + 1) hs₂ hokI
        (by rw [hTI]; exact lbb_instantiate1 rfl hc.2) hr
      have ht23 : TabLe s₀ s₃ := ht₂.trans ht₃
      cases r' with
      | none =>
        obtain ⟨rfl, rfl⟩ := pure_run h
        exact ⟨hs₃, ht23, by rintro _ ⟨⟩⟩
      | some rows' =>
        obtain ⟨rfl, rfl⟩ := pure_run h
        refine ⟨hs₃, ht23, ?_⟩
        rintro rows ⟨⟩
        obtain ⟨hokr, hm⟩ := hR rows' rfl
        refine ⟨?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact ⟨okS_of_tabLe ht23 hok.1, by rw [TrS_of_tabLe ht23 hok.1]; exact hc.1⟩
          · exact hokr p hp
        · simp only [ConLeche.projGuardRowsGo, ← hlb, hb, ↓reduceIte]
          rw [← hTI, hm]
          simp only [List.map_cons, TrS_of_tabLe ht23 hok.1]
  | 0, _, .bvar _, _, _, _, hs, _, _, h | 0, _, .fvar _, _, _, _, hs, _, _, h
  | 0, _, .mvar _, _, _, _, hs, _, _, h | 0, _, .sort _, _, _, _, hs, _, _, h
  | 0, _, .const _ _, _, _, _, hs, _, _, h | 0, _, .app _ _, _, _, _, hs, _, _, h
  | 0, _, .lam _ _ _ _, _, _, _, hs, _, _, h | 0, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | 0, _, .lit _, _, _, _, hs, _, _, h | 0, _, .proj _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .bvar _, _, _, _, hs, _, _, h | _ + 1, _, .fvar _, _, _, _, hs, _, _, h
  | _ + 1, _, .mvar _, _, _, _, hs, _, _, h | _ + 1, _, .sort _, _, _, _, hs, _, _, h
  | _ + 1, _, .const _ _, _, _, _, hs, _, _, h | _ + 1, _, .app _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lam _ _ _ _, _, _, _, hs, _, _, h | _ + 1, _, .letE _ _ _ _ _, _, _, _, hs, _, _, h
  | _ + 1, _, .lit _, _, _, _, hs, _, _, h | _ + 1, _, .proj _ _ _, _, _, _, hs, _, _, h => by
    simp only [InLean.projGuardRowsGoM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by rintro _ ⟨⟩⟩

/-! ## The rows' sorts -/

variable {r : InLean.CoreFnsI}

/-- **The rows of a projection's guard** (`checkGuardRowsC_spec`'s twin): each
row's domain read at the starting state, master's rows on the readings. -/
theorem checkGuardRowsI_run (ih : KnotSpecI mode eager env r) {g : Level} (hg : okL g = true) :
    ∀ (rows : List (Nat × Lean.Expr)) {s₀ s' : InLean.CState} {v : Unit},
      CSOKI mode eager env s₀ →
      (∀ p ∈ rows, OkS s₀ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₀ p.2) ∧
        (TrS s₀ p.2).looseBVarsBounded 0 = true) →
      InLean.checkGuardRowsI r.inferIO r.whnf g rows s₀ = .ok (v, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkGuardRows (ConLeche.fueledFns mode eager env).inferIO
          (ConLeche.fueledFns mode eager env).whnf (trL g)
          (rows.map fun p => (p.1, TrS s₀ p.2))) ()
  | [], s₀, s', v, hs, _, h => by
    rw [InLean.checkGuardRowsI] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | (d, dom) :: rest, s₀, s', v, hs, hrows, h => by
    obtain ⟨hok, hw, hc⟩ := hrows _ List.mem_cons_self
    rw [InLean.checkGuardRowsI] at h
    obtain ⟨t, s₁, hti, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokt, hRt, hwt, hct⟩ := tripleI_iff_run.1 (ih.inferIO hs hok hw hc) t s₁ hti
    obtain ⟨w, s₂, hwi, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokw, hRw, -, -⟩ := tripleI_iff_run.1 (ih.whnf hs₁ hokt hwt hct) w s₂ hwi
    have ht12 : TabLe s₀ s₂ := ht₁.trans ht₂
    generalize hx : EO.stripTop w = x at h
    have hT : TrS s₂ w = TrS s₂ x := by rw [← hx, TrS_stripTop]
    have hokx : OkS s₂ x = true := by rw [← hx, OkS_stripTop]; exact hokw
    cases x with
    | sort u =>
      simp only at h
      have hu : okL u = true := by
        simp only [OkS_sort, okLv, Bool.and_eq_true] at hokx; exact hokx.1
      cases hz : InLean.Lvl.zeroWhereZero g u
      · simp only [hz] at h
        obtain ⟨_, _, h1, _⟩ := bind_run h
        exact (throw_run h1).elim
      · simp only [hz] at h
        have hrest : ∀ p ∈ rest, OkS s₂ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₂ p.2) ∧
            (TrS s₂ p.2).looseBVarsBounded 0 = true := by
          intro p hp
          obtain ⟨h1, h2, h3⟩ := hrows p (List.mem_cons_of_mem _ hp)
          rw [TrS_of_tabLe ht12 h1]
          exact ⟨okS_of_tabLe ht12 h1, h2, h3⟩
        obtain ⟨hs', ht', hR⟩ := checkGuardRowsI_run ih hg rest hs₂ hrest h
        have hmap : (rest.map fun p => (p.1, TrS s₂ p.2)) = rest.map fun p => (p.1, TrS s₀ p.2) := by
          apply List.map_congr_left
          intro p hp
          rw [TrS_of_tabLe ht12 (hrows p (List.mem_cons_of_mem _ hp)).1]
        rw [hmap] at hR
        refine ⟨hs', ht12.trans ht', ?_⟩
        simp only [List.map_cons]
        rw [ConLeche.checkGuardRows]
        refine Runs.bind hRt (Runs.bind hRw ?_)
        rw [hT, TrS_sort]
        simp only [zeroWhereZero_trL hg hu, hz]
        first | exact hR | exact Runs.bind (Runs.pure ()) hR
    | mdata _ _ => exact (stripTop_ne_mdata hx).elim
    | _ => exact (throw_run h).elim

/-! ## The sort the rows answer to -/

theorem isAlwaysZero_trL (u : Level) :
    ConLeche.Level.isAlwaysZero (trL u) = InLean.Lvl.isAlwaysZero u := by
  unfold ConLeche.Level.isAlwaysZero InLean.Lvl.isAlwaysZero
  rw [← trPW_zeronessOf]
  cases InLean.Lvl.zeronessOf u with
  | never => rfl
  | ifAllZero ps => cases ps <;> rfl

/-- **The sort a projection's rows answer to** (`projGuardSortC_spec`'s twin):
the structure is a stored record, closed. -/
theorem projGuardSortI_run (ih : KnotSpecI mode eager env r) {cvT : Lean.ConstantVal}
    {ccvT : ConLeche.ConstantVal} (hcv : CVRel cvT ccvT) (hcl : ccvT.type.hasFvar = false)
    (hlbb : ccvT.type.looseBVarsBounded 0 = true) (caps : InLean.IndCaps) {us : List Level}
    (hus : us.all okLv = true) {s₀ s' : InLean.CState} {o : Option Level}
    (hs : CSOKI mode eager env s₀)
    (hr : InLean.projGuardSortI r.whnf cvT caps us s₀ = .ok (o, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ (∀ g, o = some g → okL g = true) ∧
      Runs (ConLeche.projGuardSort (ConLeche.fueledFns mode eager env).whnf ccvT (toCaps caps)
        (us.map trL)) (o.map trL) := by
  have hty : TrS s₀ cvT.type = ccvT.type := hcv.2.2.trS s₀
  have hrs : ConLeche.formerResSort ccvT.type = (InLean.formerResSort cvT.type).map trL := by
    rw [← hty, formerResSort_TrS]
  unfold ConLeche.projGuardSort
  unfold InLean.projGuardSortI at hr
  rw [hrs]
  cases hf : InLean.formerResSort cvT.type with
  | some u =>
    simp only [hf] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    refine ⟨hs, TabLe.refl _, ?_, ?_⟩
    · intro g hg
      cases hz : InLean.Lvl.isAlwaysZero u <;> simp [hz] at hg; subst hg; rfl
    · simp only [Option.map_some, isAlwaysZero_trL]
      cases InLean.Lvl.isAlwaysZero u <;> exact Runs.pure _
  | none =>
    simp only [hf] at hr
    obtain ⟨ty, s₁, hty1, hr⟩ := bind_run hr
    obtain ⟨hs₁, ht₁, hok₁, htr₁⟩ := tripleI_iff_run.1
      (instLevelParamsM_specI hs (hcv.2.2.okS s₀) hcv.2.2.1 hus) ty s₁ hty1
    rw [hty, ← hcv.2.1] at htr₁
    have hw : ConLeche.Expr.WScoped 0 (TrS s₁ ty) := by
      rw [htr₁]; exact ConLeche.Expr.WScoped.of_not_hasFvar
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl)
    have hc : (TrS s₁ ty).looseBVarsBounded 0 = true := by
      rw [htr₁, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hlbb
    obtain ⟨o', s₂, ho, hr⟩ := bind_run hr
    obtain ⟨hs₂, ht₂, hoko, hruno⟩ := tripleI_iff_run.1
      (formerSortLoopI_specI ih (n := caps.nparams + caps.nIdx) hs₁ hok₁ hw hc) o' s₂ ho
    rw [htr₁] at hruno
    simp only [Option.map_none]
    cases o' with
    | none => exact (throw_run hr).elim
    | some u =>
      obtain ⟨rfl, rfl⟩ := pure_run hr
      have hu : okL u = true := by
        simp only [Option.all_some, okLv, Bool.and_eq_true] at hoko; exact hoko.1
      refine ⟨hs₂, ht₁.trans ht₂, ?_, Runs.bind hruno ?_⟩
      · intro g hg
        cases hn : (InLean.Lvl.zeronessOf u).isNever <;> simp [hn] at hg; subst hg; exact hu
      · simp only [Option.map_some]
        rw [← trPW_zeronessOf, trPW_isNever]
        cases (InLean.Lvl.zeronessOf u).isNever <;> exact Runs.pure _

/-! ## The raw opener, the cursor instantiation, the fast case (master's `projGuardRowsC`) -/

/-- **Instantiation at a cursor keeps a term in range** (closed values). -/
theorem RangeOk_instantiateRevAt {e : Lean.Expr} {subst : Array Lean.Expr} (c : Nat)
    (hr : Expr.RangeOk e) (hsr : ∀ j (hj : j < subst.size), Expr.RangeOk subst[j])
    (hcl : ∀ j (hj : j < subst.size), subst[j].looseBVarRange = 0) :
    Expr.RangeOk (EO.instantiateRevAt e subst c) := by
  have hsr' : ∀ j (hj : j < subst.reverse.size), Expr.RangeOk subst.reverse[j] := by
    intro j hj; rw [Array.getElem_reverse]; exact hsr _ _
  have hcl' : ∀ j (hj : j < subst.reverse.size), subst.reverse[j].looseBVarRange = 0 := by
    intro j hj; rw [Array.getElem_reverse]; exact hcl _ _
  unfold EO.instantiateRevAt
  split
  · exact hr
  · rw [mapOff_spec]
    refine RangeOk_mapSpec _ ?_ e c hr
    intro x k r hx h
    by_cases hc : x.looseBVarRange ≤ k
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h; subst h; exact hx
    · cases x with
      | bvar i =>
        simp only [hc, ↓reduceIte] at h
        by_cases hik : i < k
        · simp only [hik, ↓reduceIte, Option.some.injEq] at h; subst h; exact hx
        · by_cases hin : i - k < subst.size
          · simp only [hik, hin, ↓reduceIte, Option.some.injEq] at h; subst h
            rw [getElem!_pos subst _ (by omega), liftLooseBVars_closed (hcl _ _)]
            exact hsr _ _
          · simp only [hik, hin, ↓reduceIte, Option.some.injEq, mkBvar_eq] at h; subst h
            simp only [Expr.RangeOk] at hx ⊢; omega
      | _ => simp [hc] at h

/-- `EO.instantiateRevAt` is the instantiation callback at the reversed values,
from the cursor. -/
theorem instantiateRevAt_eq (e : Lean.Expr) (subst : Array Lean.Expr) (c : Nat) :
    EO.instantiateRevAt e subst c =
      if subst.size == 0 || e.looseBVarRange ≤ c then e else mapSpec (instF subst.reverse) e c := by
  unfold EO.instantiateRevAt
  split
  · rfl
  · rw [mapOff_spec]
    congr 1
    funext x k
    unfold instF
    by_cases hc : x.looseBVarRange ≤ k
    · simp [hc]
    · cases x with
      | bvar i =>
        simp only [hc, ↓reduceIte, Array.size_reverse, mkBvar_eq]
        by_cases hik : i < k
        · simp [hik]
        · by_cases hin : i - k < subst.size
          · simp only [hik, hin, ↓reduceIte]
            rw [getElem!_pos subst.reverse _ (by simpa using hin), Array.getElem_reverse,
              getElem!_pos subst _ (by omega)]
          · simp [hik, hin]
      | _ => simp [hc]

/-- **Instantiation at a cursor, at closed values, reads as con-leche's**
`instantiateList` at the reversed values from that cursor. -/
theorem TrS_instantiateRevAt {s : InLean.CState} {e : Lean.Expr} {acc : Array Lean.Expr}
    (he : OkS s e = true) (hv : OkSL s acc.toList = true) (hcl : AllClosed (TrSL s acc.toList) = true)
    (c : Nat) :
    OkS s (EO.instantiateRevAt e acc c) = true ∧
      TrS s (EO.instantiateRevAt e acc c) = (TrS s e).instantiateList (TrSL s acc.toList).reverse c := by
  have hfv := FVarTable.trans_fvarsOnly (tableOf s)
  have hmem : ∀ x ∈ acc.toList, Expr.RangeOk x ∧ x.looseBVarRange = 0 := by
    intro x hx
    have hok : OkS s x = true := by
      simp only [OkSL, List.all_eq_true] at hv; exact hv x hx
    have hcx : (TrS s x).looseBVarsBounded 0 = true := by
      simp only [AllClosed, TrSL, List.all_eq_true, List.mem_map] at hcl
      exact hcl _ ⟨x, hx, rfl⟩
    refine ⟨RangeOk_of_OkS hok, ?_⟩
    rw [looseBVarRange_toExpr hfv (RangeOk_of_OkS hok) (TransS_of_ok hok)]
    have := ConLeche.Expr.looseBVarsBounded_iff.1 hcx
    omega
  have hr' : Expr.RangeOk (EO.instantiateRevAt e acc c) :=
    RangeOk_instantiateRevAt c (RangeOk_of_OkS he)
      (fun j hj => (hmem _ (Array.getElem_mem_toList hj)).1)
      (fun j hj => (hmem _ (Array.getElem_mem_toList hj)).2)
  have htr : TransS s (EO.instantiateRevAt e acc c) =
      some ((TrS s e).instantiateList (TrSL s acc.toList).reverse c) := by
    rw [instantiateRevAt_eq]
    split
    · rename_i hcut
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcut
      rw [TransS_of_ok he]
      rcases hcut with h0 | hb
      · have : acc.toList = [] := by simpa using h0
        rw [this]; simp [TrSL, ConLeche.Expr.instantiateList_nil]
      · rw [ConLeche.Expr.instantiateList_eq_self]
        have h := looseBVarRange_toExpr hfv (RangeOk_of_OkS he) (TransS_of_ok he)
        exact ConLeche.Expr.looseBVarsBounded_iff.2 (by omega)
    · have hsr := (substReads_of_ok hv hcl).reverse
      exact toExpr_mapSpec_inst hfv hsr e (RangeOk_of_OkS he) c (TrS s e) (TransS_of_ok he)
  exact ok_of_TransS hr' htr

/-- **Opening a telescope with the residual left raw** (master's
`openPisRawGoC` at the translation): an answer's variables and residual read,
at the final state, as master's. -/
theorem openPisRawI_run :
    ∀ (n i : Nat) {acc : Array Lean.Expr} {e : Lean.Expr} {s₀ : InLean.CState}
      {r : Option (Array Lean.Expr × Lean.Expr)} {s' : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ e = true → OkSL s₀ acc.toList = true →
      AllClosed (TrSL s₀ acc.toList) = true →
      ((TrS s₀ e).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true →
      InLean.openPisRawM acc n e i s₀ = .ok (r, s') →
      CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ∀ acc' b, r = some (acc', b) → OkSL s' acc'.toList = true ∧
          AllClosed (TrSL s' acc'.toList) = true ∧ OkS s' b = true ∧
          ((TrS s' b).instantiateList (TrSL s' acc'.toList).reverse).looseBVarsBounded 0 = true ∧
          ∃ fvs, ConLeche.openPisRawGoC (TrSL s₀ acc.toList).reverse n (TrS s₀ e) i =
            some (fvs, (TrSL s' acc'.toList).reverse, TrS s' b)
  | 0, i, acc, e, s₀, r, s', hs, hok, hacc, hcl, hlb, h => by
    rw [InLean.openPisRawM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    rintro acc' b ⟨⟩
    exact ⟨hacc, hcl, hok, hlb, [], rfl⟩
  | n + 1, i, acc, .mdata _ e, s₀, r, s', hs, hok, hacc, hcl, hlb, h => by
    rw [InLean.openPisRawM] at h
    rw [OkS_mdata] at hok
    rw [TrS_mdata] at hlb ⊢
    exact openPisRawI_run (n + 1) i hs hok hacc hcl hlb h
  | n + 1, i, acc, .forallE nm dom body bi, s₀, r, s', hs, hok, hacc, hcl, hlb, h => by
    rw [InLean.openPisRawM] at h
    simp only [OkS_forallE, Bool.and_eq_true] at hok
    rw [TrS_forallE, instList_forallE_eq, lbb_forallE, Bool.and_eq_true] at hlb
    obtain ⟨hod, htd⟩ := TrS_instantiateRevAt (c := 0) hok.1 hacc hcl
    have hrev : EO.instantiateRevAt dom acc 0 = dom.instRevI acc := by
      show _ = EO.instantiateRev dom acc
      rw [instantiateRevAt_eq, instantiateRev_eq, instantiate_eq, Array.size_reverse]
      by_cases h0 : acc.size = 0
      · simp [h0]
      · by_cases hl : dom.looseBVarRange ≤ 0
        · have : dom.hasLooseBVars = false := by simp [Lean.Expr.hasLooseBVars]; omega
          simp [hl, this]
        · have : dom.hasLooseBVars = true := by simp [Lean.Expr.hasLooseBVars]; omega
          simp [h0, hl, this]
    rw [hrev] at hod htd
    obtain ⟨x, s₂, hx, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hokx, htx⟩ := tripleI_iff_run.1
      (mkFVarM_specI hs i hod (by rw [htd]; exact hlb.1)) x s₂ hx
    have hb₂ : OkS s₂ body = true := okS_of_tabLe ht₂ hok.2
    have hacc₂ : OkSL s₂ (acc.push x).toList = true := by
      rw [OkSL_push, okSL_of_tabLe ht₂ hacc, hokx]; rfl
    have hTacc : TrSL s₂ acc.toList = TrSL s₀ acc.toList := TrSL_of_tabLe ht₂ hacc
    have hcl₂ : AllClosed (TrSL s₂ (acc.push x).toList) = true := by
      rw [AllClosed_push, hTacc, hcl, htx]; rfl
    have hV₂ : (TrSL s₂ (acc.push x).toList).reverse = TrS s₂ x :: (TrSL s₀ acc.toList).reverse := by
      rw [TrSL_push_rev, hTacc]
    have hlb₂ : ((TrS s₂ body).instantiateList (TrSL s₂ (acc.push x).toList).reverse).looseBVarsBounded 0
        = true := by
      rw [hV₂, TrS_of_tabLe ht₂ hok.2, htx]
      exact lbb_open_binder rfl hlb.2
    obtain ⟨hs₃, ht₃, hR⟩ := openPisRawI_run n (i + 1) hs₂ hb₂ hacc₂ hcl₂ hlb₂ h
    refine ⟨hs₃, ht₂.trans ht₃, ?_⟩
    intro acc' b hab
    obtain ⟨g1, g2, g3, g4, fvs, hm⟩ := hR acc' b hab
    refine ⟨g1, g2, g3, g4, ?_⟩
    rw [TrS_forallE]
    simp only [ConLeche.openPisRawGoC]
    rw [hV₂, TrS_of_tabLe ht₂ hok.2, htx, htd, ← ConLeche.Expr.instantiateListC_spec] at hm
    rw [hm]
    exact ⟨_, rfl⟩
  | _ + 1, _, _, .bvar _, _, _, _, hs, _, _, _, _, h | _ + 1, _, _, .fvar _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .mvar _, _, _, _, hs, _, _, _, _, h | _ + 1, _, _, .sort _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .const _ _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .app _ _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .lam _ _ _ _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .letE _ _ _ _ _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .lit _, _, _, _, hs, _, _, _, _, h
  | _ + 1, _, _, .proj _ _ _, _, _, _, hs, _, _, _, _, h => by
    simp only [InLean.openPisRawM] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by rintro _ _ ⟨⟩⟩

/-- **The guard's fast case at the translation** (master's `projGuardFastC`):
InLean's answer, read, is master's on the translated raw telescope. -/
theorem projGuardFast_tr {s : InLean.CState} :
    ∀ (k j : Nat) {e : Lean.Expr}, OkS s e = true →
      ConLeche.projGuardFastC k j (TrS s e) = (InLean.projGuardFast k j e).map (TrS s) ∧
      ∀ dom, InLean.projGuardFast k j e = some dom → OkS s dom = true
  | k, j, .mdata _ e, h => by
    rw [OkS_mdata] at h
    rw [TrS_mdata, InLean.projGuardFast]
    exact projGuardFast_tr k j h
  | 0, j, .forallE nm dom body bi, h => by
    have hr := RangeOk_of_OkS h
    have hq := toExpr_hasLooseBVarIn (FVarTable.trans_fvarsOnly (tableOf s)) hr (TransS_of_ok h) 0 j
    simp only [OkS_forallE, Bool.and_eq_true] at h
    simp only [InLean.projGuardFast]
    rw [TrS_forallE] at hq ⊢
    simp only [ConLeche.projGuardFastC, hq]
    split
    · exact ⟨rfl, by intro _ h; cases h⟩
    · exact ⟨rfl, by intro d h'; cases h'; exact h.1⟩
  | k + 1, j, .forallE nm dom body bi, h => by
    simp only [OkS_forallE, Bool.and_eq_true] at h
    have hq := toExpr_hasLooseBVarIn (FVarTable.trans_fvarsOnly (tableOf s)) (RangeOk_of_OkS h.1)
      (TransS_of_ok h.1) 0 j
    simp only [InLean.projGuardFast]
    rw [TrS_forallE]
    simp only [ConLeche.projGuardFastC, hq]
    split
    · exact ⟨rfl, by intro _ h; cases h⟩
    · exact projGuardFast_tr k (j + 1) h.2
  | k, j, .fvar id, _ => by
    refine ⟨?_, by intro _ h; cases k <;> simp [InLean.projGuardFast] at h⟩
    rcases trans_getD_cases s id with ⟨i, ty, h'⟩ | h' <;>
      cases k <;> simp [TrS, trE, h', ConLeche.projGuardFastC, InLean.projGuardFast]
  | 0, j, .bvar _, _ | 0, j, .mvar _, _ | 0, j, .sort _, _
  | 0, j, .const _ _, _ | 0, j, .app _ _, _ | 0, j, .lam _ _ _ _, _ | 0, j, .letE _ _ _ _ _, _
  | 0, j, .lit _, _ | 0, j, .proj _ _ _, _
  | _ + 1, j, .bvar _, _ | _ + 1, j, .mvar _, _ | _ + 1, j, .sort _, _
  | _ + 1, j, .const _ _, _ | _ + 1, j, .app _ _, _ | _ + 1, j, .lam _ _ _ _, _
  | _ + 1, j, .letE _ _ _ _ _, _ | _ + 1, j, .lit _, _ | _ + 1, j, .proj _ _ _, _ => by
    refine ⟨?_, by intro _ h; simp [InLean.projGuardFast] at h⟩
    simp [TrS, trE, ConLeche.projGuardFastC, InLean.projGuardFast]

/-- Master's guard rows (`projGuardRows` after the constructor's type) are its
cached ones (`projGuardRowsC_some`, `projGuardRowsC_none`). -/
theorem projGuardRowsGo_open_eq (nP idx : Nat) (cty : ConLeche.Expr) :
    (match ConLeche.openPisAtFvars nP cty 0 with
      | some (_, r) => ConLeche.projGuardRowsGo idx nP r
      | none => none) = ConLeche.projGuardRowsC nP idx cty := by
  cases h : ConLeche.openPisAtFvars nP cty 0 with
  | none => exact (ConLeche.Cached.projGuardRowsC_none h).symm
  | some q =>
    obtain ⟨fvs, r⟩ := q
    exact (ConLeche.Cached.projGuardRowsC_some h).symm

/-! ## The rows, and the guard -/

variable {fe : InLean.FEnv}

/-- Master's guard loop on a closed telescope answers closed rows. -/
theorem projGuardRowsGo_closed :
    ∀ (k d : Nat) (e : ConLeche.Expr), e.looseBVarsBounded 0 = true →
      ∀ {rows : List (Nat × ConLeche.Expr)}, ConLeche.projGuardRowsGo k d e = some rows →
        ∀ p ∈ rows, p.2.looseBVarsBounded 0 = true
  | 0, d, .forallE dom body, hc, rows, h => by
    simp only [ConLeche.projGuardRowsGo, Option.some.injEq] at h
    subst h
    rw [lbb_forallE, Bool.and_eq_true] at hc
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact hc.1
  | k + 1, d, .forallE dom body, hc, rows, h => by
    rw [lbb_forallE, Bool.and_eq_true] at hc
    simp only [ConLeche.projGuardRowsGo] at h
    split at h
    · cases hr : ConLeche.projGuardRowsGo k (d + 1) (body.instantiate1 (.fvar d dom)) with
      | none => rw [hr] at h; cases h
      | some rows' =>
        rw [hr] at h
        simp only [Option.some.injEq] at h
        subst h
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hc.1
        · exact projGuardRowsGo_closed k (d + 1) _ (lbb_instantiate1 rfl hc.2) hr p hp
    · rename_i hn
      have hn' : body.hasLooseBVarB 0 = false := by simpa using hn
      exact projGuardRowsGo_closed k (d + 1) body
        (ConLeche.Expr.looseBVarsBounded_of_not_hasLooseBVar _ hc.2
          (by rw [← ConLeche.Expr.hasLooseBVarB_eq]; exact hn')) h
  | 0, _, .bvar _, _, _, h | 0, _, .fvar .., _, _, h | 0, _, .sort _, _, _, h
  | 0, _, .const .., _, _, h | 0, _, .app .., _, _, h | 0, _, .lam .., _, _, h
  | 0, _, .letE .., _, _, h | 0, _, .lit _, _, _, h | 0, _, .proj .., _, _, h
  | _ + 1, _, .bvar _, _, _, h | _ + 1, _, .fvar .., _, _, h | _ + 1, _, .sort _, _, _, h
  | _ + 1, _, .const .., _, _, h | _ + 1, _, .app .., _, _, h | _ + 1, _, .lam .., _, _, h
  | _ + 1, _, .letE .., _, _, h | _ + 1, _, .lit _, _, _, h | _ + 1, _, .proj .., _, _, h => by
    simp [ConLeche.projGuardRowsGo] at h

/-- **The rows at a sort** (`projRowsC_spec`'s twin): the constructor's type at
the use's levels, its parameters opened, its fields stepped; master's
`projGuardRows` on the translated entry, then its rows' check. -/
theorem checkProjRowsI_run (ih : KnotSpecI mode eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) {e : InLean.ProjEntry} {ce : ConLeche.ProjEntry}
    (hrel : ProjEntryRel e ce) {us : List Level} (hus : us.all okLv = true) {g : Level}
    (hg : okL g = true) {s₀ s' : InLean.CState} {v : Unit} (hs : CSOKI mode eager env s₀)
    (h : InLean.checkProjRowsI r.inferIO r.whnf fe e us g s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (match ConLeche.projGuardRows env.find? ce (us.map trL) with
        | some rows => ConLeche.checkGuardRows (ConLeche.fueledFns mode eager env).inferIO
            (ConLeche.fueledFns mode eager env).whnf (trL g) rows
        | none => throw (.invalid "projection from a propositional structure must be a proposition"))
        () := by
  obtain ⟨-, hidx, hctor, hnP, -⟩ := hrel
  unfold InLean.checkProjRowsI at h
  cases hf : fe.find? e.ctor with
  | none => rw [hf] at h; exact (throw_run h).elim
  | some ci =>
    rw [hf] at h
    simp only at h
    obtain ⟨cci, cty, hL, -, -, -, -, -⟩ := hfe.ty e.ctor ci hf
    have hwf := henv.consts _ (ConLeche.Env.find?_mem hL)
    have hct : ConLeche.Cached.constTyOf env (toName e.ctor) (us.map trL) =
        cci.toConstantVal.type.instantiateLevelParams cci.toConstantVal.levelParams
          (us.map trL) := by
      simp only [ConLeche.Cached.constTyOf, hL]
    obtain ⟨t, s₁, htc, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokt, htrt⟩ :=
      tripleI_iff_run.1 (constTyAtM_specI hfe hs e.ctor hus) t s₁ htc
    rw [hct] at htrt
    have hlbt : (TrS s₁ t).looseBVarsBounded 0 = true := by
      rw [htrt, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
    -- master's rows are its cached ones
    have hpgC : ConLeche.projGuardRows env.find? ce (us.map trL) =
        ConLeche.projGuardRowsC e.numParams e.idx (TrS s₁ t) := by
      unfold ConLeche.projGuardRows
      rw [hctor, hL]
      simp only
      rw [← htrt, hnP, hidx]
      exact projGuardRowsGo_open_eq _ _ _
    rw [hpgC]
    -- the raw opener
    obtain ⟨o, s₂, ho, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hR⟩ := openPisRawI_run (acc := #[]) e.numParams 0 hs₁ hokt (OkSL_empty _)
      (AllClosed_empty _) (by rw [TrSL_empty_rev, ConLeche.Expr.instantiateList_nil]; exact hlbt) ho
    cases o with
    | none => exact (throw_run h).elim
    | some q =>
      obtain ⟨acc, b⟩ := q
      obtain ⟨hacc, hcl, hokb, hlbb, fvs, hm⟩ := hR acc b rfl
      rw [TrSL_empty_rev] at hm
      have hfacts_of : ∀ (rows : List (Nat × Lean.Expr)) (crows : List (Nat × ConLeche.Expr)),
          ConLeche.projGuardRowsC e.numParams e.idx (TrS s₁ t) = some crows →
          crows = rows.map (fun p => (p.1, TrS s₂ p.2)) →
          (∀ p ∈ rows, OkS s₂ p.2 = true ∧ (TrS s₂ p.2).looseBVarsBounded 0 = true) →
          ∀ p ∈ rows, OkS s₂ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₂ p.2) ∧
            (TrS s₂ p.2).looseBVarsBounded 0 = true := by
        intro rows crows hc hcr hok p hp
        have hws := ConLeche.projGuardRows_ws
          (fun ci' hc' => (henv.consts _ (ConLeche.Env.find?_mem hc')).1) (hpgC.trans hc)
        rw [hcr] at hws
        exact ⟨(hok p hp).1, hws _ (List.mem_map_of_mem hp), (hok p hp).2⟩
      have hraw : ConLeche.openPisRawGoC [] e.numParams (TrS s₁ t) 0 =
          some (fvs, (TrSL s₂ acc.toList).reverse, TrS s₂ b) := hm
      obtain ⟨hfq, hfok⟩ := projGuardFast_tr (s := s₂) e.idx 0 hokb
      simp only at h
      cases hq : InLean.projGuardFast e.idx 0 b with
      | some dom =>
        rw [hq] at h hfq
        simp only at h
        have hokd := hfok dom hq
        obtain ⟨hokr, htrr⟩ := TrS_instantiateRevAt (c := e.idx) hokd hacc hcl
        have hcrows : ConLeche.projGuardRowsC e.numParams e.idx (TrS s₁ t) =
            some [(e.numParams + e.idx, TrS s₂ (EO.instantiateRevAt dom acc e.idx))] := by
          unfold ConLeche.projGuardRowsC
          rw [hraw]
          simp only [hfq, Option.map_some, htrr, ConLeche.Expr.instantiateListC_spec]
        have hrowsOk : ∀ p ∈ [(e.numParams + e.idx, EO.instantiateRevAt dom acc e.idx)],
            OkS s₂ p.2 = true ∧ (TrS s₂ p.2).looseBVarsBounded 0 = true := by
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          refine ⟨hokr, ?_⟩
          -- master's loop on the substituted telescope answers the same row, and its rows are closed
          have hgo : ConLeche.projGuardRowsGo e.idx e.numParams
              ((TrS s₂ b).instantiateList (TrSL s₂ acc.toList).reverse) =
              some [(e.numParams + e.idx, TrS s₂ (EO.instantiateRevAt dom acc e.idx))] := by
            rw [htrr]
            have := ConLeche.Cached.projGuardFastC_rows
              (ConLeche.Cached.openPisRawGoC_fvars [] e.numParams (TrS s₁ t) 0 (by simp) hraw)
              e.idx 0 e.numParams (TrS s₂ b) (by rw [hfq]; rfl)
            simpa using this
          exact projGuardRowsGo_closed _ _ _ hlbb hgo _ (List.mem_singleton_self _)
        have hfacts := hfacts_of _ _ hcrows rfl hrowsOk
        obtain ⟨hs', ht', hRr⟩ := checkGuardRowsI_run ih hg _ hs₂ hfacts h
        refine ⟨hs', ht₁.trans (ht₂.trans ht'), ?_⟩
        rw [hcrows]
        exact hRr
      | none =>
        rw [hq] at h hfq
        simp only at h
        obtain ⟨hokr, htrr⟩ := TrS_instantiateRevAt (c := 0) hokb hacc hcl
        have hrev : EO.instantiateRevAt b acc 0 = b.instRevI acc := by
          show _ = EO.instantiateRev b acc
          rw [instantiateRevAt_eq, instantiateRev_eq, instantiate_eq, Array.size_reverse]
          by_cases h0 : acc.size = 0
          · simp [h0]
          · by_cases hl : b.looseBVarRange ≤ 0
            · have : b.hasLooseBVars = false := by simp [Lean.Expr.hasLooseBVars]; omega
              simp [hl, this]
            · have : b.hasLooseBVars = true := by simp [Lean.Expr.hasLooseBVars]; omega
              simp [h0, hl, this]
        rw [hrev] at hokr htrr
        obtain ⟨o2, s₃, ho2, h⟩ := bind_run h
        obtain ⟨hs₃, ht₃, hR2⟩ := projGuardRowsGoI_run e.idx e.numParams hs₂ hokr
          (by rw [htrr]; exact hlbb) ho2
        cases o2 with
        | none => exact (throw_run h).elim
        | some rows =>
          obtain ⟨hrowsOk, hm2⟩ := hR2 rows rfl
          have hcrows : ConLeche.projGuardRowsC e.numParams e.idx (TrS s₁ t) =
              some (rows.map fun p => (p.1, TrS s₃ p.2)) := by
            unfold ConLeche.projGuardRowsC
            rw [hraw]
            simp only [hfq, Option.map_none, ConLeche.Expr.instantiateListC_spec,
              ConLeche.Cached.projGuardRowsGoC_eq]
            rw [← htrr]
            exact hm2
          have hws := ConLeche.projGuardRows_ws
            (fun ci' hc' => (henv.consts _ (ConLeche.Env.find?_mem hc')).1) (hpgC.trans hcrows)
          have hfacts : ∀ p ∈ rows, OkS s₃ p.2 = true ∧ ConLeche.Expr.WScoped p.1 (TrS s₃ p.2) ∧
              (TrS s₃ p.2).looseBVarsBounded 0 = true := by
            intro p hp
            exact ⟨(hrowsOk p hp).1, hws _ (List.mem_map_of_mem hp), (hrowsOk p hp).2⟩
          obtain ⟨hs', ht', hRr⟩ := checkGuardRowsI_run ih hg rows hs₃ hfacts h
          refine ⟨hs', ht₁.trans (ht₂.trans (ht₃.trans ht')), ?_⟩
          rw [hcrows]
          exact hRr

/-- **The projection guard's spec, proved** (`checkProjGuardC_spec`'s twin):
from the knot's specs, the environment's well-formedness, the relation and
the former view. -/
theorem projGuardSpecI_of (ih : KnotSpecI .verified eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hview : EnvViewI fe env) : ProjGuardSpecI eager env r fe := by
  intro e ce us s₀ hs hrel hus
  refine tripleI_iff_run.2 fun v s' h => ?_
  unfold InLean.checkProjGuardI at h
  unfold ConLeche.checkProjGuard
  rw [hrel.1]
  cases hv : fe.indView? e.structName with
  | none => rw [hv] at h; exact (throw_run h).elim
  | some p =>
    obtain ⟨cvT, caps⟩ := p
    rw [hv] at h
    simp only at h
    obtain ⟨ccv, hcv, hL⟩ := hview.ind _ _ _ hv
    rw [hL]
    simp only
    have hwf := henv.consts _ (ConLeche.Env.find?_mem hL)
    obtain ⟨o, s₁, ho, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hog, hRo⟩ := projGuardSortI_run ih hcv hwf.1 hwf.2.2.2.1 caps hus hs ho
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₁, ht₁, Runs.bind hRo (Runs.pure ())⟩
    | some g =>
      simp only at h
      obtain ⟨hs', ht', hR⟩ := checkProjRowsI_run ih henv hfe hrel hus (hog g rfl) hs₁ h
      exact ⟨hs', ht₁.trans ht', Runs.bind hRo hR⟩

end InLeanProof
