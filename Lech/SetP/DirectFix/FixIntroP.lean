import Lech.SetP.DirectSum.SumIntroP
import Lech.Semantics.Tower.FixRecI

/-!
# The recursive recursor leaf's bit validity (task #188)

The sum route's validity kit (`SumIntroP.lean`) extended by the
inductive-hypothesis arguments of the case split
(`caseRecAVI`, `Lech/Semantics/Tower/FixCaseI.lean`): an ih argument
applies the unfolded function to the block's variables, the field's
index expressions moved to the payload frame (`substProj`) and the
payload's projection; its validity is the index expressions' at the
projections — which fit the constructor's fields.  Then the recursor
body, the one-step unfolding, the fixed-point sigma and the selected
fixed point (`fixSelAVI`) are valid.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Substitution of the payload's projections -/

/-- `substProj` preserves bit validity: the substituted term is valid
exactly when the original is at the projections' frame. -/
theorem AnnotValidV_substProj (σ : Nat → V) (y : V) :
    ∀ (i : Nat) (e : AVExpr),
      AnnotValidV V (cons y σ) (substProj i e) ↔
        AnnotValidV V (consList (projList i y) (cons y σ)) e
  | 0, _ => Iff.rfl
  | i + 1, e => by
    show AnnotValidV V (cons y σ) (substProj i (e.inst (projAV i (.bvar i)))) ↔ _
    have hp : AnnotValidV V (consList (projList i y) (cons y σ)) (projAV i (.bvar i)) :=
      projAV_validV (by rw [AnnotValidV_bvar]; trivial)
    rw [AnnotValidV_substProj σ y i, AnnotValidV_inst0 V hp, projAV_interp, interp2_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, consList_snoc', ← projList_snoc]

/-! ## The ih arguments -/

section IhValid

variable {ℓ w nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
  {famAt : List V → V} {ihDoms : Nat → List V → List V} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))} {D : Nat}

/-- The payload of constructor `j`'s fibre projects to a fitting field
spine at the parameter frame. -/
theorem fibre_projList_fit (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    {j : Nat} (hj : j < Fss.length) {y : V}
    (hy : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j) :
    SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) (projList (Fss.getD j []).length y) := by
  have hjF := hyp.rChain_getElem? hj
  rw [sumFibre_of_getElem? hjF] at hy
  have helim := restricted_member_elim hw
    (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
    (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
    (ρ := ρ₀) (y := y) hy
  rw [liftFields_length] at helim
  exact (spineFit_liftFields (Ids.length + Fss.length + 1)).mp helim.1

/-- **The ih arguments are bit-valid** at a payload of the
constructor's fibre: the index expressions are valid at the fitting
projections. -/
theorem ihArgsI_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hfin : ∀ j i, (tlss.getD j []).getD i [] = [])
    (hfr : RecFrameS D ρ₀ σ) {j : Nat} (hj : j < Fss.length)
    (hEV : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length, ∀ fs : List V,
      SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValidV V (consList (fs.take i) (frP Fss.length Ids.length ρ₀)) E)
    {y : V} (hy : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j) :
    ∀ a ∈ ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length) D j,
      AnnotValidV V (cons y σ) a := by
  have hspP := fibre_projList_fit hyp hw hj hy
  intro a ha
  rw [ihArgsI_fin hfin] at ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  obtain ⟨hik, -⟩ := mem_recIdx.mp hi
  unfold ihArgAV₀
  refine mkAppN_validV trivial fun a ha => ?_
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
      trivial
    · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
      rw [AnnotValidV_substProj, AnnotValidV_liftN]
      have h := shiftE_consList_len (D + Ids.length + Fss.length + 2) (projList i y) (cons y σ)
      rw [projList_length] at h
      rw [h, shiftE_payload hfr]
      have := hEV i hi _ hspP E hE
      rwa [projList_take _ _ _ (Nat.le_of_lt hik)] at this
  · rw [List.mem_singleton] at ha
    subst ha
    exact projAV_validV trivial

/-- Constructor `j`'s branch with ih arguments is bit-valid. -/
theorem fixBase_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hfin : ∀ j i, (tlss.getD j []).getD i [] = []) (hfr : RecFrameS D ρ₀ σ)
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValidV V (consList (fs.take i) (frP Fss.length Ids.length ρ₀)) E)
    (j : Nat) :
    AnnotValidV V σ
      (caseBaseAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
        (fun j => (Fss.getD j []).length)
        (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
        Fss.length Ids.length D j) := by
  show AnnotValidV V σ (.lam ℓ _ _)
  rw [AnnotValidV_lam]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [AnnotValidV_liftN, hfr]
    by_cases hj : j < (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).length
    · have hjF : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[j]?
          = some ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      exact towerBodyAV_validV (hv _ (List.mem_of_getElem? hjF))
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact towerBodyAV_validV trivial
  · refine mkAppN_validV trivial fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_validV trivial
    · by_cases hj : j < Fss.length
      · -- the payload is in the fibre
        have hjF := hyp.rChain_getElem? hj
        have hokF : FieldsOkB w ρ₀
            (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
          hyp.hok _ (List.mem_of_getElem? hjF)
        have hy' : y ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j := by
          rw [sumFibre_of_getElem? hjF]
          rw [interp2_liftN, hfr, List.getD_eq_getElem?_getD, hjF, Option.getD_some,
            towerBodyAV_interp (hokF.toBound)] at hy
          exact hy
        exact ihArgsI_validV hyp hw hfin hfr hj (hEV j hj) hy' a ha
      · -- no ih arguments at a stage past the constructors
        exfalso
        have h0 : (Fss.getD j []).length = 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        unfold ihArgsI at ha
        simp only [h0, recIdx, List.range_zero, List.filter_nil, List.map_nil] at ha
        exact (List.not_mem_nil ha).elim

/-- **The case recursor with ih arguments is bit-valid.** -/
theorem fixCaseRec_validV (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms) (hw : w ≠ 0)
    (hfin : ∀ j i, (tlss.getD j []).getD i [] = [])
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValidV V (consList (fs.take i) (frP Fss.length Ids.length ρ₀)) E) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {kx : AVExpr},
      RecFrameS D ρ₀ σ → AnnotValidV V σ kx →
      AnnotValidV V σ
        (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (ihArgsI ℓ nP Fss.length Ids.length rss tlss Eiss (fun j => (Fss.getD j []).length))
          Fss.length Ids.length r D j kx)
  | 0, _, _, σ, _, _, _ => by
    show AnnotValidV V σ (.lam ℓ (.const .empty [w]) .prf)
    rw [AnnotValidV_lam]
    exact ⟨trivial, fun _ _ => trivial⟩
  | r + 1, D, j, σ, kx, hfr, hk => by
    refine natRecAV_validV (motive_validV hfr hyp.toRecHypCore hv j)
      (fixBase_validV hyp hw hfin hfr hv hEV j) ?_ hk
    rw [AnnotValidV_lam]
    refine ⟨trivial, fun b _ => ?_⟩
    rw [AnnotValidV_lam]
    refine ⟨motiveBody_validV hfr hyp.toRecHypCore hv j b, fun a _ => ?_⟩
    exact fixCaseRec_validV hyp hw hfin hv hEV r (hfr.step a b) trivial

/-- **The recursor body is bit-valid** at the frame under the K-frame,
both regimes. -/
theorem fixRecBody_validV (hfr : RecFrameS 1 ρ₀ σ) (hyp : RecHypI ℓ w ρ₀ Fss Ess Ids famAt ihDoms)
    (hfin : w ≠ 0 → ∀ j i, (tlss.getD j []).getD i [] = [])
    (hv : SumFieldsValid ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
    (hEV : w ≠ 0 → ∀ j, j < Fss.length → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
      ∀ fs : List V, SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) fs →
      ∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotValidV V (consList (fs.take i) (frP Fss.length Ids.length ρ₀)) E) :
    AnnotValidV V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) := by
  by_cases hw : w = 0
  · subst hw
    rw [fixRecBodyAVI_zero]
    trivial
  · rw [fixRecBodyAVI_pos hw, AnnotValidV_app]
    exact ⟨fixCaseRec_validV hyp hw (hfin hw) hv (hEV hw) Fss.length hfr (major_proj_validV 0 σ),
      major_proj_validV 1 σ⟩

end IhValid

/-! ## The leaf -/

/-- **The recursor leaf is bit-valid**: from the type's validity and the
body's validity under the binder data over every function value. -/
theorem fixSelAVI_validV {ℓ w nP s : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))}
    {rds : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hTy : AnnotValidV V ρ (recTyAV Fss.length Ids.length rds))
    (hbody : ∀ r : V, r ∈ˢ interp2 V ρ (recTyAV Fss.length Ids.length rds) →
      UnderTowerValid (cons r ρ) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) rds) :
    AnnotValidV V ρ (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
  have hstep : AnnotValidV V ρ (fixStepAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
    show AnnotValidV V ρ (.lam s (recTyAV Fss.length Ids.length rds) _)
    rw [AnnotValidV_lam]
    exact ⟨hTy, fun r hr => mkLamsC_validV (hbody r hr)⟩
  have hsig : AnnotValidV V ρ (fixSigAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) := by
    show AnnotValidV V ρ (.app (.app (.const .psigma [s, 0]) (recTyAV Fss.length Ids.length rds))
      (.lam 1 (recTyAV Fss.length Ids.length rds) _))
    simp only [AnnotValidV_app, AnnotValidV_const, AnnotValidV_lam, AnnotValidV_eqE,
      AnnotValidV_bvar, and_true, true_and]
    refine ⟨hTy, hTy, fun r _ => ?_⟩
    rw [AnnotValidV_liftN, shiftE_succ_cons, shiftE_zero_zero]
    exact hstep
  show AnnotValidV V ρ (.proj 0 (.app (.app (.const .choice [s]) _) .prf))
  simp only [AnnotValidV_proj, AnnotValidV_app, AnnotValidV_const, AnnotValidV_prf, and_true,
    true_and]
  exact hsig

end Lech.SetP
