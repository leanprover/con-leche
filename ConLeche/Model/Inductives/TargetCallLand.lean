module

public import ConLeche.Model.Inductives.TargetCallWalk
public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Semantics.Tower.FixLeafI
import ConLeche.Semantics.Tower.TowerMk
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The calls' landing kit (lane NESTIND, session 27)

* `holeVal_foldl_mem`, `former_foldl_mem` — an element of a hole value (or
  a recorded member's former) applied to a parameter frame and an index
  spine: the spine fits and the element is in the tuple's (the carrier's)
  component there — off the index telescope the application is empty;
* `wStar_agree` — the rule's valuation seen through the walk's
  substitution agrees off the holes with a walk valuation holding the
  prefix's parameters, the earlier fields and the rule's tail.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level NestCtx NestHole)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Hole values and formers, applied -/

/-- **An element of a hole value applied at the frame's parameters**: its
index spine fits the component's telescope and the element is in the
tuple's component there. -/
theorem holeVal_foldl_mem {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}
    (hcl : LfpClause acval D) {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat} {ρp Y : Nat → V}
    (hs : Sat V (D.params ψ).reverse ρp) {is : List V} (his : is.length = (D.ids mm ψ).length)
    {y : V} (hy : y ∈ˢ (frameIdx (D.params ψ).length ρp ++ is).foldl app (D.holeVal ψ ρp Y mm)) :
    SpineFit ρp (D.ids mm ψ) is ∧ y ∈ˢ app (Y mm) (tupW (D.u mm ψ) is) := by
  have hpl := hcl.parsLen mm hmm ψ
  have hsP := hcl.parsSat mm hmm ψ ρp hs
  unfold LfpDatum.holeVal at hy
  rcases holeFam_foldl_full (ρ := shiftE (D.pars mm ψ).length 0 ρp)
      (Fs := D.pars mm ψ ++ D.ids mm ψ) (vs := frameIdx (D.params ψ).length ρp ++ is)
      (fun vs => app (Y mm) (tupW (D.u mm ψ) (vs.drop (D.pars mm ψ).length)))
      (by simp [frameIdx, his, hpl]) with ⟨hfit, heq⟩ | he
  · rw [heq] at hy
    obtain ⟨as₁, as₂, hsplit, h1, h2⟩ := spineFit_append_split hfit
    have hl1 : as₁.length = (D.pars mm ψ).length := SpineFit.length_eq h1
    have hlm : (frameIdx (D.params ψ).length ρp).length = as₁.length := by simp [frameIdx, hl1, hpl]
    obtain ⟨hA, rfl⟩ := List.append_inj hsplit hlm
    rw [← hA] at h2
    rw [List.drop_left' (by simp [frameIdx, hpl])] at hy
    have hfr : consList (frameIdx (D.pars mm ψ).length ρp) (shiftE (D.pars mm ψ).length 0 ρp) = ρp :=
      consList_frameIdx _ ρp
    rw [← hpl, hfr] at h2
    exact ⟨h2, hy⟩
  · rw [he] at hy
    exact absurd hy (not_mem_empty y)

/-- **An element of a recorded member's former applied at the block's
parameters**: the index spine fits and the element is in the carrier's
component there. -/
theorem former_foldl_mem {env : Env} {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat}
    {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp) (ρ : Nat → V) {is : List V}
    (his : is.length = (D.ids mm ψ).length) {y : V}
    (hy : y ∈ˢ (frameIdx (D.params ψ).length ρp ++ is).foldl app
      (interp V ρ (mp.base2.acval (D.member mm) ψ))) :
    SpineFit ρp (D.ids mm ψ) is ∧ y ∈ˢ app (D.carrier ψ ρp mm) (tupW (D.u mm ψ) is) := by
  rw [former_app_eq mp hD hmm hs ρ is] at hy
  exact holeVal_foldl_mem (mp.lfpClause_of_mem hD) hmm hs his hy

/-! ## The rule's valuation through the walk's substitution -/

/-- **The substituted rule valuation agrees off the holes with the walk's**
(see the module docstring). -/
theorem wStar_agree {nP hiP i rP B : Nat} {x : Nat → AnnotTerm} {xs fs : List V}
    (hB : B = rP + fs.length) (hxl : xs.length = rP) (hnP : nP ≤ rP) (hi : i ≤ fs.length)
    (hnh : nP ≤ hiP)
    (hxP : ∀ v, v < nP → x v = .bvar (B - 1 - v))
    (hxF : ∀ l, l < i → x (hiP + l) = .bvar (B - 1 - (rP + l)))
    {ρ σW : Nat → V}
    (hpar : ∀ v, v < nP → σW (hiP - 1 - v) = xs.getD v pt)
    (htail : ∀ q, σW (q + hiP) = ρ q) :
    AgreeOff (holeP (hiP + i) nP hiP)
      (substE V (substTau (hiP + i) B x) 0 (consList (xs ++ fs) ρ)) (consList (fs.take i) σW) := by
  intro p hp
  have hlen : (xs ++ fs).length = B := by rw [List.length_append, hxl, hB]
  have hti : (fs.take i).length = i := by rw [List.length_take]; omega
  simp only [substE, Nat.not_lt_zero, if_false, shiftE_zero_zero, Nat.sub_zero, substTau]
  by_cases hpb : p < hiP + i
  · rw [if_pos hpb]
    by_cases hv : hiP + i - 1 - p < nP
    · -- a parameter
      obtain ⟨a, ha⟩ : ∃ a, xs[hiP + i - 1 - p]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hxP _ hv, interp_bvar, consList_apply_lt _ _ _ (by omega), hlen,
        show B - 1 - (B - 1 - (hiP + i - 1 - p)) = hiP + i - 1 - p by omega,
        List.getElem?_append_left (by omega), ha, Option.getD_some]
      rw [show p = (hiP - 1 - (hiP + i - 1 - p)) + (fs.take i).length by omega,
        consList_apply_add, hpar _ hv, List.getD_eq_getElem?_getD, ha, Option.getD_some]
    · -- a field
      have hnh' : ¬ (nP ≤ hiP + i - 1 - p ∧ hiP + i - 1 - p < hiP) := fun h => hp ⟨hpb, h⟩
      have hl : hiP + i - 1 - p - hiP < i := by omega
      obtain ⟨a, ha⟩ : ∃ a, fs[hiP + i - 1 - p - hiP]? = some a :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [show hiP + i - 1 - p = hiP + (hiP + i - 1 - p - hiP) by omega, hxF _ hl, interp_bvar,
        consList_apply_lt _ _ _ (by omega), hlen,
        show B - 1 - (B - 1 - (rP + (hiP + i - 1 - p - hiP))) = rP + (hiP + i - 1 - p - hiP) by
          omega, List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left, ha,
        Option.getD_some, consList_apply_lt _ _ _ (by omega), hti,
        List.getElem?_take_of_lt (by omega),
        show i - 1 - p = hiP + i - 1 - p - hiP by omega, ha, Option.getD_some]
  · rw [if_neg hpb, interp_bvar, show p - (hiP + i) + B = (p - (hiP + i)) + (xs ++ fs).length by
      omega, consList_apply_add]
    rw [show p = (p - (hiP + i) + hiP) + (fs.take i).length by omega, consList_apply_add, htail]
    congr 1
    omega

end ConLeche.Model
