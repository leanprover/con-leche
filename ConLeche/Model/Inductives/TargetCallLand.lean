module

import ConLeche.Model.Env.LfpFormer
import ConLeche.Model.Env.LfpAcc
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Denote.Lemmas
public import ConLeche.Model.Reading.SubstFvars
public import ConLeche.Model.Inductives.NestPosMono

public section

/-!
# The calls' landing kit

* `holeVal_foldl_mem`, `former_foldl_mem` — an element of a hole value
  applied to an index spine (or a recorded member's former applied to a
  parameter frame and an index spine): the spine fits and the element is in the tuple's (the carrier's)
  component there — off the index telescope the application is empty;
* `wStar_agree` — the rule's valuation seen through the walk's
  substitution agrees off the holes with a walk valuation holding the
  prefix's parameters, the earlier fields and the rule's tail.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level NestCtx NestHole)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Hole values and formers, applied -/

/-- **A tower applied off its fit where every fitting prefix extends to a
fitting spine is not the point**: no level along the spine is the point
(each has a fitting continuation and leaves never the point at a fit),
so off the fit a graph is applied off its domain, giving `∅`. -/
theorem holeFam_foldl_ne_pt :
    ∀ {ρ : Nat → V} {Fs : List Term} {vs : List V} {g : List V → V},
      (∀ ws, SpineFit ρ Fs ws → g ws ≠ pt) → vs.length = Fs.length →
      (∀ k, SpineFit ρ (Fs.take k) (vs.take k) →
        ∃ ws, SpineFit ρ Fs ws ∧ ws.take k = vs.take k) →
      vs.foldl app (holeFam ρ Fs g) ≠ pt
  | _, [], [], _, hg, _, _ => hg [] trivial
  | _, [], _ :: _, _, _, h, _ => by simp at h
  | _, _ :: _, [], _, _, h, _ => by simp at h
  | ρ, F :: Fs, a :: vs, g, hg, hlen, hext => by
    show vs.foldl app (app (lamV (interp V ρ F) _) a) ≠ pt
    obtain ⟨ws, hws, -⟩ := hext 0 trivial
    obtain ⟨w0, ws', rfl⟩ : ∃ w0 ws', ws = w0 :: ws' := by
      cases ws with
      | nil => exact hws.elim
      | cons w0 ws' => exact ⟨w0, ws', rfl⟩
    have hlv : lamV (interp V ρ F) (fun x => holeFam (cons x ρ) Fs fun as => g (x :: as)) ≠ pt := by
      refine lamV_ne_pt_of hws.1 fun h0 => ?_
      have h1 := holeFam_app (ρ := cons w0 ρ) (Fs := Fs) (fun as => g (w0 :: as)) hws.2
      rw [h0, foldlApp_pt] at h1
      exact hg (w0 :: ws') hws h1.symm
    by_cases ha : a ∈ˢ interp V ρ F
    · rw [app_lamV ha]
      refine holeFam_foldl_ne_pt (fun ws hws => hg (a :: ws) ⟨ha, hws⟩) (by simpa using hlen)
        fun k hk => ?_
      obtain ⟨ws, hws, htk⟩ := hext (k + 1) ⟨ha, hk⟩
      cases ws with
      | nil => exact hws.elim
      | cons w ws =>
        simp only [List.take_succ_cons, List.cons.injEq] at htk
        obtain ⟨rfl, htk⟩ := htk
        exact ⟨ws, hws.2, htk⟩
    · rw [lamV_eq_graph hlv, app_graph_of_not_mem ha, foldlApp_empty]
      exact pt_ne_empty.symm

/-- A bounded telescope's prefixes are bounded. -/
theorem fieldsBound_take {w : Nat} :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsBound w ρ Fs → ∀ k, FieldsBound w ρ (Fs.take k)
  | [], _, _, k => by rw [List.take_nil]; trivial
  | _ :: _, _, _, 0 => trivial
  | _ :: _, _, h, k + 1 => ⟨h.1, fun a ha => fieldsBound_take (h.2 a ha) k⟩

/-- **A spine whose tuple lies in the index set extends every fitting
prefix**: above `0` the tuple is the spine's (`mkTower_inj`), so the
spine fits; at `0` every fitting spine is the points' (the index types
are truth values), and so is every fitting prefix. -/
theorem idx_ext_of_tupW_mem {u : Nat} {ρp : Nat → V} {Ids : List Term} {is : List V}
    (hI : IdxOk u ρp Ids) (hlen : is.length = Ids.length)
    (ht : tupW u is ∈ˢ idxSet u ρp Ids) :
    ∀ k, SpineFit ρp (Ids.take k) (is.take k) →
      ∃ ws, SpineFit ρp Ids ws ∧ ws.take k = is.take k := by
  obtain ⟨ws, hws, heq⟩ := mem_idxSet_elim ht
  intro k hk
  by_cases hu : u = 0
  · subst hu
    refine ⟨ws, hws, ?_⟩
    rw [spineFit_zero_replicate hI.2 hws, spineFit_zero_replicate (fieldsBound_take hI.2 k) hk,
      List.take_replicate, List.length_take]
  · rw [tupW_pos hu, tupW_pos hu] at heq
    obtain rfl := ConLeche.SetTheory.Tower.mkTower_inj (by rw [hlen, hws.length_eq]) heq
    exact ⟨is, hws, rfl⟩

/-- **An element of a hole value applied to an index spine that is not
the point**: the spine fits the component's index telescope and the
element is in the tuple's component there (off the fit the value is `∅`,
or the point where a level of the tower is). -/
theorem holeVal_foldl_mem {D : LfpDatum V} {mm : Nat} {ψ : Name → Nat} {ρp Y : Nat → V}
    {is : List V} (his : is.length = (D.ids mm ψ).length)
    (hne : is.foldl app (D.holeVal ψ ρp Y mm) ≠ pt)
    {y : V} (hy : y ∈ˢ is.foldl app (D.holeVal ψ ρp Y mm)) :
    SpineFit ρp (D.ids mm ψ) is ∧ y ∈ˢ app (Y mm) (tupW (D.u mm ψ) is) := by
  unfold LfpDatum.holeVal at hy hne
  rcases holeFam_foldl_full (ρ := ρp) (Fs := D.ids mm ψ) (vs := is)
      (fun vs => app (Y mm) (tupW (D.u mm ψ) vs)) his with ⟨hfit, heq⟩ | ⟨-, he | he⟩
  · rw [heq] at hy
    exact ⟨hfit, hy⟩
  · rw [he] at hy
    exact absurd hy (not_mem_empty y)
  · exact absurd he hne

/-- **An element of a recorded member's former applied at the block's
parameters**: the index spine fits and the element is in the carrier's
component there. -/
theorem former_foldl_mem {env : Env} (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {ψ : Name → Nat}
    {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp) (ρ : Nat → V) {is : List V}
    (his : is.length = (D.ids mm ψ).length)
    (ht : tupW (D.u mm ψ) is ∈ˢ D.idx ψ ρp mm) {y : V}
    (hy : y ∈ˢ (frameIdx (D.params ψ).length ρp ++ is).foldl app
      (interp V ρ (mp.base2.acval (D.member mm) ψ))) :
    SpineFit ρp (D.ids mm ψ) is ∧ y ∈ˢ app (D.carrier ψ ρp mm) (tupW (D.u mm ψ) is) := by
  rw [List.foldl_append, former_app_eq mp hD hmm hs ρ] at hy
  -- the value is not the point: the spine's tuple lies in the index set, so
  -- every fitting prefix extends, and the carrier's fibres are never the point
  have hcl := mp.lfpClause_of_mem hD
  have hmmN : mm < D.N := Nat.lt_of_lt_of_le hmm hcl.kN
  have hne : is.foldl app (D.holeVal ψ ρp (D.carrier ψ ρp) mm) ≠ pt := by
    unfold LfpDatum.holeVal
    exact holeFam_foldl_ne_pt (fun ws hws => (IsTy_of_mem_strictU (famSpace_app
      ((lfpTuple_mem _ _ _ _ : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) (D.carrier ψ ρp)) mm hmmN)
      (tupW_mem hws))).ne_pt) his
      (idx_ext_of_tupW_mem (hcl.idxOk ψ ρp hs mm hmmN) his ht)
  exact holeVal_foldl_mem his hne hy

/-! ## The rule's valuation through the walk's substitution -/

/-- **The substituted rule valuation agrees off the holes with the walk's**
(see the module docstring). -/
theorem wStar_agree {nP hiP i rP B : Nat} {x : Nat → Term} {xs fs : List V}
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
  simp only [substE, Nat.not_lt_zero, ite_false, shiftE_zero_zero, Nat.sub_zero, substTau]
  by_cases hpb : p < hiP + i
  · rw [ite_eq_left hpb]
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
  · rw [ite_eq_right hpb, interp_bvar, show p - (hiP + i) + B = (p - (hiP + i)) + (xs ++ fs).length by
      omega, consList_apply_add]
    rw [show p = (p - (hiP + i) + hiP) + (fs.take i).length by omega, consList_apply_add, htail]
    congr 1
    omega

end ConLeche.Model
