module

public import ConLeche.Model.Inductives.CopyCtors
import ConLeche.Model.Inductives.FixCtorReads
import ConLeche.Model.Inductives.MutualChains
public section

/-!
# The forward fold `ψ`: the setup ASSEMBLED (task #279 M-B′ step 3j)

`PsiSetup` (`PsiSetup.lean`) is the datum-level bundle under which ψ is
typed and fires.  This module assembles it for ONE mint group of copies
— the container's datum `dJ` at the level assignment the pin names, the
copies' carriers as the targets, the copies' constructors as the heads,
the transports at the copies the group refers to — from:

* the container's representation at the scratch environment (its
  `IndRep`, whence `RecReadAt`, the formers' and constructors' facts);
* the copies' side of the auxiliary datum `d` (the copies are REAL
  members there: their formers' facts, their constructors' readings
  `ctorAtPins_real`, their `NoBVar` facts `noBVar_entries`);
* `CopyIdxRead` for every copy involved (the copy's index telescope is
  the container's at the pin) and `PinRead` for the group's pin;
* the constructor-side record `CopyCtorAsRead` (DESIGN §M.25 (c));
* for each transport's target copy, the term the fold built for it
  earlier along the order, TYPED (`PsiTypedPi`) and graded.

The frames: `ρ₀` below the block's parameters `psA`, `σ` the block's
parameter frame, and the fold's `ps` the pin's readings `DsA` at `σ`.
The copy's carrier is applied to the block's parameters through
`pinsT t = paramBvarsAt d.nP (d.nP + dJ.nP)` — the parameter variables
seen from under the pin's readings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames -/

omit [SetTheory V] in
/-- The parameter variables at depth `D`, lifted by `n`, are the
parameter variables at depth `D + n`. -/
theorem map_liftN_paramBvarsAt' (nP D n : Nat) (h : nP ≤ D) :
    (paramBvarsAt nP D).map (·.liftN n 0) = paramBvarsAt nP (D + n) := by
  simp only [paramBvarsAt, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < nP := List.mem_range.mp hk
  simp only [Function.comp_def, AnnotTerm.liftN_bvar, Nat.not_lt_zero, if_false]
  congr 1
  omega

/-- **The copy's carrier at the block's parameters, read under the pin's
readings and the index values**: the leaf `L` (closed) applied to the
block's parameter values `as` and the indices. -/
theorem interp_famAppAV_aux {L : AnnotTerm} (hL : Term.bvarsBelow 0 L.erase)
    {nP nPJ nIdx : Nat} {Ds is : List V} (hDs : Ds.length = nPJ) (his : is.length = nIdx)
    (σ : Nat → V) :
    interp V (consList is (consList Ds σ))
        (famAppAV L (paramBvarsAt nP (nP + nPJ)) nPJ (nPJ + nIdx) nIdx)
      = ((List.range nP).reverse.map σ ++ is).foldl SetTheory.app (interp V σ L) := by
  subst his
  have h := interp_famAppAV_at (L := L) (fun σ₁ σ₂ => interp_closed (V := V) hL σ₁ σ₂)
    (paramBvarsAt nP (nP + nPJ)) nPJ (extra := []) (is := is) (σ := consList Ds σ)
  simp only [consList_nil, List.length_nil, Nat.add_zero] at h
  rw [h, map_paramBvarsAt_interp (ρp := σ)
      (fun j => by have := consList_apply_add Ds σ j; rw [hDs] at this; exact this),
    interp_closed (V := V) hL _ σ]

/-! ## The copy's target, from its former and the pin -/

namespace IndRepData

variable (d : IndRepData V)

set_option maxHeartbeats 800000 in
/-- **A copy is the target of its container's fold** (`targetOk_copy`
with the roles swapped): over the container datum `dJ` at the pin's
readings `DsA`, member `t`'s target is the COPY `tA`'s carrier at the
block's parameters — its index telescope is the container's at the pin
(`targetOk_real` for the container, first half); at every fitting index
spine the copy's leaf at the parameters and the indices is graded (the
copy's former tower lifted to the index frame) and lies in the
container's sort, which is the copy's (`CopyIdxRead`: the index fit
transfers to the copy's own telescope, the sorts agree). -/
theorem targetOk_psi {μ : CheckMode} (mp : EnvModelM V μ env) {ψ ψ' : Name → Nat} {ρ₀ : Nat → V}
    {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP) {t : Nat} (ht : t < dJ.k)
    (hFFJ : dJ.FormerFacts mp.base2 ψ' t)
    (hpIffJ : ∀ ρ' : Nat → V, Sat V (dJ.params ψ').reverse ρ' ↔
      Sat V (((dJ.ppsM t ψ').take dJ.nP).map (·.2.2)).reverse ρ')
    (hparamsJ : SpineFit (consList (psA.map (interp V ρ₀)) ρ₀) (dJ.params ψ')
      (DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀))))
    (hlev : dJ.elimL.eval ψ' = dJ.w ψ')
    -- the copy: a real member of the auxiliary datum
    {tA : Nat} (hFFA : d.FormerFacts mp.base2 ψ tA)
    (hpIffA : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM tA ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hidx : d.CopyIdxRead ψ tA dJ ψ' t DsA)
    {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
    (hL : L t = mp.base2.acval (d.memberName tA) ψ)
    (hp : pinsT t = paramBvarsAt d.nP (d.nP + dJ.nP)) :
    dJ.TargetOk ψ' (consList (psA.map (interp V ρ₀)) ρ₀) DsA L pinsT t := by
  obtain ⟨hlenA, hbitsA, hmemLA, hokFA⟩ := hFFA
  have hb : pwBit ψ' ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  -- the frames
  generalize hσ : consList (psA.map (interp V ρ₀)) ρ₀ = σ at hparamsJ ⊢
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
  have hclosedA : Term.bvarsBelow 0 (mp.base2.acval (d.memberName tA) ψ).erase :=
    mp.base2.cval_closedL _ ψ
  have hsatA : Sat V (d.params ψ).reverse σ := by
    rw [← hσ]
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparamsA
    rwa [List.append_nil] at h
  -- the parameters fit the copy's own parameter telescope
  have hfitP : SpineFit ρ₀ (((d.ppsM tA ψ).take d.nP).map (·.2.2)) (psA.map (interp V ρ₀)) :=
    spineFit_of_paramsIff hpsALen (by rw [List.length_map, List.length_take, hlenA]; omega) hparamsA
      hpIffA
  refine ⟨(dJ.targetOk_real mp hDsA ht hFFJ hpIffJ hparamsJ hlev).1, ?_⟩
  intro is hsp
  -- the index fit, transferred to the copy's own telescope
  have hspJ : SpineFit (consList (DsA.map (interp V σ)) σ) (dJ.IdsM t ψ') is := by
    rw [dJ.ipss_getD ψ' ht, rebit_map_dom] at hsp
    exact hsp
  have hspA : SpineFit σ (d.IdsM tA ψ) is := (hidx.idxIff σ hsatA is).mpr hspJ
  have hisLen : is.length = d.nIdxAt tA := by
    have := hspA.length_eq
    unfold IndRepData.IdsM at this
    rw [List.length_map, List.length_drop, hlenA] at this
    omega
  have hnIJ : dJ.nIdxs.getD t 0 = is.length := by
    have := hspJ.length_eq
    unfold IndRepData.IdsM at this
    rw [List.length_map, List.length_drop, hFFJ.1] at this
    show dJ.nIdxAt t = is.length
    omega
  -- the full fit into the copy's former
  have hsplit : (d.ppsM tA ψ).map (·.2.2)
      = ((d.ppsM tA ψ).take d.nP).map (·.2.2) ++ ((d.ppsM tA ψ).drop d.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  have hfitAll : SpineFit ρ₀ ((d.ppsM tA ψ).map (·.2.2)) (psA.map (interp V ρ₀) ++ is) := by
    rw [hsplit]
    refine SpineFit.append hfitP ?_
    rw [hσ]; exact hspA
  -- the frame at the indices, and its shift to the base
  have hframe : consList is (consList (DsA.map (interp V σ)) σ)
      = consList (psA.map (interp V ρ₀) ++ DsA.map (interp V σ) ++ is) ρ₀ := by
    rw [← hσ, consList_append, consList_append]
  have hN : d.nP + (dJ.nP + is.length)
      = (psA.map (interp V ρ₀) ++ DsA.map (interp V σ) ++ is).length := by
    rw [List.length_append, List.length_append, hpsALen, hDsLen]; omega
  have hshift : shiftE (d.nP + (dJ.nP + is.length)) 0 (consList is (consList (DsA.map (interp V σ)) σ))
      = ρ₀ := by
    rw [hframe, hN]; exact shiftE_consList _ _
  have hσj : ∀ j, consList is (consList (DsA.map (interp V σ)) σ) (j + (dJ.nP + is.length)) = σ j := by
    intro j
    rw [show j + (dJ.nP + is.length) = j + (DsA.map (interp V σ) ++ is).length from by
        rw [List.length_append, hDsLen],
      ← consList_append, consList_apply_add]
  -- the family at the parameters and the indices, as a term
  rw [hL, hp, hnIJ]
  have hfam : famAppAV (mp.base2.acval (d.memberName tA) ψ) (paramBvarsAt d.nP (d.nP + dJ.nP)) dJ.nP
        (dJ.nP + is.length) is.length
      = AnnotTerm.mkAppN (mp.base2.acval (d.memberName tA) ψ)
          (paramBvarsAt d.nP (d.nP + (dJ.nP + is.length)) ++ fieldBvars is.length) := by
    unfold famAppAV
    rw [show dJ.nP + is.length - dJ.nP = is.length from by omega,
      map_liftN_paramBvarsAt' _ _ _ (Nat.le_add_right _ _), Nat.add_assoc]
  refine ⟨?_, ?_⟩
  · -- graded: the copy's former tower lifted to the index frame
    rw [hfam]
    have hT : WellDenotedV V (consList is (consList (DsA.map (interp V σ)) σ))
        (mkPisAV (liftDoms (d.nP + (dJ.nP + is.length)) 0 (d.ppsM tA ψ))
          ((AnnotTerm.sort (d.w ψ)).liftN (d.nP + (dJ.nP + is.length)) (0 + (d.ppsM tA ψ).length))) := by
      rw [← liftN_mkPisAV, WellDenotedV_liftN, hshift]
      exact hokFA ρ₀
    have hmem : interp V (consList is (consList (DsA.map (interp V σ)) σ))
          (mp.base2.acval (d.memberName tA) ψ)
        ∈ˢ interp V (consList is (consList (DsA.map (interp V σ)) σ))
          (mkPisAV (liftDoms (d.nP + (dJ.nP + is.length)) 0 (d.ppsM tA ψ))
            ((AnnotTerm.sort (d.w ψ)).liftN (d.nP + (dJ.nP + is.length)) (0 + (d.ppsM tA ψ).length))) := by
      rw [← liftN_mkPisAV, interp_liftN, hshift, interp_closed (V := V) hclosedA _ ρ₀]
      exact hmemLA ρ₀
    have hfit : SpineFit (consList is (consList (DsA.map (interp V σ)) σ))
        ((liftDoms (d.nP + (dJ.nP + is.length)) 0 (d.ppsM tA ψ)).map (·.2.2))
        ((paramBvarsAt d.nP (d.nP + (dJ.nP + is.length)) ++ fieldBvars is.length).map
          (interp V (consList is (consList (DsA.map (interp V σ)) σ)))) := by
      rw [spineFit_liftDoms, hshift, List.map_append,
        map_paramBvarsAt_interp (ρp := σ) hσj,
        show fieldBvars is.length
          = (List.range is.length).map (fun k => AnnotTerm.bvar (is.length - 1 - k)) from rfl,
        map_fieldBvars_interp rfl, ← hσ, range_reverse_map_consList' hpsALen]
      exact hfitAll
    exact (wellDenotedV_mkAppN_of_spineFit hT
      ⟨mp.base2.acval_wellDenoted _ ψ _, mp.acval_validV _ ψ _⟩
      (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
          exact ⟨by simp, by simp⟩
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
          exact ⟨by simp, by simp⟩) hmem hfit).1
  · -- in the sort: the copy's, which is the container's
    rw [interp_famAppAV_aux hclosedA hDsLen rfl, ← hσ, range_reverse_map_consList' hpsALen,
      interp_closed (V := V) hclosedA _ ρ₀, hlev, hidx.sort]
    have := mkPisAV_fold_mem (m := 1)
      (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbitsA dd hd)⟩)
      (fun h => absurd h Nat.one_ne_zero) (hmemLA ρ₀) hfitAll
    rw [interp_sort] at this
    exact this

end IndRepData

end ConLeche.Model
