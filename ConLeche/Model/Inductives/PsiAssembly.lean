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

/-! ## Two Π-towers with the same interpretation -/

/-- **Two Π-towers interpret alike** when their bits agree in zeroness,
their domains read alike under every fitting prefix (of the first) and
their bodies alike at every fitting spine. -/
theorem interp_mkPisAV_congr :
    ∀ {Γ₁ Γ₂ : List (Nat × Nat × AnnotTerm)} {B₁ B₂ : AnnotTerm} {σ₁ σ₂ : Nat → V},
      Γ₁.length = Γ₂.length →
      (∀ (k : Nat) (d₁ d₂ : Nat × Nat × AnnotTerm), Γ₁[k]? = some d₁ → Γ₂[k]? = some d₂ →
        (d₁.2.1 = 0 ↔ d₂.2.1 = 0)) →
      (∀ (k : Nat) (d₁ d₂ : Nat × Nat × AnnotTerm) (as : List V), Γ₁[k]? = some d₁ →
        Γ₂[k]? = some d₂ →
        SpineFit σ₁ ((Γ₁.take k).map (·.2.2)) as →
        interp V (consList as σ₁) d₁.2.2 = interp V (consList as σ₂) d₂.2.2) →
      (∀ as : List V, SpineFit σ₁ (Γ₁.map (·.2.2)) as →
        interp V (consList as σ₁) B₁ = interp V (consList as σ₂) B₂) →
      interp V σ₁ (mkPisAV Γ₁ B₁) = interp V σ₂ (mkPisAV Γ₂ B₂)
  | [], [], B₁, B₂, σ₁, σ₂, _, _, _, hB => by
    have := hB [] trivial
    simp only [consList_nil] at this
    exact this
  | [], _ :: _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _, _ => by simp at hlen
  | d₁ :: Γ₁, d₂ :: Γ₂, B₁, B₂, σ₁, σ₂, hlen, hbits, hdom, hB => by
    simp only [mkPisAV, interp_pi]
    have h0 := hdom 0 d₁ d₂ [] rfl rfl trivial
    simp only [consList_nil] at h0
    rw [piR_congr_bit (hbits 0 d₁ d₂ rfl rfl) (interp V σ₁ d₁.2.2)
      (fun x => interp V (cons x σ₁) (mkPisAV Γ₁ B₁)), h0]
    refine piR_congr fun x hx => ?_
    rw [← h0] at hx
    refine interp_mkPisAV_congr (by simpa using hlen) ?_ ?_ ?_
    · intro k e₁ e₂ h₁ h₂
      exact hbits (k + 1) e₁ e₂ (by simpa using h₁) (by simpa using h₂)
    · intro k e₁ e₂ as h₁ h₂ hsp
      have := hdom (k + 1) e₁ e₂ (x :: as) (by simpa using h₁) (by simpa using h₂)
        (by rw [List.take_succ_cons, List.map_cons]; exact ⟨hx, hsp⟩)
      simpa [consList_cons] using this
    · intro as hsp
      have := hB (x :: as) ⟨hx, hsp⟩
      simpa [consList_cons] using this

/-! ## A recursive field's entry, recursive or reflexive -/

/-- A recursive or reflexive field's entry, in ONE shape: the Π-tower
over its telescope (empty at a recursive one) of the target member's
leaf at the parameter variables and the field's index readings. -/
theorem FixCtorDataI.recRefl_entry {env₀ : Env} {m : EnvModel V env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {tgtOf : Nat → Name}
    {nIdxOf : Nat → Nat}
    (hD : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks
      fvsP xFvs xrest Eiss tss tgtOf nIdxOf)
    (ψ : Name → Nat) {i : Nat} (hi : i ∈ ConLeche.recIdxOf ks) :
    ((ds ψ).getD (nP + i) default).2.2
      = mkPisAV ((tss ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (tgtOf i) ψ)
            (paramBvarsAt nP (nP + i + ((tss ψ).getD i []).length) ++ (Eiss ψ).getD i [])) := by
  obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hi
  rw [hD.ksLen] at hlt
  rcases hk with hk | hk
  · rw [hD.recEntry ψ i hk hlt, hD.tssNone ψ i (by rw [hk]; decide)]
    rfl
  · exact hD.reflEntry ψ i hk hlt

/-! ## The index fit of a recursive field, from its graded entry -/

namespace IndRepData

variable (d : IndRepData V)

/-- **A recursive field's index readings fit the target's index
telescope** at the block's parameter frame, from the field's entry
graded under fitting earlier fields and telescope values: the entry's
body is the target's leaf at the parameters and the readings, the leaf
is a λ-tower (`LeafShape`), so the readings fit its index binders
(`leafSpineFit_full`). -/
theorem idxFit_of_entry {m : EnvModel V env} {ψ : Name → Nat} {ρ₀ : Nat → V}
    {psA : List AnnotTerm} (hpsA : psA.length = d.nP) {tgt : Nat}
    (hFF : d.FormerFacts m ψ tgt) (hLS : d.LeafShape m ψ tgt)
    {σas : List V} {e : Nat} (he : σas.length = e) {Eis : List AnnotTerm}
    (hok : WellDenoted V (consList σas (consList (psA.map (interp V ρ₀)) ρ₀))
      (AnnotTerm.mkAppN (m.acval (d.memberName tgt) ψ) (paramBvarsAt d.nP (d.nP + e) ++ Eis)))
    (hEl : Eis.length = d.nIdxAt tgt) :
    SpineFit (consList (psA.map (interp V ρ₀)) ρ₀) (d.IdsM tgt ψ)
      (Eis.map (interp V (consList σas (consList (psA.map (interp V ρ₀)) ρ₀)))) := by
  obtain ⟨hlen, -, -, -⟩ := hFF
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  have hfit := leafSpineFit_full (nIdx := d.nIdxAt tgt) (w := d.w ψ) hlen
    (m.cval_closedL _ ψ) hLS he hEl hok
  have hshift : (fun j => consList (psA.map (interp V ρ₀)) ρ₀ (j + d.nP)) = ρ₀ := by
    funext j
    rw [← hpsALen, consList_apply_add]
  rw [hshift, range_reverse_map_consList' hpsALen] at hfit
  have hsplit : (d.ppsM tgt ψ).map (·.2.2)
      = ((d.ppsM tgt ψ).take d.nP).map (·.2.2) ++ ((d.ppsM tgt ψ).drop d.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hsplit] at hfit
  obtain ⟨as₁, as₂, heq, h₁, h₂⟩ := spineFit_append_inv hfit
  have hlen₁ : as₁.length = d.nP := by
    have := SpineFit.length_eq h₁
    rw [this, List.length_map, List.length_take, hlen]; omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq (by rw [hlen₁, hpsALen])
  exact h₂

end IndRepData

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
