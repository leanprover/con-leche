module

public import ConLeche.Model.Inductives.CopyCtors
import ConLeche.Model.Inductives.FixCtorReads
import ConLeche.Model.Inductives.FixRuleKit
import ConLeche.Model.Inductives.MutualChains
public import ConLeche.Verify.Inductives.NestedOrder
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

/-! ## The choice: the copies' data, the leaves, the heads, the transports -/

/-- **A copy's data** (pin `j`): its container's datum, the member of it
the copy is, the level assignment the pin names, the pin's readings at
the block's parameter frame, and the mint group's base in the pin list
(`j = base + mm`). -/
structure CopyData (V : Type w) where
  dJ : IndRepData V
  mm : Nat
  ψ' : Name → Nat
  DsA : List AnnotTerm
  base : Nat

namespace IndRepData

variable (d : IndRepData V)

/-- The fold's leaves for a group at base `j₀`: member `t`'s copy, the
auxiliary member `k₀ + j₀ + t`. -/
@[expose] def psiL (m : EnvModel V env) (ψ : Name → Nat) (k₀ j₀ : Nat) : Nat → AnnotTerm :=
  fun t => m.acval (d.memberName (k₀ + j₀ + t)) ψ

/-- The block's parameters seen from under a container's `nPJ` pin
readings. -/
@[expose] def psiPinsT (nPJ : Nat) : Nat → List AnnotTerm :=
  fun _ => paramBvarsAt d.nP (d.nP + nPJ)

/-- The target a copy `c` is for the fold that refers to it: its
container's fold target at its pin. -/
@[expose] def psiTgOf (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (c : CopyData V) : AnnotTerm :=
  c.dJ.invTgAV c.ψ' c.DsA (d.psiL m ψ k₀ c.base) (d.psiPinsT c.dJ.nP) c.mm

/-- The head of container constructor `Jc`: the copy's constructor
`auxOf Jc` at the block's parameters, lifted over the pin's readings. -/
@[expose] def psiHead (m : EnvModel V env) (ψ : Name → Nat) (nPJ : Nat) (auxOf : Nat → Nat) :
    Nat → AnnotTerm :=
  fun Jc =>
    (AnnotTerm.mkAppN (m.acval (d.ctorsA.getD (auxOf Jc) default).1.name ψ) (paramBvarsAt d.nP d.nP)).liftN
      nPJ 0

/-- Which fields use the hypothesis: the container's recursive ones. -/
@[expose] def psiUseIh (dJ : IndRepData V) : Nat → Nat → Bool :=
  fun Jc i => decide (i ∈ ConLeche.recIdxOf (dJ.ksF Jc))

/-- The transports: a field recursive in the copy's constructor but not
in the container's, carried by the table's term for the target copy
(lifted over the pin's readings), the copy's index readings and
telescope (lifted over the pin's readings, the telescope's bits the
elimination's). -/
@[expose] def psiVia (dJ : IndRepData V) (ψ : Name → Nat) (k₀ nPJ : Nat) (auxOf : Nat → Nat)
    (b : Nat) (tbl : Nat → AnnotTerm) : Nat → Nat → Option ViaSpec :=
  fun Jc i =>
    if i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) ∧ i ∉ ConLeche.recIdxOf (dJ.ksF Jc) then
      some ((tbl (d.tgtsR (auxOf Jc) i - k₀)).liftN nPJ 0,
        ((d.eissR (auxOf Jc) ψ).getD i []).map
          (·.liftN nPJ (i + ((d.tssR (auxOf Jc) ψ).getD i []).length)),
        rebit b (liftDoms nPJ i ((d.tssR (auxOf Jc) ψ).getD i [])))
    else none

/-- The transports' targets, per constructor and field. -/
@[expose] def psiTgV (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (auxOf : Nat → Nat)
    (cd : Nat → CopyData V) : Nat → Nat → AnnotTerm :=
  fun Jc i => d.psiTgOf m ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀))

end IndRepData

/-- **A copy's data are live** (for the copy at pin `j'`): the group's
base and the member give the pin, the member is one of the container's
with its former's facts, the readings are one per container parameter,
and the copy's index telescope is the container's at the pin
(`CopyIdxRead`). -/
structure CopyData.Ok (m : EnvModel V env) (d : IndRepData V) (ψ : Name → Nat) (k₀ j' : Nat)
    (c : CopyData V) : Prop where
  base : k₀ + c.base + c.mm = k₀ + j'
  mm : c.mm < c.dJ.k
  len : c.DsA.length = c.dJ.nP
  ff : c.dJ.FormerFacts m c.ψ' c.mm
  ls : c.dJ.LeafShape m c.ψ' c.mm
  pins : ∀ φ : Name → Nat, c.dJ.pinsAV c.mm φ = paramBvarsAt c.dJ.nP c.dJ.nP
  pIffM : ∀ ρ' : Nat → V, Sat V (c.dJ.params c.ψ').reverse ρ' ↔
    Sat V (((c.dJ.ppsM c.mm c.ψ').take c.dJ.nP).map (·.2.2)).reverse ρ'
  pin : d.PinRead ψ (m.acval (c.dJ.memberName c.mm) c.ψ') c.DsA c.dJ.nP
  idx : d.CopyIdxRead ψ (k₀ + j') c.dJ c.ψ' c.mm c.DsA

namespace IndRepData

variable (d : IndRepData V)

/-- **A copy's target, applied**: at index values fitting its
container's index telescope at the pin, the target is the copy's leaf
at the block's parameters and those values. -/
theorem psiTgOf_fold (m : EnvModel V env) {ψ : Name → Nat} {k₀ j' : Nat} {c : CopyData V}
    (hc : CopyData.Ok m d ψ k₀ j' c) {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    {EisV : List V}
    (hfit : SpineFit (consList (c.DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀)))
      (consList (psA.map (interp V ρ₀)) ρ₀)) (c.dJ.IdsM c.mm c.ψ') EisV) :
    EisV.foldl SetTheory.app (interp V (consList (psA.map (interp V ρ₀)) ρ₀) (d.psiTgOf m ψ k₀ c))
      = (psA.map (interp V ρ₀) ++ EisV).foldl SetTheory.app
          (interp V ρ₀ (m.acval (d.memberName (k₀ + j')) ψ)) := by
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  have hDsLen : (c.DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀))).length = c.dJ.nP := by
    rw [List.length_map, hc.len]
  have hfit' : SpineFit (consList (c.DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀)))
      (consList (psA.map (interp V ρ₀)) ρ₀))
      ((rebit (pwBit c.ψ' ConLeche.PropWhen.never) ((c.dJ.ipss c.ψ').getD c.mm [])).map (·.2.2)) EisV := by
    rw [c.dJ.ipss_getD c.ψ' hc.mm, rebit_map_dom]; exact hfit
  have hnI : c.dJ.nIdxs.getD c.mm 0 = EisV.length := by
    have := hfit.length_eq
    unfold IndRepData.IdsM at this
    rw [List.length_map, List.length_drop, hc.ff.1] at this
    show c.dJ.nIdxAt c.mm = EisV.length
    omega
  unfold psiTgOf
  rw [c.dJ.invTg_fold c.ψ' hfit', hnI]
  show interp V _ (famAppAV (m.acval (d.memberName (k₀ + c.base + c.mm)) ψ)
    (paramBvarsAt d.nP (d.nP + c.dJ.nP)) c.dJ.nP (c.dJ.nP + EisV.length) EisV.length) = _
  rw [interp_famAppAV_aux (m.cval_closedL _ ψ) hDsLen rfl, range_reverse_map_consList' hpsALen,
    interp_closed (V := V) (m.cval_closedL _ ψ) _ ρ₀, hc.base]

end IndRepData

/-! ## The transported domains, unfolded -/

omit [SetTheory V] in
theorem rebit_rebit (b b' : Nat) (ds : List (Nat × Nat × AnnotTerm)) :
    rebit b (rebit b' ds) = rebit b ds := by simp [rebit]

omit [SetTheory V] in
theorem psiDomAV_some {Tg TgV : Nat → AnnotTerm} {useIh : Nat → Bool} {via : Nat → Option ViaSpec}
    {nP b : Nat} {tgt : Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))} {i : Nat} {Ψ : AnnotTerm} {Eis : List AnnotTerm}
    {tl : List (Nat × Nat × AnnotTerm)} (h : via i = some (Ψ, Eis, tl)) :
    psiDomAV Tg TgV useIh via nP b tgt ds Eiss tls i
      = mkPisAV (rebit b tl) (AnnotTerm.mkAppN ((TgV i).liftN (nP + i + tl.length) 0) Eis) := by
  unfold psiDomAV; rw [h]

omit [SetTheory V] in
theorem psiDomAV_none {Tg TgV : Nat → AnnotTerm} {useIh : Nat → Bool} {via : Nat → Option ViaSpec}
    {nP b : Nat} {tgt : Nat → Nat} {ds : List (Nat × Nat × AnnotTerm)} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))} {i : Nat} (h : via i = none) :
    psiDomAV Tg TgV useIh via nP b tgt ds Eiss tls i = tgFieldAV Tg useIh nP b tgt ds Eiss tls i := by
  unfold psiDomAV; rw [h]

omit [SetTheory V] in
theorem psiDomsAV_getD (Tg TgV : Nat → AnnotTerm) (useIh : Nat → Bool) (via : Nat → Option ViaSpec)
    (nP b : Nat) (tgt : Nat → Nat) (ds : List (Nat × Nat × AnnotTerm)) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) {nF i : Nat} (hi : i < nF) :
    (psiDomsAV Tg TgV useIh via nP b tgt ds Eiss tls nF).getD i default
      = psiDomAV Tg TgV useIh via nP b tgt ds Eiss tls i := by
  simp [psiDomsAV, List.getD_eq_getElem?_getD, List.getElem?_range hi]

omit [SetTheory V] in
theorem instSeqDoms_getElem? (ws : List AnnotTerm) :
    ∀ (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)) (k : Nat),
      (instSeqDoms ws t Γ)[k]?
        = Γ[k]?.map fun d => (d.1, d.2.1, ConLeche.Model.AnnotTerm.instSeq ws (t + k) d.2.2)
  | _, [], _ => rfl
  | t, (u, v, A) :: Γ, 0 => by simp [instSeqDoms]
  | t, (u, v, A) :: Γ, k + 1 => by
    simp only [instSeqDoms, List.getElem?_cons_succ, instSeqDoms_getElem? ws (t + 1) Γ k]
    rw [show t + 1 + k = t + (k + 1) from by omega]

omit [SetTheory V] in
/-- The bits of the transports' telescopes are the elimination bit. -/
theorem psiVia_bits (d dJ : IndRepData V) (ψ : Name → Nat) (k₀ nPJ : Nat) (auxOf : Nat → Nat) (b : Nat)
    (tbl : Nat → AnnotTerm) (Jc i : Nat) {Ψ : AnnotTerm} {Eis : List AnnotTerm}
    {tl : List (Nat × Nat × AnnotTerm)}
    (h : d.psiVia dJ ψ k₀ nPJ auxOf b tbl Jc i = some (Ψ, Eis, tl)) : ∀ dd ∈ tl, dd.2.1 = b := by
  unfold IndRepData.psiVia at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, rfl⟩ := h
    exact fun dd hd => mem_rebit hd
  · exact nomatch h

omit [SetTheory V] in
/-- The transports' positions: recursive in the copy's constructor, not
in the container's. -/
theorem psiVia_isSome (d dJ : IndRepData V) (ψ : Name → Nat) (k₀ nPJ : Nat) (auxOf : Nat → Nat)
    (b : Nat) (tbl : Nat → AnnotTerm) (Jc i : Nat) :
    (d.psiVia dJ ψ k₀ nPJ auxOf b tbl Jc i).isSome = true ↔
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) ∧ i ∉ ConLeche.recIdxOf (dJ.ksF Jc) := by
  unfold IndRepData.psiVia
  split
  · next h => simp [h]
  · next h => simp [h]

namespace IndRepData

variable (d : IndRepData V)

set_option maxHeartbeats 3200000 in
/-- **A transported domain reads as the copy's field domain**: at every
prefix fitting the copy's earlier fields, field `i`'s domain in ψ's
transported form (over the container's data at the pin's readings)
interprets as the copy's own field domain (at the block's parameter
frame) — a transport or a container-recursive field by the copy's
recursive entry and the target copy's fold target
(`psiTgOf_fold`), an ordinary field by the record's substitution
equation. -/
theorem psiDom_eq_copyDom {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ ψ' : Name → Nat} {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP)
    (hlev : dJ.elimL.eval ψ' = dJ.w ψ')
    {k₀ j₀ : Nat} (auxOf : Nat → Nat) (cd : Nat → CopyData V) (tbl : Nat → AnnotTerm)
    {Jc : Nat} {cAJ cAa : ConstantVal × Nat} (hnF : cAa.2 = cAJ.2)
    (hrec : d.CopyCtorAsRead mp.base2 dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) cAJ.2)
    (hC : FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems (auxOf Jc))) lpsT d.nP
      (d.nIdxAt (d.mems (auxOf Jc))) d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF
      d.fvsPF d.xFvsF d.xrestF d.eissF d.tssF (auxOf Jc) cAa
      (fun i => d.memberName (d.tgts (auxOf Jc) i)) (fun i => d.nIdxAt (d.tgts (auxOf Jc) i)))
    (hviewA : d.ksR (auxOf Jc) = d.ksF (auxOf Jc) ∧ d.tgtsR (auxOf Jc) = d.tgts (auxOf Jc) ∧
      d.eissR (auxOf Jc) = d.eissF (auxOf Jc) ∧ d.tssR (auxOf Jc) = d.tssF (auxOf Jc))
    (htgtsA : ∀ i, d.tgtsR (auxOf Jc) i < d.k)
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hLSA : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hTσ : WellDenotedV V (consList (psA.map (interp V ρ₀)) ρ₀)
      (mkPisAV ((d.dsF (auxOf Jc) ψ).drop d.nP)
        (ctorBodyAVI mp.base2 (d.memberName (d.mems (auxOf Jc))) d.nP cAa.2 ψ (d.esF (auxOf Jc) ψ))))
    (hviewJ : dJ.tgtsR Jc = dJ.tgts Jc ∧ dJ.eissR Jc = dJ.eissF Jc ∧ dJ.tssR Jc = dJ.tssF Jc)
    (htgtsJ : ∀ i, dJ.tgts Jc i < dJ.k)
    (hbitsJ : ∀ i, ∀ dd ∈ (dJ.tssF Jc ψ').getD i [], (dd.2.1 = 0 ↔ dJ.resSort.eval ψ' = 0))
    (hgrp : ∀ t, t < dJ.k → CopyData.Ok mp.base2 d ψ k₀ (j₀ + t) ⟨dJ, t, ψ', DsA, j₀⟩)
    (hcd : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR (auxOf Jc) i - k₀) (cd (d.tgtsR (auxOf Jc) i - k₀)))
    {i : Nat} (hi : i < cAJ.2) {ws : List V} (hws : ws.length = i)
    (hwsA : SpineFit (consList (psA.map (interp V ρ₀)) ρ₀)
      ((((d.dsF (auxOf Jc) ψ).drop d.nP).take i).map (·.2.2)) ws) :
    interp V (consList ws (consList (DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀)))
        (consList (psA.map (interp V ρ₀)) ρ₀)))
        (psiDomAV (dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP))
          (d.psiTgV mp.base2 ψ k₀ auxOf cd Jc) (psiUseIh dJ Jc)
          (d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc) dJ.nP (dJ.bb ψ') (dJ.tgtsR Jc)
          (dJ.dsF Jc ψ') (dJ.eissR Jc ψ') (dJ.tssR Jc ψ') i)
      = interp V (consList ws (consList (psA.map (interp V ρ₀)) ρ₀))
          ((d.dsF (auxOf Jc) ψ).getD (d.nP + i) default).2.2 := by
  obtain ⟨-, -, hD⟩ := hC
  obtain ⟨hviewK, hviewT, hviewE, hviewS⟩ := hviewA
  obtain ⟨hviewTJ, hviewEJ, hviewSJ⟩ := hviewJ
  generalize hσ : consList (psA.map (interp V ρ₀)) ρ₀ = σ at hwsA hTσ ⊢
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
  have hlenDs := hD.len ψ
  have hsatA : Sat V (d.params ψ).reverse σ := by
    rw [← hσ]
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparamsA
    rwa [List.append_nil] at h
  have hσshift : ∀ (xs : List V) (e : Nat), xs.length = e → ∀ j, consList xs σ (j + e) = σ j := by
    intro xs e he j; rw [← he]; exact consList_apply_add xs σ j
  -- the elimination bit's zeroness is the block's sort's
  have hbz : dJ.bb ψ' = 0 ↔ d.resSort.eval ψ = 0 := by
    have h0 := hgrp 0 (Nat.lt_of_le_of_lt (Nat.zero_le _) (htgtsJ 0))
    have hs : dJ.w ψ' = d.w ψ := h0.idx.sort
    unfold IndRepData.bb
    rw [pwBit_zeronessOf, hlev]
    show dJ.w ψ' = 0 ↔ d.w ψ = 0
    rw [hs]
  have hbzJ : dJ.bb ψ' = 0 ↔ dJ.resSort.eval ψ' = 0 := by
    unfold IndRepData.bb
    rw [pwBit_zeronessOf, hlev]
    exact Iff.rfl
  -- the copy's entry at a recursive position, and its graded body
  have hentry : ∀ (hiR : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc))),
      ((d.dsF (auxOf Jc) ψ).getD (d.nP + i) default).2.2
        = mkPisAV ((d.tssR (auxOf Jc) ψ).getD i [])
            (AnnotTerm.mkAppN (mp.base2.acval (d.memberName (d.tgtsR (auxOf Jc) i)) ψ)
              (paramBvarsAt d.nP (d.nP + i + ((d.tssR (auxOf Jc) ψ).getD i []).length) ++
                (d.eissR (auxOf Jc) ψ).getD i [])) := by
    intro hiR
    rw [hviewK] at hiR
    rw [hviewS, hviewE, hviewT]
    exact FixCtorDataI.recRefl_entry hD ψ hiR
  have hentryWD : WellDenoted V (consList ws σ) ((d.dsF (auxOf Jc) ψ).getD (d.nP + i) default).2.2 := by
    have h := wellDenoted_mkPisAV_dom hTσ.1 ws i (((d.dsF (auxOf Jc) ψ).drop d.nP).getD i default)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_drop, hlenDs, hnF]; omega)]; rfl)
      hwsA
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD] at h
    exact h
  -- a recursive entry's index readings fit the target copy's telescope
  have hidxA : ∀ (hiR : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc))) (as : List V),
      SpineFit (consList ws σ) (((d.tssR (auxOf Jc) ψ).getD i []).map (·.2.2)) as →
      SpineFit σ (d.IdsM (d.tgtsR (auxOf Jc) i) ψ)
        (((d.eissR (auxOf Jc) ψ).getD i []).map (interp V (consList as (consList ws σ)))) := by
    intro hiR as has
    have hbody := wellDenoted_mkPisAV_body (by rw [← hentry hiR]; exact hentryWD) as has
    rw [← hσ] at hbody ⊢
    rw [← consList_append] at hbody ⊢
    have hEl : ((d.eissR (auxOf Jc) ψ).getD i []).length = d.nIdxAt (d.tgtsR (auxOf Jc) i) := by
      obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hiR
      rw [hviewK, hD.ksLen] at hlt
      rw [hviewE, hviewT]
      rw [hviewK] at hk
      rcases hk with hk | hk
      · exact hD.eisLen ψ i hk hlt
      · exact hD.eisLenRefl ψ i hk hlt
    rw [Nat.add_assoc] at hbody
    exact d.idxFit_of_entry hpsA (hFFA _ (htgtsA i)) (hLSA _ (htgtsA i))
      (σas := ws ++ as) (e := i + ((d.tssR (auxOf Jc) ψ).getD i []).length)
      (by rw [List.length_append, hws, has.length_eq, List.length_map]) hbody hEl
  -- the copy's entry, read at the parameter frame
  have hentryInterp : ∀ (hiR : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc))) (as : List V),
      as.length = ((d.tssR (auxOf Jc) ψ).getD i []).length →
      interp V (consList as (consList ws σ))
          (AnnotTerm.mkAppN (mp.base2.acval (d.memberName (d.tgtsR (auxOf Jc) i)) ψ)
            (paramBvarsAt d.nP (d.nP + i + ((d.tssR (auxOf Jc) ψ).getD i []).length) ++
              (d.eissR (auxOf Jc) ψ).getD i []))
        = (psA.map (interp V ρ₀) ++
            ((d.eissR (auxOf Jc) ψ).getD i []).map (interp V (consList as (consList ws σ)))).foldl
            SetTheory.app (interp V ρ₀ (mp.base2.acval (d.memberName (d.tgtsR (auxOf Jc) i)) ψ)) := by
    intro _ as has
    rw [interp_mkAppN_map, List.map_append, Nat.add_assoc,
      map_paramBvarsAt_interp (ρp := σ) (fun j => by
        rw [← consList_append]
        exact hσshift _ _ (by rw [List.length_append, hws, has]) j),
      ← hσ, range_reverse_map_consList' hpsALen, interp_closed (V := V) (mp.base2.cval_closedL _ ψ) _ ρ₀]
  by_cases hT : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) ∧ i ∉ ConLeche.recIdxOf (dJ.ksF Jc)
  · -- a TRANSPORT
    have hvia : d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc i
        = some ((tbl (d.tgtsR (auxOf Jc) i - k₀)).liftN dJ.nP 0,
          ((d.eissR (auxOf Jc) ψ).getD i []).map
            (·.liftN dJ.nP (i + ((d.tssR (auxOf Jc) ψ).getD i []).length)),
          rebit (dJ.bb ψ') (liftDoms dJ.nP i ((d.tssR (auxOf Jc) ψ).getD i []))) := by
      unfold IndRepData.psiVia; rw [if_pos hT]
    rw [psiDomAV_some hvia, rebit_rebit, hentry hT.1]
    simp only [rebit_length, liftDoms_length]
    have hc := hcd i hi hT.1 hT.2
    generalize htssA : (d.tssR (auxOf Jc) ψ).getD i [] = tssA at hidxA hentryInterp hc ⊢
    generalize heissA : (d.eissR (auxOf Jc) ψ).getD i [] = eissA at hidxA hentryInterp hc ⊢
    refine interp_mkPisAV_congr (by simp [liftDoms_length]) ?_ ?_ ?_
    · intro k d₁ d₂ h₁ h₂
      rw [rebit_getElem?, liftDoms_getElem?] at h₁
      obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨d'', hd'', rfl⟩ := Option.map_eq_some_iff.mp hd'
      rw [h₂] at hd''
      obtain rfl := Option.some.inj hd''
      show dJ.bb ψ' = 0 ↔ d₂.2.1 = 0
      rw [hbz]
      have hmem : d₂ ∈ (d.tssF (auxOf Jc) ψ).getD i [] := by
        rw [← hviewS, htssA]; exact List.mem_of_getElem? h₂
      exact (hD.tssBits ψ i d₂ hmem).symm
    · intro k d₁ d₂ as h₁ h₂ hsp
      rw [rebit_getElem?, liftDoms_getElem?] at h₁
      obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
      obtain ⟨d'', hd'', rfl⟩ := Option.map_eq_some_iff.mp hd'
      rw [h₂] at hd''
      obtain rfl := Option.some.inj hd''
      have hask : as.length = k := by
        have := hsp.length_eq
        rw [List.length_map, List.length_take, rebit_length, liftDoms_length] at this
        have hk : k < tssA.length := (List.getElem?_eq_some_iff.mp h₂).1
        omega
      show interp V (consList as (consList ws (consList (DsA.map (interp V σ)) σ)))
        (d₂.2.2.liftN dJ.nP (i + k)) = interp V (consList as (consList ws σ)) d₂.2.2
      rw [← consList_append (xs := ws) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
        ← consList_append (xs := ws) (ys := as) (ρ := σ), ← hDsLen,
        show i + k = (ws ++ as).length from by rw [List.length_append, hws, hask],
        interp_liftN_middle]
    · intro as hsp
      rw [rebit_map_dom] at hsp
      have hasA : SpineFit (consList ws σ) (tssA.map (·.2.2)) as := by
        rw [spineFit_liftDoms, ← hDsLen, ← hws, shiftE_consList_middle] at hsp
        exact hsp
      have hasLen : as.length = tssA.length := by rw [hasA.length_eq, List.length_map]
      rw [interp_mkAppN_map, List.map_map, interp_liftN, ← consList_append, ← consList_append,
        ← consList_append,
        show dJ.nP + i + tssA.length = (DsA.map (interp V σ) ++ (ws ++ as)).length from by
          rw [List.length_append, List.length_append, hDsLen, hws, hasLen]; exact Nat.add_assoc _ _ _,
        shiftE_consList]
      have hEv : eissA.map (interp V (consList (DsA.map (interp V σ) ++ (ws ++ as)) σ) ∘
          fun E => E.liftN dJ.nP (i + tssA.length))
          = eissA.map (interp V (consList as (consList ws σ))) := by
        apply List.map_congr_left
        intro E _
        simp only [Function.comp_def]
        rw [consList_append, ← hDsLen,
          show i + tssA.length = (ws ++ as).length from by rw [List.length_append, hws, hasLen],
          interp_liftN_middle, consList_append]
      rw [hEv, consList_append, hentryInterp hT.1 as hasLen]
      -- the target copy's fold target, applied
      unfold IndRepData.psiTgV
      have hfitT : SpineFit (consList ((cd (d.tgtsR (auxOf Jc) i - k₀)).DsA.map (interp V σ)) σ)
          ((cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.IdsM (cd (d.tgtsR (auxOf Jc) i - k₀)).mm
            (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ')
          (eissA.map (interp V (consList as (consList ws σ)))) := by
        have h := (hc.idx.idxIff σ hsatA _).mp
          (by
            have h' := hidxA hT.1 as hasA
            rw [show k₀ + (d.tgtsR (auxOf Jc) i - k₀) = d.tgtsR (auxOf Jc) i from by
              have := hrec.kindT i hi hT.2 hT.1
              obtain ⟨j', hj', -, -⟩ := this
              omega]
            exact h')
        exact h
      rw [← hσ] at hfitT ⊢
      rw [d.psiTgOf_fold mp.base2 hc hpsA hfitT, hσ,
        show k₀ + (d.tgtsR (auxOf Jc) i - k₀) = d.tgtsR (auxOf Jc) i from by
          obtain ⟨j', hj', -, -⟩ := hrec.kindT i hi hT.2 hT.1
          omega]
  · have hvia : d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc i = none := by
      unfold IndRepData.psiVia; rw [if_neg hT]
    rw [psiDomAV_none hvia]
    unfold tgFieldAV
    by_cases hR : i ∈ ConLeche.recIdxOf (dJ.ksF Jc)
    · -- a field the container sees as recursive
      rw [if_pos (by unfold psiUseIh; exact decide_eq_true hR)]
      obtain ⟨hkind, htgtR, htss, heiss⟩ := hrec.kindR i hR
      have hiR : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) := by
        obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hR
        refine mem_recIdxOf.mpr ⟨?_, by rw [hkind]; exact hk⟩
        rw [hviewK, hD.ksLen, hnF]; exact hi
      rw [hentry hiR, hviewSJ, hviewEJ, hviewTJ]
      generalize htssA : (d.tssR (auxOf Jc) ψ).getD i [] = tssA at hidxA hentryInterp htss ⊢
      generalize heissA : (d.eissR (auxOf Jc) ψ).getD i [] = eissA at hidxA hentryInterp heiss ⊢
      generalize htssJ : (dJ.tssF Jc ψ').getD i [] = tssJ at htss heiss hbitsJ ⊢
      generalize heissJ : (dJ.eissF Jc ψ').getD i [] = eissJ at heiss ⊢
      have hnPJ : DsA ≠ [] → DsA.length = dJ.nP := fun _ => hDsA
      have hpos : DsA ≠ [] → 1 ≤ dJ.nP := fun hne => by
        rw [← hDsA]
        cases DsA with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
      refine interp_mkPisAV_congr (by rw [rebit_length, htss, instSeqDoms_length]) ?_ ?_ ?_
      · intro k d₁ d₂ h₁ h₂
        rw [rebit_getElem?] at h₁
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
        rw [htss, instSeqDoms_getElem?, hd'] at h₂
        obtain rfl := Option.some.inj h₂
        show dJ.bb ψ' = 0 ↔ d'.2.1 = 0
        rw [hbzJ]
        exact (hbitsJ i d' (by rw [htssJ]; exact List.mem_of_getElem? hd')).symm
      · intro k d₁ d₂ as h₁ h₂ hsp
        rw [rebit_getElem?] at h₁
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
        rw [htss, instSeqDoms_getElem?, hd'] at h₂
        obtain rfl := Option.some.inj h₂
        have hask : as.length = k := by
          have := hsp.length_eq
          rw [List.length_map, List.length_take, rebit_length] at this
          have hk : k < tssJ.length := (List.getElem?_eq_some_iff.mp hd').1
          omega
        show interp V (consList as (consList ws (consList (DsA.map (interp V σ)) σ))) d'.2.2
          = interp V (consList as (consList ws σ))
              (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1 + k) d'.2.2)
        rw [← consList_append (xs := ws) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← consList_append (xs := ws) (ys := as) (ρ := σ),
          interp_instSeq_under σ DsA (ws ++ as) (dJ.nP + i - 1 + k) d'.2.2 (fun hne => by
            rw [List.length_append, hws, hask, hnPJ hne]; have := hpos hne; omega)]
      · intro as hsp
        rw [rebit_map_dom] at hsp
        have hasLen : as.length = tssJ.length := by rw [hsp.length_eq, List.length_map]
        have hasA : SpineFit (consList ws σ) (tssA.map (·.2.2)) as := by
          rw [htss]
          exact (spineFit_instSeqDoms_iff ws (dJ.nP + i - 1) tssJ as (fun hne => by
            rw [hws, hnPJ hne]; have := hpos hne; omega)).mpr hsp
        rw [interp_mkAppN_map, interp_liftN, ← consList_append, ← consList_append,
          ← consList_append,
          show dJ.nP + i + tssJ.length = (DsA.map (interp V σ) ++ (ws ++ as)).length from by
            rw [List.length_append, List.length_append, hDsLen, hws, hasLen]; exact Nat.add_assoc _ _ _,
          shiftE_consList]
        have hEv : eissJ.map (interp V (consList (DsA.map (interp V σ) ++ (ws ++ as)) σ))
            = eissA.map (interp V (consList as (consList ws σ))) := by
          rw [heiss, List.map_map]
          apply List.map_congr_left
          intro E _
          simp only [Function.comp_def]
          rw [consList_append, ← consList_append (xs := ws),
            interp_instSeq_under σ DsA (ws ++ as) (dJ.nP + i + tssJ.length - 1) E (fun hne => by
              rw [List.length_append, hws, hasLen, hnPJ hne]; have := hpos hne; omega)]
        rw [hEv, consList_append, hentryInterp hiR as (by rw [hasLen, htss, instSeqDoms_length])]
        -- the group-mate's copy, applied
        have hcg := hgrp (dJ.tgts Jc i) (htgtsJ i)
        have hTg : dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP) (dJ.tgts Jc i)
            = d.psiTgOf mp.base2 ψ k₀ ⟨dJ, dJ.tgts Jc i, ψ', DsA, j₀⟩ := rfl
        have hfitT : SpineFit (consList (DsA.map (interp V σ)) σ) (dJ.IdsM (dJ.tgts Jc i) ψ')
            (eissA.map (interp V (consList as (consList ws σ)))) := by
          have h := (hcg.idx.idxIff σ hsatA _).mp
            (by
              have h' := hidxA hiR as hasA
              rw [htgtR, Nat.add_assoc] at h'
              exact h')
          exact h
        rw [hTg]
        rw [← hσ] at hfitT ⊢
        rw [d.psiTgOf_fold mp.base2 hcg hpsA hfitT, hσ, htgtR, Nat.add_assoc]
    · -- an ordinary field on both sides
      rw [if_neg (by unfold psiUseIh; exact fun h => hR (of_decide_eq_true h))]
      have hnA : i ∉ ConLeche.recIdxOf (d.ksR (auxOf Jc)) := fun h => hT ⟨h, hR⟩
      have hpos : DsA ≠ [] → 1 ≤ dJ.nP := fun hne => by
        rw [← hDsA]
        cases DsA with
        | nil => exact absurd rfl hne
        | cons _ _ => simp
      rw [hrec.ord i hi hR hnA,
        interp_instSeq_under σ DsA ws (dJ.nP + i - 1) _ (fun hne => by
          rw [hws, hDsA]; have := hpos hne; omega)]


set_option maxHeartbeats 3200000 in
/-- **The copy's constructor at the transported domains** (`PsiSetup.hCAD`):
the copy's constructor tower (a real constructor of the auxiliary block,
graded at the block's parameter frame) lifted over the pin's readings;
a spine fitting ψ's transported domains fits it, field by field
(`psiDom_eq_copyDom`); and at such a spine its body — the copy at the
parameters and its index readings — is the container's fold target at
the container constructor's index readings (the readings agree under
the substitution, the copy's index readings fit the container's
telescope at the pin, `psiTgOf_fold`). -/
theorem ctorAtDoms_psi {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ ψ' : Name → Nat} {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP)
    (hlev : dJ.elimL.eval ψ' = dJ.w ψ')
    {k₀ j₀ : Nat} (auxOf : Nat → Nat) (cd : Nat → CopyData V) (tbl : Nat → AnnotTerm)
    {Jc : Nat} {cAJ cAa : ConstantVal × Nat}
    (hJa : d.ctorsA[auxOf Jc]? = some cAa) (hnF : cAa.2 = cAJ.2)
    (hrec : d.CopyCtorAsRead mp.base2 dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) cAJ.2)
    (hC : FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems (auxOf Jc))) lpsT d.nP
      (d.nIdxAt (d.mems (auxOf Jc))) d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF
      d.fvsPF d.xFvsF d.xrestF d.eissF d.tssF (auxOf Jc) cAa
      (fun i => d.memberName (d.tgts (auxOf Jc) i)) (fun i => d.nIdxAt (d.tgts (auxOf Jc) i)))
    (hpIffA : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.dsF (auxOf Jc) ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hviewA : d.ksR (auxOf Jc) = d.ksF (auxOf Jc) ∧ d.tgtsR (auxOf Jc) = d.tgts (auxOf Jc) ∧
      d.eissR (auxOf Jc) = d.eissF (auxOf Jc) ∧ d.tssR (auxOf Jc) = d.tssF (auxOf Jc))
    (htgtsA : ∀ i, d.tgtsR (auxOf Jc) i < d.k) (hmemA : d.mems (auxOf Jc) < d.k)
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hLSA : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hEsFit : ∀ fs : List V,
      SpineFit (consList (psA.map (interp V ρ₀)) ρ₀) (((d.dsF (auxOf Jc) ψ).drop d.nP).map (·.2.2)) fs →
      SpineFit (consList (psA.map (interp V ρ₀)) ρ₀)
        ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems (auxOf Jc)) [])).map (·.2.2))
        ((d.esF (auxOf Jc) ψ).map (interp V (consList fs (consList (psA.map (interp V ρ₀)) ρ₀)))))
    (hviewJ : dJ.tgtsR Jc = dJ.tgts Jc ∧ dJ.eissR Jc = dJ.eissF Jc ∧ dJ.tssR Jc = dJ.tssF Jc)
    (htgtsJ : ∀ i, dJ.tgts Jc i < dJ.k) (hmemJ : dJ.mems Jc < dJ.k)
    (hbitsJ : ∀ i, ∀ dd ∈ (dJ.tssF Jc ψ').getD i [], (dd.2.1 = 0 ↔ dJ.resSort.eval ψ' = 0))
    (hgrp : ∀ t, t < dJ.k → CopyData.Ok mp.base2 d ψ k₀ (j₀ + t) ⟨dJ, t, ψ', DsA, j₀⟩)
    (hcd : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR (auxOf Jc) i - k₀) (cd (d.tgtsR (auxOf Jc) i - k₀))) :
    dJ.CtorAtDoms (consList (psA.map (interp V ρ₀)) ρ₀) DsA
      (dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP)) Jc
      (d.psiHead mp.base2 ψ dJ.nP auxOf Jc) cAJ.2
      (psiDomsAV (dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP))
        (d.psiTgV mp.base2 ψ k₀ auxOf cd Jc) (psiUseIh dJ Jc)
        (d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc) dJ.nP (dJ.bb ψ') (dJ.tgtsR Jc)
        (dJ.dsF Jc ψ') (dJ.eissR Jc ψ') (dJ.tssR Jc ψ') cAJ.2)
      (dJ.esF Jc ψ') := by
  have hC' := hC
  obtain ⟨hfind, -, hD⟩ := hC'
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  have hlenDs := hD.len ψ
  have hclosedC : Term.bvarsBelow 0 (mp.base2.acval cAa.1.name ψ).erase := mp.base2.cval_closedL _ ψ
  have hclosedT : Term.bvarsBelow 0 (mp.base2.acval (d.memberName (d.mems (auxOf Jc))) ψ).erase :=
    mp.base2.cval_closedL _ ψ
  have hfitP : SpineFit ρ₀ (((d.dsF (auxOf Jc) ψ).take d.nP).map (·.2.2)) (psA.map (interp V ρ₀)) :=
    spineFit_of_paramsIff hpsALen (by simp [hlenDs]) hparamsA hpIffA
  -- the copy's tower at the parameter frame, and its head
  generalize hbody : ctorBodyAVI mp.base2 (d.memberName (d.mems (auxOf Jc))) d.nP cAa.2 ψ
    (d.esF (auxOf Jc) ψ) = body
  have hsplitT : mkPisAV (d.dsF (auxOf Jc) ψ) body
      = mkPisAV ((d.dsF (auxOf Jc) ψ).take d.nP) (mkPisAV ((d.dsF (auxOf Jc) ψ).drop d.nP) body) := by
    rw [← mkPisAV_append, List.take_append_drop]
  have hshift : shiftE d.nP 0 (consList (psA.map (interp V ρ₀)) ρ₀) = ρ₀ := by
    rw [← hpsALen]; exact shiftE_consList _ _
  have hokT : WellDenotedV V ρ₀ (mkPisAV (d.dsF (auxOf Jc) ψ) body) := by
    rw [← hbody]; exact hD.okTy ψ ρ₀
  have hcmem : interp V ρ₀ (mp.base2.acval cAa.1.name ψ)
      ∈ˢ interp V ρ₀ (mkPisAV (d.dsF (auxOf Jc) ψ) body) := by
    rw [← hbody]; exact mp.mem_type _ (Env.find?_mem hfind) ψ _ (hD.read ψ) ρ₀
  have hTσ : WellDenotedV V (consList (psA.map (interp V ρ₀)) ρ₀)
      (mkPisAV ((d.dsF (auxOf Jc) ψ).drop d.nP) body) := by
    have h := hokT
    rw [hsplitT] at h
    exact ⟨wellDenoted_mkPisAV_body h.1 _ hfitP, annotValid_mkPisAV_body h.2 _ hfitP⟩
  have hhead := wellDenotedV_mkAppN_of_spineFit (σ := consList (psA.map (interp V ρ₀)) ρ₀)
    (ds := liftDoms d.nP 0 ((d.dsF (auxOf Jc) ψ).take d.nP))
    (C := (mkPisAV ((d.dsF (auxOf Jc) ψ).drop d.nP) body).liftN d.nP
        (0 + ((d.dsF (auxOf Jc) ψ).take d.nP).length))
    (f := mp.base2.acval cAa.1.name ψ) (as := paramBvarsAt d.nP d.nP)
    (by rw [← liftN_mkPisAV, ← hsplitT, WellDenotedV_liftN, hshift]; exact hokT)
    ⟨mp.base2.acval_wellDenoted _ ψ _, mp.acval_validV _ ψ _⟩
    (fun a ha => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp, by simp⟩)
    (by rw [← liftN_mkPisAV, ← hsplitT, interp_liftN, hshift, interp_closed (V := V) hclosedC _ ρ₀]
        exact hcmem)
    (by rw [spineFit_liftDoms, hshift, interp_paramBvarsAt_self hpsALen]; exact hfitP)
  have htakeLen : 0 + ((d.dsF (auxOf Jc) ψ).take d.nP).length = (psA.map (interp V ρ₀)).length := by
    rw [Nat.zero_add, List.length_take, hlenDs, hpsALen]; omega
  rw [interp_paramBvarsAt_self hpsALen, interp_liftN, htakeLen, shiftE_consList_len, hshift] at hhead
  -- the pointwise field readings
  have hpt : ∀ i, i < cAJ.2 → ∀ ws : List V, ws.length = i →
      SpineFit (consList (psA.map (interp V ρ₀)) ρ₀)
        ((((d.dsF (auxOf Jc) ψ).drop d.nP).take i).map (·.2.2)) ws →
      interp V (consList ws (consList (DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀)))
          (consList (psA.map (interp V ρ₀)) ρ₀)))
          (psiDomAV (dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP))
            (d.psiTgV mp.base2 ψ k₀ auxOf cd Jc) (psiUseIh dJ Jc)
            (d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc) dJ.nP (dJ.bb ψ') (dJ.tgtsR Jc)
            (dJ.dsF Jc ψ') (dJ.eissR Jc ψ') (dJ.tssR Jc ψ') i)
        = interp V (consList ws (consList (psA.map (interp V ρ₀)) ρ₀))
            ((d.dsF (auxOf Jc) ψ).getD (d.nP + i) default).2.2 :=
    fun i hi ws hws hwsA =>
      d.psiDom_eq_copyDom mp hpsA hparamsA hDsA hlev auxOf cd tbl hnF hrec hC hviewA htgtsA hFFA
        hLSA (by rw [hbody]; exact hTσ) hviewJ htgtsJ hbitsJ hgrp hcd hi hws hwsA
  -- the frames
  generalize hσ : consList (psA.map (interp V ρ₀)) ρ₀ = σ at hfitP hTσ hhead hpt hEsFit ⊢
  have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
  have hshift' : shiftE dJ.nP 0 (consList (DsA.map (interp V σ)) σ) = σ := by
    rw [← hDsLen]; exact shiftE_consList _ _
  have hsatA : Sat V (d.params ψ).reverse σ := by
    rw [← hσ]
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparamsA
    rwa [List.append_nil] at h
  have hdropLen : ((d.dsF (auxOf Jc) ψ).drop d.nP).length = cAJ.2 := by
    rw [List.length_drop, hlenDs, hnF]; omega
  have hgetD : d.ctorsA.getD (auxOf Jc) default = cAa := by
    rw [List.getD_eq_getElem?_getD, hJa]; rfl
  refine ⟨liftDoms dJ.nP 0 ((d.dsF (auxOf Jc) ψ).drop d.nP),
    body.liftN dJ.nP (0 + ((d.dsF (auxOf Jc) ψ).drop d.nP).length),
    by rw [liftDoms_length, hdropLen], ?_, ?_, ?_, ?_⟩
  · rw [← liftN_mkPisAV, WellDenotedV_liftN, hshift']; exact hTσ
  · unfold IndRepData.psiHead
    rw [hgetD, WellDenotedV_liftN, hshift']; exact hhead.1
  · unfold IndRepData.psiHead
    rw [hgetD, ← liftN_mkPisAV, interp_liftN, interp_liftN, hshift']; exact hhead.2
  · intro vs hvs
    -- the spine fits the copy's tower, field by field
    have hfitC : SpineFit (consList (DsA.map (interp V σ)) σ)
        ((liftDoms dJ.nP 0 ((d.dsF (auxOf Jc) ψ).drop d.nP)).map (·.2.2)) vs := by
      refine spineFit_congr_pointwise (by rw [List.length_map, liftDoms_length, hdropLen]; simp [psiDomsAV])
        ?_ hvs
      intro i hi ws hws hws'
      rw [List.length_map, liftDoms_length, hdropLen] at hi
      have hwsA : SpineFit σ ((((d.dsF (auxOf Jc) ψ).drop d.nP).take i).map (·.2.2)) ws := by
        rw [← List.map_take, liftDoms_take, spineFit_liftDoms, hshift'] at hws'
        exact hws'
      have hR : ((liftDoms dJ.nP 0 ((d.dsF (auxOf Jc) ψ).drop d.nP)).map (·.2.2)).getD i default
          = (((d.dsF (auxOf Jc) ψ).getD (d.nP + i) default).2.2).liftN dJ.nP i := by
        have hlt : d.nP + i < (d.dsF (auxOf Jc) ψ).length := by rw [hlenDs, hnF]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, liftDoms_getElem?, List.getElem?_drop,
          List.getElem?_eq_getElem hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        simp
      rw [psiDomsAV_getD _ _ _ _ _ _ _ _ _ _ hi, hR, ← hDsLen, ← hws, interp_liftN_middle, hws, hDsLen]
      exact hpt i hi ws hws hwsA
    refine ⟨hfitC, ?_⟩
    have hfitA : SpineFit σ (((d.dsF (auxOf Jc) ψ).drop d.nP).map (·.2.2)) vs := by
      rw [spineFit_liftDoms, hshift'] at hfitC; exact hfitC
    have hvsLen : vs.length = cAJ.2 := by
      rw [hfitA.length_eq, List.length_map, hdropLen]
    -- the body, at the copy's frame
    rw [show 0 + ((d.dsF (auxOf Jc) ψ).drop d.nP).length = vs.length from by rw [Nat.zero_add, hdropLen, hvsLen],
      ← hDsLen, interp_liftN_middle, hDsLen, ← hbody]
    unfold ctorBodyAVI
    rw [paramBvars_eq_paramBvarsAt, interp_mkAppN_map, List.map_append,
      map_paramBvarsAt_interp (ρp := σ) (fun j => by
        rw [hnF, ← hvsLen]; exact consList_apply_add vs σ j),
      ← hσ, range_reverse_map_consList' hpsALen, interp_closed (V := V) hclosedT _ ρ₀, hσ]
    -- the container's index readings are the copy's
    have hEv : (dJ.esF Jc ψ').map (interp V (consList vs (consList (DsA.map (interp V σ)) σ)))
        = (d.esF (auxOf Jc) ψ).map (interp V (consList vs σ)) := by
      rw [hrec.es, List.map_map]
      apply List.map_congr_left
      intro E _
      simp only [Function.comp_def]
      rw [interp_instSeq_under σ DsA vs (dJ.nP + cAJ.2 - 1) E (fun hne => by
        rw [hvsLen, hDsA]
        cases DsA with
        | nil => exact absurd rfl hne
        | cons _ _ => simp at hDsA; omega)]
    rw [hEv]
    -- the container's fold target at the readings is the copy at the parameters
    have hcg := hgrp (dJ.mems Jc) hmemJ
    have hTg : dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP) (dJ.mems Jc)
        = d.psiTgOf mp.base2 ψ k₀ ⟨dJ, dJ.mems Jc, ψ', DsA, j₀⟩ := rfl
    have hfitE := hEsFit vs hfitA
    rw [d.ipss_getD ψ hmemA, rebit_map_dom] at hfitE
    have hfitT : SpineFit (consList (DsA.map (interp V σ)) σ) (dJ.IdsM (dJ.mems Jc) ψ')
        ((d.esF (auxOf Jc) ψ).map (interp V (consList vs σ))) := by
      refine (hcg.idx.idxIff σ hsatA _).mp ?_
      rw [← Nat.add_assoc, ← hrec.mem]
      exact hfitE
    rw [hTg]
    rw [← hσ] at hfitT ⊢
    rw [d.psiTgOf_fold mp.base2 hcg hpsA hfitT, hσ, hrec.mem, Nat.add_assoc]

end IndRepData

/-! ## The replaced positions, as index sets -/

omit [SetTheory V] in
/-- The excluded slots of the replaced positions below `n`, at depth
`nP + n + k`: the indices `n + k - 1 - l` for a replaced `l < n`. -/
theorem exclP_replP_iff {nP : Nat} {P : Nat → Prop} {n k D j : Nat} (hD : D = nP + n + k) :
    exclP (replP nP P n) D j ↔ ∃ l, l < n ∧ P l ∧ j = n + k - 1 - l := by
  constructor
  · rintro ⟨q, ⟨h1, h2, h3⟩, hq, hj⟩
    exact ⟨q - nP, by omega, h2, by omega⟩
  · rintro ⟨l, hl, hP, hj⟩
    refine ⟨nP + l, ⟨Nat.le_add_right _ _, by rw [Nat.add_sub_cancel_left]; exact hP, by omega⟩,
      by omega, by omega⟩

omit [SetTheory V] in
/-- A recursive position, as membership in `recIdxOf`. -/
theorem recAt_add_iff {nP : Nat} {ks : List RecFieldKind} {l : Nat} :
    recAt nP ks (nP + l) ↔ l ∈ ConLeche.recIdxOf ks := by
  unfold recAt
  rw [Nat.add_sub_cancel_left, mem_recIdxOf]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨?_, h⟩
    refine Classical.byContradiction fun hlt => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hlt)] at h
    rcases h with h | h <;> exact nomatch h
  · rintro ⟨-, h⟩
    exact ⟨Nat.le_add_right _ _, h⟩

omit [SetTheory V] in
/-- The excluded slots of the recursive positions below `n`, at depth
`nP + n + k`. -/
theorem exclP_recAt_iff {nP : Nat} {ks : List RecFieldKind} {n k D j : Nat} (hD : D = nP + n + k) :
    exclP (fun q => recAt nP ks q ∧ q < nP + n) D j ↔
      ∃ l, l < n ∧ l ∈ ConLeche.recIdxOf ks ∧ j = n + k - 1 - l := by
  constructor
  · rintro ⟨q, ⟨hr, hlt⟩, hq, hj⟩
    have hle : nP ≤ q := hr.1
    refine ⟨q - nP, by omega, ?_, by omega⟩
    rw [← recAt_add_iff (nP := nP), Nat.add_sub_cancel' hle]
    exact hr
  · rintro ⟨l, hl, hm, hj⟩
    exact ⟨nP + l, ⟨recAt_add_iff.mpr hm, by omega⟩, by omega, by omega⟩

omit [SetTheory V] in
/-- A position outside `recIdxOf` is neither recursive nor reflexive. -/
theorem kind_of_not_mem_recIdxOf {ks : List RecFieldKind} {i : Nat} (h : i ∉ ConLeche.recIdxOf ks) :
    ks.getD i .ordinary ≠ .recursive ∧ ks.getD i .ordinary ≠ .reflexive := by
  have hlt : ks.getD i .ordinary ≠ .ordinary → i < ks.length := by
    intro hne
    refine Classical.byContradiction fun hge => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hge)] at hne
    exact hne rfl
  constructor
  · intro hk; exact h (mem_recIdxOf.mpr ⟨hlt (by rw [hk]; decide), Or.inl hk⟩)
  · intro hk; exact h (mem_recIdxOf.mpr ⟨hlt (by rw [hk]; decide), Or.inr hk⟩)

omit [SetTheory V] in
/-- A lift at a cutoff above every index of `P` changes nothing `P`
sees. -/
theorem NoBVar_liftN_below_iff {n : Nat} :
    ∀ (e : AnnotTerm) {c : Nat} {P : Nat → Prop}, (∀ j, P j → j < c) →
      (NoBVar P (e.liftN n c) ↔ NoBVar P e)
  | .bvar i, c, P, hP => by
    show ¬ P (if i < c then i else i + n) ↔ ¬ P i
    split
    · exact Iff.rfl
    · next hic =>
      constructor
      · intro _ h; have := hP _ h; omega
      · intro _ h; have := hP _ h; omega
  | .sort _, _, _, _ => Iff.rfl
  | .const _ _, _, _, _ => Iff.rfl
  | .prf, _, _, _ => Iff.rfl
  | .app f a, c, P, hP => by
    show NoBVar P (f.liftN n c) ∧ NoBVar P (a.liftN n c) ↔ NoBVar P f ∧ NoBVar P a
    rw [NoBVar_liftN_below_iff f hP, NoBVar_liftN_below_iff a hP]
  | .lam _ A b, c, P, hP => by
    show NoBVar P (A.liftN n c) ∧ NoBVar (shiftP P) (b.liftN n (c + 1)) ↔
      NoBVar P A ∧ NoBVar (shiftP P) b
    rw [NoBVar_liftN_below_iff A hP, NoBVar_liftN_below_iff b (c := c + 1) (P := shiftP P)
      fun j hj => by
        cases j with
        | zero => exact hj.elim
        | succ j => have := hP j hj; omega]
  | .pi _ _ A B, c, P, hP => by
    show NoBVar P (A.liftN n c) ∧ NoBVar (shiftP P) (B.liftN n (c + 1)) ↔
      NoBVar P A ∧ NoBVar (shiftP P) B
    rw [NoBVar_liftN_below_iff A hP, NoBVar_liftN_below_iff B (c := c + 1) (P := shiftP P)
      fun j hj => by
        cases j with
        | zero => exact hj.elim
        | succ j => have := hP j hj; omega]
  | .eqE a b, c, P, hP => by
    show NoBVar P (a.liftN n c) ∧ NoBVar P (b.liftN n c) ↔ NoBVar P a ∧ NoBVar P b
    rw [NoBVar_liftN_below_iff a hP, NoBVar_liftN_below_iff b hP]
  | .fst e, c, P, hP => NoBVar_liftN_below_iff e hP
  | .snd e, c, P, hP => NoBVar_liftN_below_iff e hP

namespace IndRepData

variable (d : IndRepData V)

set_option maxHeartbeats 3200000 in
/-- **No later reading mentions a replaced position** (`PsiSetup.hnbP`):
the replaced positions of ψ's body are exactly the copy constructor's
recursive fields, whose `NoBVar` facts the auxiliary datum carries
(`noBVar_entries`); every container reading is the copy's reading
under the substitution of the pin's readings for the container's
parameters (the record), which touches no field variable
(`NoBVar_instSeq_iff`), and the transports' telescopes and readings
are the copy's lifted over the pin's readings. -/
theorem noBVar_psi {m : EnvModel V env} {env₀ env₀J : Env} {lpsT lpsJ : List Name} {ψ ψ' : Name → Nat}
    {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP) {k₀ j₀ : Nat}
    (auxOf : Nat → Nat) (cd : Nat → CopyData V) (tbl : Nat → AnnotTerm) (b : Nat)
    {Jc : Nat} {cAJ cAa : ConstantVal × Nat} (hnF : cAa.2 = cAJ.2)
    (hrec : d.CopyCtorAsRead m dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) cAJ.2)
    (hDA : FixCtorDataI m env₀ (d.memberName (d.mems (auxOf Jc))) lpsT cAa.1 d.nP cAa.2
      (d.nIdxAt (d.mems (auxOf Jc))) d.resSort d.isProp d.large (d.idxF (auxOf Jc)) (d.dsF (auxOf Jc))
      (d.esF (auxOf Jc)) (d.srcsF (auxOf Jc)) (d.ksF (auxOf Jc)) (d.fvsPF (auxOf Jc))
      (d.xFvsF (auxOf Jc)) (d.xrestF (auxOf Jc)) (d.eissF (auxOf Jc)) (d.tssF (auxOf Jc))
      (fun i => d.memberName (d.tgts (auxOf Jc) i)) (fun i => d.nIdxAt (d.tgts (auxOf Jc) i)))
    (hcf : cAa.1.type.hasFvar = false) (hcb : cAa.1.type.looseBVarsBounded 0 = true)
    (hviewA : d.ksR (auxOf Jc) = d.ksF (auxOf Jc) ∧ d.tgtsR (auxOf Jc) = d.tgts (auxOf Jc) ∧
      d.eissR (auxOf Jc) = d.eissF (auxOf Jc) ∧ d.tssR (auxOf Jc) = d.tssF (auxOf Jc))
    (hDJ : FixCtorDataI m env₀J (dJ.memberName (dJ.mems Jc)) lpsJ cAJ.1 dJ.nP cAJ.2
      (dJ.nIdxAt (dJ.mems Jc)) dJ.resSort dJ.isProp dJ.large (dJ.idxF Jc) (dJ.dsF Jc) (dJ.esF Jc)
      (dJ.srcsF Jc) (dJ.ksF Jc) (dJ.fvsPF Jc) (dJ.xFvsF Jc) (dJ.xrestF Jc) (dJ.eissF Jc) (dJ.tssF Jc)
      (fun i => dJ.memberName (dJ.tgts Jc i)) (fun i => dJ.nIdxAt (dJ.tgts Jc i))) :
    let P := replaced (psiUseIh dJ Jc) (d.psiVia dJ ψ k₀ dJ.nP auxOf b tbl Jc)
    (∀ i, i < cAJ.2 →
      NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i)) ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2) ∧
    (∀ i, i < cAJ.2 → ∀ k dd, ((dJ.tssF Jc ψ').getD i [])[k]? = some dd →
      NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + k)) dd.2.2) ∧
    (∀ i, i < cAJ.2 → ∀ E ∈ (dJ.eissF Jc ψ').getD i [],
      NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + ((dJ.tssF Jc ψ').getD i []).length)) E) ∧
    (∀ E ∈ dJ.esF Jc ψ', NoBVar (exclP (replP dJ.nP P cAJ.2) (dJ.nP + cAJ.2)) E) ∧
    (∀ i, i < cAJ.2 → ∀ Ψ Eis tl, d.psiVia dJ ψ k₀ dJ.nP auxOf b tbl Jc i = some (Ψ, Eis, tl) →
      (∀ k dd, tl[k]? = some dd → NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + k)) dd.2.2) ∧
      ∀ E ∈ Eis, NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + tl.length)) E) := by
  intro P
  obtain ⟨hviewK, hviewT, hviewE, hviewS⟩ := hviewA
  obtain ⟨hnb, hnbT, hnbE, hnbEs⟩ := FixCtorDataI.noBVar_entries hDA hcf hcb ψ
  have hlenK : (d.ksF (auxOf Jc)).length = cAJ.2 := by rw [hDA.ksLen, hnF]
  have hlenKJ : (dJ.ksF Jc).length = cAJ.2 := hDJ.ksLen
  -- the replaced positions are the copy's recursive fields
  have hPiff : ∀ l, P l ↔ l ∈ ConLeche.recIdxOf (d.ksF (auxOf Jc)) := by
    intro l
    show psiUseIh dJ Jc l = true ∨ (d.psiVia dJ ψ k₀ dJ.nP auxOf b tbl Jc l).isSome = true ↔ _
    rw [psiVia_isSome, hviewK]
    constructor
    · rintro (h | ⟨h, -⟩)
      · have hl : l ∈ ConLeche.recIdxOf (dJ.ksF Jc) := of_decide_eq_true h
        obtain ⟨hkind, -, -, -⟩ := hrec.kindR l hl
        obtain ⟨hlt, hk⟩ := mem_recIdxOf.mp hl
        rw [hviewK] at hkind
        exact mem_recIdxOf.mpr ⟨by rw [hlenK, ← hlenKJ]; exact hlt, by rw [hkind]; exact hk⟩
      · exact h
    · intro h
      by_cases hl : l ∈ ConLeche.recIdxOf (dJ.ksF Jc)
      · exact Or.inl (decide_eq_true hl)
      · exact Or.inr ⟨h, hl⟩
  have hPeq : ∀ n k j, exclP (replP dJ.nP P n) (dJ.nP + n + k) j ↔
      exclP (fun q => recAt d.nP (d.ksF (auxOf Jc)) q ∧ q < d.nP + n) (d.nP + n + k) j := by
    intro n k j
    rw [exclP_replP_iff rfl, exclP_recAt_iff rfl]
    constructor
    · rintro ⟨l, hl, hP, hj⟩; exact ⟨l, hl, (hPiff l).mp hP, hj⟩
    · rintro ⟨l, hl, hP, hj⟩; exact ⟨l, hl, (hPiff l).mpr hP, hj⟩
  have hPbelow : ∀ n k j, exclP (replP dJ.nP P n) (dJ.nP + n + k) j → j < n + k := by
    intro n k j h
    obtain ⟨l, hl, -, hj⟩ := (exclP_replP_iff rfl).mp h
    omega
  have hQbelow : ∀ n k j, exclP (fun q => recAt d.nP (d.ksF (auxOf Jc)) q ∧ q < d.nP + n)
      (d.nP + n + k) j → j < n + k := by
    intro n k j h
    obtain ⟨l, hl, -, hj⟩ := (exclP_recAt_iff rfl).mp h
    omega
  have hpos : DsA ≠ [] → 1 ≤ dJ.nP := fun hne => by
    rw [← hDsA]
    cases DsA with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  -- a container telescope entry and index reading at a recursive position
  have htssJ : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
      ∀ k dd, ((dJ.tssF Jc ψ').getD i [])[k]? = some dd →
        NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + k)) dd.2.2 := by
    intro i hi hR k dd hk
    obtain ⟨-, -, htss, -⟩ := hrec.kindR i hR
    have hA : ((d.tssF (auxOf Jc) ψ).getD i [])[k]?
        = some (dd.1, dd.2.1, ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1 + k) dd.2.2) := by
      rw [← hviewS, htss, instSeqDoms_getElem?, hk]; rfl
    have h := hnbT i (by rw [hnF]; exact hi) k _ hA
    refine NoBVar_congr (fun j => (hPeq i k j).symm) _ ?_
    exact (NoBVar_instSeq_iff DsA _ _ (fun q hq => by
      have := hQbelow i k q hq
      rw [hDsA]
      rcases Nat.eq_zero_or_pos dJ.nP with h0 | h0
      · omega
      · omega)).mp h
  have heissJ : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
      ∀ E ∈ (dJ.eissF Jc ψ').getD i [],
        NoBVar (exclP (replP dJ.nP P i) (dJ.nP + i + ((dJ.tssF Jc ψ').getD i []).length)) E := by
    intro i hi hR E hE
    obtain ⟨-, -, htss, heiss⟩ := hrec.kindR i hR
    have hlenT : ((d.tssF (auxOf Jc) ψ).getD i []).length = ((dJ.tssF Jc ψ').getD i []).length := by
      rw [← hviewS, htss, instSeqDoms_length]
    have hA : ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i + ((dJ.tssF Jc ψ').getD i []).length - 1) E
        ∈ (d.eissF (auxOf Jc) ψ).getD i [] := by
      rw [← hviewE, heiss]; exact List.mem_map_of_mem hE
    have h := hnbE i (by rw [hnF]; exact hi) _ hA
    rw [hlenT] at h
    refine NoBVar_congr (fun j => (hPeq i _ j).symm) _ ?_
    exact (NoBVar_instSeq_iff DsA _ _ (fun q hq => by
      have := hQbelow i _ q hq
      rw [hDsA]
      rcases Nat.eq_zero_or_pos dJ.nP with h0 | h0
      · omega
      · omega)).mp h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the field domains
    intro i hi
    by_cases hR : i ∈ ConLeche.recIdxOf (dJ.ksF Jc)
    · -- a field the container sees as recursive: the container's own entry
      rw [FixCtorDataI.recRefl_entry hDJ ψ' hR]
      refine NoBVar_mkPisAV_exclP _ (fun q hq => replP_lt q hq) (htssJ i hi hR) ?_
      refine NoBVar_mkAppN (NoBVar_of_bvarsBelow (m.cval_closedL _ ψ') (fun j _ => Nat.zero_le _)) _ ?_
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
        have hk' : k < dJ.nP := List.mem_range.mp hk
        show ¬ exclP _ _ _
        intro hq
        have := hPbelow i _ _ hq
        omega
      · exact heissJ i hi hR a ha
    · by_cases hT : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc))
      · -- a transport: the container's substituted domain is the copy's tower
        obtain ⟨j', -, -, heq⟩ := hrec.kindT i hi hR hT
        rw [hviewK] at hT
        have hrhs : NoBVar (exclP (fun q => recAt d.nP (d.ksF (auxOf Jc)) q ∧ q < d.nP + i) (d.nP + i))
            (mkPisAV ((d.tssR (auxOf Jc) ψ).getD i [])
              (AnnotTerm.mkAppN (m.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')
                (((cd j').DsA).map (·.liftN (i + ((d.tssR (auxOf Jc) ψ).getD i []).length) 0) ++
                  (d.eissR (auxOf Jc) ψ).getD i []))) := by
          rw [hviewS, hviewE]
          refine NoBVar_mkPisAV_exclP _ (fun q hq => hq.2) (hnbT i (by rw [hnF]; exact hi)) ?_
          refine NoBVar_mkAppN (NoBVar_of_bvarsBelow (m.cval_closedL _ _) (fun j _ => Nat.zero_le _)) _ ?_
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨D, -, rfl⟩ := List.mem_map.mp ha
            exact NoBVar_liftN_zero (fun j hj => hQbelow i _ j hj) D
          · exact hnbE i (by rw [hnF]; exact hi) a ha
        rw [← heq] at hrhs
        refine NoBVar_congr (fun j => (hPeq i 0 j).symm) _ ?_
        exact (NoBVar_instSeq_iff DsA _ _ (fun q hq => by
          have := hQbelow i 0 q hq
          rw [hDsA]
          rcases Nat.eq_zero_or_pos dJ.nP with h0 | h0
          · omega
          · omega)).mp hrhs
      · -- ordinary on both sides
        have h := hnb i (by rw [hnF]; exact hi)
        rw [hrec.ord i hi hR hT] at h
        refine NoBVar_congr (fun j => (hPeq i 0 j).symm) _ ?_
        exact (NoBVar_instSeq_iff DsA _ _ (fun q hq => by
          have := hQbelow i 0 q hq
          rw [hDsA]
          rcases Nat.eq_zero_or_pos dJ.nP with h0 | h0
          · omega
          · omega)).mp h
  · -- the container's telescopes
    intro i hi k dd hk
    by_cases hR : i ∈ ConLeche.recIdxOf (dJ.ksF Jc)
    · exact htssJ i hi hR k dd hk
    · rw [hDJ.tssNone ψ' i (kind_of_not_mem_recIdxOf hR).2] at hk
      exact nomatch hk
  · -- the container's index readings
    intro i hi E hE
    by_cases hR : i ∈ ConLeche.recIdxOf (dJ.ksF Jc)
    · exact heissJ i hi hR E hE
    · rw [hDJ.ordNone ψ' i (kind_of_not_mem_recIdxOf hR).1 (kind_of_not_mem_recIdxOf hR).2] at hE
      exact nomatch hE
  · -- the result's index readings
    intro E hE
    have hA : ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + cAJ.2 - 1) E ∈ d.esF (auxOf Jc) ψ := by
      rw [hrec.es]; exact List.mem_map_of_mem hE
    have h := hnbEs _ hA
    rw [hnF] at h
    refine NoBVar_congr (fun j => (hPeq cAJ.2 0 j).symm) _ ?_
    exact (NoBVar_instSeq_iff DsA _ _ (fun q hq => by
      have := hQbelow cAJ.2 0 q hq
      rw [hDsA]
      rcases Nat.eq_zero_or_pos dJ.nP with h0 | h0
      · omega
      · omega)).mp h
  · -- the transports' telescopes and readings
    intro i hi Ψ Eis tl hvia
    unfold IndRepData.psiVia at hvia
    split at hvia
    · next hT =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hvia
      obtain ⟨-, rfl, rfl⟩ := hvia
      rw [hviewK] at hT
      refine ⟨?_, ?_⟩
      · intro k dd hk
        rw [rebit_getElem?, liftDoms_getElem?] at hk
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hk
        obtain ⟨d'', hd'', rfl⟩ := Option.map_eq_some_iff.mp hd'
        show NoBVar _ (d''.2.2.liftN dJ.nP (i + k))
        rw [NoBVar_liftN_below_iff _ (fun j hj => hPbelow i k j hj)]
        rw [hviewS] at hd''
        exact NoBVar_congr (fun j => (hPeq i k j).symm) _ (hnbT i (by rw [hnF]; exact hi) k d'' hd'')
      · intro E hE
        obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
        rw [rebit_length, liftDoms_length]
        rw [NoBVar_liftN_below_iff _ (fun j hj => hPbelow i _ j hj)]
        rw [hviewE] at hE'
        rw [hviewS]
        exact NoBVar_congr (fun j => (hPeq i _ j).symm) _ (hnbE i (by rw [hnF]; exact hi) E' hE')
    · exact nomatch hvia


/-! ## The transports: the container's field domain at a nested occurrence -/

/-- **A transport's container domain, substituted**: at a prefix
fitting the container's earlier fields, the container's field domain
at the pin's readings reads as — and is graded like — the Π-tower over
the copy's telescope of the target container at the target pin's
readings at the copy's index readings (the record's `kindT`, through
`interp_instSeq_under`/`wellDenotedV_instSeq_under`). -/
theorem containerDom_transport (m : EnvModel V env) {ψ ψ' : Name → Nat} {σ : Nat → V}
    {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP)
    (hDsWD : ∀ p ∈ DsA, WellDenotedV V σ p) {k₀ j₀ : Nat} (auxOf : Nat → Nat) (cd : Nat → CopyData V)
    {Jc nF : Nat}
    (hrec : d.CopyCtorAsRead m dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) nF)
    {bodyJ : AnnotTerm}
    (hTJ : WellDenotedV V (consList (DsA.map (interp V σ)) σ)
      (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ))
    (hlenJ : (dJ.dsF Jc ψ').length = dJ.nP + nF)
    {i : Nat} (hi : i < nF) (hT : i ∉ ConLeche.recIdxOf (dJ.ksF Jc))
    (hA : i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)))
    {fs' : List V} (hfs' : fs'.length = i)
    (hfit : SpineFit (consList (DsA.map (interp V σ)) σ)
      ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) fs') :
    ∃ j', d.tgtsR (auxOf Jc) i = k₀ + j' ∧ ¬ (j₀ ≤ j' ∧ j' < j₀ + dJ.k) ∧
      interp V (consList fs' (consList (DsA.map (interp V σ)) σ))
          ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2
        = interp V (consList fs' σ)
            (mkPisAV ((d.tssR (auxOf Jc) ψ).getD i [])
              (AnnotTerm.mkAppN (m.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')
                (((cd j').DsA).map (·.liftN (i + ((d.tssR (auxOf Jc) ψ).getD i []).length) 0) ++
                  (d.eissR (auxOf Jc) ψ).getD i []))) ∧
      WellDenotedV V (consList fs' σ)
        (mkPisAV ((d.tssR (auxOf Jc) ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')
            (((cd j').DsA).map (·.liftN (i + ((d.tssR (auxOf Jc) ψ).getD i []).length) 0) ++
              (d.eissR (auxOf Jc) ψ).getD i []))) := by
  obtain ⟨j', h1, h2, heq⟩ := hrec.kindT i hi hT hA
  have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
  have hlen : DsA ≠ [] → DsA.length + fs'.length = dJ.nP + i - 1 + 1 := by
    intro hne
    rw [hDsA, hfs']
    have : 1 ≤ dJ.nP := by
      rw [← hDsA]
      cases DsA with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    omega
  have hlt : dJ.nP + i < (dJ.dsF Jc ψ').length := by rw [hlenJ]; omega
  have hentry : ((dJ.dsF Jc ψ').drop dJ.nP).getD i default = (dJ.dsF Jc ψ').getD (dJ.nP + i) default := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hi' : i < ((dJ.dsF Jc ψ').drop dJ.nP).length := by rw [List.length_drop, hlenJ]; omega
  have hget : ((dJ.dsF Jc ψ').drop dJ.nP)[i]? = some (((dJ.dsF Jc ψ').drop dJ.nP).getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  refine ⟨j', h1, h2, ?_, ?_⟩
  · rw [← heq, interp_instSeq_under σ DsA fs' _ _ hlen]
  · have hE := wellDenoted_mkPisAV_dom hTJ.1 fs' i _ hget hfit
    have hE' := annotValid_mkPisAV_dom hTJ.2 fs' i _ hget hfit
    rw [hentry] at hE hE'
    rw [← heq]
    exact wellDenotedV_instSeq_under σ DsA fs' _ _ hlen hDsWD ⟨hE, hE'⟩

/-- **A transport's fits**: under telescope values fitting the copy's
telescope, the target container's application (graded, by the Π-tower
of `containerDom_transport`) is the leaf at the target pin's readings
and the copy's index readings, which fit the target container's
parameter and index telescopes (`LeafShape`), the index part at the
target pin's readings. -/
theorem transport_fits (m : EnvModel V env) {ψ : Name → Nat} {σ : Nat → V} {k₀ j' : Nat}
    {c : CopyData V} (hc : CopyData.Ok m d ψ k₀ j' c)
    {tssA : List (Nat × Nat × AnnotTerm)} {eissA : List AnnotTerm}
    (hEl : eissA.length = d.nIdxAt (k₀ + j')) {fs' : List V} {i : Nat} (hfs' : fs'.length = i)
    (hWD : WellDenotedV V (consList fs' σ)
      (mkPisAV tssA (AnnotTerm.mkAppN (m.acval (c.dJ.memberName c.mm) c.ψ')
        (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA))))
    {as : List V} (has : SpineFit (consList fs' σ) (tssA.map (·.2.2)) as) :
    WellDenotedV V (consList as (consList fs' σ))
        (AnnotTerm.mkAppN (m.acval (c.dJ.memberName c.mm) c.ψ')
          (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA)) ∧
      interp V (consList as (consList fs' σ))
          (AnnotTerm.mkAppN (m.acval (c.dJ.memberName c.mm) c.ψ')
            (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA))
        = (c.DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList fs' σ)))).foldl
            SetTheory.app (interp V σ (m.acval (c.dJ.memberName c.mm) c.ψ')) ∧
      SpineFit σ ((c.dJ.ppsM c.mm c.ψ').map (·.2.2))
        (c.DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList fs' σ)))) ∧
      SpineFit (consList (c.DsA.map (interp V σ)) σ) (c.dJ.IdsM c.mm c.ψ')
        (eissA.map (interp V (consList as (consList fs' σ)))) := by
  have hasLen : as.length = tssA.length := by rw [has.length_eq, List.length_map]
  have hclosed : Term.bvarsBelow 0 (m.acval (c.dJ.memberName c.mm) c.ψ').erase := m.cval_closedL _ c.ψ'
  have hbodyWD : WellDenotedV V (consList as (consList fs' σ))
      (AnnotTerm.mkAppN (m.acval (c.dJ.memberName c.mm) c.ψ')
        (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA)) :=
    ⟨wellDenoted_mkPisAV_body hWD.1 as has, annotValid_mkPisAV_body hWD.2 as has⟩
  have hDsV : (c.DsA.map (·.liftN (i + tssA.length) 0)).map (interp V (consList as (consList fs' σ)))
      = c.DsA.map (interp V σ) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro D _
    simp only [Function.comp_def]
    rw [interp_liftN, ← consList_append, show i + tssA.length = (fs' ++ as).length from by
      rw [List.length_append, hfs', hasLen], shiftE_consList]
  have hval : interp V (consList as (consList fs' σ))
      (AnnotTerm.mkAppN (m.acval (c.dJ.memberName c.mm) c.ψ')
        (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA))
      = (c.DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList fs' σ)))).foldl
          SetTheory.app (interp V σ (m.acval (c.dJ.memberName c.mm) c.ψ')) := by
    rw [interp_mkAppN_map, List.map_append, hDsV, interp_closed (V := V) hclosed _ σ]
  -- the leaf's tower: the readings fit its binders
  obtain ⟨hlenP, -, -, -⟩ := hc.ff
  obtain ⟨B, hB⟩ := hc.ls
  have hargsLen : (c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA).length
      = (c.dJ.ppsM c.mm c.ψ').length := by
    rw [List.length_append, List.length_map, hc.len, hEl, ← hc.idx.nIdx, hlenP]
  have hfitAll := spineFit_of_wellDenoted_lams (u := c.dJ.w c.ψ' + 1) (Nat.succ_ne_zero _) (b := B)
    (args := c.DsA.map (·.liftN (i + tssA.length) 0) ++ eissA) (ds := c.dJ.ppsM c.mm c.ψ')
    (σ := σ) (ρ := consList as (consList fs' σ)) (f := m.acval (c.dJ.memberName c.mm) c.ψ')
    (Nat.le_of_eq hargsLen) hbodyWD.1
    (by rw [hB]; exact interp_closed (V := V) (by rw [← hB]; exact hclosed) _ _)
  rw [hargsLen, List.take_of_length_le (Nat.le_refl _), List.map_append, hDsV] at hfitAll
  refine ⟨hbodyWD, hval, hfitAll, ?_⟩
  have hsplit : (c.dJ.ppsM c.mm c.ψ').map (·.2.2)
      = ((c.dJ.ppsM c.mm c.ψ').take c.dJ.nP).map (·.2.2) ++
        ((c.dJ.ppsM c.mm c.ψ').drop c.dJ.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  have h := hfitAll
  rw [hsplit] at h
  obtain ⟨as₁, as₂, heq, h₁, h₂⟩ := spineFit_append_inv h
  have hlen₁ : as₁.length = (c.DsA.map (interp V σ)).length := by
    rw [h₁.length_eq, List.length_map, List.length_take, hlenP, List.length_map, hc.len]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hlen₁.symm
  exact h₂

set_option maxHeartbeats 3200000 in
/-- **The ONE fact of each transport** (`PsiSetup.hvia`): at a spine
fitting the container's fields and telescope values fitting the
transport's telescope, the earlier copy's term (lifted over the pin's
readings) at the copy's index readings and the field lands in the
target copy's fold target — `via_of_typed` at the target's `PsiTyped`,
the fits from the container's field domain read as the target
container at its pin (`containerDom_transport`, `transport_fits`). -/
theorem via_psi {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name} {ψ ψ' : Name → Nat}
    {σ : Nat → V} {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP)
    (hDsWD : ∀ p ∈ DsA, WellDenotedV V σ p) {k₀ j₀ : Nat} (auxOf : Nat → Nat) (cd : Nat → CopyData V)
    (tbl : Nat → AnnotTerm) {Jc : Nat} {cAJ cAa : ConstantVal × Nat} (hnF : cAa.2 = cAJ.2)
    (hrec : d.CopyCtorAsRead mp.base2 dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) cAJ.2)
    (hDA : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems (auxOf Jc))) lpsT cAa.1 d.nP cAa.2
      (d.nIdxAt (d.mems (auxOf Jc))) d.resSort d.isProp d.large (d.idxF (auxOf Jc)) (d.dsF (auxOf Jc))
      (d.esF (auxOf Jc)) (d.srcsF (auxOf Jc)) (d.ksF (auxOf Jc)) (d.fvsPF (auxOf Jc))
      (d.xFvsF (auxOf Jc)) (d.xrestF (auxOf Jc)) (d.eissF (auxOf Jc)) (d.tssF (auxOf Jc))
      (fun i => d.memberName (d.tgts (auxOf Jc) i)) (fun i => d.nIdxAt (d.tgts (auxOf Jc) i)))
    (hviewA : d.ksR (auxOf Jc) = d.ksF (auxOf Jc) ∧ d.tgtsR (auxOf Jc) = d.tgts (auxOf Jc) ∧
      d.eissR (auxOf Jc) = d.eissF (auxOf Jc) ∧ d.tssR (auxOf Jc) = d.tssF (auxOf Jc))
    {bodyJ : AnnotTerm}
    (hTJ : WellDenotedV V (consList (DsA.map (interp V σ)) σ)
      (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ))
    (hlenJ : (dJ.dsF Jc ψ').length = dJ.nP + cAJ.2)
    (hbz : dJ.bb ψ' = 0 ↔ d.resSort.eval ψ = 0)
    (hcd : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR (auxOf Jc) i - k₀) (cd (d.tgtsR (auxOf Jc) i - k₀)))
    (htbl : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.PsiTyped mp.base2 (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ' σ
        (cd (d.tgtsR (auxOf Jc) i - k₀)).DsA
        (d.psiL mp.base2 ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀)).base)
        (d.psiPinsT (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.nP) (cd (d.tgtsR (auxOf Jc) i - k₀)).mm
        (tbl (d.tgtsR (auxOf Jc) i - k₀))) :
    ∀ i, i < cAJ.2 → ∀ Ψ Eis tl, d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc i = some (Ψ, Eis, tl) →
      ∀ fs : List V,
        SpineFit (consList (DsA.map (interp V σ)) σ) (((dJ.dsF Jc ψ').drop dJ.nP).map (·.2.2)) fs →
        ∀ as, SpineFit (consList (fs.take i) (consList (DsA.map (interp V σ)) σ)) (tl.map (·.2.2)) as →
          (Eis.map (interp V (consList as (consList (fs.take i) (consList (DsA.map (interp V σ)) σ)))) ++
            [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
              (interp V (consList (DsA.map (interp V σ)) σ) Ψ)
            ∈ˢ (Eis.map (interp V (consList as (consList (fs.take i)
                  (consList (DsA.map (interp V σ)) σ))))).foldl SetTheory.app
                (interp V σ (d.psiTgV mp.base2 ψ k₀ auxOf cd Jc i)) := by
  intro i hi Ψ Eis tl hvia fs hfs as has
  obtain ⟨hviewK, hviewT, hviewE, hviewS⟩ := hviewA
  unfold IndRepData.psiVia at hvia
  split at hvia
  · next hT =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hvia
    obtain ⟨rfl, rfl, rfl⟩ := hvia
    have hc := hcd i hi hT.1 hT.2
    have hT' := htbl i hi hT.1 hT.2
    have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
    generalize htssA : (d.tssR (auxOf Jc) ψ).getD i [] = tssA at has ⊢
    generalize heissA : (d.eissR (auxOf Jc) ψ).getD i [] = eissA at ⊢
    -- the fields' prefix fit and the field's membership
    have hfsLen : fs.length = cAJ.2 := by
      rw [hfs.length_eq, List.length_map, List.length_drop, hlenJ]; omega
    have hfsTake : (fs.take i).length = i := by rw [List.length_take]; omega
    have hfit' : SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) (fs.take i) := by
      have h := hfs
      rw [← List.take_append_drop i ((dJ.dsF Jc ψ').drop dJ.nP), List.map_append] at h
      obtain ⟨as₁, as₂, heq, h₁, -⟩ := spineFit_append_inv h
      have hlen₁ : as₁.length = i := by
        rw [h₁.length_eq, List.length_map, List.length_take, List.length_drop, hlenJ]; omega
      have hfsTake' : fs.take i = as₁ := by
        rw [heq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      rw [hfsTake']
      exact h₁
    have hlt : dJ.nP + i < (dJ.dsF Jc ψ').length := by rw [hlenJ]; omega
    have hmemI : fs.getD i pt ∈ˢ interp V (consList (fs.take i) (consList (DsA.map (interp V σ)) σ))
        ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2 :=
      spineFit_getElem? hfs i (fs.getD i pt) ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < fs.length)]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem hlt,
          Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
    -- the container's domain, substituted
    obtain ⟨j', h1, -, hint, hWD⟩ := containerDom_transport d mp.base2 hDsA hDsWD auxOf cd hrec hTJ
      hlenJ hi hT.2 hT.1 hfsTake hfit'
    rw [htssA, heissA] at hint hWD
    have hj' : d.tgtsR (auxOf Jc) i - k₀ = j' := by omega
    rw [hj'] at hc hT' ⊢
    -- the telescope values fit the copy's telescope at the block's frame
    have hasA : SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as := by
      have hsh := shiftE_consList_middle (fs.take i) (DsA.map (interp V σ)) σ
      rw [hfsTake, hDsLen] at hsh
      rw [rebit_map_dom, spineFit_liftDoms, hsh] at has
      exact has
    have hasLen : as.length = tssA.length := by rw [hasA.length_eq, List.length_map]
    -- the copy's index count is the target's
    have hEl : eissA.length = d.nIdxAt (k₀ + j') := by
      obtain ⟨hlt', hk⟩ := mem_recIdxOf.mp hT.1
      rw [hviewK, hDA.ksLen] at hlt'
      rw [← h1, ← heissA, hviewE, hviewT]
      rw [hviewK] at hk
      rcases hk with hk | hk
      · exact hDA.eisLen ψ i hk hlt'
      · exact hDA.eisLenRefl ψ i hk hlt'
    obtain ⟨hbodyWD, hval, hfitAll, hfitIdx⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD hasA
    -- the field's value at the telescope values lands in the target container
    have hbitsT : ∀ dd ∈ tssA, (dJ.bb ψ' = 0 ↔ dd.2.1 = 0) := by
      intro dd hd
      rw [hbz]
      exact (hDA.tssBits ψ i dd (by rw [← hviewS, htssA]; exact hd)).symm
    have hx : as.foldl SetTheory.app (fs.getD i pt)
        ∈ˢ ((cd j').DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList (fs.take i) σ)))).foldl
          SetTheory.app (interp V σ (mp.base2.acval ((cd j').dJ.memberName (cd j').mm) (cd j').ψ')) := by
      rw [hint] at hmemI
      have h := mkPisAV_fold_mem (m := dJ.bb ψ') hbitsT
        (fun h0 as' has' => by
          obtain ⟨-, hval', hfitAll', -⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD has'
          rw [hval']
          obtain ⟨hlenP, hbitsP, hmemL, -⟩ := hc.ff
          have := mkPisAV_fold_mem (m := 1)
            (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbitsP dd hd)⟩)
            (fun h => absurd h Nat.one_ne_zero) (hmemL σ) hfitAll'
          rw [interp_sort] at this
          have hw0 : (cd j').dJ.w (cd j').ψ' = 0 := by
            rw [hc.idx.sort]; exact hbz.mp h0
          rw [hw0, univ_zero] at this
          exact this)
        hmemI hasA
      rw [hval] at h
      exact h
    -- `via_of_typed` at the target
    have hDsLen' : ((cd j').DsA.map (interp V σ)).length = (cd j').dJ.nP := by
      rw [List.length_map, hc.len]
    have hEisLen : (eissA.map (interp V (consList as (consList (fs.take i) σ)))).length
        = (cd j').dJ.nIdxs.getD (cd j').mm 0 := by
      have := hfitIdx.length_eq
      unfold IndRepData.IdsM at this
      simp only [List.length_map, List.length_drop] at this
      rw [hc.ff.1] at this
      rw [List.length_map]
      show eissA.length = (cd j').dJ.nIdxAt (cd j').mm
      omega
    have hfitM : SpineFit (consList ((cd j').DsA.map (interp V σ)) σ)
        (((cd j').dJ.motDataAV mp.base2 (cd j').ψ' (cd j').mm).map (·.2.2))
        (eissA.map (interp V (consList as (consList (fs.take i) σ))) ++ [as.foldl SetTheory.app (fs.getD i pt)]) := by
      unfold IndRepData.motDataAV
      rw [List.map_append, List.map_singleton, rebit_map_dom, (cd j').dJ.ipss_getD _ hc.mm]
      refine SpineFit.append hfitIdx ⟨?_, trivial⟩
      rw [(cd j').dJ.Ls_getD_eq mp.base2 _ hc.mm,
        show (cd j').dJ.pinsOf (cd j').ψ' (cd j').mm = paramBvarsAt (cd j').dJ.nP (cd j').dJ.nP from
          hc.pins _,
        ← hEisLen, interp_famAppAV_params (mp.base2.cval_closedL _ _) hDsLen' rfl σ]
      exact hx
    have hisFit : SpineFit (consList ((cd j').DsA.map (interp V σ)) σ)
        ((rebit (pwBit (cd j').ψ' ConLeche.PropWhen.never) (((cd j').dJ.ipss (cd j').ψ').getD (cd j').mm [])).map
          (·.2.2))
        (eissA.map (interp V (consList as (consList (fs.take i) σ)))) := by
      rw [rebit_map_dom, (cd j').dJ.ipss_getD _ hc.mm]; exact hfitIdx
    have hres := (cd j').dJ.via_of_typed mp.base2 hT' (psV := DsA.map (interp V σ)) hfitM hisFit
    -- the transport's readings are the copy's
    have hEv : (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
        (interp V (consList as (consList (fs.take i) (consList (DsA.map (interp V σ)) σ))))
        = eissA.map (interp V (consList as (consList (fs.take i) σ))) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro E _
      simp only [Function.comp_def]
      rw [← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
        ← consList_append (xs := fs.take i) (ys := as) (ρ := σ), ← hDsLen,
        show i + tssA.length = (fs.take i ++ as).length from by
          rw [List.length_append, hfsTake, hasLen],
        interp_liftN_middle]
    rw [hEv, ← hDsLen]
    have hTg : d.psiTgV mp.base2 ψ k₀ auxOf cd Jc i = d.psiTgOf mp.base2 ψ k₀ (cd j') := by
      unfold IndRepData.psiTgV; rw [hj']
    first
    | (rw [hTg]; exact hres)
    | exact hres
  · exact nomatch hvia

end IndRepData

/-! ## Towers at the ih frame, entry by entry -/

omit [SetTheory V] in
theorem ihTeleAtGo_take (nF o i l : Nat) :
    ∀ (k₀ : Nat) (tl : List (Nat × Nat × AnnotTerm)) (k : Nat),
      (ihTeleAtGo nF o i l k₀ tl).take k = ihTeleAtGo nF o i l k₀ (tl.take k)
  | _, [], _ => by simp [ihTeleAtGo]
  | k₀, d :: tl, 0 => rfl
  | k₀, d :: tl, k + 1 => by
    simp only [ihTeleAtGo, List.take_succ_cons, ihTeleAtGo_take nF o i l (k₀ + 1) tl k]

/-- A Π-tower is graded when its entries are graded under every
fitting prefix and its body under every fitting spine (the converse of
`wellDenoted_mkPisAV_dom`/`wellDenoted_mkPisAV_body`). -/
theorem wellDenoted_mkPisAV_of {B : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ (k : Nat) (dd : Nat × Nat × AnnotTerm), ds[k]? = some dd →
        ∀ as : List V, SpineFit ρ ((ds.take k).map (·.2.2)) as → WellDenoted V (consList as ρ) dd.2.2) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as → WellDenoted V (consList as ρ) B) →
      WellDenoted V ρ (mkPisAV ds B)
  | [], ρ, _, hB => by
    have := hB [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hds, hB => by
    simp only [mkPisAV, WellDenoted_pi]
    refine ⟨by simpa using hds 0 d rfl [] trivial, fun x hx => ?_⟩
    rw [show cons x ρ = consList [x] ρ from rfl]
    refine wellDenoted_mkPisAV_of (fun k dd hk as hsp => ?_) (fun as hsp => ?_)
    · have := hds (k + 1) dd (by simpa using hk) (x :: as)
        (by rw [List.take_succ_cons, List.map_cons]; exact ⟨hx, hsp⟩)
      simpa [consList_cons] using this
    · have := hB (x :: as) ⟨hx, hsp⟩
      simpa [consList_cons] using this

/-! ## ψ's Π-type, and the fold's property -/

namespace IndRepData

variable (d : IndRepData V)

/-- **ψ's Π-type** at the block's parameter frame: over the container's
motive binders at the pin (its index telescope, then the major
`J DsA ı⃗`) at the elimination bit, the copy's carrier at the parameters
and the indices (lifted over the major) — the pin's readings
substituted for the container's parameters. -/
@[expose] def psiTyAV (m : EnvModel V env) (ψ' : Name → Nat) (DsA : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (t : Nat) : AnnotTerm :=
  ConLeche.Model.AnnotTerm.instSeq DsA (DsA.length - 1)
    (mkPisAV (rebit (d.bb ψ') (d.motDataAV m ψ' t))
      ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0))

/-- **The fold's property at a copy**: the term is graded and inhabits
ψ's Π-type — what a later copy's transport consumes (`via_of_typed`
through `psiTyped_of_pi`, and the transport's own grading). -/
@[expose] def PsiTypedPi (m : EnvModel V env) (ψ' : Name → Nat) (σ : Nat → V) (DsA : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (t : Nat) (Ψ : AnnotTerm) : Prop :=
  WellDenotedV V σ Ψ ∧ WellDenotedV V σ (d.psiTyAV m ψ' DsA L pinsT t) ∧
    interp V σ Ψ ∈ˢ interp V σ (d.psiTyAV m ψ' DsA L pinsT t)

/-- The Π-type's reading at the pin's readings. -/
theorem interp_psiTyAV (m : EnvModel V env) (ψ' : Name → Nat) (DsA : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (t : Nat) (σ : Nat → V) :
    interp V σ (d.psiTyAV m ψ' DsA L pinsT t)
      = interp V (consList (DsA.map (interp V σ)) σ)
          (mkPisAV (rebit (d.bb ψ') (d.motDataAV m ψ' t))
            ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0)) := by
  unfold psiTyAV
  rw [interp_instSeq_consList]

/-- **The pointwise typing from the Π-typing** (`mkPisAV_fold_mem` at
the target's `TargetOk`: at the zero bit the target is a truth
value). -/
theorem psiTyped_of_pi (m : EnvModel V env) {ψ' : Name → Nat} {σ : Nat → V} {DsA : List AnnotTerm}
    {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm} {t : Nat}
    (hips : ((d.ipss ψ').getD t []).length = d.nIdxs.getD t 0)
    (hTg : d.TargetOk ψ' σ DsA L pinsT t) {Ψ : AnnotTerm}
    (h : d.PsiTypedPi m ψ' σ DsA L pinsT t Ψ) : d.PsiTyped m ψ' σ DsA L pinsT t Ψ := by
  intro is x hfit
  have hmem := h.2.2
  rw [d.interp_psiTyAV] at hmem
  have hfit' : SpineFit (consList (DsA.map (interp V σ)) σ)
      ((rebit (d.bb ψ') (d.motDataAV m ψ' t)).map (·.2.2)) (is ++ [x]) := by
    rw [rebit_map_dom]; exact hfit
  have hisLen : is.length = d.nIdxs.getD t 0 := by
    have := hfit.length_eq
    unfold IndRepData.motDataAV at this
    rw [List.length_append, List.length_singleton, List.length_map, List.length_append,
      rebit_length, List.length_singleton, hips] at this
    omega
  have hzero : d.bb ψ' = 0 → ∀ vs : List V,
      SpineFit (consList (DsA.map (interp V σ)) σ) ((rebit (d.bb ψ') (d.motDataAV m ψ' t)).map (·.2.2)) vs →
      interp V (consList vs (consList (DsA.map (interp V σ)) σ))
        ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0)
        ∈ˢ (univZero : V) := by
    intro h0 vs hvs
    rw [rebit_map_dom] at hvs
    unfold IndRepData.motDataAV at hvs
    rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hvs
    obtain ⟨is', x', rfl, hisFit, -⟩ := hvs
    rw [consList_append, consList_cons, consList_nil, interp_liftN, shiftE_succ_cons,
      shiftE_zero_zero]
    have := ((hTg.2 is' hisFit).2)
    have h0' : d.elimL.eval ψ' = 0 := (pwBit_zeronessOf ψ' d.elimL).mp h0
    rw [h0', univ_zero] at this
    exact this
  have := mkPisAV_fold_mem (m := d.bb ψ') (fun dd hd => by rw [mem_rebit hd]) hzero hmem hfit'
  rw [consList_append, consList_cons, consList_nil, interp_liftN, shiftE_succ_cons,
    shiftE_zero_zero] at this
  exact this

end IndRepData

/-- A Π-tower at one bit is bit-valid when its entries are valid under
fitting prefixes and its body is valid under fitting spines — a truth
value at the zero bit (`annotValid_mkPisAV_rebit_sort`'s general
form). -/
theorem annotValid_mkPisAV_of {b : Nat} {B : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}, (∀ dd ∈ ds, dd.2.1 = b) →
      (∀ (k : Nat) (dd : Nat × Nat × AnnotTerm), ds[k]? = some dd →
        ∀ as : List V, SpineFit ρ ((ds.take k).map (·.2.2)) as → AnnotValid V (consList as ρ) dd.2.2) →
      (∀ as : List V, SpineFit ρ (ds.map (·.2.2)) as →
        AnnotValid V (consList as ρ) B ∧ (b = 0 → interp V (consList as ρ) B ∈ˢ (univZero : V))) →
      AnnotValid V ρ (mkPisAV ds B)
  | [], ρ, _, _, hB => by
    have := (hB [] trivial).1
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hbits, hds, hB => by
    simp only [mkPisAV, AnnotValid_pi]
    refine ⟨by simpa using hds 0 d rfl [] trivial, fun x hx => ?_, fun h0 x hx => ?_⟩
    · rw [show cons x ρ = consList [x] ρ from rfl]
      refine annotValid_mkPisAV_of (fun dd hd => hbits dd (List.mem_cons_of_mem _ hd))
        (fun k dd hk as hsp => ?_) (fun as hsp => ?_)
      · have := hds (k + 1) dd (by simpa using hk) (x :: as)
          (by rw [List.take_succ_cons, List.map_cons]; exact ⟨hx, hsp⟩)
        simpa [consList_cons] using this
      · have := hB (x :: as) ⟨hx, hsp⟩
        simpa [consList_cons] using this
    · have hb0 : b = 0 := by rw [← hbits d List.mem_cons_self]; exact h0
      cases ds with
      | nil =>
        have := (hB [x] ⟨hx, trivial⟩).2 hb0
        exact this
      | cons d' ds' =>
        exact mkPisAV_mem_univZero_of_bits (List.cons_ne_nil _ _)
          (fun dd hd => by rw [hbits dd (List.mem_cons_of_mem _ hd)]; exact hb0) _

namespace IndRepData

variable (d : IndRepData V)

set_option maxHeartbeats 6400000 in
/-- **The transports are graded at the leaf frame** (`PsiSetup.hviaWD`):
the transport entry is a λ-tower over the copy's telescope (moved to
the ih frame) whose body is the earlier copy's term at the copy's index
readings and the field at the telescope's variables.  The telescope's
entries are graded at the field frame (the container's domain, read as
the target container at its pin, `containerDom_transport`); the body is
graded by the earlier term's Π-type (`PsiTypedPi`) at the fit of the
readings and the field (`transport_fits`); the λ-tower's own type is
the target-form ih domain, graded by the target's fold target. -/
theorem viaWD_psi {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name} {ψ ψ' : Name → Nat}
    {σ : Nat → V} {dJ : IndRepData V} {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP)
    (hDsWD : ∀ p ∈ DsA, WellDenotedV V σ p) {k₀ j₀ : Nat} (auxOf : Nat → Nat) (cd : Nat → CopyData V)
    (tbl : Nat → AnnotTerm) {Jc : Nat} {cAJ cAa : ConstantVal × Nat} (hnF : cAa.2 = cAJ.2)
    (hrec : d.CopyCtorAsRead mp.base2 dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
      (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc (auxOf Jc) cAJ.2)
    (hDA : FixCtorDataI mp.base2 d.env₀ (d.memberName (d.mems (auxOf Jc))) lpsT cAa.1 d.nP cAa.2
      (d.nIdxAt (d.mems (auxOf Jc))) d.resSort d.isProp d.large (d.idxF (auxOf Jc)) (d.dsF (auxOf Jc))
      (d.esF (auxOf Jc)) (d.srcsF (auxOf Jc)) (d.ksF (auxOf Jc)) (d.fvsPF (auxOf Jc))
      (d.xFvsF (auxOf Jc)) (d.xrestF (auxOf Jc)) (d.eissF (auxOf Jc)) (d.tssF (auxOf Jc))
      (fun i => d.memberName (d.tgts (auxOf Jc) i)) (fun i => d.nIdxAt (d.tgts (auxOf Jc) i)))
    (hviewA : d.ksR (auxOf Jc) = d.ksF (auxOf Jc) ∧ d.tgtsR (auxOf Jc) = d.tgts (auxOf Jc) ∧
      d.eissR (auxOf Jc) = d.eissF (auxOf Jc) ∧ d.tssR (auxOf Jc) = d.tssF (auxOf Jc))
    {bodyJ : AnnotTerm}
    (hTJ : WellDenotedV V (consList (DsA.map (interp V σ)) σ)
      (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ))
    (hlenJ : (dJ.dsF Jc ψ').length = dJ.nP + cAJ.2)
    (hbz : dJ.bb ψ' = 0 ↔ d.resSort.eval ψ = 0) (hsatA : Sat V (d.params ψ).reverse σ)
    (hk : 0 < dJ.k)
    (hcd : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR (auxOf Jc) i - k₀) (cd (d.tgtsR (auxOf Jc) i - k₀)))
    (htbl : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.PsiTypedPi mp.base2 (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ' σ
        (cd (d.tgtsR (auxOf Jc) i - k₀)).DsA
        (d.psiL mp.base2 ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀)).base)
        (d.psiPinsT (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.nP) (cd (d.tgtsR (auxOf Jc) i - k₀)).mm
        (tbl (d.tgtsR (auxOf Jc) i - k₀)))
    (htgTg : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) →
      i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.TargetOk (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ' σ
        (cd (d.tgtsR (auxOf Jc) i - k₀)).DsA
        (d.psiL mp.base2 ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀)).base)
        (d.psiPinsT (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.nP) (cd (d.tgtsR (auxOf Jc) i - k₀)).mm ∧
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.elimL.eval (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ'
        = (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.w (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ')
    {Ms prior : List AnnotTerm} (hMs : Ms.length = dJ.k) (hprior : prior.length = Jc)
    (Tg : Nat → AnnotTerm) :
    ∀ fs ihs : List V, fs.length = cAJ.2 → ihs.length = (ConLeche.recIdxOf (dJ.ksF Jc)).length →
      SpineFit (consList ((DsA ++ Ms ++ prior).map (interp V σ)) σ)
        ((minorDataTg Tg (dJ.tgtsR Jc) dJ.nP cAJ.2 (dJ.bb ψ') (dJ.k + Jc) (dJ.dsF Jc ψ')
          (ConLeche.recIdxOf (dJ.ksF Jc)) (dJ.tssR Jc ψ') (dJ.eissR Jc ψ')).map (·.2.2))
        (fs ++ ihs) →
      ∀ i Ψ Eis tl, d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl Jc i = some (Ψ, Eis, tl) →
        WellDenotedV V (consList (fs ++ ihs) (consList ((DsA ++ Ms ++ prior).map (interp V σ)) σ))
          (viaEntryAV Ψ cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl Eis) := by
  intro fs ihs hfs hihs hfit i Ψ Eis tl hvia
  obtain ⟨hviewK, hviewT, hviewE, hviewS⟩ := hviewA
  unfold IndRepData.psiVia at hvia
  split at hvia
  · next hT =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hvia
    obtain ⟨rfl, rfl, rfl⟩ := hvia
    have hi : i < cAJ.2 := by
      obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hT.1
      rw [hviewK, hDA.ksLen, hnF] at hlt; exact hlt
    have hc := hcd i hi hT.1 hT.2
    obtain ⟨hTpiWD, hTyWD, hTpiMem⟩ := htbl i hi hT.1 hT.2
    obtain ⟨hTg', hlev'⟩ := htgTg i hi hT.1 hT.2
    have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
    -- the copy's index count is the target's
    have hEl : ((d.eissR (auxOf Jc) ψ).getD i []).length = d.nIdxAt (d.tgtsR (auxOf Jc) i) := by
      obtain ⟨hlt', hk'⟩ := mem_recIdxOf.mp hT.1
      rw [hviewK, hDA.ksLen] at hlt'
      rw [hviewE, hviewT]
      rw [hviewK] at hk'
      rcases hk' with hk' | hk'
      · exact hDA.eisLen ψ i hk' hlt'
      · exact hDA.eisLenRefl ψ i hk' hlt'
    have hbitsT : ∀ dd ∈ (d.tssR (auxOf Jc) ψ).getD i [], (dJ.bb ψ' = 0 ↔ dd.2.1 = 0) := by
      intro dd hd
      rw [hbz]
      exact (hDA.tssBits ψ i dd (by rw [← hviewS]; exact hd)).symm
    -- the container's domain, at the fields' prefix
    have hfsLen : fs.length = cAJ.2 := hfs
    have hfsTake : (fs.take i).length = i := by rw [List.length_take]; omega
    -- the frame: the fields and the hypotheses over the minors, the motives and the pin
    obtain ⟨M0, Mrest, rfl⟩ : ∃ M0 Mrest, Ms = M0 :: Mrest := by
      cases Ms with
      | nil => simp at hMs; omega
      | cons M0 Mrest => exact ⟨M0, Mrest, rfl⟩
    have hMrest : Mrest.length + 1 = dJ.k := by simpa using hMs
    generalize hσ' : consList (DsA.map (interp V σ)) σ = σ' at hTJ ⊢
    have hframe₀ : consList ((DsA ++ M0 :: Mrest ++ prior).map (interp V σ)) σ
        = consList (Mrest.map (interp V σ) ++ prior.map (interp V σ)) (cons (interp V σ M0) σ') := by
      rw [← hσ', List.map_append, List.map_append, consList_append, consList_append,
        List.map_cons, consList_motives_cons]
    have hms : (Mrest.map (interp V σ) ++ prior.map (interp V σ)).length + 1 = dJ.k + Jc := by
      rw [List.length_append, List.length_map, List.length_map, hprior]; omega
    rw [hframe₀] at hfit
    rw [hframe₀, consList_append]
    generalize hmsv : Mrest.map (interp V σ) ++ prior.map (interp V σ) = ms at hms hfit ⊢
    generalize hM : interp V σ M0 = M at hfit ⊢
    -- the fields fit the container's field domains at the pin's readings
    have hfsFit : SpineFit σ' (((dJ.dsF Jc ψ').drop dJ.nP).map (·.2.2)) fs := by
      unfold minorDataTg at hfit
      rw [List.map_append] at hfit
      obtain ⟨fs', ihs', heq, hfitF, -⟩ := spineFit_append_inv hfit
      have hlenF' : fs'.length = cAJ.2 := by
        rw [hfitF.length_eq, List.length_map, rebit_length, liftDoms_length, List.length_drop, hlenJ]
        omega
      obtain ⟨rfl, -⟩ := List.append_inj heq (by rw [hlenF', hfs])
      rw [rebit_map_dom, spineFit_liftDoms] at hfitF
      have hsh : shiftE (dJ.k + Jc) 0 (consList ms (cons M σ')) = σ' := by
        rw [← consList_cons, show dJ.k + Jc = (M :: ms).length from by simp; omega]
        exact shiftE_consList _ _
      rw [hsh] at hfitF
      exact hfitF
    have hfit' : SpineFit σ' ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) (fs.take i) := by
      have h := hfsFit
      rw [← List.take_append_drop i ((dJ.dsF Jc ψ').drop dJ.nP), List.map_append] at h
      obtain ⟨as₁, as₂, heq, h₁, -⟩ := spineFit_append_inv h
      have hlen₁ : as₁.length = i := by
        rw [h₁.length_eq, List.length_map, List.length_take, List.length_drop, hlenJ]; omega
      have hfsTake' : fs.take i = as₁ := by
        rw [heq, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      rw [hfsTake']
      exact h₁
    have hlt : dJ.nP + i < (dJ.dsF Jc ψ').length := by rw [hlenJ]; omega
    have hmemI : fs.getD i pt ∈ˢ interp V (consList (fs.take i) σ')
        ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2 :=
      spineFit_getElem? hfsFit i (fs.getD i pt) ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2
        (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < fs.length)]; rfl)
        (by rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem hlt,
          Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl)
    obtain ⟨j'', h1, -, hint, hWD⟩ := containerDom_transport d mp.base2 hDsA hDsWD auxOf cd hrec
      (by rw [hσ']; exact hTJ) hlenJ hi hT.2 hT.1 hfsTake (by rw [hσ']; exact hfit')
    have hj' : d.tgtsR (auxOf Jc) i - k₀ = j'' := by omega
    rw [hj'] at hc hTpiWD hTyWD hTpiMem hTg' hlev' ⊢
    rw [hσ'] at hint
    generalize htssA : (d.tssR (auxOf Jc) ψ).getD i [] = tssA at hint hWD hbitsT ⊢
    generalize heissA : (d.eissR (auxOf Jc) ψ).getD i [] = eissA at hint hWD hEl ⊢
    rw [h1] at hEl
    -- the telescope, as the transport carries it
    generalize htl : rebit (dJ.bb ψ') (liftDoms dJ.nP i tssA) = tl
    have htlLen : tl.length = tssA.length := by rw [← htl, rebit_length, liftDoms_length]
    have htlBits : ∀ dd ∈ tl, dd.2.1 = dJ.bb ψ' := fun dd hd => by rw [← htl] at hd; exact mem_rebit hd
    have htlGet : ∀ (k : Nat) (dd : Nat × Nat × AnnotTerm), tl[k]? = some dd →
        ∃ d' : Nat × Nat × AnnotTerm, tssA[k]? = some d' ∧ dd.2.2 = d'.2.2.liftN dJ.nP (i + k) := by
      intro k dd hk
      rw [← htl, rebit_getElem?, liftDoms_getElem?] at hk
      obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hk
      obtain ⟨d'', hd'', rfl⟩ := Option.map_eq_some_iff.mp hd'
      exact ⟨d'', hd'', rfl⟩
    have htlTake : ∀ k, (tl.take k).map (·.2.2) = (liftDoms dJ.nP i (tssA.take k)).map (·.2.2) := by
      intro k
      rw [← htl, List.map_take, rebit_map_dom, ← List.map_take, liftDoms_take]
    -- a spine fitting a prefix of the moved telescope fits the copy's telescope
    have hfitTele : ∀ (k : Nat) (as : List V),
        SpineFit (consList ihs (consList fs (consList ms (cons M σ')))) (((ihTeleAtR cAJ.2 (dJ.k + Jc) i
          (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).take k).map (·.2.2)) as →
        SpineFit (consList (fs.take i) σ) ((tssA.take k).map (·.2.2)) as := by
      intro k as hsp
      unfold ihTeleAtR at hsp
      rw [ihTeleAtGo_take] at hsp
      have h := (spineFit_ihTeleAtGo (M := M) (ρp := σ') hms hfs hihs (Nat.le_of_lt hi) (tl.take k) [] as).mp
        (by simpa using hsp)
      simp only [consList_nil] at h
      have hsh := shiftE_consList_middle (fs.take i) (DsA.map (interp V σ)) σ
      rw [hfsTake, hDsLen] at hsh
      rw [htlTake, spineFit_liftDoms, ← hσ', hsh] at h
      exact h
    have hfitFull : ∀ as : List V,
        SpineFit (consList ihs (consList fs (consList ms (cons M σ')))) ((ihTeleAtR cAJ.2 (dJ.k + Jc) i
          (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).map (·.2.2)) as →
        SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as := by
      intro as hsp
      have := hfitTele tl.length as (by
        rw [List.take_of_length_le (Nat.le_of_eq (ihTeleAtR_length _ _ _ _ _))]; exact hsp)
      rw [List.take_of_length_le (l := tssA) (Nat.le_of_eq htlLen.symm)] at this
      exact this
    -- the entries of the moved telescope, at the ih frame
    have hentryWD : ∀ (k : Nat) (dd : Nat × Nat × AnnotTerm),
        (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl)[k]? = some dd →
        ∀ as : List V, SpineFit (consList ihs (consList fs (consList ms (cons M σ'))))
          (((ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).take k).map (·.2.2)) as →
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) dd.2.2 := by
      intro k dd hk as hsp
      have hasA := hfitTele k as hsp
      have hasLen : as.length = k := by
        rw [hasA.length_eq, List.length_map, List.length_take]
        have := (List.getElem?_eq_some_iff.mp hk).1
        rw [ihTeleAtR_length, htlLen] at this
        omega
      unfold ihTeleAtR at hk
      rw [ihTeleAtGo_getElem?] at hk
      obtain ⟨d₁, hd₁, rfl⟩ := Option.map_eq_some_iff.mp hk
      obtain ⟨d₂, hd₂, he⟩ := htlGet k d₁ hd₁
      show WellDenotedV V _ (ihIdxAtM cAJ.2 (dJ.k + Jc) i _ (0 + k) d₁.2.2)
      rw [Nat.zero_add, ← hasLen]
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), he, ← hσ',
          ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← hDsLen, show i + k = (fs.take i ++ as).length from by rw [List.length_append, hfsTake, hasLen],
          WellDenoted_liftN, shiftE_consList_middle, consList_append]
        exact (wellDenoted_mkPisAV_dom hWD.1 as k d₂ hd₂ hasA)
      · rw [AnnotValid_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), he, ← hσ',
          ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← hDsLen, show i + k = (fs.take i ++ as).length from by rw [List.length_append, hfsTake, hasLen],
          AnnotValid_liftN, shiftE_consList_middle, consList_append]
        exact (annotValid_mkPisAV_dom hWD.2 as k d₂ hd₂ hasA)
    -- the moved readings, at the ih frame under the telescope values
    have hEisRead : ∀ as : List V, as.length = tl.length →
        eissA.map (fun E => interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
            (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length
              (E.liftN dJ.nP (i + tssA.length))))
          = eissA.map (interp V (consList as (consList (fs.take i) σ))) := by
      intro as hasLen
      apply List.map_congr_left
      intro E _
      rw [← hasLen, interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), ← hσ',
        ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
        ← consList_append (xs := fs.take i) (ys := as) (ρ := σ), ← hDsLen,
        show i + tssA.length = (fs.take i ++ as).length from by
          rw [List.length_append, hfsTake, hasLen, htlLen],
        interp_liftN_middle]
    have hEisWD : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        ∀ a ∈ (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
          (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length),
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) a := by
      intro as hasA a ha
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      rw [List.map_map] at ha
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
      simp only [Function.comp_def]
      obtain ⟨hbodyWD, -, -, -⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD hasA
      have hEwd : WellDenotedV V (consList as (consList (fs.take i) σ)) E :=
        (WellDenotedV.mkAppN_args hbodyWD).2 E (List.mem_append_right _ hE)
      rw [← hasLen]
      refine ⟨?_, ?_⟩
      · rw [WellDenoted_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), ← hσ',
          ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← hDsLen, show i + tssA.length = (fs.take i ++ as).length from by
            rw [List.length_append, hfsTake, hasLen, htlLen],
          WellDenoted_liftN, shiftE_consList_middle, consList_append]
        exact hEwd.1
      · rw [AnnotValid_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), ← hσ',
          ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← hDsLen, show i + tssA.length = (fs.take i ++ as).length from by
            rw [List.length_append, hfsTake, hasLen, htlLen],
          AnnotValid_liftN, shiftE_consList_middle, consList_append]
        exact hEwd.2
    -- the frame below the telescope values, as one spine over the block's frame
    have hF₀ : ∀ as : List V, as.length = tl.length →
        consList as (consList ihs (consList fs (consList ms (cons M σ'))))
          = consList (DsA.map (interp V σ) ++ (M :: ms ++ fs ++ ihs ++ as)) σ := by
      intro as _
      rw [← hσ', consList_append, consList_append, consList_append, consList_append, consList_cons]
    have hN₀ : ∀ as : List V, as.length = tl.length →
        dJ.nP + (dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length
          = (DsA.map (interp V σ) ++ (M :: ms ++ fs ++ ihs ++ as)).length := by
      intro as hasLen
      simp only [List.length_append, List.length_cons, hDsLen, hfs, hihs, hasLen]
      omega
    have hshiftN₀ : ∀ as : List V, as.length = tl.length →
        shiftE (dJ.nP + (dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length) 0
          (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) = σ := by
      intro as hasLen
      rw [hF₀ as hasLen, hN₀ as hasLen]; exact shiftE_consList _ _
    have hshiftO : ∀ as : List V, as.length = tl.length →
        shiftE ((dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length) 0
          (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) = σ' := by
      intro as hasLen
      rw [← consList_append, ← consList_append, ← consList_append, ← consList_cons,
        show (dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length
          = (M :: (ms ++ (fs ++ (ihs ++ as)))).length from by
            simp only [List.length_append, List.length_cons, hfs, hihs, hasLen]; omega]
      exact shiftE_consList _ _
    -- the target: its data
    have hDsWD'' : ∀ p ∈ (cd j'').DsA, WellDenotedV V σ p :=
      (WellDenotedV.mkAppN_args (hc.pin.wd σ hsatA)).2
    have hDsLen'' : ((cd j'').DsA.map (interp V σ)).length = (cd j'').dJ.nP := by
      rw [List.length_map, hc.len]
    have hchain : chain V σ (cd j'').DsA = consList ((cd j'').DsA.map (interp V σ)) σ := by
      unfold chain; exact consN_eq_consList _ _
    have hTgF := (cd j'').dJ.invTg_fact (cd j'').ψ' (ps := (cd j'').DsA) hDsWD'' hTg'
    -- the field's value at telescope values, and the moved readings' values
    have hxVal : ∀ as : List V, as.length = tl.length →
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN (.bvar (cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length))
            (teleVarsAV tl.length))
          = as.foldl SetTheory.app (fs.getD i pt) := by
      intro as hasLen
      rw [interp_mkAppN_map, interp_bvar, ← hasLen, map_teleVarsAV_interp]
      congr 1
      rw [consList_apply_add,
        show cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length
          = (cAJ.2 - 1 - i) + ihs.length from by omega,
        consList_apply_add, consList_apply_lt' fs _ (by omega),
        show fs.length - 1 - (cAJ.2 - 1 - i) = i from by omega]
    -- the per-spine facts of a transport
    have hspine : ∀ as : List V,
        SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        let EisV := eissA.map (interp V (consList as (consList (fs.take i) σ)))
        let x := as.foldl SetTheory.app (fs.getD i pt)
        SpineFit (consList ((cd j'').DsA.map (interp V σ)) σ) ((cd j'').dJ.IdsM (cd j'').mm (cd j'').ψ') EisV ∧
        SpineFit (consList ((cd j'').DsA.map (interp V σ)) σ)
          (((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm).map (·.2.2)) (EisV ++ [x]) ∧
        x ∈ˢ ((cd j'').DsA.map (interp V σ) ++ EisV).foldl SetTheory.app
          (interp V σ (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')) ∧
        EisV.length = (cd j'').dJ.nIdxs.getD (cd j'').mm 0 := by
      intro as hasA
      obtain ⟨hbodyWD, hval, hfitAll, hfitIdx⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD hasA
      have hx : as.foldl SetTheory.app (fs.getD i pt)
          ∈ˢ ((cd j'').DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList (fs.take i) σ)))).foldl
            SetTheory.app (interp V σ (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')) := by
        rw [hint] at hmemI
        have h := mkPisAV_fold_mem (m := dJ.bb ψ') hbitsT
          (fun h0 as' has' => by
            obtain ⟨-, hval', hfitAll', -⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD has'
            rw [hval']
            obtain ⟨hlenP, hbitsP, hmemL, -⟩ := hc.ff
            have := mkPisAV_fold_mem (m := 1)
              (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbitsP dd hd)⟩)
              (fun h => absurd h Nat.one_ne_zero) (hmemL σ) hfitAll'
            rw [interp_sort] at this
            have hw0 : (cd j'').dJ.w (cd j'').ψ' = 0 := by rw [hc.idx.sort]; exact hbz.mp h0
            rw [hw0, univ_zero] at this
            exact this)
          hmemI hasA
        rw [hval] at h
        exact h
      have hEisLen : (eissA.map (interp V (consList as (consList (fs.take i) σ)))).length
          = (cd j'').dJ.nIdxs.getD (cd j'').mm 0 := by
        have := hfitIdx.length_eq
        unfold IndRepData.IdsM at this
        simp only [List.length_map, List.length_drop] at this
        rw [hc.ff.1] at this
        rw [List.length_map]
        show eissA.length = (cd j'').dJ.nIdxAt (cd j'').mm
        omega
      refine ⟨hfitIdx, ?_, hx, hEisLen⟩
      unfold IndRepData.motDataAV
      rw [List.map_append, List.map_singleton, rebit_map_dom, (cd j'').dJ.ipss_getD _ hc.mm]
      refine SpineFit.append hfitIdx ⟨?_, trivial⟩
      rw [(cd j'').dJ.Ls_getD_eq mp.base2 _ hc.mm,
        show (cd j'').dJ.pinsOf (cd j'').ψ' (cd j'').mm = paramBvarsAt (cd j'').dJ.nP (cd j'').dJ.nP from
          hc.pins _,
        ← hEisLen, interp_famAppAV_params (mp.base2.cval_closedL _ _) hDsLen'' rfl σ]
      exact hx
    -- the target-form body `T`, and the target container's body `TJ`
    generalize hN : dJ.nP + (dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length = N₀
      at hshiftN₀ hN₀
    have hTval : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
            ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
              (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length)))
          = interp V (consList (eissA.map (interp V (consList as (consList (fs.take i) σ))))
              (consList ((cd j'').DsA.map (interp V σ)) σ))
              (famAppAV (d.psiL mp.base2 ψ k₀ (cd j'').base (cd j'').mm)
                (d.psiPinsT (cd j'').dJ.nP (cd j'').mm) (cd j'').dJ.nP
                ((cd j'').dJ.nP + (cd j'').dJ.nIdxs.getD (cd j'').mm 0) ((cd j'').dJ.nIdxs.getD (cd j'').mm 0)) := by
      intro as hasA
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      obtain ⟨hfitIdx, -, -, -⟩ := hspine as hasA
      rw [interp_mkAppN_map]
      simp only [List.map_map, Function.comp_def]
      rw [hEisRead as hasLen, interp_liftN, hshiftN₀ as hasLen]
      unfold IndRepData.psiTgOf
      rw [(cd j'').dJ.invTg_fold _ (by rw [rebit_map_dom, (cd j'').dJ.ipss_getD _ hc.mm]; exact hfitIdx)]
    have hTgraded : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
            ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
              (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length))) ∧
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
            ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
              (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length)))
          ∈ˢ (univ ((cd j'').dJ.elimL.eval (cd j'').ψ') : V) := by
      intro as hasA
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      obtain ⟨hfitIdx, -, -, -⟩ := hspine as hasA
      -- the target's tower at the block's frame, lifted
      have hTT : WellDenotedV V σ
          (ConLeche.Model.AnnotTerm.instSeq (cd j'').DsA ((cd j'').DsA.length - 1)
            (mkPisAV (rebit (pwBit (cd j'').ψ' ConLeche.PropWhen.never) (((cd j'').dJ.ipss (cd j'').ψ').getD (cd j'').mm []))
              (.sort ((cd j'').dJ.elimL.eval (cd j'').ψ')))) := by
        refine wellDenotedV_instSeq _ hDsWD'' ?_
        rw [hchain]; exact hTg'.1
      have hTTmem : interp V σ (d.psiTgOf mp.base2 ψ k₀ (cd j''))
          ∈ˢ interp V σ (ConLeche.Model.AnnotTerm.instSeq (cd j'').DsA ((cd j'').DsA.length - 1)
            (mkPisAV (rebit (pwBit (cd j'').ψ' ConLeche.PropWhen.never) (((cd j'').dJ.ipss (cd j'').ψ').getD (cd j'').mm []))
              (.sort ((cd j'').dJ.elimL.eval (cd j'').ψ')))) := by
        rw [interp_instSeq_consList]; exact hTgF.2
      rw [instSeq_mkPisAV _ _ _ _ (by omega), instSeq_sort] at hTT hTTmem
      have h := wellDenotedV_mkAppN_of_spineFit
        (σ := consList as (consList ihs (consList fs (consList ms (cons M σ')))))
        (ds := liftDoms N₀ 0 (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
          (rebit (pwBit (cd j'').ψ' ConLeche.PropWhen.never) (((cd j'').dJ.ipss (cd j'').ψ').getD (cd j'').mm []))))
        (C := (AnnotTerm.sort ((cd j'').dJ.elimL.eval (cd j'').ψ')).liftN N₀
          (0 + (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
            (rebit (pwBit (cd j'').ψ' ConLeche.PropWhen.never) (((cd j'').dJ.ipss (cd j'').ψ').getD (cd j'').mm []))).length))
        (f := (d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
        (as := (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
          (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length))
        (by rw [← liftN_mkPisAV, WellDenotedV_liftN, hshiftN₀ as hasLen]; exact hTT)
        (by rw [WellDenotedV_liftN, hshiftN₀ as hasLen]; exact hTgF.1)
        (hEisWD as hasA)
        (by rw [← liftN_mkPisAV, interp_liftN, interp_liftN, hshiftN₀ as hasLen]; exact hTTmem)
        (by
          rw [spineFit_liftDoms, hshiftN₀ as hasLen]
          simp only [List.map_map, Function.comp_def]
          rw [hEisRead as hasLen]
          refine (spineFit_instSeqDoms_iff (xs := []) _ _ _ (fun hne => by
              rw [hc.len, List.length_nil]
              have : 1 ≤ (cd j'').dJ.nP := by
                rw [← hc.len]
                exact Nat.pos_of_ne_zero (fun h0 => hne (List.eq_nil_of_length_eq_zero h0))
              omega)).mpr ?_
          simp only [consList_nil, rebit_map_dom]
          rw [(cd j'').dJ.ipss_getD _ hc.mm]
          exact hfitIdx)
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [AnnotTerm.liftN_sort, interp_sort] at h2
      exact h2
    have hzeroT : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        dJ.bb ψ' = 0 →
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
            ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
              (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length)))
          ∈ˢ (univZero : V) := by
      intro as hasA h0
      have h := (hTgraded as hasA).2
      have hw0 : (cd j'').dJ.elimL.eval (cd j'').ψ' = 0 := by
        rw [hlev', hc.idx.sort]; exact hbz.mp h0
      rw [hw0, univ_zero] at h
      exact h
    -- the target container's body at the ih frame, for the field's type
    generalize hTJbody : AnnotTerm.mkAppN (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')
        (((cd j'').DsA.map (·.liftN N₀ 0)) ++
          (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
            (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length)) = TJbody
    have hTJval : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) TJbody
          = ((cd j'').DsA.map (interp V σ) ++ eissA.map (interp V (consList as (consList (fs.take i) σ)))).foldl
              SetTheory.app (interp V σ (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')) := by
      intro as hasA
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      rw [← hTJbody, interp_mkAppN_map, List.map_append]
      simp only [List.map_map, Function.comp_def]
      rw [hEisRead as hasLen, interp_closed (V := V) (mp.base2.cval_closedL _ _) _ σ]
      congr 2
      apply List.map_congr_left
      intro D _
      rw [interp_liftN, hshiftN₀ as hasLen]
    have hTJwd : ∀ as : List V, SpineFit (consList (fs.take i) σ) (tssA.map (·.2.2)) as →
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) TJbody ∧
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) TJbody
          ∈ˢ (univ ((cd j'').dJ.w (cd j'').ψ') : V) := by
      intro as hasA
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      obtain ⟨hbodyWD, hval, hfitAll, -⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD hasA
      obtain ⟨hlenP, hbitsP, hmemL, hokF⟩ := hc.ff
      obtain ⟨B, hB⟩ := hc.ls
      have hclosed : Term.bvarsBelow 0 (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ').erase :=
        mp.base2.cval_closedL _ _
      -- the fit of the readings into the leaf's binders, at the ih frame
      have hargsLen : ((cd j'').DsA.map (·.liftN (i + tssA.length) 0) ++ eissA).length
          = ((cd j'').dJ.ppsM (cd j'').mm (cd j'').ψ').length := by
        rw [List.length_append, List.length_map, hc.len, hEl, ← hc.idx.nIdx, hlenP]
      have hfitIh := spineFit_of_wellDenoted_lams (u := (cd j'').dJ.w (cd j'').ψ' + 1) (Nat.succ_ne_zero _)
        (b := B) (args := (cd j'').DsA.map (·.liftN (i + tssA.length) 0) ++ eissA)
        (ds := (cd j'').dJ.ppsM (cd j'').mm (cd j'').ψ')
        (σ := consList as (consList ihs (consList fs (consList ms (cons M σ')))))
        (ρ := consList as (consList (fs.take i) σ))
        (f := mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')
        (Nat.le_of_eq hargsLen) hbodyWD.1
        (by rw [hB]; exact interp_closed (V := V) (by rw [← hB]; exact hclosed) _ _)
      rw [hargsLen, List.take_of_length_le (Nat.le_refl _), List.map_append] at hfitIh
      have hDsV : ((cd j'').DsA.map (·.liftN (i + tssA.length) 0)).map
          (interp V (consList as (consList (fs.take i) σ))) = (cd j'').DsA.map (interp V σ) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro D _
        simp only [Function.comp_def]
        rw [interp_liftN, ← consList_append, show i + tssA.length = (fs.take i ++ as).length from by
          rw [List.length_append, hfsTake, hasLen, htlLen], shiftE_consList]
      rw [hDsV] at hfitIh
      have h := wellDenotedV_mkAppN_of_spineFit
        (σ := consList as (consList ihs (consList fs (consList ms (cons M σ')))))
        (ds := (cd j'').dJ.ppsM (cd j'').mm (cd j'').ψ') (C := .sort ((cd j'').dJ.w (cd j'').ψ'))
        (f := mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')
        (as := ((cd j'').DsA.map (·.liftN N₀ 0)) ++
          (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
            (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length))
        (hokF _) ⟨mp.base2.acval_wellDenoted _ _ _, mp.acval_validV _ _ _⟩
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp ha
            rw [WellDenotedV_liftN, hshiftN₀ as hasLen]
            exact hDsWD'' D hD
          · exact hEisWD as hasA a ha)
        (hmemL _)
        (by
          rw [List.map_append]
          simp only [List.map_map, Function.comp_def]
          rw [hEisRead as hasLen]
          have hDsV' : (cd j'').DsA.map (fun x => interp V
              (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) (AnnotTerm.liftN N₀ x 0))
              = (cd j'').DsA.map (interp V σ) := by
            apply List.map_congr_left
            intro D _
            rw [interp_liftN, hshiftN₀ as hasLen]
          rw [hDsV']
          exact hfitIh)
      rw [hTJbody] at h
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [interp_sort] at h2
      exact h2
    -- the field's type at the ih frame: the tower over the moved telescope of `TJbody`
    have hTJtower : interp V (consList ihs (consList fs (consList ms (cons M σ'))))
        (mkPisAV (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl) TJbody)
        = interp V (consList (fs.take i) σ)
            (mkPisAV tssA (AnnotTerm.mkAppN (mp.base2.acval ((cd j'').dJ.memberName (cd j'').mm) (cd j'').ψ')
              (((cd j'').DsA).map (·.liftN (i + tssA.length) 0) ++ eissA))) := by
      refine interp_mkPisAV_congr (by rw [ihTeleAtR_length, htlLen]) ?_ ?_ ?_
      · intro k d₁ d₂ h₁ h₂
        unfold ihTeleAtR at h₁
        rw [ihTeleAtGo_getElem?] at h₁
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨d'', hd'', -⟩ := htlGet k d' hd'
        rw [h₂] at hd''
        obtain rfl := Option.some.inj hd''
        show d'.2.1 = 0 ↔ d₂.2.1 = 0
        rw [htlBits d' (List.mem_of_getElem? hd')]
        exact hbitsT d₂ (List.mem_of_getElem? h₂)
      · intro k d₁ d₂ as h₁ h₂ hsp
        have hasA := hfitTele k as hsp
        have hasLen : as.length = k := by
          rw [hasA.length_eq, List.length_map, List.length_take]
          have := (List.getElem?_eq_some_iff.mp h₂).1
          omega
        unfold ihTeleAtR at h₁
        rw [ihTeleAtGo_getElem?] at h₁
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨d'', hd'', he⟩ := htlGet k d' hd'
        rw [h₂] at hd''
        obtain rfl := Option.some.inj hd''
        show interp V _ (ihIdxAtM cAJ.2 (dJ.k + Jc) i _ (0 + k) d'.2.2) = _
        rw [Nat.zero_add, ← hasLen, interp_ihIdxAtM hms hfs hihs (Nat.le_of_lt hi), he, ← hσ',
          ← consList_append (xs := fs.take i) (ys := as) (ρ := consList (DsA.map (interp V σ)) σ),
          ← consList_append (xs := fs.take i) (ys := as) (ρ := σ), ← hDsLen,
          show i + k = (fs.take i ++ as).length from by rw [List.length_append, hfsTake, hasLen],
          interp_liftN_middle]
      · intro as hsp
        have hasA := hfitFull as hsp
        obtain ⟨-, hval, -, -⟩ := d.transport_fits mp.base2 hc hEl hfsTake hWD hasA
        rw [hTJval as hasA, hval]
    have hTJmem : fs.getD i pt ∈ˢ interp V (consList ihs (consList fs (consList ms (cons M σ'))))
        (mkPisAV (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl) TJbody) := by
      rw [hTJtower, ← hint]; exact hmemI
    have hzb : ∀ dd ∈ ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl,
        (dJ.bb ψ' = 0 ↔ dd.2.1 = 0) := by
      intro dd hd
      obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd
      rw [he, htlBits d' hd']
    have hTJtowerWD : WellDenotedV V (consList ihs (consList fs (consList ms (cons M σ'))))
        (mkPisAV (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl) TJbody) := by
      refine ⟨wellDenoted_mkPisAV_of (fun k dd hk as hsp => (hentryWD k dd hk as hsp).1)
          (fun as hsp => (hTJwd as (hfitFull as hsp)).1.1),
        annotValid_mkPisAV_of (b := dJ.bb ψ')
          (fun dd hd => by obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hd; rw [he]; exact htlBits d' hd')
          (fun k dd hk as hsp => (hentryWD k dd hk as hsp).2)
          (fun as hsp => ⟨(hTJwd as (hfitFull as hsp)).1.2, fun h0 => ?_⟩)⟩
      have h := (hTJwd as (hfitFull as hsp)).2
      have hw0 : (cd j'').dJ.w (cd j'').ψ' = 0 := by rw [hc.idx.sort]; exact hbz.mp h0
      rw [hw0, univ_zero] at h
      exact h
    -- the field applied to the telescope's variables is graded
    have hxWD : ∀ as : List V,
        SpineFit (consList ihs (consList fs (consList ms (cons M σ'))))
          ((ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).map (·.2.2)) as →
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (AnnotTerm.mkAppN (.bvar (cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length))
            (teleVarsAV tl.length)) := by
      intro as hsp
      have hasA := hfitFull as hsp
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      have hshiftM : shiftE tl.length 0 (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          = consList ihs (consList fs (consList ms (cons M σ'))) := by
        rw [← hasLen]; exact shiftE_consList _ _
      have h := wellDenotedV_mkAppN_of_spineFit
        (σ := consList as (consList ihs (consList fs (consList ms (cons M σ')))))
        (ds := liftDoms tl.length 0 (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl))
        (C := TJbody.liftN tl.length
          (0 + (ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).length))
        (f := .bvar (cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length))
        (as := teleVarsAV tl.length)
        (by rw [← liftN_mkPisAV, WellDenotedV_liftN, hshiftM]; exact hTJtowerWD)
        ⟨by simp, by simp⟩
        (fun a ha => by
          obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
          exact ⟨by simp, by simp⟩)
        (by
          rw [← liftN_mkPisAV, interp_liftN, hshiftM, interp_bvar, ← hasLen, consList_apply_add,
            show cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length
              = (cAJ.2 - 1 - i) + ihs.length from by omega,
            consList_apply_add, consList_apply_lt' fs _ (by omega),
            show fs.length - 1 - (cAJ.2 - 1 - i) = i from by omega]
          exact hTJmem)
        (by rw [spineFit_liftDoms, hshiftM, ← hasLen, map_teleVarsAV_interp]; exact hsp)
      exact h.1
    -- the body: the earlier copy's term at the readings and the field
    have hbodyFacts : ∀ as : List V,
        SpineFit (consList ihs (consList fs (consList ms (cons M σ'))))
          ((ihTeleAtR cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl).map (·.2.2)) as →
        WellDenotedV V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (viaBodyAV ((tbl j'').liftN dJ.nP 0) cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length
            tl.length (eissA.map (·.liftN dJ.nP (i + tssA.length)))) ∧
        interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
          (viaBodyAV ((tbl j'').liftN dJ.nP 0) cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length
            tl.length (eissA.map (·.liftN dJ.nP (i + tssA.length))))
          ∈ˢ interp V (consList as (consList ihs (consList fs (consList ms (cons M σ')))))
            (AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
              ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
                (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length))) := by
      intro as hsp
      have hasA := hfitFull as hsp
      have hasLen : as.length = tl.length := by rw [hasA.length_eq, List.length_map, htlLen]
      obtain ⟨hfitIdx, hfitM, hx, hEisLen⟩ := hspine as hasA
      -- ψ's Π-type, lifted to the frame
      have hpiEq := (cd j'').dJ.interp_psiTyAV mp.base2 (cd j'').ψ' (cd j'').DsA
        (d.psiL mp.base2 ψ k₀ (cd j'').base) (d.psiPinsT (cd j'').dJ.nP) (cd j'').mm σ
      have hpos'' : (cd j'').DsA ≠ [] → 1 ≤ (cd j'').dJ.nP := fun hne => by
        rw [← hc.len]
        exact Nat.pos_of_ne_zero (fun h0 => hne (List.eq_nil_of_length_eq_zero h0))
      have hTy : (cd j'').dJ.psiTyAV mp.base2 (cd j'').ψ' (cd j'').DsA (d.psiL mp.base2 ψ k₀ (cd j'').base)
          (d.psiPinsT (cd j'').dJ.nP) (cd j'').mm
          = mkPisAV (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
              (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm)))
              (ConLeche.Model.AnnotTerm.instSeq (cd j'').DsA
                ((cd j'').DsA.length - 1 +
                  (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm)).length)
                ((famAppAV (d.psiL mp.base2 ψ k₀ (cd j'').base (cd j'').mm) (d.psiPinsT (cd j'').dJ.nP (cd j'').mm)
                  (cd j'').dJ.nP ((cd j'').dJ.nP + (cd j'').dJ.nIdxs.getD (cd j'').mm 0)
                  ((cd j'').dJ.nIdxs.getD (cd j'').mm 0)).liftN 1 0)) := by
        unfold IndRepData.psiTyAV
        rw [instSeq_mkPisAV _ _ _ _ (by omega)]
      have hshiftO' : shiftE ((dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length) 0
          (consList as (consList ihs (consList fs (consList ms (cons M σ'))))) = σ' := hshiftO as hasLen
      have hshiftD : shiftE dJ.nP 0 σ' = σ := by rw [← hσ', ← hDsLen]; exact shiftE_consList _ _
      unfold viaBodyAV
      have h := wellDenotedV_mkAppN_of_spineFit
        (σ := consList as (consList ihs (consList fs (consList ms (cons M σ')))))
        (ds := liftDoms N₀ 0 (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
          (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm))))
        (C := (ConLeche.Model.AnnotTerm.instSeq (cd j'').DsA
            ((cd j'').DsA.length - 1 +
              (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm)).length)
            ((famAppAV (d.psiL mp.base2 ψ k₀ (cd j'').base (cd j'').mm) (d.psiPinsT (cd j'').dJ.nP (cd j'').mm)
              (cd j'').dJ.nP ((cd j'').dJ.nP + (cd j'').dJ.nIdxs.getD (cd j'').mm 0)
              ((cd j'').dJ.nIdxs.getD (cd j'').mm 0)).liftN 1 0)).liftN N₀
          (0 + (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
            (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm))).length))
        (f := ((tbl j'').liftN dJ.nP 0).liftN ((dJ.k + Jc) + cAJ.2 + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length) 0)
        (as := (eissA.map (·.liftN dJ.nP (i + tssA.length))).map
            (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length) ++
          [AnnotTerm.mkAppN (.bvar (cAJ.2 - 1 - i + (ConLeche.recIdxOf (dJ.ksF Jc)).length + tl.length))
            (teleVarsAV tl.length)])
        (by rw [← liftN_mkPisAV, ← hTy, WellDenotedV_liftN, hshiftN₀ as hasLen]; exact hTyWD)
        (by rw [WellDenotedV_liftN, hshiftO', WellDenotedV_liftN, hshiftD]; exact hTpiWD)
        (fun a ha => by
          rcases List.mem_append.mp ha with ha | ha
          · exact hEisWD as hasA a ha
          · rw [List.mem_singleton] at ha
            rw [ha]; exact hxWD as hsp)
        (by
          rw [← liftN_mkPisAV, ← hTy, interp_liftN, interp_liftN, interp_liftN, hshiftN₀ as hasLen,
            hshiftO', hshiftD]
          exact hTpiMem)
        (by
          rw [spineFit_liftDoms, hshiftN₀ as hasLen, List.map_append, List.map_singleton, hxVal as hasLen]
          simp only [List.map_map, Function.comp_def]
          rw [hEisRead as hasLen]
          refine (spineFit_instSeqDoms_iff (xs := []) _ _ _ (fun hne => by
              rw [hc.len, List.length_nil]; have := hpos'' hne; omega)).mpr ?_
          simp only [consList_nil, rebit_map_dom]
          exact hfitM)
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [List.map_append, List.map_singleton, hxVal as hasLen] at h2
      simp only [List.map_map, Function.comp_def] at h2
      rw [hEisRead as hasLen, interp_liftN] at h2
      rw [hTval as hasA]
      -- the body's type at the readings is the target at the readings
      have hlenVals : (eissA.map (interp V (consList as (consList (fs.take i) σ))) ++ [as.foldl SetTheory.app (fs.getD i pt)]).length
          = (instSeqDoms (cd j'').DsA ((cd j'').DsA.length - 1)
              (rebit ((cd j'').dJ.bb (cd j'').ψ') ((cd j'').dJ.motDataAV mp.base2 (cd j'').ψ' (cd j'').mm))).length := by
        rw [instSeqDoms_length, rebit_length, List.length_append, List.length_singleton, hEisLen]
        unfold IndRepData.motDataAV
        rw [List.length_append, rebit_length, List.length_singleton, (cd j'').dJ.ipss_getD _ hc.mm,
          List.length_drop, hc.ff.1]
        unfold IndRepData.nIdxAt
        omega
      rw [Nat.zero_add, ← hlenVals, shiftE_consList_len, hshiftN₀ as hasLen,
        interp_instSeq_under σ _ _ _ _ (fun hne => by
          rw [hlenVals, instSeqDoms_length, rebit_length, hc.len]
          have := hpos'' hne
          omega),
        consList_append, consList_cons, consList_nil, interp_liftN, shiftE_succ_cons, shiftE_zero_zero] at h2
      simp only [List.map_map, Function.comp_def]
      exact h2
    -- the λ-tower
    unfold viaEntryAV
    refine ⟨mkLamsAV_bits_wellDenoted (m := dJ.bb ψ')
        (T := AnnotTerm.mkAppN ((d.psiTgOf mp.base2 ψ k₀ (cd j'')).liftN N₀ 0)
          ((eissA.map (·.liftN dJ.nP (i + tssA.length))).map
            (ihIdxAtM cAJ.2 (dJ.k + Jc) i (ConLeche.recIdxOf (dJ.ksF Jc)).length tl.length)))
        hzb ?_, mkLamsAV_bits_validV ?_⟩
    · refine underTowerOk_of_wellDenoted
        (wellDenoted_mkPisAV_of (fun k dd hk as hsp => (hentryWD k dd hk as hsp).1)
          (fun as hsp => (hTgraded as (hfitFull as hsp)).1.1)) ?_
      intro as hsp
      exact ⟨(hbodyFacts as hsp).1.1, (hbodyFacts as hsp).2, hzeroT as (hfitFull as hsp)⟩
    · exact underTowerValid_of (fun k dd hk as hsp => (hentryWD k dd hk as hsp).2)
        (fun as hsp => (hbodyFacts as hsp).1.2)
  · exact nomatch hvia

end IndRepData

/-! ## The setup, assembled -/

/-- **The copy-side facts of one container constructor** `Jc`, whose
copy's constructor is `Ja` (`auxOf Jc`) with entry `cAa` in the
auxiliary datum: the field counts agree, the record (DESIGN §M.25 (c)),
and the auxiliary datum's facts of `Ja` — its `FixCtorFactsAt`, its
stored type closed, its parameter telescope the block's, the view
identities, its targets and member within the block. -/
structure CopyCtorFacts (m : EnvModel V env) (d dJ : IndRepData V) (ψ ψ' : Name → Nat)
    (DsA : List AnnotTerm) (k₀ j₀ : Nat) (cd : Nat → CopyData V) (lpsT : List Name)
    (Jc Ja : Nat) (cAJ cAa : ConstantVal × Nat) : Prop where
  nF : cAa.2 = cAJ.2
  read : d.CopyCtorAsRead m dJ ψ ψ' DsA k₀ j₀ (fun j' => (cd j').dJ.memberName (cd j').mm)
    (fun j' => (cd j').ψ') (fun j' => (cd j').DsA) Jc Ja cAJ.2
  ctor : FixCtorFactsAt m d.env₀ (d.memberName (d.mems Ja)) lpsT d.nP (d.nIdxAt (d.mems Ja))
    d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
    d.tssF Ja cAa (fun i => d.memberName (d.tgts Ja i)) (fun i => d.nIdxAt (d.tgts Ja i))
  cf : cAa.1.type.hasFvar = false
  cb : cAa.1.type.looseBVarsBounded 0 = true
  pIff : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
    Sat V (((d.dsF Ja ψ).take d.nP).map (·.2.2)).reverse ρ'
  view : d.ksR Ja = d.ksF Ja ∧ d.tgtsR Ja = d.tgts Ja ∧ d.eissR Ja = d.eissF Ja ∧ d.tssR Ja = d.tssF Ja
  tgts : ∀ i, d.tgtsR Ja i < d.k
  mem : d.mems Ja < d.k

namespace IndRepData

variable (d : IndRepData V)

set_option maxHeartbeats 3200000 in
/-- **The ψ setup of one mint group, assembled** (the datum-level twin
of `invSetup_of_member`): over the container datum `dJ` (its
representation at the scratch environment) at the pin's readings, with
the copies' carriers as the targets (`targetOk_psi`), the copies'
constructors as the heads at the transported domains
(`ctorAtDoms_psi`), the replaced positions unmentioned (`noBVar_psi`),
and the transports at the earlier copies' terms (`via_psi`,
`viaWD_psi`) — from the container's `IndRep`, the auxiliary datum's
facts of the copies (`CopyCtorFacts` per constructor, the copies'
formers and leaves), the copies' index reads (`CopyData.Ok` for the
group and for every transport's target), and the fold's property at
every transport's target (`PsiTypedPi`, with the target's fold target). -/
theorem psiSetup_of_group {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ ψ' : Name → Nat} {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    -- the auxiliary datum: the copies are real members
    (hpinsA : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP)
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hLSA : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hpIffMA : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    -- the container's representation
    {dJ : IndRepData V} (hctorsCJ : dJ.ctorsC = []) (hkRJ : dJ.kReal = dJ.k)
    (hpinsAVJ : ∀ (t : Nat) (φ : Name → Nat), dJ.pinsAV t φ = paramBvarsAt dJ.nP dJ.nP)
    (hviewJ : ∀ J, dJ.ksR J = dJ.ksF J ∧ dJ.tgtsR J = dJ.tgts J ∧ dJ.eissR J = dJ.eissF J ∧
      dJ.tssR J = dJ.tssF J)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (ht₀ : t₀ < dJ.k) (hrules : rules ≠ [])
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules))
    (hrepJ : IndRep mp.base2 T cvT cvR mI rP rules dJ t₀)
    -- the group: its pin, its level assignment, its copies
    {DsA : List AnnotTerm} (hDsA : DsA.length = dJ.nP) (hlev : dJ.elimL.eval ψ' = dJ.w ψ')
    {k₀ j₀ : Nat} (hkA : ∀ t, t < dJ.k → k₀ + j₀ + t < d.k)
    (hgrp : ∀ t, t < dJ.k → CopyData.Ok mp.base2 d ψ k₀ (j₀ + t) ⟨dJ, t, ψ', DsA, j₀⟩)
    -- the copies' constructors
    (auxOf : Nat → Nat) (cd : Nat → CopyData V) (tbl : Nat → AnnotTerm)
    (hctors : ∀ Jc cAJ, dJ.ctorsA[Jc]? = some cAJ → ∃ cAa, d.ctorsA[auxOf Jc]? = some cAa ∧
      CopyCtorFacts mp.base2 d dJ ψ ψ' DsA k₀ j₀ cd lpsT Jc (auxOf Jc) cAJ cAa)
    -- the transports' targets
    (hcd : ∀ Jc cAJ, dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR (auxOf Jc) i - k₀) (cd (d.tgtsR (auxOf Jc) i - k₀)))
    (htbl : ∀ Jc cAJ, dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.PsiTypedPi mp.base2 (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ'
        (consList (psA.map (interp V ρ₀)) ρ₀) (cd (d.tgtsR (auxOf Jc) i - k₀)).DsA
        (d.psiL mp.base2 ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀)).base)
        (d.psiPinsT (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.nP) (cd (d.tgtsR (auxOf Jc) i - k₀)).mm
        (tbl (d.tgtsR (auxOf Jc) i - k₀)))
    (htgTg : ∀ Jc cAJ, dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOf Jc)) → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.TargetOk (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ'
        (consList (psA.map (interp V ρ₀)) ρ₀) (cd (d.tgtsR (auxOf Jc) i - k₀)).DsA
        (d.psiL mp.base2 ψ k₀ (cd (d.tgtsR (auxOf Jc) i - k₀)).base)
        (d.psiPinsT (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.nP) (cd (d.tgtsR (auxOf Jc) i - k₀)).mm ∧
      (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.elimL.eval (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ'
        = (cd (d.tgtsR (auxOf Jc) i - k₀)).dJ.w (cd (d.tgtsR (auxOf Jc) i - k₀)).ψ') :
    dJ.PsiSetup mp cvT.levelParams cvT.levelParams ψ' (consList (psA.map (interp V ρ₀)) ρ₀) DsA
      (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP) (d.psiHead mp.base2 ψ dJ.nP auxOf) (psiUseIh dJ)
      (d.psiVia dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl) (d.psiTgV mp.base2 ψ k₀ auxOf cd) := by
  have hk : 0 < dJ.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  have hFFJ : ∀ t, t < dJ.k → dJ.FormerFacts mp.base2 ψ' t :=
    fun t ht => dJ.formerFacts_of_indRep hrepJ hkRJ ψ' ht
  have hnAllJ : dJ.nAll = dJ.ctorsA.length := by
    show dJ.ctorsA.length + dJ.ctorsC.length = _
    rw [hctorsCJ]
    rfl
  have hpsALen : (psA.map (interp V ρ₀)).length = d.nP := by simp [hpsA]
  generalize hσ : consList (psA.map (interp V ρ₀)) ρ₀ = σ at htbl htgTg ⊢
  have hsatA : Sat V (d.params ψ).reverse σ := by
    rw [← hσ]
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparamsA
    rwa [List.append_nil] at h
  -- the pin's readings are graded and fit the container's parameters
  have hc0 := hgrp 0 hk
  have hDsWD : ∀ p ∈ DsA, WellDenotedV V σ p := (WellDenotedV.mkAppN_args (hc0.pin.wd σ hsatA)).2
  have hparamsJ : SpineFit σ (dJ.params ψ') (DsA.map (interp V σ)) :=
    d.pinFit_of_leafShape rfl (hFFJ 0 hk) (hrepJ.leafShape 0 (by rw [hkRJ]; exact hk) ψ') hc0.pin hsatA
  have hbz : dJ.bb ψ' = 0 ↔ d.resSort.eval ψ = 0 := by
    have hs : dJ.w ψ' = d.w ψ := hc0.idx.sort
    unfold IndRepData.bb
    rw [pwBit_zeronessOf, hlev]
    show dJ.w ψ' = 0 ↔ d.w ψ = 0
    rw [hs]
  -- the container constructor's tower at the pin's readings
  have hTJ : ∀ Jc cAJ, dJ.ctorsA[Jc]? = some cAJ →
      WellDenotedV V (consList (DsA.map (interp V σ)) σ)
        (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP)
          (ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ' (dJ.esF Jc ψ'))) ∧
      (dJ.dsF Jc ψ').length = dJ.nP + cAJ.2 := by
    intro Jc cAJ hJc
    obtain ⟨-, -, hDJ⟩ := hrepJ.ctors Jc cAJ hJc
    have hlenDs := hDJ.len ψ'
    have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hDsA]
    have hfitP : SpineFit σ (((dJ.dsF Jc ψ').take dJ.nP).map (·.2.2)) (DsA.map (interp V σ)) :=
      spineFit_of_paramsIff hDsLen (by simp [hlenDs]) hparamsJ (hrepJ.paramsIff Jc cAJ hJc ψ')
    have hsplitT : mkPisAV (dJ.dsF Jc ψ')
        (ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ' (dJ.esF Jc ψ'))
        = mkPisAV ((dJ.dsF Jc ψ').take dJ.nP) (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP)
            (ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ' (dJ.esF Jc ψ'))) := by
      rw [← mkPisAV_append, List.take_append_drop]
    have h := hDJ.okTy ψ' σ
    rw [hsplitT] at h
    exact ⟨⟨wellDenoted_mkPisAV_body h.1 _ hfitP, annotValid_mkPisAV_body h.2 _ hfitP⟩, hlenDs⟩
  refine
    { hR := fun t ht => hrepJ.rulesRead hrules hfR t ht, hps := hDsA, hpsWD := hDsWD,
      hparams := hparamsJ, hpps := ?_, hipsLen := ?_, hk := hk, hctorsC := hctorsCJ,
      hpins := fun t => hpinsAVJ t ψ', hview := hviewJ,
      hLS := fun t ht => hrepJ.leafShape t (by rw [hkRJ]; exact ht) ψ', hFF := hFFJ,
      hctors := fun J cA hJ => hrepJ.ctors J cA hJ, hpIff := fun J cA hJ => hrepJ.paramsIff J cA hJ ψ',
      hmems := ?_, htgts := ?_, hTg := ?_, huse := ?_, hbits := ?_, hnbP := ?_, hvia := ?_,
      hviaWD := ?_, hCAD := ?_ }
  · rw [List.length_take, (hFFJ 0 hk).1]
    omega
  · intro t ht
    rw [dJ.ipss_getD ψ' ht, List.length_drop, (hFFJ t ht).1]
    show dJ.nP + dJ.nIdxAt t - dJ.nP = dJ.nIdxAt t
    omega
  · intro J hJ
    have h := (hrepJ.memsReal J (by rw [hnAllJ]; exact hJ)).mpr hJ
    rw [hkRJ] at h
    exact h
  · intro J i
    have h := hrepJ.tgtsRLt J i
    rw [show dJ.tgtsR J = dJ.tgts J from (hviewJ J).2.1] at h
    exact h
  · -- the targets: the copies' carriers
    intro t ht
    have hc := hgrp t ht
    rw [← hσ]
    rw [← hσ] at hparamsJ
    refine d.targetOk_psi mp hpsA hparamsA hDsA ht (hFFJ t ht)
      (hrepJ.paramsIffM t (by rw [hkRJ]; exact ht) ψ') hparamsJ hlev (hFFA _ (hkA t ht))
      (hpIffMA _ (hkA t ht)) ?_ rfl rfl
    have h := hc.idx
    rwa [← Nat.add_assoc] at h
  · intro J i hu
    rw [(hviewJ J).1]
    exact of_decide_eq_true hu
  · intro J i Ψ Eis tl hv
    exact psiVia_bits d dJ ψ k₀ dJ.nP auxOf (dJ.bb ψ') tbl J i hv
  · -- no later reading mentions a replaced position
    intro J cA hJ C nF ds Es recIdx Eiss tls hcd'
    have hcd'' := hcd'
    unfold IndRepData.cdsR at hcd''
    rw [fixCtorDataList_getElem?, Nat.zero_add] at hcd''
    have hJall : dJ.ctorsAll[J]? = some cA := by
      unfold IndRepData.ctorsAll; rw [hctorsCJ, List.append_nil]; exact hJ
    rw [hJall] at hcd''
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcd''
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcd''
    obtain ⟨cAa, hJa, hf⟩ := hctors J cA hJ
    obtain ⟨-, -, hDJ⟩ := hrepJ.ctors J cA hJ
    have h := d.noBVar_psi (m := mp.base2) hDsA auxOf cd tbl (dJ.bb ψ') hf.nF hf.read hf.ctor.2.2
      hf.cf hf.cb hf.view hDJ
    rw [(hviewJ J).2.2.1, (hviewJ J).2.2.2]
    exact h
  · -- the transports' ONE fact
    intro J cA hJ C nF ds Es recIdx Eiss tls hcd' i hi Ψ Eis tl hv fs hfs as has
    have hcd'' := hcd'
    unfold IndRepData.cdsR at hcd''
    rw [fixCtorDataList_getElem?, Nat.zero_add] at hcd''
    have hJall : dJ.ctorsAll[J]? = some cA := by
      unfold IndRepData.ctorsAll; rw [hctorsCJ, List.append_nil]; exact hJ
    rw [hJall] at hcd''
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcd''
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcd''
    obtain ⟨cAa, hJa, hf⟩ := hctors J cA hJ
    obtain ⟨hTJ', hlenJ⟩ := hTJ J cA hJ
    refine d.via_psi mp hDsA hDsWD auxOf cd tbl hf.nF hf.read hf.ctor.2.2 hf.view hTJ' hlenJ hbz
      (hcd J cA hJ) (fun i hi hA hT => ?_) i hi Ψ Eis tl hv fs hfs as has
    -- the target's pointwise typing from its Π-typing
    have hc := hcd J cA hJ i hi hA hT
    obtain ⟨hTg', -⟩ := htgTg J cA hJ i hi hA hT
    exact (cd (d.tgtsR (auxOf J) i - k₀)).dJ.psiTyped_of_pi mp.base2
      (by rw [(cd (d.tgtsR (auxOf J) i - k₀)).dJ.ipss_getD _ hc.mm, List.length_drop, hc.ff.1]
          show _ = (cd (d.tgtsR (auxOf J) i - k₀)).dJ.nIdxAt (cd (d.tgtsR (auxOf J) i - k₀)).mm
          omega)
      hTg' (htbl J cA hJ i hi hA hT)
  · -- the transports are graded
    intro J cA hJ C nF ds Es recIdx Eiss tls hcd' fs ihs hfs hihs hfit i Ψ Eis tl hv
    have hcd'' := hcd'
    unfold IndRepData.cdsR at hcd''
    rw [fixCtorDataList_getElem?, Nat.zero_add] at hcd''
    have hJall : dJ.ctorsAll[J]? = some cA := by
      unfold IndRepData.ctorsAll; rw [hctorsCJ, List.append_nil]; exact hJ
    rw [hJall] at hcd''
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcd''
    obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcd''
    obtain ⟨cAa, hJa, hf⟩ := hctors J cA hJ
    obtain ⟨hTJ', hlenJ⟩ := hTJ J cA hJ
    rw [(hviewJ J).1] at hfit hihs ⊢
    have h := d.viaWD_psi mp hDsA hDsWD auxOf cd tbl hf.nF hf.read hf.ctor.2.2 hf.view hTJ' hlenJ hbz
      hsatA hk (hcd J cA hJ) (htbl J cA hJ) (htgTg J cA hJ) (dJ.motChoiceAVs_length _ _ _ _)
      (dJ.minChoiceAVs_length _ _ _ _ _) (dJ.invTgAV ψ' DsA (d.psiL mp.base2 ψ k₀ j₀) (d.psiPinsT dJ.nP))
      fs ihs hfs hihs hfit i Ψ Eis tl hv
    exact h
  · -- the copy's constructor at the transported domains
    intro J cA hJ
    obtain ⟨cAa, hJa, hf⟩ := hctors J cA hJ
    obtain ⟨-, -, hDJ⟩ := hrepJ.ctors J cA hJ
    have hmemJ : dJ.mems J < dJ.k := by
      have h := (hrepJ.memsReal J (by rw [hnAllJ]; exact (List.getElem?_eq_some_iff.mp hJ).1)).mpr
        (List.getElem?_eq_some_iff.mp hJ).1
      rw [hkRJ] at h
      exact h
    have htgtsJ : ∀ i, dJ.tgts J i < dJ.k := fun i => by
      have h := hrepJ.tgtsRLt J i
      rw [(hviewJ J).2.1] at h
      exact h
    have hviewA' := hf.view
    have cff := d.ctorFieldFacts_of mp hpsA hpinsA hLSA hFFA hparamsA hf.ctor hf.pIff hf.mem
      (fun i => by have := hf.tgts i; rw [hviewA'.2.1] at this; exact this)
      (fun i => by rw [hviewA'.2.1])
    rw [← hσ]
    refine d.ctorAtDoms_psi mp hpsA hparamsA hDsA hlev auxOf cd tbl hJa hf.nF hf.read hf.ctor hf.pIff
      hf.view hf.tgts hf.mem hFFA hLSA (fun fs hfs => (cff.2 fs hfs).1) ⟨(hviewJ J).2.1, (hviewJ J).2.2.1, (hviewJ J).2.2.2⟩
      htgtsJ hmemJ (fun i dd hd => hDJ.tssBits ψ' i dd hd) hgrp (hcd J cA hJ)


/-! ## The fold's output: the term graded and in ψ's Π-type -/

namespace PsiSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
  {TgV : Nat → Nat → AnnotTerm}

/-- **The fold term is graded**: the recursor's tower is graded, the
choice's prefix terms are graded (`choice_prefix_wellDenoted`) and fit
it (`prefixFit`). -/
theorem fold_wellDenoted (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) {t : Nat}
    (ht : t < d.k) :
    WellDenotedV V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
      (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
        d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
          (d.psiBodyAV head useIh via) d.nAll)) := by
  have hT := (S.hR t ht).tower_wellDenotedV mp ψ ρ
  have hmem := (S.hR t ht).leaf_mem mp ψ ρ
  rw [d.recDataAV_split, mkPisAV_append] at hT hmem
  have hall := d.choice_prefix_wellDenoted mp.base2 (d.psiBodyAV head useIh via) S.hps S.hpsWD S.hk
    S.hpps S.hipsLen ((S.hR 0 S.hk).tower_wellDenotedV mp ψ ρ)
    (by rw [rebit_map_dom]; exact S.hparams)
    (fun t ht => d.invTg_fact ψ S.hpsWD (S.hTg t ht)) S.hmin
  exact (wellDenotedV_mkAppN_of_spineFit hT ⟨mp.base2.acval_wellDenoted _ ψ _, mp.acval_validV _ ψ _⟩
    hall hmem S.prefixFit).1

set_option maxHeartbeats 3200000 in
/-- **The fold term inhabits ψ's Π-type**: the recursor's residual tower
at the choice's prefix interprets as ψ's Π-type at the parameter frame
(`interp_mkPisAV_congr`: the index binders lifted over the motives and
minors, the major `majorAVP` and `famAppAV` at their two lift amounts,
the body by `interp_mutualConcAV_frame` + `motChoiceAV_fold` +
`invTg_fold` — `fold_mem`'s `hconc`). -/
theorem fold_mem_pi (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) {t : Nat}
    (ht : t < d.k) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.psiBodyAV head useIh via) d.nAll))
      ∈ˢ interp V ρ (d.psiTyAV mp.base2 ψ ps L pinsT t) := by
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨Ns, hNs⟩ : ∃ Ns, Ns = d.minChoiceAVs ψ ps Ms (d.psiBodyAV head useIh via) d.nAll :=
    ⟨_, rfl⟩
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hNsLen : Ns.length = d.nAll := by rw [hNs]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpre := S.prefixFit
  rw [← hMs, ← hNs] at hpre ⊢
  have h1 := recFold_mem mp (S.hR t ht) ψ hpre
  have hframe : consList ((ps ++ Ms ++ Ns).map (interp V ρ)) ρ
      = consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ := by
    rw [List.map_append, List.map_append]
  rw [hframe] at h1
  rw [d.interp_psiTyAV]
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [S.hps]
  have hMsvLen : (Ms.map (interp V ρ)).length = d.k := by rw [List.length_map, hMsLen]
  have hNsvLen : (Ns.map (interp V ρ)).length = d.nAll := by rw [List.length_map, hNsLen]
  have hipsLen := S.hipsLen t ht
  have hLcl : Term.bvarsBelow 0 ((d.Ls mp.base2 ψ).getD t default).erase := by
    rw [d.Ls_getD_eq mp.base2 ψ ht]; exact mp.base2.cval_closedL _ ψ
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ
  have hframe2 : consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ
      = consList (Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) σ := by
    rw [← hσ, List.append_assoc, consList_append]
  rw [hframe2] at h1
  have hMNlen : (Ms.map (interp V ρ) ++ Ns.map (interp V ρ)).length = d.k + d.nAll := by
    rw [List.length_append, hMsvLen, hNsvLen]
  -- the residual tower's binders, positionally
  have hpostLen : (d.recPostAV mp.base2 ψ t).length = d.nIdxs.getD t 0 + 1 := by
    unfold IndRepData.recPostAV
    rw [List.length_append, rebit_length, liftDoms_length, List.length_singleton, hipsLen]
  have hmotLen : (rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t)).length = d.nIdxs.getD t 0 + 1 := by
    unfold IndRepData.motDataAV
    rw [rebit_length, List.length_append, rebit_length, List.length_singleton, hipsLen]
  have hpostGet : ∀ k, (d.recPostAV mp.base2 ψ t)[k]? =
      if k < d.nIdxs.getD t 0 then
        (((d.ipss ψ).getD t [])[k]?).map fun dd =>
          (dd.1, d.bb ψ, dd.2.2.liftN ((d.Ls mp.base2 ψ).length + (d.cdsR ψ).length) (0 + k))
      else if k = d.nIdxs.getD t 0 then
        some (0, d.bb ψ, majorAVP ((d.Ls mp.base2 ψ).getD t default) (d.pinsOf ψ t) d.nP
          (d.nIdxs.getD t 0) (d.Ls mp.base2 ψ).length (d.cdsR ψ).length)
      else none := by
    intro k
    unfold IndRepData.recPostAV
    split
    · next h =>
      rw [List.getElem?_append_left (by rw [rebit_length, liftDoms_length, hipsLen]; exact h),
        rebit_getElem?, liftDoms_getElem?, Option.map_map]
      rfl
    · next h =>
      rw [List.getElem?_append_right (by rw [rebit_length, liftDoms_length, hipsLen]; omega),
        rebit_length, liftDoms_length, hipsLen]
      split
      · next h' => subst h'; simp
      · next h' =>
        rw [List.getElem?_singleton]
        simp only [ite_eq_right_iff]
        intro h''
        omega
  have hmotGet : ∀ k, (rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t))[k]? =
      if k < d.nIdxs.getD t 0 then
        (((d.ipss ψ).getD t [])[k]?).map fun dd => (dd.1, d.bb ψ, dd.2.2)
      else if k = d.nIdxs.getD t 0 then
        some (0, d.bb ψ, famAppAV ((d.Ls mp.base2 ψ).getD t default) (d.pinsOf ψ t) d.nP
          (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))
      else none := by
    intro k
    unfold IndRepData.motDataAV
    rw [rebit_getElem?]
    split
    · next h =>
      rw [List.getElem?_append_left (by rw [rebit_length, hipsLen]; exact h), rebit_getElem?,
        Option.map_map]
      rfl
    · next h =>
      rw [List.getElem?_append_right (by rw [rebit_length, hipsLen]; omega), rebit_length, hipsLen]
      split
      · next h' => subst h'; simp
      · next h' =>
        rw [List.getElem?_singleton]
        simp only [ite_eq_right_iff, Option.map_eq_none_iff]
        intro h''
        omega
  -- the two towers interpret alike
  have htower : interp V (consList (Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) σ)
        (mkPisAV (d.recPostAV mp.base2 ψ t) (mutualConcAV d.k d.nAll (d.nIdxAt t) t))
      = interp V σ (mkPisAV (rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t))
          ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0)) := by
    refine interp_mkPisAV_congr (by rw [hpostLen, hmotLen]) ?_ ?_ ?_
    · intro k d₁ d₂ h₁ h₂
      rw [hpostGet] at h₁
      rw [hmotGet] at h₂
      split at h₁
      · obtain ⟨dd, -, rfl⟩ := Option.map_eq_some_iff.mp h₁
        rw [if_pos ‹_›] at h₂
        obtain ⟨dd', -, rfl⟩ := Option.map_eq_some_iff.mp h₂
        exact Iff.rfl
      · split at h₁
        · obtain rfl := Option.some.inj h₁
          rw [if_neg ‹_›, if_pos ‹_›] at h₂
          obtain rfl := Option.some.inj h₂
          exact Iff.rfl
        · exact nomatch h₁
    · intro k d₁ d₂ as h₁ h₂ hsp
      have hasLen : as.length = k := by
        rw [hsp.length_eq, List.length_map, List.length_take, hpostLen]
        have := (List.getElem?_eq_some_iff.mp h₁).1
        rw [hpostLen] at this
        omega
      rw [hpostGet] at h₁
      rw [hmotGet] at h₂
      split at h₁
      · next hk =>
        obtain ⟨dd, hdd, rfl⟩ := Option.map_eq_some_iff.mp h₁
        rw [if_pos hk, hdd] at h₂
        obtain rfl := Option.some.inj h₂
        show interp V _ (dd.2.2.liftN ((d.Ls mp.base2 ψ).length + (d.cdsR ψ).length) (0 + k)) = _
        rw [Nat.zero_add, d.Ls_length, d.cdsR_length, ← hMNlen, ← hasLen, interp_liftN_middle]
      · next hk =>
        split at h₁
        · next hk' =>
          obtain rfl := Option.some.inj h₁
          rw [if_neg hk, if_pos hk'] at h₂
          obtain rfl := Option.some.inj h₂
          show interp V _ (majorAVP _ _ _ _ _ _) = _
          unfold majorAVP
          have h := interp_famAppAV_at (L := (d.Ls mp.base2 ψ).getD t default)
            (fun σ₁ σ₂ => interp_closed (V := V) hLcl σ₁ σ₂) (d.pinsOf ψ t) d.nP
            (extra := Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) (is := as) (σ := σ)
          have h' := interp_famAppAV_at (L := (d.Ls mp.base2 ψ).getD t default)
            (fun σ₁ σ₂ => interp_closed (V := V) hLcl σ₁ σ₂) (d.pinsOf ψ t) d.nP
            (extra := []) (is := as) (σ := σ)
          simp only [consList_nil, List.length_nil, Nat.add_zero] at h'
          rw [hMNlen, hasLen, hk', ← Nat.add_assoc] at h
          rw [hasLen, hk'] at h'
          rw [d.Ls_length, d.cdsR_length, h, h']
        · exact nomatch h₁
    · intro as hsp
      have hfitM := (d.spineFit_recPostAV_iff mp.base2 ψ ht hipsLen (ρ := ρ) (psV := ps.map (interp V ρ))
        (MsV := Ms.map (interp V ρ)) (NsV := Ns.map (interp V ρ)) hMsvLen hNsvLen as).mp
        (by rw [List.append_assoc, consList_append, hσ]; exact hsp)
      have hfitM₀ := hfitM
      have hsplit := hfitM
      unfold IndRepData.motDataAV at hsplit
      rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hsplit
      obtain ⟨is, x, rfl, hisFit, -⟩ := hsplit
      have hisLen : is.length = d.nIdxAt t := by
        rw [hisFit.length_eq, List.length_map, rebit_length]; exact hipsLen
      rw [← consList_append, ← hσ, ← consList_append, ← List.append_assoc, ← List.append_assoc,
        ← List.append_assoc, interp_mutualConcAV_frame hMsvLen hNsvLen hisLen ht, hMs,
        d.motChoiceAVs_getD mp.base2 ψ ps _ ρ ht]
      have hfold := d.motChoiceAV_fold mp.base2 (Tg := d.invTgAV ψ ps L pinsT) S.hps hipsLen hfitM₀
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hfold
      rw [hfold, d.invTg_fold ψ hisFit, hσ, consList_append, consList_cons, consList_nil, interp_liftN,
        shiftE_succ_cons, shiftE_zero_zero]
  rw [← htower]
  exact h1

/-- **ψ's Π-type is graded** at the parameter frame: its index binders
by the target's own tower, its major by the container's leaf at the
parameters (`targetOk_real`), its body by the target at the indices. -/
theorem psiTyAV_wellDenotedV (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV)
    (hpIffM : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hlev : d.elimL.eval ψ = d.w ψ) {t : Nat} (ht : t < d.k) :
    WellDenotedV V ρ (d.psiTyAV mp.base2 ψ ps L pinsT t) := by
  have hTgt := S.hTg t ht
  have hTgR := d.targetOk_real mp S.hps ht (S.hFF t ht) (hpIffM t ht) S.hparams hlev
  have hipsLen := S.hipsLen t ht
  unfold IndRepData.TargetOk at hTgt hTgR
  unfold IndRepData.psiTyAV
  refine wellDenotedV_instSeq ps S.hpsWD ?_
  have hch : chain V ρ ps = consList (ps.map (interp V ρ)) ρ := by
    unfold chain; exact consN_eq_consList _ _
  rw [hch]
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ at hTgt hTgR ⊢
  have hidxLen : (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).length
      = d.nIdxs.getD t 0 := by rw [rebit_length, hipsLen]
  -- the entries
  have hentries : ∀ (k : Nat) (dd : Nat × Nat × AnnotTerm),
      (rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t))[k]? = some dd →
      ∀ as : List V,
        SpineFit σ (((rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t)).take k).map (·.2.2)) as →
        WellDenotedV V (consList as σ) dd.2.2 := by
    intro k dd hk as hsp
    have hk' : k < d.nIdxs.getD t 0 + 1 := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      unfold IndRepData.motDataAV at this
      rw [rebit_length, List.length_append, rebit_length, List.length_singleton, hipsLen] at this
      exact this
    have hspIdx : SpineFit σ (((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).take k).map
        (·.2.2)) as := by
      have h := hsp
      unfold IndRepData.motDataAV at h
      rw [List.map_take, rebit_map_dom, List.map_append,
        List.take_append_of_le_length (by rw [List.length_map, rebit_length, hipsLen]; omega),
        ← List.map_take] at h
      exact h
    unfold IndRepData.motDataAV at hk
    rw [rebit_getElem?] at hk
    rcases Nat.lt_or_ge k (d.nIdxs.getD t 0) with hlt | hge
    · rw [List.getElem?_append_left (by rw [rebit_length, hipsLen]; exact hlt), rebit_getElem?] at hk
      obtain ⟨d₁, hd₁, rfl⟩ := Option.map_eq_some_iff.mp hk
      obtain ⟨d₂, hd₂, rfl⟩ := Option.map_eq_some_iff.mp hd₁
      have hk₂ : (rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t []))[k]?
          = some (d₂.1, pwBit ψ ConLeche.PropWhen.never, d₂.2.2) := by
        rw [rebit_getElem?, hd₂]; rfl
      exact ⟨wellDenoted_mkPisAV_dom hTgt.1.1 as k (d₂.1, pwBit ψ ConLeche.PropWhen.never, d₂.2.2) hk₂
          hspIdx,
        annotValid_mkPisAV_dom hTgt.1.2 as k (d₂.1, pwBit ψ ConLeche.PropWhen.never, d₂.2.2) hk₂ hspIdx⟩
    · have hkeq : k = d.nIdxs.getD t 0 := by omega
      subst hkeq
      rw [List.getElem?_append_right (by rw [rebit_length, hipsLen]; exact Nat.le_refl _), rebit_length,
        hipsLen, Nat.sub_self, List.getElem?_singleton, if_pos rfl] at hk
      obtain rfl := Option.some.inj hk
      show WellDenotedV V (consList as σ)
        (famAppAV ((d.Ls mp.base2 ψ).getD t default) (d.pinsOf ψ t) d.nP _ _)
      rw [d.Ls_getD_eq mp.base2 ψ ht, S.hpins t]
      rw [List.take_of_length_le (by rw [hidxLen]; exact Nat.le_refl _)] at hspIdx
      exact (hTgR.2 as hspIdx).1
  -- the body
  have hbody : ∀ as : List V, SpineFit σ ((rebit (d.bb ψ) (d.motDataAV mp.base2 ψ t)).map (·.2.2)) as →
      WellDenotedV V (consList as σ)
        ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0) ∧
      (d.bb ψ = 0 → interp V (consList as σ)
        ((famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)).liftN 1 0)
          ∈ˢ (univZero : V)) := by
    intro as hsp
    rw [rebit_map_dom] at hsp
    unfold IndRepData.motDataAV at hsp
    rw [List.map_append, List.map_singleton, rebit_map_dom, spineFit_append_singleton_iff] at hsp
    obtain ⟨is, x, rfl, hisFit, -⟩ := hsp
    rw [consList_append, consList_cons, consList_nil, WellDenotedV_liftN, interp_liftN,
      shiftE_succ_cons, shiftE_zero_zero]
    have hisFit' : SpineFit σ
        ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is := by
      rw [rebit_map_dom]; exact hisFit
    refine ⟨(hTgt.2 is hisFit').1, fun h0 => ?_⟩
    have h := (hTgt.2 is hisFit').2
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp h0
    rw [h0', univ_zero] at h
    exact h
  exact ⟨wellDenoted_mkPisAV_of (fun k dd hk as hsp => (hentries k dd hk as hsp).1)
      (fun as hsp => (hbody as hsp).1.1),
    annotValid_mkPisAV_of (b := d.bb ψ) (fun dd hd => mem_rebit hd)
      (fun k dd hk as hsp => (hentries k dd hk as hsp).2)
      (fun as hsp => ⟨(hbody as hsp).1.2, (hbody as hsp).2⟩)⟩

/-- **The fold's property at member `t`** — what the step returns for
the copy of `t`: the fold term is graded, ψ's Π-type is graded, and the
term inhabits it. -/
theorem typedPi (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV)
    (hpIffM : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hlev : d.elimL.eval ψ = d.w ψ) {t : Nat} (ht : t < d.k) :
    d.PsiTypedPi mp.base2 ψ ρ ps L pinsT t
      (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.psiBodyAV head useIh via) d.nAll)) :=
  ⟨fold_wellDenoted d S ht, psiTyAV_wellDenotedV d S hpIffM hlev ht, fold_mem_pi d S ht⟩

end PsiSetup


/-! ## The step and the fold over the order

The fold (`orderFold`, `Verify/Inductives/NestedOrder`) builds one term
per pin along the kernel's topological order; the step for pin `j'`
builds the copy's term `psiTerm` from the table of the earlier terms
(through `psiVia`).  Under the group's facts (`GroupFacts`, the
hypotheses of `psiSetup_of_group` that are the group's own) and the
BRIDGE — every transport's target is a reference `R j' j''` of the
order's relation — the step returns `PsiTypedPi` for its copy from
`PsiTypedPi` at the copies it refers to (`psiStep_typed`), and
`TopoOrder.orderFold_all` gives it at every pin (`psiFold_typed`).  At
the run level `R` is `CopyRef` (`topoOrder_of_run`) and the bridge is
owed from the constructor-side identity (DESIGN §M.26). -/

/-- The fold's term for the copy `c` (its group's `auxOf`) from the
table `tbl` of the earlier copies' terms. -/
@[expose] def psiTerm (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (c : CopyData V)
    (auxOf : Nat → Nat) (tbl : Nat → AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (m.acval (c.dJ.recNames c.mm) c.ψ')
    (c.DsA ++ c.dJ.motChoiceAVs m c.ψ' c.DsA
        (c.dJ.invTgAV c.ψ' c.DsA (d.psiL m ψ k₀ c.base) (d.psiPinsT c.dJ.nP)) ++
      c.dJ.minChoiceAVs c.ψ' c.DsA
        (c.dJ.motChoiceAVs m c.ψ' c.DsA
          (c.dJ.invTgAV c.ψ' c.DsA (d.psiL m ψ k₀ c.base) (d.psiPinsT c.dJ.nP)))
        (c.dJ.psiBodyAV (d.psiHead m ψ c.dJ.nP auxOf) (psiUseIh c.dJ)
          (d.psiVia c.dJ ψ k₀ c.dJ.nP auxOf (c.dJ.bb c.ψ') tbl)) c.dJ.nAll)

/-- The fold's step: pin `j'`'s term from the table. -/
@[expose] def psiStep (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) (tbl : Nat → AnnotTerm) (j' : Nat) : AnnotTerm :=
  d.psiTerm m ψ k₀ (cd j') (auxOfs j') tbl

/-- The fold's property at pin `j'`: the term is `PsiTypedPi` for the
copy there. -/
@[expose] def PsiP (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (σ : Nat → V)
    (cd : Nat → CopyData V) (j' : Nat) (Ψ : AnnotTerm) : Prop :=
  (cd j').dJ.PsiTypedPi m (cd j').ψ' σ (cd j').DsA (d.psiL m ψ k₀ (cd j').base)
    (d.psiPinsT (cd j').dJ.nP) (cd j').mm Ψ

end IndRepData

/-- **A copy's group is live** — `psiSetup_of_group`'s hypotheses that
are the group's own, at the copy `c` (pin `c.base + c.mm`) with the
group's `auxOf`: the container's representation and views, the pin's
level assignment, the members' data, the copies' constructors. -/
structure GroupFacts {μ : CheckMode} (mp : EnvModelM V μ env) (d : IndRepData V) (ψ : Name → Nat)
    (k₀ : Nat) (lpsT : List Name) (cd : Nat → CopyData V) (c : CopyData V) (auxOf : Nat → Nat) :
    Prop where
  mm : c.mm < c.dJ.k
  ctorsC : c.dJ.ctorsC = []
  kReal : c.dJ.kReal = c.dJ.k
  pinsAV : ∀ (t : Nat) (φ : Name → Nat), c.dJ.pinsAV t φ = paramBvarsAt c.dJ.nP c.dJ.nP
  view : ∀ J, c.dJ.ksR J = c.dJ.ksF J ∧ c.dJ.tgtsR J = c.dJ.tgts J ∧ c.dJ.eissR J = c.dJ.eissF J ∧
    c.dJ.tssR J = c.dJ.tssF J
  rep : ∃ (T : Name) (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule) (t₀ : Nat),
    t₀ < c.dJ.k ∧ rules ≠ [] ∧ env.find? cvR.name = some (.recInfo cvR mI rP rules) ∧
    IndRep mp.base2 T cvT cvR mI rP rules c.dJ t₀
  len : c.DsA.length = c.dJ.nP
  lev : c.dJ.elimL.eval c.ψ' = c.dJ.w c.ψ'
  kA : ∀ t, t < c.dJ.k → k₀ + c.base + t < d.k
  grp : ∀ t, t < c.dJ.k → CopyData.Ok mp.base2 d ψ k₀ (c.base + t) ⟨c.dJ, t, c.ψ', c.DsA, c.base⟩
  ctors : ∀ Jc cAJ, c.dJ.ctorsA[Jc]? = some cAJ → ∃ cAa, d.ctorsA[auxOf Jc]? = some cAa ∧
    CopyCtorFacts mp.base2 d c.dJ ψ c.ψ' c.DsA k₀ c.base cd lpsT Jc (auxOf Jc) cAJ cAa

namespace GroupFacts

/-- A live copy's data are `CopyData.Ok` at its pin. -/
theorem ok {μ : CheckMode} {mp : EnvModelM V μ env} {d : IndRepData V} {ψ : Name → Nat} {k₀ : Nat}
    {lpsT : List Name} {cd : Nat → CopyData V} {c : CopyData V} {auxOf : Nat → Nat}
    (hg : GroupFacts mp d ψ k₀ lpsT cd c auxOf) {j' : Nat} (hj : c.base + c.mm = j') :
    CopyData.Ok mp.base2 d ψ k₀ j' c := by
  have h := hg.grp c.mm hg.mm
  rw [hj] at h
  exact h

/-- A live copy's carrier is a fold target for its container
(`targetOk_psi` at the group's facts). -/
theorem targetOk {μ : CheckMode} {mp : EnvModelM V μ env} {d : IndRepData V} {ψ : Name → Nat}
    {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hpIffMA : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    {k₀ : Nat} {lpsT : List Name} {cd : Nat → CopyData V} {c : CopyData V} {auxOf : Nat → Nat}
    (hg : GroupFacts mp d ψ k₀ lpsT cd c auxOf) :
    c.dJ.TargetOk c.ψ' (consList (psA.map (interp V ρ₀)) ρ₀) c.DsA (d.psiL mp.base2 ψ k₀ c.base)
      (d.psiPinsT c.dJ.nP) c.mm := by
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, -, -, hrepJ⟩ := hg.rep
  have hk : 0 < c.dJ.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  have hFFJ : ∀ t, t < c.dJ.k → c.dJ.FormerFacts mp.base2 c.ψ' t :=
    fun t ht => c.dJ.formerFacts_of_indRep hrepJ hg.kReal c.ψ' ht
  have hsatA : Sat V (d.params ψ).reverse (consList (psA.map (interp V ρ₀)) ρ₀) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparamsA
    rwa [List.append_nil] at h
  have hc0 := hg.grp 0 hk
  have hparamsJ : SpineFit (consList (psA.map (interp V ρ₀)) ρ₀) (c.dJ.params c.ψ')
      (c.DsA.map (interp V (consList (psA.map (interp V ρ₀)) ρ₀))) :=
    d.pinFit_of_leafShape rfl (hFFJ 0 hk) (hrepJ.leafShape 0 (by rw [hg.kReal]; exact hk) c.ψ')
      hc0.pin hsatA
  have hc := hg.grp c.mm hg.mm
  refine d.targetOk_psi mp hpsA hparamsA hg.len hg.mm (hFFJ c.mm hg.mm)
    (hrepJ.paramsIffM c.mm (by rw [hg.kReal]; exact hg.mm) c.ψ') hparamsJ hg.lev
    (hFFA _ (hg.kA c.mm hg.mm)) (hpIffMA _ (hg.kA c.mm hg.mm)) ?_ rfl rfl
  have h := hc.idx
  rwa [← Nat.add_assoc] at h

end GroupFacts

namespace IndRepData

variable (d : IndRepData V)

/-- **The step is typed**: under the group's facts, the bridge (every
transport's target is a reference of `R`) and `PsiTypedPi` at the
copies referred to, the step's term is `PsiTypedPi` for its copy —
`psiSetup_of_group` then `PsiSetup.typedPi`. -/
theorem psiStep_typed {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name} {ψ : Name → Nat}
    {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    (hpinsA : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP)
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hLSA : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hpIffMA : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    {k₀ n : Nat} (hkn : d.k ≤ k₀ + n) {cd : Nat → CopyData V} {auxOfs : Nat → Nat → Nat}
    (hall : ∀ j', j' < n → GroupFacts mp d ψ k₀ lpsT cd (cd j') (auxOfs j') ∧
      (cd j').base + (cd j').mm = j')
    {R : Nat → Nat → Prop}
    (href : ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
      R j' (d.tgtsR (auxOfs j' Jc) i - k₀))
    (tbl : Nat → AnnotTerm) (j' : Nat)
    (ih : ∀ j'', R j' j'' → j'' < n → d.PsiP mp.base2 ψ k₀ (consList (psA.map (interp V ρ₀)) ρ₀) cd j''
      (tbl j'')) (hj' : j' < n) :
    d.PsiP mp.base2 ψ k₀ (consList (psA.map (interp V ρ₀)) ρ₀) cd j'
      (d.psiStep mp.base2 ψ k₀ cd auxOfs tbl j') := by
  obtain ⟨hg, hj⟩ := hall j' hj'
  obtain ⟨T, cvT, cvR, mI, rP, rules, t₀, ht₀, hrules, hfR, hrepJ⟩ := hg.rep
  -- the targets of the transports are live, typed and fold targets
  have htgt : ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
      d.tgtsR (auxOfs j' Jc) i - k₀ < n := by
    intro Jc cAJ hJc i hi hA hT
    obtain ⟨cAa, -, hf⟩ := hg.ctors Jc cAJ hJc
    have := hf.tgts i
    omega
  have S := d.psiSetup_of_group mp hpsA hparamsA hpinsA hFFA hLSA hpIffMA hg.ctorsC hg.kReal hg.pinsAV
    hg.view ht₀ hrules hfR hrepJ hg.len hg.lev hg.kA hg.grp (auxOfs j') cd tbl hg.ctors
    (fun Jc cAJ hJc i hi hA hT =>
      (hall _ (htgt Jc cAJ hJc i hi hA hT)).1.ok (hall _ (htgt Jc cAJ hJc i hi hA hT)).2)
    (fun Jc cAJ hJc i hi hA hT =>
      ih _ (href j' hj' Jc cAJ hJc i hi hA hT) (htgt Jc cAJ hJc i hi hA hT))
    (fun Jc cAJ hJc i hi hA hT =>
      ⟨(hall _ (htgt Jc cAJ hJc i hi hA hT)).1.targetOk hpsA hparamsA hFFA hpIffMA,
        (hall _ (htgt Jc cAJ hJc i hi hA hT)).1.lev⟩)
  exact S.typedPi (cd j').dJ (fun t ht => hrepJ.paramsIffM t (by rw [hg.kReal]; exact ht) (cd j').ψ')
    hg.lev hg.mm

/-- **ψ at every pin** (the datum level): the fold along a topological
order of `R` from any initial table is `PsiTypedPi` at every pin. -/
theorem psiFold_typed {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name} {ψ : Name → Nat}
    {ρ₀ : Nat → V} {psA : List AnnotTerm} (hpsA : psA.length = d.nP)
    (hparamsA : SpineFit ρ₀ (d.params ψ) (psA.map (interp V ρ₀)))
    (hpinsA : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP)
    (hFFA : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t)
    (hLSA : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t)
    (hpIffMA : ∀ t, t < d.k → ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    {k₀ n : Nat} (hkn : d.k ≤ k₀ + n) {cd : Nat → CopyData V} {auxOfs : Nat → Nat → Nat}
    (hall : ∀ j', j' < n → GroupFacts mp d ψ k₀ lpsT cd (cd j') (auxOfs j') ∧
      (cd j').base + (cd j').mm = j')
    {R : Nat → Nat → Prop}
    (href : ∀ j', j' < n → ∀ Jc cAJ, (cd j').dJ.ctorsA[Jc]? = some cAJ → ∀ i, i < cAJ.2 →
      i ∈ ConLeche.recIdxOf (d.ksR (auxOfs j' Jc)) → i ∉ ConLeche.recIdxOf ((cd j').dJ.ksF Jc) →
      R j' (d.tgtsR (auxOfs j' Jc) i - k₀))
    {order : List Nat} (hord : TopoOrder R n order) (tbl₀ : Nat → AnnotTerm) :
    ∀ j', j' < n → d.PsiP mp.base2 ψ k₀ (consList (psA.map (interp V ρ₀)) ρ₀) cd j'
      (orderFold (d.psiStep mp.base2 ψ k₀ cd auxOfs) order tbl₀ j') := by
  intro j' hj'
  exact hord.orderFold_all (d.psiStep mp.base2 ψ k₀ cd auxOfs)
    (fun j Ψ => j < n → d.PsiP mp.base2 ψ k₀ (consList (psA.map (interp V ρ₀)) ρ₀) cd j Ψ)
    (fun tbl j ih hj => d.psiStep_typed mp hpsA hparamsA hpinsA hFFA hLSA hpIffMA hkn hall href tbl j
      (fun j'' hR hj'' => ih j'' hR hj'') hj)
    tbl₀ j' hj' hj'

end IndRepData

end ConLeche.Model
