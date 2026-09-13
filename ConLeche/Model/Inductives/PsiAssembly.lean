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

end IndRepData

end ConLeche.Model
