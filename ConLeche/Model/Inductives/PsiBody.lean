module

public import ConLeche.Model.Inductives.PsiFold
public import ConLeche.Model.Inductives.InvFold
public section

/-!
# The forward fold `ψ`: the body (task #279 M-B′ step 3h)

`ψ_A` folds the container's recursor at the choice whose targets are
the copies' carriers at the block's parameters and whose bodies rebuild
with the copies' constructors (DESIGN §M.22).  A body's spine has three
kinds of entry, decided per field: the FIELD variable, the kit's
HYPOTHESIS (`useIh`, as ψ⁻¹'s `mixedVarsAV`), and the TRANSPORT
(`viaEntryAV`, `PsiFold.lean`) — a `J`-ordinary field that is
aux-recursive into another copy.  This module spells the spine and the
body (`psiVarsAV`, `psiBodyAV`), reads the spine at the minor's leaf
frame (`interp_psiVarsAV`), and proves the kit's body fact
(`psiBody_leaf`) from the constructor's tower at the transported
domains (`CtorAtDoms`, `InvFold.CtorAtPins` with the domains explicit)
and the ONE fact each transport consumes of the earlier copy's term.

The bridge between the fields' prefix and the replaced prefix is
`ShadowRelP`: two spines agreeing off a SET of positions (the
hypotheses' and the transports'), `InvFold.ShadowRel` with the
recursive slots replaced by a predicate — the readings that mention no
replaced position below their depth are the same at both.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Spines agreeing off a set of positions -/

/-- Two field spines agreeing off the positions `P`. -/
@[expose] def ShadowRelP (P : Nat → Prop) (as as' : List V) : Prop :=
  as'.length = as.length ∧ ∀ l, l < as.length → ¬ P l → as'.getD l pt = as.getD l pt

theorem ShadowRelP.take {P : Nat → Prop} {fs vs : List V} (h : ShadowRelP P fs vs) (i : Nat) :
    ShadowRelP P (fs.take i) (vs.take i) := by
  refine ⟨by rw [List.length_take, List.length_take, h.1], fun l hl hr => ?_⟩
  rw [List.length_take] at hl
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega),
    List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  exact h.2 l (by omega) hr

/-- The excluded slots of `P` below the fields, at the parameter depth
`nP`: slot `q` is field `q - nP`. -/
@[expose] def replP (nP : Nat) (P : Nat → Prop) (n : Nat) : Nat → Prop :=
  fun q => nP ≤ q ∧ P (q - nP) ∧ q < nP + n

omit [SetTheory V] in
theorem replP_lt {nP : Nat} {P : Nat → Prop} {n : Nat} : ∀ q, replP nP P n q → q < nP + n :=
  fun _ h => h.2.2

/-- Two spines agreeing off `P` give frames agreeing off the excluded
slots (`agreeOff_shadow` at a predicate). -/
theorem agreeOff_shadowP {nP : Nat} {P : Nat → Prop} {as as' : List V}
    (h : ShadowRelP P as as') (ρp : Nat → V) :
    AgreeOff (exclP (replP nP P as.length) (nP + as.length)) (consList as ρp) (consList as' ρp) := by
  intro j hj
  by_cases hji : j < as.length
  · rw [consList_apply_lt' as ρp hji, consList_apply_lt' as' ρp (by rw [h.1]; exact hji), h.1]
    have hnr : ¬ P (as.length - 1 - j) := by
      intro hr
      apply hj
      refine ⟨nP + (as.length - 1 - j), ⟨Nat.le_add_right _ _, ?_, by omega⟩, by omega, by omega⟩
      rw [Nat.add_sub_cancel_left]; exact hr
    exact (h.2 (as.length - 1 - j) (by omega) hnr).symm
  · have h1 := consList_apply_add as ρp (j - as.length)
    have h2 := consList_apply_add as' ρp (j - as.length)
    rw [show j - as.length + as.length = j from by omega] at h1
    rw [h.1, show j - as.length + as.length = j from by omega] at h2
    rw [h1, h2]

/-- The transport under `as` more binders. -/
theorem interp_congr_shadowRelP {nP : Nat} {P : Nat → Prop} {fs vs : List V}
    (h : ShadowRelP P fs vs) (σ : Nat → V) (as : List V) {E : AnnotTerm}
    (hnb : NoBVar (exclP (replP nP P fs.length) (nP + fs.length + as.length)) E) :
    interp V (consList as (consList fs σ)) E = interp V (consList as (consList vs σ)) E :=
  interp_congr_noBVar E hnb (agreeOff_consList_exclP as replP_lt (agreeOff_shadowP h σ))

/-- The transport at a prefix of the spines. -/
theorem interp_congr_shadowRelP_at {nP : Nat} {P : Nat → Prop} {fs vs : List V}
    (h : ShadowRelP P fs vs) (σ : Nat → V) {n : Nat} (hn : n ≤ fs.length) {E : AnnotTerm}
    (hnb : NoBVar (exclP (replP nP P n) (nP + n)) E) :
    interp V (consList (fs.take n) σ) E = interp V (consList (vs.take n) σ) E := by
  have hlen : (fs.take n).length = n := by rw [List.length_take]; omega
  have := interp_congr_shadowRelP (h.take n) σ [] (E := E)
    (by rw [hlen, List.length_nil, Nat.add_zero]; exact hnb)
  simpa using this

/-! ## The spine and the body -/

/-- The transport specification of a field: the term built for the
target copy (at the parameter frame), the field's index readings and
its telescope (both at the field's own frame, as the container
constructor's field domain shows them). -/
abbrev ViaSpec := AnnotTerm × List AnnotTerm × List (Nat × Nat × AnnotTerm)

/-- **ψ's variable spine** at a minor's leaf frame: the transport where
`via` gives one, the hypothesis where `useIh`, the field otherwise. -/
@[expose] def psiVarsAV (recIdx : List Nat) (useIh : Nat → Bool) (via : Nat → Option ViaSpec)
    (nF o : Nat) : List AnnotTerm :=
  (List.range nF).map fun i =>
    match via i with
    | some (Ψ, Eis, tl) => viaEntryAV Ψ nF o i recIdx.length tl Eis
    | none =>
      if useIh i then AnnotTerm.bvar (recIdx.length - 1 - recIdx.idxOf i)
      else AnnotTerm.bvar (nF + recIdx.length - 1 - i)

/-- The transport's VALUE at field `i`: the λ-tower over the field's
telescope of the earlier copy's term at the index values and the field
at the telescope's values (`interp_viaEntryAV`). -/
noncomputable def viaVal (b : Nat) (ρp : Nat → V) (fs : List V) (i : Nat) : ViaSpec → V
  | (Ψ, Eis, tl) =>
    lamTower b (consList (fs.take i) ρp) tl fun σ' =>
      (Eis.map (interp V σ') ++
        [(Semantics.frameIdx tl.length σ').foldl SetTheory.app (fs.getD i pt)]).foldl
        SetTheory.app (interp V ρp Ψ)

/-- **ψ's values**: the transport's value, the hypothesis value, or the
field value. -/
noncomputable def psiVals (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) : List V :=
  (List.range fs.length).map fun i =>
    match via i with
    | some v => viaVal b ρp fs i v
    | none => if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt

theorem psiVals_length (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) :
    (psiVals b ρp recIdx useIh via fs ihs).length = fs.length := by simp [psiVals]

theorem psiVals_getD (b : Nat) (ρp : Nat → V) (recIdx : List Nat) (useIh : Nat → Bool)
    (via : Nat → Option ViaSpec) (fs ihs : List V) {i : Nat} (hi : i < fs.length) :
    (psiVals b ρp recIdx useIh via fs ihs).getD i pt
      = match via i with
        | some v => viaVal b ρp fs i v
        | none => if useIh i then ihs.getD (recIdx.idxOf i) pt else fs.getD i pt := by
  unfold psiVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **The spine reads to the values** at the leaf frame: the parameter
frame under the motives `Ms`, the earlier minors `ms`, the fields and
the hypotheses. -/
theorem interp_psiVarsAV {b o : Nat} {ρp : Nat → V} {Ms ms : List V}
    (hms : ms.length + Ms.length = o) (hk : 0 < Ms.length) {recIdx : List Nat}
    {useIh : Nat → Bool} {via : Nat → Option ViaSpec}
    (huse : ∀ i, useIh i = true → i ∈ recIdx) {fs ihs : List V}
    (hihs : ihs.length = recIdx.length)
    (hbits : ∀ i Ψ Eis tl, via i = some (Ψ, Eis, tl) → ∀ d ∈ tl, d.2.1 = b) :
    (psiVarsAV recIdx useIh via fs.length o).map
        (interp V (consList ihs (consList fs (consList ms (consList Ms ρp)))))
      = psiVals b ρp recIdx useIh via fs ihs := by
  apply List.ext_getElem
  · simp [psiVarsAV, psiVals]
  · intro i h1 h2
    have hi : i < fs.length := by simpa [psiVarsAV] using h1
    simp only [psiVarsAV, psiVals, List.getElem_map, List.getElem_range]
    have hfr : consList ihs (consList fs (consList ms (consList Ms ρp)))
        = consList (fs ++ ihs) (consList ms (consList Ms ρp)) := by rw [consList_append]
    cases hv : via i with
    | some v =>
      obtain ⟨Ψ, Eis, tl⟩ := v
      rw [interp_viaEntryAV hms hk rfl hihs hi (hbits i Ψ Eis tl hv) Ψ Eis]
      simp only [viaVal]
    | none =>
      rw [hfr]
      dsimp only
      split
      · next hu =>
        have hmem := huse i hu
        have hlt := List.idxOf_lt_length_of_mem hmem
        rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
          List.length_append, hihs, List.getD_eq_getElem?_getD,
          show fs.length + recIdx.length - 1 - (recIdx.length - 1 - recIdx.idxOf i)
            = fs.length + recIdx.idxOf i from by omega,
          List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
          ← List.getD_eq_getElem?_getD]
      · rw [interp_bvar, consList_apply_lt' _ _ (by rw [List.length_append, hihs]; omega),
          List.length_append, hihs, List.getD_eq_getElem?_getD,
          show fs.length + recIdx.length - 1 - (fs.length + recIdx.length - 1 - i) = i from by omega,
          List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

namespace IndRepData

variable (d : IndRepData V)

/-- **ψ's body** for constructor `J`: the head (the copy's constructor
at the block's parameters, lifted over the motives, the earlier
minors, the fields and the hypotheses) at ψ's spine. -/
@[expose] def psiBodyAV (head : Nat → AnnotTerm) (useIh : Nat → Nat → Bool)
    (via : Nat → Nat → Option ViaSpec) (J : Nat) : AnnotTerm :=
  AnnotTerm.mkAppN
    ((head J).liftN
      (d.k + J + (d.ctorsAll.getD J default).2 + (ConLeche.recIdxOf (d.ksR J)).length) 0)
    (psiVarsAV (ConLeche.recIdxOf (d.ksR J)) (useIh J) (via J) (d.ctorsAll.getD J default).2
      (d.k + J))

end IndRepData

end ConLeche.Model
