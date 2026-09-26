module

public import ConLeche.Semantics.Tower.FixLeafI
public import ConLeche.Semantics.Tower.SumRecCase

@[expose] public section

/-!
# The recursive family's functor: readings and laws (task #188, indexed)

The X-chain's entries at the **X-frame** `(ρp, X, t, f₀ … f_{i-1})`
(`FixLeafI.lean`): an ordinary entry reads the domain at the parameter
frame below the fields (`interp_chainXI_ord`), a recursive entry
reads `X ⟨e⃗_i⟩` — the family at the tuple of the index expressions'
values (`recSlot_facts`, through the tupler's fold; graded through the
tupler's Π-tower chain, `appChainOk_of_mkPisAV`), and the terminator
reads the index equation against the tuple's projections
(`EqAll_eqsXI`).  On top of these the functor's laws: monotonicity in
the family (`chainXIGo_tele_sub`, `fixStepI_mono`), the closed member
family (the premise's witness, task #202 Stage B: the container
instance at `Type`, the top family at `Prop`), the fixed point
(`fixFamI_app_eq`), and the identification
of the fibre at `⟨ı⃗⟩` with the indexed sum route's restricted tagged
union (`fixFamI_app_eq_sum`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The X-frame kit -/


omit [SetTheory V] in
theorem Xframe_X (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) (as.length + 1) = X := by
  have := consList_apply_add as (cons t (cons X ρp)) 1
  rw [Nat.add_comm] at this
  exact this

omit [SetTheory V] in
theorem Xframe_t (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) as.length = t := by
  have := consList_apply_add as (cons t (cons X ρp)) 0
  rw [Nat.zero_add] at this
  exact this


/-! ## The recursive slot -/


section Slot

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm}


/-! ## The terminator -/

/-- At index level `0` every index value is the point. -/
theorem spineFit_pt_of_bound0 {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs as →
      ∀ l, l < as.length → as.getD l pt = pt
  | [], [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, hsp, _, _ => hsp.elim
  | _ :: _, [], _, hsp, _, _ => hsp.elim
  | F :: Fs, a :: as, hb, hsp, l, hl => by
    cases l with
    | zero =>
      have h0 : interp V ρ F ∈ˢ (univZero : V) := by
        have := hb.1; rwa [univ_zero] at this
      exact eq_pt_of_mem_univZero h0 hsp.1
    | succ l =>
      exact spineFit_pt_of_bound0 (hb.2 a hsp.1) hsp.2 l (by simpa using hl)


/-- **The index tuple's retraction**, at both regimes. -/
theorem projS_tupW (hI : IdxOk u ρp Ids) {is : List V} (hsp : SpineFit ρp Ids is) {l : Nat}
    (hl : l < Ids.length) : projS l (tupW u is) = is.getD l pt := by
  have hislen : is.length = Ids.length := hsp.length_eq
  by_cases hu : u = 0
  · subst hu
    rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
  · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]


end Slot

/-! ## The functor's laws -/

section Fam

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))} {Fss Ess : List (List AnnotTerm)}

omit [SetTheory V] in
theorem consList_snoc' (a : V) (as : List V) (ρ : Nat → V) :
    cons a (consList as ρ) = consList (as ++ [a]) ρ := by
  rw [consList_append]; rfl


-- `u` (the slot's tuple level) is unused by the fit itself; kept for uniformity


/-- **A Π-tower is graded** when its domains are along the telescope
and its body is at every fitting spine. -/
theorem WellDenoted_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      FieldsOkB w σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R) →
      WellDenoted V σ (mkPisAV gds R)
  | [], _, _, hR => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hF, hR => by
    rw [List.map_cons] at hF
    obtain ⟨hok, -, hrest⟩ := hF
    simp only [mkPisAV, WellDenoted_pi]
    refine ⟨hok, fun x hx => ?_⟩
    refine WellDenoted_mkPisAV_of (hrest x hx) fun as hsp => ?_
    have := hR (x :: as) ⟨hx, hsp⟩
    rwa [consList_cons] at this


/-- **A graded Π-tower's pieces**: at a `Prop`-regime family the
domains are graded along the telescope, and the body is graded at
every fitting spine. -/
theorem WellDenoted_mkPisAV_inv {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      WellDenoted V σ (mkPisAV gds R) →
      FieldsOkB 0 σ (gds.map (·.2.2)) ∧
      ∀ as, SpineFit σ (gds.map (·.2.2)) as → WellDenoted V (consList as σ) R
  | [], σ, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [mkPisAV, consList] using h
      | cons a as => exact hsp.elim⟩
  | d :: gds, σ, h => by
    simp only [mkPisAV, WellDenoted_pi] at h
    obtain ⟨hok, hB⟩ := h
    refine ⟨⟨hok, fun h0 => absurd rfl h0, fun x hx => (WellDenoted_mkPisAV_inv (hB x hx)).1⟩,
      fun as hsp => ?_⟩
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons]
      exact (WellDenoted_mkPisAV_inv (hB a ha)).2 as hsp'


/-! ## `FieldsOkB`, pointwise -/


/-! ## The identification with the real chains -/


/-! ## Elimination at a stage -/


end Fam

end ConLeche.Semantics
