module

public import ConLeche.Model.Inductives.FixChainFacts
public import ConLeche.Semantics.Tower.FixWire
import ConLeche.Model.Inductives.SumIntro
public section

/-!
# The fixed-point leaf's P currency (task #188)

The former's leaf `nativeTyAVI` at the P carrier: closed
(`nativeTyAVI_below`), graded and inhabiting its type's reading
(`FixLeafI.lean`'s `nativeTyAVI_wellDenoted/_mem` at the hereditary premise
`ParamsOkXI`, walked from the former's data — `fixLeafWalks`), and
bit-valid (`AnnotValid`, the annotation's second currency): the
functor's λ's are valid over the X-chains, which are valid at every
family (`fixChainWalkValid`, the walk of `FixChainsP.lean` for the
validity predicate — the entries' validity carries off the recursive
slots exactly as their grading, `AnnotValid_congr_noBVar`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Validity ignores the variables a term does not mention -/

/-! ## The X-chains, valid at every family -/

section Valid

variable {u w : Nat} {ρp : Nat → V} {Ids : List AnnotTerm} {nP nF : Nat} {ks : List RecFieldKind}
  {tls : List (List (Nat × Nat × AnnotTerm))} {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm}

/-- A Π-tower over `Prop`-regime binders is a truth value. -/
theorem interp_mkPisAV_mem_univZero {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}, (∀ d ∈ gds, d.2.1 = 0) →
      (gds = [] → interp V σ R ∈ˢ (univZero : V)) →
      interp V σ (mkPisAV gds R) ∈ˢ (univZero : V)
  | [], _, _, hR => by simpa [mkPisAV] using hR rfl
  | d :: gds, σ, hb, _ => by
    simp only [mkPisAV, interp_pi]
    rw [hb d List.mem_cons_self]
    exact piR_zero_mem_univZero

/-- **A Π-tower is valid** when its domains are along the telescope,
its body is at every fitting spine, and at the `Prop` regime the body
is a truth value there. -/
theorem AnnotValid_mkPisAV_of {w : Nat} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ w = 0)) →
      FieldsValid σ (gds.map (·.2.2)) →
      (∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R) →
      (w = 0 → ∀ as, SpineFit σ (gds.map (·.2.2)) as →
        interp V (consList as σ) R ∈ˢ (univZero : V)) →
      AnnotValid V σ (mkPisAV gds R)
  | [], _, _, _, hR, _ => by simpa [mkPisAV, consList] using hR [] trivial
  | d :: gds, σ, hb, hF, hR, h0 => by
    rw [List.map_cons] at hF
    obtain ⟨hv, hrest⟩ := hF
    simp only [mkPisAV, AnnotValid_pi]
    refine ⟨hv, fun x hx => ?_, fun hd x hx => ?_⟩
    · refine AnnotValid_mkPisAV_of (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd'))
        (hrest x hx) (fun as hsp => ?_) (fun hw as hsp => ?_)
      · have := hR (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
      · have := h0 hw (x :: as) ⟨hx, hsp⟩
        rwa [consList_cons] at this
    · have hw : w = 0 := (hb d List.mem_cons_self).mp hd
      refine interp_mkPisAV_mem_univZero
        (fun d' hd' => (hb d' (List.mem_cons_of_mem _ hd')).mpr hw) fun hnil => ?_
      subst hnil
      have := h0 hw [x] ⟨hx, trivial⟩
      simpa [consList] using this

/-- **A valid Π-tower's pieces**: the domains are valid along the
telescope, and the body is valid at every fitting spine. -/
theorem AnnotValid_mkPisAV_inv {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      AnnotValid V σ (mkPisAV gds R) →
      FieldsValid σ (gds.map (·.2.2)) ∧
      ∀ as, SpineFit σ (gds.map (·.2.2)) as → AnnotValid V (consList as σ) R
  | [], σ, h => ⟨trivial, fun as hsp => by
      cases as with
      | nil => simpa [mkPisAV, consList] using h
      | cons a as => exact hsp.elim⟩
  | d :: gds, σ, h => by
    simp only [mkPisAV, AnnotValid_pi] at h
    obtain ⟨hv, hB, -⟩ := h
    refine ⟨⟨hv, fun x hx => (AnnotValid_mkPisAV_inv (hB x hx)).1⟩, fun as hsp => ?_⟩
    cases as with
    | nil => exact hsp.elim
    | cons a as =>
      obtain ⟨ha, hsp'⟩ := hsp
      rw [consList_cons]
      exact (AnnotValid_mkPisAV_inv (hB a ha)).2 as hsp'

end Valid

/-! ## Closedness -/

end ConLeche.Model
