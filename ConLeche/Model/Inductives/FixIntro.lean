module

public import ConLeche.Model.Inductives.SumIntro
import ConLeche.Semantics.Tower.FixSquashI

public section

/-!
# The recursive recursor leaf's bit validity (task #188)

The sum route's validity kit (`SumIntroP.lean`) extended by the
inductive-hypothesis arguments of the case split
(`caseRecAVI`, `ConLeche/Semantics/Tower/FixCaseI.lean`): an ih argument
applies the unfolded function to the block's variables, the field's
index expressions moved to the payload frame (`substProj`) and the
payload's projection; its validity is the index expressions' at the
projections — which fit the constructor's fields.  Then the recursor
body, the one-step unfolding, the fixed-point sigma and the selected
fixed point (`fixSelAVI`) are valid.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Substitution of the payload's projections -/

/-- `UnderTowerValid` from the domains' validity and the leaf's at
every fitting spine. -/
theorem underTowerValid_of_fieldsValid {b : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      FieldsValid ρ (ds.map (·.2.2)) →
      (∀ as, SpineFit ρ (ds.map (·.2.2)) as → AnnotValid V (consList as ρ) b) →
      UnderTowerValid ρ b ds
  | [], ρ, _, hb => by
    show AnnotValid V ρ b
    simpa using hb [] trivial
  | d :: ds, ρ, hv, hb => by
    rw [List.map_cons] at hv
    refine ⟨hv.1, fun a ha => underTowerValid_of_fieldsValid (hv.2 a ha) fun as hsp => ?_⟩
    have := hb (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

end ConLeche.Model
