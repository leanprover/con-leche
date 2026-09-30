module

public import ConLeche.Model.Annot.Valid

public section

/-!
# Bit validity of the literal spines (task #161, P3.5)

The `natLit`/`strLit` infer clauses grade the numeral and character
spines `denoteMeta` builds; the `WellDenoted` halves live with
`natLit_factsAV` in the canonical lane, and these are the `AnnotValid`
halves: pure app-spine recursions — a spine node is an `.app`, whose
clause recurses, and the leaves are the routed `AcvalValid` facts at
the clause's own `acval` reads.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- The numeral spine is bit-valid at valid leaves. -/
theorem AnnotValid_natLitAV {za sa : AnnotTerm} {ρ : Nat → V}
    (hz : AnnotValid V ρ za) (hs : AnnotValid V ρ sa) :
    ∀ n : Nat, AnnotValid V ρ (natLitAV za sa n)
  | 0 => hz
  | n + 1 => by
    rw [natLitAV, AnnotValid_app]
    exact ⟨hs, AnnotValid_natLitAV hz hs n⟩

end ConLeche.Model
