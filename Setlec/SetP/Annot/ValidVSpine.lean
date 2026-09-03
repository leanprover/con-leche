import Setlec.SetP.Annot.ValidV
import Setlec.SetP.Annot.Bit

/-!
# Bit validity of the literal spines (task #161, P3.5)

The `natLit`/`strLit` infer clauses grade the numeral and character
spines `denoteP` builds; the `AnnotOk2` halves live with
`natLit_facts2` in the canonical lane, and these are the `AnnotValidV`
halves: pure app-spine recursions — a spine node is an `.app`, whose
clause recurses, and the leaves are the routed `AcvalValidP` facts at
the clause's own `acval` reads.
-/

namespace Setlec.SetR.Interp2

open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- The numeral spine is bit-valid at valid leaves. -/
theorem AnnotValidV_natLitT2 {za sa : AVExpr} {ρ : Nat → V}
    (hz : AnnotValidV V ρ za) (hs : AnnotValidV V ρ sa) :
    ∀ n : Nat, AnnotValidV V ρ (natLitT2 za sa n)
  | 0 => hz
  | n + 1 => by
    rw [natLitT2, AnnotValidV_app]
    exact ⟨hs, AnnotValidV_natLitT2 hz hs n⟩

/-- The character-list spine is bit-valid at valid leaves. -/
theorem AnnotValidV_charListT2 {nilA consA ofNatA za sa : AVExpr}
    {ρ : Nat → V}
    (h1 : AnnotValidV V ρ nilA) (h2 : AnnotValidV V ρ consA)
    (h3 : AnnotValidV V ρ ofNatA) (hz : AnnotValidV V ρ za)
    (hs : AnnotValidV V ρ sa) :
    ∀ cs : List Char,
      AnnotValidV V ρ (charListT2 nilA consA ofNatA za sa cs)
  | [] => h1
  | c :: cs => by
    rw [charListT2, AnnotValidV_app, AnnotValidV_app]
    exact ⟨⟨h2, by
      rw [AnnotValidV_app]
      exact ⟨h3, AnnotValidV_natLitT2 hz hs c.toNat⟩⟩,
      AnnotValidV_charListT2 h1 h2 h3 hz hs cs⟩

end Setlec.SetR.Interp2
