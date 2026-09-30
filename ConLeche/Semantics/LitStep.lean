module

public import ConLeche.Semantics.Canon

@[expose] public section

/-!
# The literal clauses: the numeral facts

`natLit_factsAV`, the module's only theorem, mentions no fuel and no
mode — a pure `interp`/`WellDenoted` statement about the annotated
numeral spine (`natLitAV`, `Semantics/Canon.lean`) — and the model's
numeral clauses consume it.

The numeral induction is stated over the two head facts as **explicit
arguments** rather than re-deriving them from the environment.  That is
deliberate: the head facts are one chain over the stored
`Nat`/`Nat.zero`/`Nat.succ` shapes — the *same* chain for every numeral
— and factoring them out keeps the induction free of the literal
guards' inversion plumbing.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The numeral facts.**  Every annotated numeral is truthful and
inhabits the stored `Nat`'s interpretation — by induction on the
numeral, from the zero's membership and the successor's `piR`
membership.

`Nat → Nat` sits at result sort `1`, so the successor's product is in
the **graph regime** and `app_mem_piR_pos` applies with no fibre
premise; the app slot's kind-`0` component is vacuous for the same
reason. -/
theorem natLit_factsAV {ρ : Nat → V} {za sa natA : AnnotTerm}
    (hokz : WellDenoted V ρ za) (hoks : WellDenoted V ρ sa)
    (hz : interp V ρ za ∈ˢ interp V ρ natA)
    (hsucc : interp V ρ sa
      ∈ˢ piR 1 (interp V ρ natA) fun _ => interp V ρ natA) :
    ∀ n : Nat,
      WellDenoted V ρ (natLitAV za sa n) ∧
        interp V ρ (natLitAV za sa n) ∈ˢ interp V ρ natA := by
  intro n
  induction n with
  | zero => exact ⟨hokz, hz⟩
  | succ n ih =>
    obtain ⟨ihA, ihm⟩ := ih
    refine ⟨?_, ?_⟩
    · show WellDenoted V ρ (.app sa (natLitAV za sa n))
      rw [WellDenoted_app]
      exact ⟨hoks, ihA, 1, _, _, hsucc, ihm,
        fun h => absurd h Nat.one_ne_zero⟩
    · show interp V ρ (.app sa (natLitAV za sa n)) ∈ˢ _
      rw [interp_app]
      exact app_mem_piR_pos Nat.one_ne_zero hsucc ihm

open ConLeche (CheckMode Env Expr Name inferTypeCore inferBody
  natLitSupported)

variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

end ConLeche.Semantics
