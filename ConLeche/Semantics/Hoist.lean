module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# The `WellDenoted` hoist kit

Every lemma here is an implication between `∀ ρ, Sat V Δa ρ → …`
shapes: the splitters that take a hoisted node fact apart, the
converses that build one from its parts, the head transfer that moves a
hoisted fact across a domain equality, and the lift.  They mention no
fuel, no run and no environment — the trap-check section at the end of
this file makes exactly that observation — and the inference quarters
consume them at every congruence.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The positive half: the hoist is self-propagating at a `∀`.**  A
hoisted `WellDenoted` of the node gives the domain's hoisted form and the
codomain's *in the extended context*, which is exactly the pair the
recursive call needs.  So paying the repair at the congruence costs
nothing beyond restating it. -/
theorem WellDenoted.hoist_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) := by
  refine ⟨fun ρ hρ => ((WellDenoted_pi V ρ u v A B) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((WellDenoted_pi V _ u v A B) ▸ h _ (Sat_tail hρ)).2
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-- The same at a `λ`, where the node's second component has the same
shape.  Together these cover all five congruence sites. -/
theorem WellDenoted.hoist_lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ b) := by
  refine ⟨fun ρ hρ => ((WellDenoted_lam V ρ v A b) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((WellDenoted_lam V _ v A b) ▸ h _ (Sat_tail hρ)).2.1
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-! ### The converses -/

/-- **The converse at a `Π`.**  `Sat_cons` is the whole content: an
inhabitant of the domain extends the valuation into `A :: Δa`. -/
theorem WellDenoted.of_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (hA : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A)
    (hB : ∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi u v A B) := by
  intro ρ hρ
  rw [WellDenoted_pi]
  exact ⟨hA ρ hρ, fun x hx => hB _ (Sat_cons (V := V) hρ hx)⟩

/-! ### The head transfer

Without these two the split kit stops one step short of the binder
congruences: `hoist_pi`/`hoist_lam` hand the right side's codomain
fact over `ta₂ :: Δa`, and the recursive call runs in `ta₁ :: Δa`. -/

/-- **A satisfying valuation transfers across a head equality.**
`Sat` reads the head at the *tail* valuation, which is exactly where
the domains' agreement is stated, so the transfer is immediate. -/
theorem Sat.head_congr {Δa : List AnnotTerm} {A B : AnnotTerm}
    {ρ : Nat → V}
    (heq : ∀ ρ' : Nat → V, Sat V Δa ρ' →
      interp V ρ' A = interp V ρ' B)
    (hρ : Sat V (A :: Δa) ρ) : Sat V (B :: Δa) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : B = Aa := by simpa using hi
    have h0 : ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) A := hρ 0 A rfl
    show ρ 0 ∈ˢ interp V (fun j => ρ (j + 1)) B
    rwa [heq _ (Sat_tail hρ)] at h0
  | succ i => exact hρ (i + 1) Aa (by simpa using hi)

/-! ### Trap-check on the kit

Every lemma above is an implication between `∀ ρ, Sat → …` shapes and
mentions no fuel and no run, so the smallest-fuel test
has nothing to bite on — and, per seal 11, that is *not* a clean bill
of health on its own.  The semantic check that matters is inhabitation
in a *non-vacuous* context, which the two examples below give: the
splitters and the converses are exercised at a `Δa` whose `Sat` is
satisfiable, so neither direction is a vacuous implication. -/

/-- `ρ ≡ ∅` satisfies `[⟪Sort 0⟫]`: the context used below is
genuinely inhabited. -/
private theorem sat_sort0_empty :
    Sat V [AnnotTerm.sort 0] (fun _ => (empty : V)) := by
  intro i Aa hi
  cases i with
  | zero =>
    obtain rfl : AnnotTerm.sort 0 = Aa := by simpa using hi
    simpa using empty_mem_univ (V := V) 0
  | succ i => simp at hi

/-- The converse builds a `Π` fact over that context and the splitter
takes it back apart, so neither direction of the kit is a vacuous
implication. -/
example :
    WellDenoted V (fun _ => (empty : V))
      (.pi 1 2 (.sort 0) (.sort 1)) ∧
    (∀ ρ : Nat → V, Sat V [AnnotTerm.sort 0] ρ →
      WellDenoted V ρ (AnnotTerm.sort 0)) := by
  have hpi : ∀ ρ : Nat → V, Sat V [AnnotTerm.sort 0] ρ →
      WellDenoted V ρ (.pi 1 2 (.sort 0) (.sort 1)) :=
    WellDenoted.of_pi (fun _ _ => by simp) (fun _ _ => by simp)
  exact ⟨hpi _ sat_sort0_empty, (WellDenoted.hoist_pi hpi).1⟩

end ConLeche.Semantics
