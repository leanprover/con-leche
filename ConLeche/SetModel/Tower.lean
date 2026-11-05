module

public import ConLeche.SetModel.Ops

/-!
# A tower of function spaces over a universe determines its universe, along a fit

Task #480.  A family's former is stored at its declared type, which may reach
its telescope only after reduction.  What the use computes (`formerSortLoop`) and
what the block recorded are then two towers with one value, and the question is
whether they end in the same universe.  They do along a *fit*: over an empty
domain a function space is the unit, whatever its fibres, so nothing can be said
without arguments.

* `TowerEnds k X n`: `X` is `k` function spaces over `univ n`, at every argument.
* `TowerEndsPt k X n`: the same, where at each stage `X` may also be the point:
  what a use's walk knows, since a reduction claims nothing of the point.
* `TowerPath k X n`: a tower with one chain of arguments.
* `TowerPath.univ_eq`: a path and a walked tower of one value end in one universe.
-/

@[expose] public section

namespace ConLeche.SetModel

open SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- `X` is `k` function spaces over `univ n`, at every argument. -/
def TowerEnds : Nat → V → Nat → Prop
  | 0, X, n => X = univ n
  | k + 1, X, n => ∃ (A : V) (B : V → V), X = piV A B ∧ ∀ a, a ∈ˢ A → TowerEnds k (B a) n

/-- What a walk knows: `k` function spaces over `univ n`, unless a stage is the
point. -/
def TowerEndsPt : Nat → V → Nat → Prop
  | 0, X, n => X = pt ∨ X = univ n
  | k + 1, X, n => X = pt ∨ ∃ (A : V) (B : V → V), X = piV A B ∧ ∀ a, a ∈ˢ A → TowerEndsPt k (B a) n

theorem TowerEnds.toPt : ∀ {k : Nat} {X : V} {n : Nat}, TowerEnds k X n → TowerEndsPt k X n
  | 0, _, _, h => .inr h
  | _ + 1, _, _, ⟨A, B, hX, hB⟩ => .inr ⟨A, B, hX, fun a ha => (hB a ha).toPt⟩

/-- A tower with one chain of arguments. -/
inductive TowerPath : Nat → V → Nat → Prop where
  | zero {n : Nat} : TowerPath 0 (univ n) n
  | succ {k n : Nat} {A a : V} {B : V → V} :
      (∀ x, x ∈ˢ A → TowerEnds k (B x) n) → a ∈ˢ A → TowerPath k (B a) n →
      TowerPath (k + 1) (piV A B) n

/-- A function space over inhabited fibres is inhabited. -/
theorem piV_nonempty {A : V} {B : V → V} (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) :
    ∃ f, f ∈ˢ piV A B := by
  classical
  unfold piV
  by_cases hp : propN A B = 0
  · rw [hp, piR_zero, truthVal_eq_unitSet h]
    exact ⟨pt, pt_mem_unitSet⟩
  · rw [piR_pos hp]
    let F : V → V := fun x => if hx : x ∈ˢ A then Classical.choose (h x hx) else x
    refine ⟨graph F A, graph_mem_piSet fun x hx => ?_⟩
    simp only [F, hx, dite_true]
    exact Classical.choose_spec (h x hx)

/-- A universe is inhabited: it holds the truth values. -/
theorem univ_nonempty (n : Nat) : ∃ y, y ∈ˢ (univ n : V) :=
  ⟨unitSet, mem_univ_of_mem_univZero (mem_univZero.mpr fun _ h => h)⟩

/-- A tower is inhabited. -/
theorem TowerEnds.nonempty : ∀ {k : Nat} {X : V} {n : Nat}, TowerEnds k X n → ∃ y, y ∈ˢ X
  | 0, _, n, h => by rw [show _ = _ from h]; exact univ_nonempty n
  | _ + 1, _, _, ⟨_, _, rfl, hB⟩ => piV_nonempty fun x hx => (hB x hx).nonempty

/-- A strict inhabited set is no truth value. -/
theorem not_mem_univZero_of {X : V} (hs : Strict X) (hn : ∃ y, y ∈ˢ X) : ¬ X ∈ˢ (univZero : V) := by
  intro h
  obtain ⟨y, hy⟩ := hn
  have := mem_unitSet_iff.mp (mem_univZero.mp h y hy)
  exact hs.2 (this ▸ hy)

/-- A path's value is strict. -/
theorem TowerPath.strict : ∀ {k : Nat} {X : V} {n : Nat}, TowerPath k X n → Strict X
  | _, _, n, .zero => strict_univ n
  | _, _, _, .succ (A := A) (B := B) (a := a) hB ha hp => by
    have hs := hp.strict
    have hne : ¬ B a ∈ˢ (univZero : V) :=
      not_mem_univZero_of hs (TowerEnds.nonempty (hB a ha))
    rw [piV_eq_pos (v := 1) (by decide) ha hne, piR_pos (by decide)]
    exact strict_piSet

/-- A function space that is strict and inhabited is its graphs. -/
theorem piV_eq_piSet_of {A : V} {B : V → V} (hs : Strict (piV A B)) (hn : ∃ y, y ∈ˢ piV A B) :
    piV A B = piSet A B := by
  unfold piV at hs hn ⊢
  by_cases hp : propN A B = 0
  · exfalso
    rw [hp, piR_zero] at hs hn
    refine not_mem_univZero_of hs hn ?_
    exact mem_univZero.mpr fun z hz => by
      rw [mem_truthVal] at hz
      exact mem_unitSet_iff.mpr hz.2
  · rw [piR_pos hp]

/-- Two spaces of graphs, the one over inhabited fibres, have the one domain, and at
a point of it the one fibre. -/
theorem piSet_inj {A A' a : V} {B B' : V → V} (h : piSet A B = piSet A' B')
    (hB : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) (ha : a ∈ˢ A) : a ∈ˢ A' ∧ B a = B' a := by
  classical
  -- a function through a chosen value at `a`
  have thru : ∀ {C : V} {D : V → V}, (∀ x, x ∈ˢ C → ∃ y, y ∈ˢ D x) → ∀ {y : V},
      (a ∈ˢ C → y ∈ˢ D a) → a ∈ˢ C →
      ∃ f, f ∈ˢ piSet C D ∧ kpair a y ∈ˢ f := by
    intro C D hD y hy hc
    let F : V → V := fun x =>
      if x = a then y else if hx : x ∈ˢ C then Classical.choose (hD x hx) else x
    refine ⟨graph F C, graph_mem_piSet fun x hx => ?_, mem_graph.mpr ⟨a, hc, by simp [F]⟩⟩
    by_cases hxa : x = a
    · subst hxa; simp only [F, ite_true]; exact hy hc
    · simp only [F, hxa, hx, ite_false, dite_true]; exact Classical.choose_spec (hD x hx)
  obtain ⟨y₀, hy₀⟩ := hB a ha
  obtain ⟨f₀, hf₀, hp₀⟩ := thru hB (y := y₀) (fun _ => hy₀) ha
  -- the function lies in the other space too, whose fibres it inhabits
  have hB' : ∀ x, x ∈ˢ A' → ∃ y, y ∈ˢ B' x := by
    intro x hx
    obtain ⟨hsub, htot⟩ := mem_piSet.mp (h ▸ hf₀)
    obtain ⟨y, hy, -⟩ := htot x hx
    obtain ⟨x₂, -, y₂, hy₂, heq₂⟩ := mem_sigmaPairs.mp (hsub _ hy)
    obtain ⟨rfl, rfl⟩ := kpair_inj heq₂
    exact ⟨_, hy₂⟩
  have hmem₀ := (mem_piSet.mp (h ▸ hf₀)).1 _ hp₀
  obtain ⟨x₁, hx₁, y₁, -, heq₁⟩ := mem_sigmaPairs.mp hmem₀
  obtain ⟨rfl, -⟩ := kpair_inj heq₁
  refine ⟨hx₁, ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · obtain ⟨f, hf, hp⟩ := thru hB (y := y) (fun _ => hy) ha
    obtain ⟨x₂, -, y₂, hy₂, heq₂⟩ := mem_sigmaPairs.mp ((mem_piSet.mp (h ▸ hf)).1 _ hp)
    obtain ⟨rfl, rfl⟩ := kpair_inj heq₂
    exact hy₂
  · obtain ⟨f, hf, hp⟩ := thru hB' (y := y) (fun _ => hy) hx₁
    obtain ⟨x₂, -, y₂, hy₂, heq₂⟩ := mem_sigmaPairs.mp ((mem_piSet.mp (h.symm ▸ hf)).1 _ hp)
    obtain ⟨rfl, rfl⟩ := kpair_inj heq₂
    exact hy₂

/-- **A path and a walked tower of one value end in one universe.** -/
theorem TowerPath.univ_eq : ∀ {k : Nat} {X : V} {n m : Nat},
    TowerPath k X n → TowerEndsPt k X m → (univ n : V) = univ m
  | _, _, n, _, .zero, h => h.resolve_left (strict_univ n).1
  | _, _, _, _, .succ (A := A) (B := B) (a := a) hB ha hp, h => by
    have hstrict : Strict (piV A B) :=
      TowerPath.strict (.succ hB ha hp)
    obtain ⟨A', B', heq, hB'⟩ := h.resolve_left hstrict.1
    have hn : ∃ y, y ∈ˢ piV A B := piV_nonempty fun x hx => (hB x hx).nonempty
    have h₁ := piV_eq_piSet_of hstrict hn
    have h₂ := piV_eq_piSet_of (heq ▸ hstrict) (heq ▸ hn)
    have hs : piSet A B = piSet A' B' := by rw [← h₁, ← h₂, heq]
    obtain ⟨ha', hf⟩ := piSet_inj hs (fun x hx => (hB x hx).nonempty) ha
    exact hp.univ_eq (hf ▸ hB' a ha')

/-- A universe above `0` is not the truth values'. -/
theorem univ_ne_zero {n : Nat} (hn : n ≠ 0) : (univ n : V) ≠ univ 0 := by
  intro h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hm : (univZero : V) ∈ˢ (univ (m + 1) : V) :=
    mem_univ_of_tg_strict (univZero_mem_tg_succ m) (univ_zero (V := V) ▸ strict_univ 0)
  rw [show (univ (m + 1) : V) = univ 0 from h, univ_zero] at hm
  exact not_mem_self _ hm

/-- A path and a walked tower of one value: above `0` on one side is above `0` on
the other. -/
theorem TowerPath.ne_zero {k : Nat} {X : V} {n m : Nat} (hp : TowerPath k X n)
    (ht : TowerEndsPt k X m) (hm : m ≠ 0) : n ≠ 0 := by
  rintro rfl
  exact univ_ne_zero hm (hp.univ_eq ht).symm

/-- A path and a walked tower of one value: `0` on the path is `0` on the tower. -/
theorem TowerPath.eq_zero {k : Nat} {X : V} {m : Nat} (hp : TowerPath k X 0)
    (ht : TowerEndsPt k X m) : m = 0 := by
  exact Classical.byContradiction fun hm => hp.ne_zero ht hm rfl

end ConLeche.SetModel
