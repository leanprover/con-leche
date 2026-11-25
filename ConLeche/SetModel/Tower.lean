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
  | k + 1, X, n =>
    ∃ (A : V) (B : V → V) (h : HasSigmaPairs A B),
      X = piV A B h ∧ ∀ a, a ∈ˢ A → TowerEnds k (B a) n

/-- What a walk knows: `k` function spaces over `univ n`, unless a stage is the
point. -/
def TowerEndsPt : Nat → V → Nat → Prop
  | 0, X, n => X = pt ∨ X = univ n
  | k + 1, X, n => X = pt ∨
    ∃ (A : V) (B : V → V) (h : HasSigmaPairs A B),
      X = piV A B h ∧ ∀ a, a ∈ˢ A → TowerEndsPt k (B a) n

/-- A tower with one chain of arguments. -/
inductive TowerPath : Nat → V → Nat → Prop where
  | zero {n : Nat} : TowerPath 0 (univ n) n
  | succ {k n : Nat} {A a : V} {B : V → V} {h : HasSigmaPairs A B} :
      (∀ x, x ∈ˢ A → TowerEnds k (B x) n) → a ∈ˢ A → TowerPath k (B a) n →
      TowerPath (k + 1) (piV A B h) n

/-- A function space over inhabited fibres is inhabited (using internal
set-theoretic choice `piSet_choose`). -/
theorem piV_nonempty {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (h : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) :
    ∃ f, f ∈ˢ piV A B hS := by
  unfold piV
  by_cases hp : propN A B = 0
  · rw [hp, piR_zero, truthVal_eq_unitSet h]
    exact ⟨pt, pt_mem_unitSet⟩
  · rw [piR_pos hp]
    exact piSet_choose hS h

/-- A universe is inhabited: it holds the truth values. -/
theorem univ_nonempty (n : Nat) : ∃ y, y ∈ˢ (univ n : V) :=
  ⟨unitSet, mem_univ_of_mem_univZero (mem_univZero.mpr fun _ h => h)⟩

/-- A tower is inhabited. -/
theorem TowerEnds.nonempty : ∀ {k : Nat} {X : V} {n : Nat}, TowerEnds k X n → ∃ y, y ∈ˢ X
  | 0, _, n, h => by rw [show _ = _ from h]; exact univ_nonempty n
  | _ + 1, _, _, ⟨_, _, _, rfl, hB⟩ => piV_nonempty fun x hx => (hB x hx).nonempty

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
theorem piV_eq_piSet_of {A : V} {B : V → V} {hS : HasSigmaPairs A B}
    (hs : Strict (piV A B hS)) (hn : ∃ y, y ∈ˢ piV A B hS) :
    piV A B hS = piSet A B hS := by
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
a point of it the one fibre (choice-free via `piSet_choose` and one-point
graph modification). -/
theorem piSet_inj {A A' a : V} {B B' : V → V}
    {hS : HasSigmaPairs A B} {hS' : HasSigmaPairs A' B'}
    (h : piSet A B hS = piSet A' B' hS')
    (hB : ∀ x, x ∈ˢ A → ∃ y, y ∈ˢ B x) (ha : a ∈ˢ A) : a ∈ˢ A' ∧ B a = B' a := by
  -- modify a base function `f₀` at the single point `a` to output `y`
  have thru : ∀ {C : V} {D : V → V} {hSC : HasSigmaPairs C D} {f₀ : V},
      f₀ ∈ˢ piSet C D hSC → a ∈ˢ C → ∀ {y : V}, y ∈ˢ D a →
      ∃ f, f ∈ˢ piSet C D hSC ∧ kpair a y ∈ˢ f := by
    intro C D hSC f₀ hf₀ haC y hy
    have hsep : HasSep f₀ (fun p => ¬ ∃ y', p = kpair a y') :=
      hasSep_of_defPred
        (DefRel.not (DefRel.exists_curry
          (DefRel.eq_apply (DefFun.proj 1) (DefFun.kpair_apply (DefFun.const a) (DefFun.proj 0)))))
    let f := binUnion (sep f₀ (fun p => ¬ ∃ y', p = kpair a y') hsep) (sing (kpair a y))
    refine ⟨f, mem_piSet.mpr ⟨?_, ?_⟩, mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))⟩
    · intro p hp
      rcases mem_binUnion.mp hp with hp1 | hp2
      · exact (mem_piSet.mp hf₀).1 p (mem_sep.mp hp1).1
      · rw [mem_sing.mp hp2]
        exact mem_sigmaPairs.mpr ⟨a, haC, y, hy, rfl⟩
    · intro x hx
      by_cases hxa : x = a
      · subst hxa
        refine ⟨y, mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl)), fun y'' hy'' => ?_⟩
        rcases mem_binUnion.mp hy'' with hp1 | hp2
        · exact False.elim ((mem_sep.mp hp1).2 ⟨y'', rfl⟩)
        · exact (kpair_inj (mem_sing.mp hp2)).2
      · obtain ⟨yx, hyx, huniq⟩ := (mem_piSet.mp hf₀).2 x hx
        have hkeep : kpair x yx ∈ˢ sep f₀ (fun p => ¬ ∃ y', p = kpair a y') hsep := by
          refine mem_sep.mpr ⟨hyx, fun ⟨y', heq⟩ => ?_⟩
          exact hxa (kpair_inj heq).1
        refine ⟨yx, mem_binUnion.mpr (Or.inl hkeep), fun y'' hy'' => ?_⟩
        rcases mem_binUnion.mp hy'' with hp1 | hp2
        · exact huniq y'' (mem_sep.mp hp1).1
        · exact False.elim (hxa (kpair_inj (mem_sing.mp hp2)).1)
  obtain ⟨f₀, hf₀⟩ := piSet_choose hS hB
  obtain ⟨y₀, hp₀, -⟩ := (mem_piSet.mp hf₀).2 a ha
  have hmem₀ := (mem_piSet.mp (h ▸ hf₀)).1 _ hp₀
  obtain ⟨x₁, hx₁, y₁, -, heq₁⟩ := mem_sigmaPairs.mp hmem₀
  obtain ⟨rfl, -⟩ := kpair_inj heq₁
  refine ⟨hx₁, ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · obtain ⟨f, hf, hp⟩ := thru hf₀ ha hy
    obtain ⟨x₂, -, y₂, hy₂, heq₂⟩ := mem_sigmaPairs.mp ((mem_piSet.mp (h ▸ hf)).1 _ hp)
    obtain ⟨rfl, rfl⟩ := kpair_inj heq₂
    exact hy₂
  · obtain ⟨f, hf, hp⟩ := thru (h ▸ hf₀) hx₁ hy
    obtain ⟨x₂, -, y₂, hy₂, heq₂⟩ := mem_sigmaPairs.mp ((mem_piSet.mp (h.symm ▸ hf)).1 _ hp)
    obtain ⟨rfl, rfl⟩ := kpair_inj heq₂
    exact hy₂

/-- **A path and a walked tower of one value end in one universe.** -/
theorem TowerPath.univ_eq : ∀ {k : Nat} {X : V} {n m : Nat},
    TowerPath k X n → TowerEndsPt k X m → (univ n : V) = univ m
  | _, _, n, _, .zero, h => h.resolve_left (strict_univ n).1
  | _, _, _, _, .succ (A := A) (B := B) (a := a) (h := hS) hB ha hp, h => by
    have hstrict : Strict (piV A B hS) :=
      TowerPath.strict (.succ hB ha hp)
    obtain ⟨A', B', hS', heq, hB'⟩ := h.resolve_left hstrict.1
    have hn : ∃ y, y ∈ˢ piV A B hS := piV_nonempty fun x hx => (hB x hx).nonempty
    have h₁ := piV_eq_piSet_of hstrict hn
    have h₂ := piV_eq_piSet_of (heq ▸ hstrict) (heq ▸ hn)
    have hs : piSet A B hS = piSet A' B' hS' := by rw [← h₁, ← h₂, heq]
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
