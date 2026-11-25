module

public import ConLeche.SetTheory.Derive.TypeU
public import ConLeche.SetTheory.Derive.Choice

@[expose] public section

/-!
# `univ`: what `Sort n` means

The axiomatic chain `tg` (`Derive/Tg.lean`) is the stepping stones and
what size bounds read; a sort denotes the universe of types `tyU`
(`Derive/TypeU.lean`): the truth values at `0`, above the members of
`tg n` that are truth values or strict (task #342, ruling R2, stage S1).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## `univ` is the universe of types (task #342, ruling R2)

Every site below reads "what `Sort u` means" (type-former formation,
checked-term typing, basis-law installation) and is routed through
`univ`.  `univ n` is cumulative (`univ_mono`) and holds every truth
value (`mem_univ_of_mem_univZero`), but above `0` it is not a
Grothendieck universe: it is not transitive (`{pt}` is a member, `pt`
is not), and not closed under subsets, unions or pairing.  Those
closures are read at `tg` (`mem_tg_of_mem_univ` going down,
`mem_univ_of_tg_strict` coming back), or at the strict universe
`strictU` (the least fixed points' fibre space, `Derive/LfpFam.lean`). -/

/-- **What `Sort n` means**: the universe of types `tyU n`. -/
noncomputable def univ : Nat → V := tyU

theorem DefFun.univ_const {k : Nat} (n : Nat) :
    DefFun k fun _ => (univ n : V) :=
  DefFun.const (univ n)

theorem univ_zero : (univ 0 : V) = univZero := tyU_zero

theorem mem_tg_of_mem_univ {n : Nat} {T : V} (h : T ∈ˢ (univ n : V)) : T ∈ˢ tg n :=
  mem_tg_of_mem_tyU h

theorem IsTy_of_mem_univ {n : Nat} {T : V} (h : T ∈ˢ (univ n : V)) : IsTy T :=
  IsTy_of_mem_tyU h

theorem ne_pt_of_mem_univ {n : Nat} {T : V} (h : T ∈ˢ (univ n : V)) : T ≠ pt :=
  (IsTy_of_mem_univ h).ne_pt

/-- A member of `tg n` that is strict is a member of `univ n`. -/
theorem mem_univ_of_tg_strict {n : Nat} {T : V} (hT : T ∈ˢ tg n) (hs : Strict T) :
    T ∈ˢ (univ n : V) := mem_tyU_of_strict hT hs

/-- A truth value is a type of every sort. -/
theorem mem_univ_of_mem_univZero {n : Nat} {T : V} (hT : T ∈ˢ (univZero : V)) :
    T ∈ˢ (univ n : V) := mem_tyU_of_mem_univZero hT

/-- **Cumulativity.** -/
theorem univ_mono {m n : Nat} (h : m ≤ n) : (univ m : V) ⊆ˢ univ n := tyU_mono h

/-- The strict universe is inside the universe of types. -/
theorem strictU_subset_univ (n : Nat) : (strictU n : V) ⊆ˢ univ n := strictU_subset_tyU n

theorem mem_univ_of_mem_strictU {n : Nat} {T : V} (h : T ∈ˢ (strictU n : V)) :
    T ∈ˢ (univ n : V) := strictU_subset_univ n T h

/-- A strict member of `univ n` is a member of the strict universe. -/
theorem mem_strictU_of_mem_univ {n : Nat} {T : V} (h : T ∈ˢ (univ n : V)) (hs : Strict T) :
    T ∈ˢ (strictU n : V) := mem_strictU_of_strict h hs

/-- A member of `univ n` that is strict above `0` is a member of the
strict universe (at `0` the two agree). -/
theorem mem_strictU_of_univ {n : Nat} {T : V} (h : T ∈ˢ (univ n : V))
    (hs : n ≠ 0 → Strict T) : T ∈ˢ (strictU n : V) := by
  by_cases hn : n = 0
  · subst hn; rw [strictU_zero]; rw [univ_zero] at h; exact h
  · exact mem_strictU_of_mem_univ h (hs hn)

theorem strict_univ (n : Nat) : Strict (univ n : V) := strict_tyU n

/-- A universe is a type. -/
theorem IsTy_univ (n : Nat) : IsTy (univ n : V) := IsTy_of_strict (strict_univ n)

/-- The truth values are a type. -/
theorem IsTy_univZero : IsTy (univZero : V) := IsTy_of_strict strict_univZero

/-- `ω` is a type. -/
theorem IsTy_omega : IsTy (omega : V) := IsTy_of_strict strict_omega

/-- `∅` is a type. -/
theorem IsTy_empty : IsTy (empty : V) := IsTy_of_strict strict_empty

/-- An equation is a type (a truth value). -/
theorem IsTy_eqv (x y : V) : IsTy (eqv x y) := Or.inl (eqv_mem_univZero x y)

theorem univ_mem_univ (n : Nat) : (univ n : V) ∈ˢ univ (n + 1) := tyU_mem_tyU_succ n

theorem omega_mem_univ_succ (n : Nat) : (omega : V) ∈ˢ univ (n + 1) :=
  mem_univ_of_mem_strictU (omega_mem_strictU_succ n)

theorem empty_mem_univ (n : Nat) : (empty : V) ∈ˢ univ n :=
  mem_univ_of_mem_strictU (empty_mem_strictU n)

theorem unitSet_mem_univ (n : Nat) : (unitSet : V) ∈ˢ univ n :=
  mem_univ_of_mem_univZero (mem_univZero.mpr (Subset.refl _))

/-! ## Universe-level choice function -/

theorem hasSep_nonempty (u : V) : HasSep u (fun A => ∃ y, y ∈ˢ A) :=
  hasSep_of_defPred (DefRel.exists_curry (DefRel.mem_apply (DefFun.proj 0) (DefFun.proj 1)))

/-- A set-theoretic choice function on all nonempty members of `univ u`,
replacing the old non-first-order global selector `schoice`. -/
noncomputable def univChoiceFn (u : Nat) : V :=
  choiceFn (sep (univ u) (fun A => ∃ y, y ∈ˢ A) (hasSep_nonempty (univ u)))
    (fun _ hA => (mem_sep.mp hA).2)

theorem app_univChoiceFn_mem {u : Nat} {A : V} (hA : A ∈ˢ (univ u : V))
    (hne : ∃ y, y ∈ˢ A) : app (univChoiceFn u) A ∈ˢ A := by
  unfold univChoiceFn
  exact app_choiceFn_mem _ (mem_sep.mpr ⟨hA, hne⟩)

theorem DefFun.univChoiceFn_const {k : Nat} (u : Nat) :
    DefFun k fun _ => (univChoiceFn u : V) :=
  DefFun.const (univChoiceFn u)

attribute [irreducible] univChoiceFn

end ConLeche.SetTheory
