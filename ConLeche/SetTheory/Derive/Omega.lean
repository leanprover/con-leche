module

public import ConLeche.SetTheory.Derive.Universe

@[expose] public section

/-!
# Infinity, derived: the finite ordinals

Infinity is derived from the universe chain + first-order replacement:
an *inhabited* Grothendieck universe is an inductive *set* — it
contains `∅` and is closed under the von Neumann successor
`n ↦ n ∪ {n}` (von Neumann 1923) by the pairing/union closures — so
`ω` can be separated out of one as the members of *every* inductive set
(a first-order definable property).  Leastness is then definitional.
The inductive universe used is `univChain 1`: it is inhabited by
`univChain 0` (`empty` satisfies `IsGrothendieck` vacuously).

Because the axiomatization is strictly first-order, we do **not** assert
that every member of `ω` is a meta-level `vnat k` (`mem_omega_iff` is
absent); instead we expose internal induction `omega_ind` and the
first-order ordinal laws (`omega_transitive`, `omega_cases`,
`vsucc_inj`, `vsucc_mem_vsucc_of_mem_omega`, …) used by internal
Dedekind recursion in `Derive/Natrec.lean`.

`vnat : Nat → V` still names the standard finite ordinals from the
meta-level (`vnat_mem_omega`, `vnat_mem_vnat_of_lt`, `vnat_inj`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The von Neumann successor `n ∪ {n}`. -/
noncomputable def vsucc (n : V) : V := binUnion n (sing n)

theorem mem_vsucc {z n : V} : z ∈ˢ vsucc n ↔ z ∈ˢ n ∨ z = n := by
  rw [vsucc, mem_binUnion, mem_sing]

theorem self_mem_vsucc (n : V) : n ∈ˢ vsucc n := mem_vsucc.mpr (Or.inr rfl)

theorem vsucc_ne_empty (n : V) : vsucc n ≠ empty :=
  ne_empty_of_mem (self_mem_vsucc n)

/-- The von Neumann successor is injective. -/
theorem vsucc_inj {m m' : V} (h : vsucc m = vsucc m') : m = m' := by
  have h1 : m ∈ˢ vsucc m' := h ▸ mem_vsucc.mpr (Or.inr rfl)
  have h2 : m' ∈ˢ vsucc m := h ▸ mem_vsucc.mpr (Or.inr rfl)
  rcases mem_vsucc.mp h1 with h1 | h1
  · rcases mem_vsucc.mp h2 with h2 | h2
    · exact (no_two_cycle h1 h2).elim
    · exact h2.symm
  · exact h1

theorem DefFun.vsucc_apply {k : Nat} {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => vsucc (A env) :=
  DefFun.binUnion_apply hA (DefFun.sing_apply hA)

/-- An inductive set: contains `∅`, closed under the successor. -/
def Inductive (I : V) : Prop :=
  (empty : V) ∈ˢ I ∧ ∀ n, n ∈ˢ I → vsucc n ∈ˢ I

/-- An inhabited Grothendieck universe is an inductive set. -/
theorem _root_.ConLeche.IsGrothendieck.inductive_self {U y : V}
    (hU : IsGrothendieck (Mem (V := V)) U) (hy : y ∈ˢ U) : Inductive U :=
  ⟨hU.empty_mem hy, fun _n hn =>
    hU.binUnion_mem hn (hU.sing_mem hn)⟩

theorem univChain_one_inductive : Inductive (univChain 1 : V) :=
  (univChain_grothendieck 1).inductive_self (univChain_mem 0)

theorem defPred_inductive : DefPred (Inductive (V := V)) := by
  unfold Inductive
  fo_def [DefFun.vsucc_apply]

theorem hasSep_omega :
    HasSep (univChain (V := V) 1) (fun n => ∀ I : V, Inductive I → n ∈ˢ I) := by
  apply hasSep_of_def
  unfold Inductive
  fo_def [DefFun.vsucc_apply]

/-- The finite ordinals: the members of every inductive set, separated
from the inductive universe `univChain 1`. -/
noncomputable def omega : V :=
  sep (univChain 1) (fun n => ∀ I : V, Inductive I → n ∈ˢ I) hasSep_omega

theorem mem_omega {n : V} : n ∈ˢ (omega : V) ↔ ∀ I : V, Inductive I → n ∈ˢ I := by
  rw [omega, mem_sep]
  exact ⟨fun h => h.2, fun h => ⟨h _ univChain_one_inductive, h⟩⟩

theorem omega_subset_inductive {I : V} (hI : Inductive I) : (omega : V) ⊆ˢ I :=
  fun _ hn => mem_omega.mp hn I hI

theorem omega_inductive : Inductive (omega : V) := by
  constructor
  · exact mem_omega.mpr fun I hI => hI.1
  · intro n hn
    exact mem_omega.mpr fun I hI => hI.2 n (mem_omega.mp hn I hI)

theorem empty_mem_omega : (empty : V) ∈ˢ omega := omega_inductive.1

theorem vsucc_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) : vsucc n ∈ˢ (omega : V) :=
  omega_inductive.2 n hn

theorem omega_subset_univChain_one : (omega : V) ⊆ˢ univChain 1 := by
  rw [omega]; exact sep_subset

/-- `ω` is a member of any universe having the inductive universe
`univChain 1` as a member. -/
theorem _root_.ConLeche.IsGrothendieck.omega_mem {U : V}
    (hU : IsGrothendieck (Mem (V := V)) U) (h1 : (univChain 1 : V) ∈ˢ U) :
    (omega : V) ∈ˢ U :=
  hU.mem_of_subset_mem h1 omega_subset_univChain_one

theorem DefFun.omega_const {k : Nat} : DefFun k fun _ => (SetTheory.omega (V := V)) :=
  DefFun.const _

attribute [irreducible] omega

/-! ### Internal induction and first-order ordinal laws on `ω` -/

/-- Set-theoretic induction on `ω` for any separable predicate. -/
theorem omega_ind {p : V → Prop} (hp : HasSep (omega : V) p)
    (h0 : p empty)
    (hs : ∀ n, n ∈ˢ (omega : V) → p n → p (vsucc n)) :
    ∀ n, n ∈ˢ (omega : V) → p n := by
  have hind : Inductive (sep (omega : V) p hp) := by
    constructor
    · exact mem_sep.mpr ⟨empty_mem_omega, h0⟩
    · intro m hm
      obtain ⟨hmo, hpm⟩ := mem_sep.mp hm
      exact mem_sep.mpr ⟨vsucc_mem_omega hmo, hs m hmo hpm⟩
  intro n hn
  exact (mem_sep.mp (omega_subset_inductive hind n hn)).2

/-- Induction on `ω` for any first-order definable predicate on `ω`. -/
theorem omega_ind_of_def {p : V → Prop} (hp : DefPredOn (omega : V) p)
    (h0 : p empty)
    (hs : ∀ n, n ∈ˢ (omega : V) → p n → p (vsucc n)) :
    ∀ n, n ∈ˢ (omega : V) → p n :=
  omega_ind (hasSep_of_def hp) h0 hs

/-- A transitive set: members of members are members. -/
def Transitive (x : V) : Prop := ∀ y z, y ∈ˢ x → z ∈ˢ y → z ∈ˢ x

/-- Every member of `ω` is a transitive set. -/
theorem omega_transitive {n : V} (hn : n ∈ˢ (omega : V)) : Transitive n := by
  refine omega_ind_of_def (p := Transitive) (by unfold Transitive; fo_def) ?_ ?_ n hn
  · intro y _ hy
    exact absurd hy (not_mem_empty y)
  · intro m _ ihm y z hy hz
    rcases mem_vsucc.mp hy with h | rfl
    · exact mem_vsucc.mpr (Or.inl (ihm y z h hz))
    · exact mem_vsucc.mpr (Or.inl hz)

/-- Every member of `ω` is either `∅` or a successor of a member of `ω`. -/
theorem omega_cases {n : V} (hn : n ∈ˢ (omega : V)) :
    n = empty ∨ ∃ m, m ∈ˢ (omega : V) ∧ n = vsucc m := by
  refine omega_ind_of_def
    (p := fun x => x = empty ∨ ∃ m, m ∈ˢ (omega : V) ∧ x = vsucc m)
    (by fo_def [DefFun.omega_const, DefFun.vsucc_apply]) (Or.inl rfl) ?_ n hn
  intro m hm _
  exact Or.inr ⟨m, hm, rfl⟩

/-- Every nonzero member of `ω` has `∅` as a member. -/
theorem empty_mem_omega_or_eq {n : V} (hn : n ∈ˢ (omega : V)) :
    n = empty ∨ (empty : V) ∈ˢ n := by
  refine omega_ind_of_def (p := fun x => x = empty ∨ (empty : V) ∈ˢ x)
    (by fo_def) (Or.inl rfl) ?_ n hn
  intro m _ ihm
  refine Or.inr ?_
  rcases ihm with rfl | h0
  · exact self_mem_vsucc empty
  · exact mem_vsucc.mpr (Or.inl h0)

theorem empty_mem_vsucc_of_mem_omega {n : V} (hn : n ∈ˢ (omega : V)) :
    (empty : V) ∈ˢ vsucc n := by
  rcases empty_mem_omega_or_eq hn with rfl | h0
  · exact self_mem_vsucc empty
  · exact mem_vsucc.mpr (Or.inl h0)

theorem vsucc_mem_vsucc_of_mem_omega {k n : V} (hn : n ∈ˢ (omega : V))
    (hk : k ∈ˢ n) : vsucc k ∈ˢ vsucc n := by
  have hall : ∀ k, k ∈ˢ n → vsucc k ∈ˢ vsucc n := by
    refine omega_ind_of_def (p := fun x => ∀ k, k ∈ˢ x → vsucc k ∈ˢ vsucc x)
      (by fo_def [DefFun.vsucc_apply]) ?_ ?_ n hn
    · intro k hk'
      exact absurd hk' (not_mem_empty k)
    · intro m _ ihm k hk'
      rcases mem_vsucc.mp hk' with hkm | rfl
      · exact mem_vsucc.mpr (Or.inl (ihm k hkm))
      · exact self_mem_vsucc (vsucc k)
  exact hall k hk

theorem vsucc_mem_iff_of_mem_omega {k n : V} (hn : n ∈ˢ (omega : V)) :
    vsucc k ∈ˢ vsucc n ↔ k ∈ˢ n := by
  constructor
  · intro h
    rcases mem_vsucc.mp h with hkn | heq
    · exact omega_transitive hn (vsucc k) k hkn (self_mem_vsucc k)
    · rw [← heq]; exact self_mem_vsucc k
  · exact vsucc_mem_vsucc_of_mem_omega hn

theorem vsucc_mem_omega_iff {n : V} :
    vsucc n ∈ˢ (omega : V) ↔ n ∈ˢ (omega : V) := by
  constructor
  · intro h
    rcases omega_cases h with h0 | ⟨m, hm, heq⟩
    · exact absurd h0 (vsucc_ne_empty n)
    · rw [vsucc_inj heq]; exact hm
  · exact vsucc_mem_omega

theorem mem_omega_of_mem {m n : V} (hn : n ∈ˢ (omega : V)) (hm : m ∈ˢ n) :
    m ∈ˢ (omega : V) := by
  have hall : ∀ m, m ∈ˢ n → m ∈ˢ (omega : V) := by
    refine omega_ind_of_def (p := fun x => ∀ m, m ∈ˢ x → m ∈ˢ (omega : V))
      (by fo_def [DefFun.omega_const]) ?_ ?_ n hn
    · intro m hm'
      exact absurd hm' (not_mem_empty m)
    · intro k hk ih m hm'
      rcases mem_vsucc.mp hm' with hmk | rfl
      · exact ih m hmk
      · exact hk
  exact hall m hm

/-! ### Meta-level numerals `vnat` -/

/-- The `k`-th von Neumann natural. -/
noncomputable def vnat : Nat → V
  | 0 => empty
  | k + 1 => vsucc (vnat k)

theorem vnat_mem_omega : ∀ k, (vnat k : V) ∈ˢ omega
  | 0 => empty_mem_omega
  | k + 1 => vsucc_mem_omega (vnat_mem_omega k)

theorem vnat_mem_vnat_of_lt : ∀ {k l : Nat}, k < l → (vnat k : V) ∈ˢ vnat l := by
  intro k l hkl
  induction l with
  | zero => exact absurd hkl (Nat.not_lt_zero k)
  | succ l ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkl with h | rfl
    · exact mem_vsucc.mpr (Or.inl (ih h))
    · exact self_mem_vsucc _

theorem vnat_inj {k l : Nat} (h : (vnat k : V) = vnat l) : k = l := by
  rcases Nat.lt_trichotomy k l with hlt | heq | hgt
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hlt) (not_mem_self _)
  · exact heq
  · exact absurd (h ▸ vnat_mem_vnat_of_lt (V := V) hgt) (not_mem_self _)

end ConLeche.SetTheory
