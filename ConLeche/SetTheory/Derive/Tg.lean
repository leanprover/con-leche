module

public import ConLeche.SetTheory.Derive.Pt
public import ConLeche.SetTheory.Derive.Omega

@[expose] public section

/-!
# The universe tower

`tg 0` is the set of truth values (`univZero`, the `U₀` of Mario
Carneiro, *The Type Theory of Lean*, master's thesis, Carnegie Mellon
University, 2019);
`tg (n+1)` is the chain universe `univChain (n+2)`.  The tower
starts two levels up the chain so that every positive level has the
inductive set `univChain 1` as a member — which is what puts `ω`
inside every positive level (a bare universe need not contain `ω`;
`V_ω` is one — and `univChain 0` need not be inhabited, the empty set
satisfying `IsGrothendieck` vacuously, so `univChain 1` is the first chain
member known to be inductive).  `tg 0 ∈ tg 1` because `univZero`
is built from `∅` by pairing/power closure inside the inhabited
universe `univChain 1 ∈ univChain 2`.  Cumulativity holds because
positive levels are transitive and each level is a member of the
next.

`tg` is the axiomatic Grothendieck chain — task #342's stepping
stones, named for Tarski–Grothendieck set theory (ruling R2, 2026-10-11).
`univ` (`Derive/Univ.lean`) is the universe of types `tyU`
(`Derive/TypeU.lean`: truth values at `0`, and above the members of
`tg n` that are truth values or strict); `tg` is what size bounds read.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The axiomatic chain interpreting `Sort n`, before task #342's
restriction (ruling R2) — the stepping stones `univ` is built from. -/
noncomputable def tg : Nat → V
  | 0 => univZero
  | n + 1 => univChain (n + 2)

theorem tg_zero : (tg 0 : V) = univZero := by rfl

/-- Positive levels are Grothendieck universes. -/
theorem tg_isGrothendieck {n : Nat} (hn : n ≠ 0) :
    IsGrothendieck (Mem (V := V)) (tg n) := by
  match n, hn with
  | m + 1, _ => exact univChain_grothendieck _

theorem univChain_one_mem_tg_succ (n : Nat) :
    (univChain 1 : V) ∈ˢ tg (n + 1) :=
  univChain_mem_of_lt (Nat.succ_lt_succ n.succ_pos)

theorem tg_mem_tg (n : Nat) : (tg n : V) ∈ˢ tg (n + 1) := by
  match n with
  | 0 =>
    exact (univChain_grothendieck 2).transitive (univChain_mem 1)
      ((univChain_grothendieck 1).univZero_mem (univChain_mem 0))
  | m + 1 => exact univChain_mem (m + 2)

theorem tg_subset_succ (n : Nat) : (tg n : V) ⊆ˢ tg (n + 1) :=
  (tg_isGrothendieck (Nat.succ_ne_zero n)).subset_of_mem (tg_mem_tg n)

theorem tg_mono {m n : Nat} (h : m ≤ n) : (tg m : V) ⊆ˢ tg n := by
  induction n with
  | zero => cases Nat.le_zero.mp h; exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (tg_subset_succ n)
    · exact Subset.refl _

theorem omega_mem_tg_succ (n : Nat) : (omega : V) ∈ˢ tg (n + 1) :=
  (tg_isGrothendieck (Nat.succ_ne_zero n)).omega_mem (univChain_one_mem_tg_succ n)

theorem omega_mem_tg_pos {n : Nat} (hn : n ≠ 0) : (omega : V) ∈ˢ tg n := by
  match n, hn with
  | m + 1, _ => exact omega_mem_tg_succ m

theorem empty_mem_tg : ∀ n : Nat, (empty : V) ∈ˢ tg n
  | 0 => mem_univZero.mpr (empty_subset _)
  | n + 1 =>
    (tg_isGrothendieck (Nat.succ_ne_zero n)).empty_mem (univChain_one_mem_tg_succ n)

theorem unitSet_mem_tg : ∀ n : Nat, (unitSet : V) ∈ˢ tg n
  | 0 => mem_univZero.mpr (Subset.refl _)
  | n + 1 =>
    (tg_isGrothendieck (Nat.succ_ne_zero n)).unitSet_mem (univChain_one_mem_tg_succ n)

theorem DefFun.tg_const {k : Nat} (n : Nat) :
    DefFun k fun _ => (SetTheory.tg (V := V) n) :=
  DefFun.const _

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] tg

end ConLeche.SetTheory
