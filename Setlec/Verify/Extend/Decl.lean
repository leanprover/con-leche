import Setlec.Verify.Extend.Proj
import Setlec.Verify.Extend.Recs
import Setlec.Verify.Extend.Sibs

/-!
# Decl — the `V`-free half of `Setlec.Model.Extend.Decl`

The two list lemmas the block-install derivation runs on (the filter
fusion and the two-element split that identifies a single-constructor
block's non-recursor part), plus, by its imports, the whole `V`-free
tier of the declaration checker's inversions.

Relocated from `Setlec/Model/Extend/Decl.lean` (task #123);
`checkIndDecl_sound` stays there, being a statement about a valuation.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

theorem List.filter_filter_of_imp {α} {p q : α → Bool}
    (himp : ∀ a, q a = true → p a = true) :
    ∀ l : List α, (l.filter p).filter q = l.filter q
  | [] => rfl
  | a :: l => by
    cases hq : q a with
    | true =>
      have hp := himp a hq
      simp [List.filter_cons, hq, hp, List.filter_filter_of_imp himp l]
    | false =>
      cases hp : p a with
      | true =>
        simp [List.filter_cons, hq, hp,
          List.filter_filter_of_imp himp l]
      | false =>
        simp [List.filter_cons, hq, hp,
          List.filter_filter_of_imp himp l]

/-- A list of `p`-or-`q` elements (`p`, `q` disjoint) whose `p`-part
and `q`-part are singletons is one of the two two-element
arrangements. -/
theorem two_elem_split {α} {p q : α → Bool} {a b : α}
    (hd : ∀ x, ¬(p x = true ∧ q x = true)) :
    ∀ l : List α, (∀ x ∈ l, p x = true ∨ q x = true) →
    l.filter p = [a] → l.filter q = [b] →
    l = [a, b] ∨ l = [b, a]
  | [], _, hp, _ => by simp at hp
  | x :: xs, hall, hp, hq => by
    cases hpx : p x with
    | true =>
      have hqx : q x = false := by
        cases hqx : q x with
        | true => exact absurd ⟨hpx, hqx⟩ (hd x)
        | false => rfl
      rw [List.filter_cons, if_pos (by simp [hpx])] at hp
      obtain ⟨rfl, hpxs⟩ : x = a ∧ xs.filter p = [] := by
        have h1 := List.cons.inj hp
        exact ⟨h1.1, h1.2⟩
      rw [List.filter_cons, if_neg (by simp [hqx])] at hq
      have hallq : ∀ y ∈ xs, q y = true := by
        intro y hy
        rcases hall y (List.mem_cons_of_mem _ hy) with hpy | hqy
        · exfalso
          have hmem : y ∈ xs.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
          rw [hpxs] at hmem
          exact List.not_mem_nil hmem
        · exact hqy
      have hself : xs.filter q = xs := List.filter_eq_self.mpr (by
        intro y hy
        simp [hallq y hy])
      rw [hself] at hq
      subst hq
      exact Or.inl rfl
    | false =>
      have hqx : q x = true := by
        rcases hall x List.mem_cons_self with hpx' | hqx'
        · rw [hpx] at hpx'
          exact nomatch hpx'
        · exact hqx'
      rw [List.filter_cons, if_neg (by simp [hpx])] at hp
      rw [List.filter_cons, if_pos (by simp [hqx])] at hq
      obtain ⟨rfl, hqxs⟩ : x = b ∧ xs.filter q = [] := by
        have h1 := List.cons.inj hq
        exact ⟨h1.1, h1.2⟩
      have hallp : ∀ y ∈ xs, p y = true := by
        intro y hy
        rcases hall y (List.mem_cons_of_mem _ hy) with hpy | hqy
        · exact hpy
        · exfalso
          have hmem : y ∈ xs.filter q := List.mem_filter.mpr ⟨hy, hqy⟩
          rw [hqxs] at hmem
          exact List.not_mem_nil hmem
      have hself : xs.filter p = xs := List.filter_eq_self.mpr (by
        intro y hy
        simp [hallp y hy])
      rw [hself] at hp
      subst hp
      exact Or.inr rfl

end Setlec
