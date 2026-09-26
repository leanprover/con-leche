module

public import ConLeche.Kernel.Inductives.RecHome
import ConLeche.Verify.ExceptBind

public section

/-!
# The home closure, inverted (`Kernel/Inductives/RecHome.lean`)

What a successful run of the closure says, class by class: a reached
class was reached at the start (a member class, in the members' layout)
or by a leaf of an earlier reached, expanded class naming it
(`homeClosure_cases`), and its constructors are the recomputation at its
key (`homeClassNfs`).
-/

namespace ConLeche

variable {α β ε : Type}

/-- **`mapM` in `Except`, pointwise**: a successful run has one output per
input, each the function's output there. -/
theorem except_mapM_ok {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r →
      r.length = l.length ∧ ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, r[i]? = some b ∧ f a = .ok b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun i a h => by simp at h⟩
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; exact nomatch h
    | ok b =>
      rw [hx] at h
      cases hl : l.mapM f with
      | error e => simp only [hl] at h; exact nomatch h
      | ok rs =>
        simp only [hl] at h
        change Except.ok (b :: rs) = Except.ok r at h
        cases h
        obtain ⟨hlen, hall⟩ := except_mapM_ok hl
        refine ⟨by simp [hlen], fun i a hi => ?_⟩
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi; exact ⟨b, rfl, hx⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hi ⊢
          exact hall i a hi

/-- An output of a successful `mapM` is the function's output at an input. -/
theorem except_mapM_mem {f : α → Except ε β} {l : List α} {r : List β} (h : l.mapM f = .ok r)
    {b : β} (hb : b ∈ r) : ∃ a ∈ l, f a = .ok b := by
  obtain ⟨hlen, hall⟩ := except_mapM_ok h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨b', hb', hf⟩ := hall i l[i] (List.getElem?_eq_getElem (by omega))
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hb'
  exact ⟨l[i], List.getElem_mem _, hb' ▸ hf⟩

/-- A pointwise `mapM` over the indices, read at an index below. -/
theorem except_mapM_range {f : Nat → Except ε β} {n : Nat} {r : List β}
    (h : (List.range n).mapM f = .ok r) :
    r.length = n ∧ ∀ i, i < n → ∃ b, r[i]? = some b ∧ f i = .ok b := by
  obtain ⟨hlen, hall⟩ := except_mapM_ok h
  refine ⟨by simpa using hlen, fun i hi => ?_⟩
  exact hall i i (List.getElem?_range hi)

section Closure

variable {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx} {holes : List Expr}
  {Cs : List HomeClass}

/-- **One round, inverted**: a class reached after the round was reached
before it, or reached in it — reachable, a leaf of a reached expanded
class naming it, recomputed at the leaf's key. -/
theorem homeStep_cases {R R' : List (Option HomeReach)}
    (h : homeStep ops env ctx holes Cs R = .ok R') :
    R'.length = Cs.length ∧ ∀ c r, R'.getD c none = some r →
      R.getD c none = some r ∨
      (c < Cs.length ∧ R.getD c none = none ∧ homeReachable ctx (Cs.getD c default) = true ∧
        homeFind ctx Cs R (Cs.getD c default) = some r.key ∧
        homeClassNfs ops env ctx holes (Cs.getD c default) r.key = .ok r.nfs) := by
  obtain ⟨hlen, hall⟩ := except_mapM_range h
  refine ⟨hlen, fun c r hc => ?_⟩
  have hcl : c < Cs.length := by
    rcases Nat.lt_or_ge c Cs.length with h' | h'
    · exact h'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hc
      exact nomatch hc
  obtain ⟨b, hb, hf⟩ := hall c hcl
  rw [List.getD_eq_getElem?_getD, hb, Option.getD_some] at hc
  subst hc
  split at hf
  · rename_i r0 hr0
    simp only [pure, Except.pure, Except.ok.injEq] at hf
    exact Or.inl (by rw [hr0, hf])
  · rename_i hr0
    split at hf
    · rename_i hreach
      split at hf
      · rename_i key hkey
        cases hn : homeClassNfs ops env ctx holes (Cs.getD c default) key with
        | error e => rw [hn] at hf; exact nomatch hf
        | ok nfs =>
          rw [hn] at hf
          change Except.ok (some (⟨key, nfs⟩ : HomeReach)) = _ at hf
          cases hf
          exact Or.inr ⟨hcl, hr0, hreach, hkey, hn⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at hf; exact nomatch hf
    · simp only [pure, Except.pure, Except.ok.injEq] at hf; exact nomatch hf

/-- **The first leaf naming a class, found**: a reached expanded class
and one of its hole-carrying leaves naming it at the key. -/
theorem homeFind_some {R : List (Option HomeReach)} {C : HomeClass}
    {key : Option (List Expr)} (h : homeFind ctx Cs R C = some key) :
    ∃ a r, a < Cs.length ∧ R.getD a none = some r ∧ r.expands = true ∧
      ∃ e ∈ r.nfs, ∃ l, some l ∈ e.leaves ∧
        homeLeafKey ctx (Cs.getD a default) r.key C l = some key := by
  unfold homeFind at h
  obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some h
  have hal : a < Cs.length := List.mem_range.mp ha
  split at hfa
  · rename_i r hr
    split at hfa
    · rename_i hexp
      obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some hfa
      obtain ⟨l?, hl, hfl⟩ := List.exists_of_findSome?_eq_some hfe
      cases l? with
      | none => exact nomatch hfl
      | some l => exact ⟨a, r, hal, hr, hexp, e, he, l, hl, hfl⟩
    · exact nomatch hfa
  · exact nomatch hfa

/-- A class reached by the closure: at the start, or in a round. -/
@[expose] def HomeReached (ops : CheckerOps CheckM) (env : Env) (ctx : NestCtx)
    (holes : List Expr) (Cs : List HomeClass) (P : Nat → HomeReach → Prop) : Prop :=
  ∀ R : List (Option HomeReach), (∀ c r, R.getD c none = some r → P c r) →
    ∀ R', homeStep ops env ctx holes Cs R = .ok R' → ∀ c r, R'.getD c none = some r → P c r

/-- **The closure's invariant**: a property of reached classes that holds
at the start and survives every round holds of the closure. -/
theorem homeIter_inv {P : Nat → HomeReach → Prop} (hstep : HomeReached ops env ctx holes Cs P) :
    ∀ (fuel : Nat) (R R' : List (Option HomeReach)), (∀ c r, R.getD c none = some r → P c r) →
      homeIter ops env ctx holes Cs fuel R = .ok R' → ∀ c r, R'.getD c none = some r → P c r
  | 0, R, R', hR, h => by
    simp only [homeIter, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hR
  | fuel + 1, R, R', hR, h => by
    simp only [homeIter] at h
    cases hs : homeStep ops env ctx holes Cs R with
    | error e => rw [hs] at h; exact nomatch h
    | ok R₁ =>
      rw [hs] at h
      exact homeIter_inv hstep fuel R₁ R' (hstep R hR R₁ hs) h

/-- **The closure's start, inverted**: a class reached at the start is a
member class, recomputed in the members' layout. -/
theorem homeClosure_inv {P : Nat → HomeReach → Prop}
    (h0 : ∀ c nfs, c < Cs.length → (Cs.getD c default).member.isSome = true →
      homeClassNfs ops env ctx holes (Cs.getD c default) none = .ok nfs → P c ⟨none, nfs⟩)
    (hstep : HomeReached ops env ctx holes Cs P) {R : List (Option HomeReach)}
    (h : homeClosure ops env ctx holes Cs = .ok R) : ∀ c r, R.getD c none = some r → P c r := by
  unfold homeClosure at h
  obtain ⟨R0, h0', h⟩ := exceptBind_ok h
  refine homeIter_inv hstep _ R0 R ?_ h
  obtain ⟨hlen, hall⟩ := except_mapM_range h0'
  intro c r hc
  have hcl : c < Cs.length := by
    rcases Nat.lt_or_ge c Cs.length with h' | h'
    · exact h'
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hc
      exact nomatch hc
  obtain ⟨b, hb, hf⟩ := hall c hcl
  rw [List.getD_eq_getElem?_getD, hb, Option.getD_some] at hc
  subst hc
  split at hf
  · rename_i t hm
    cases hn : homeClassNfs ops env ctx holes (Cs.getD c default) none with
    | error e => rw [hn] at hf; exact nomatch hf
    | ok nfs =>
      rw [hn] at hf
      change Except.ok (some (⟨none, nfs⟩ : HomeReach)) = _ at hf
      cases hf
      exact h0 c nfs hcl (by rw [hm]; rfl) hn
  · simp only [pure, Except.pure, Except.ok.injEq] at hf; exact nomatch hf

end Closure

end ConLeche
