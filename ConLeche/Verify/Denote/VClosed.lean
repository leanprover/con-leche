module

public import ConLeche.Term.Subst

public section

/-!
# Closed `Term`s

`bvarsBelow n v` — `v` mentions no de Bruijn index `≥ n` — with the two
facts the bridge consumes: a term closed at the cut is invariant under
lifting and under instantiation *at that cut*.

## Why the bridge needs this and the set model does not

This is the exact mirror image of the saving recorded in
`ConLeche/Verify/Denote.lean`.  There, the free-variable valuation `ρ`
disappeared because the opened binder *is* a variable, so `denote`
needs no valuation parameter where `interpExpr` needs one.  Here we pay
for the same fact: `Term` has variables and `V` does not, so a
constant's denotation is a *term* that must be **closed**, and lifting
past it must be a no-op.  `interpExpr` needs no such condition because
`cval n ψ : V` is a set and there is nothing in it to lift.

So `EnvTT` carries a `cval_closed` field with no counterpart in
`EnvModel`, and it is not an accident: it is the syntactic shadow of
`EnvModel.val_params`' "a constant's value only reads its own level
parameters" — a constant's meaning does not depend on the local
context, which for a term means it has no loose variables.

The two lemmas below are structural inductions and nothing more; this
is not the beginning of a syntactic metatheory (cf.
`ConLeche/Term/DESIGN.md` §6), and like `ConLeche/TTVerify/Inversion.lean`
they live on the bridge side so that they stay marked as a bridge need.
-/

namespace ConLeche.Term
namespace Term

/-- `v` mentions no de Bruijn index `≥ n`. -/
@[expose] def bvarsBelow : Nat → Term → Prop
  | n, .bvar i => i < n
  | _, .sort _ => True
  | _, .const _ _ => True
  | n, .app f a => bvarsBelow n f ∧ bvarsBelow n a
  | n, .lam A b => bvarsBelow n A ∧ bvarsBelow (n + 1) b
  | n, .pi A B => bvarsBelow n A ∧ bvarsBelow (n + 1) B
  | n, .eqE a b => bvarsBelow n a ∧ bvarsBelow n b
  | n, .fst e => bvarsBelow n e
  | n, .snd e => bvarsBelow n e
  | _, .prf => True

/-- Under one binder: index `0` is bound and everything above shifts. -/
@[expose] def shiftP (P : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => P i

/-- **The positional twin of `bvarsBelow`** (task #315 L-E): every loose
de Bruijn index of `v` satisfies `P`.  `bvarsBelow n` is this at
`P := (· < n)`.

Why a predicate and not a bound: two environments that differ at
SCATTERED positions — a candidate parameter frame differs from the
recorded one exactly at the components that were replaced — are not
described by any prefix, so `bvarsBelow`'s shape cannot express the
agreement a congruence over them needs. -/
@[expose] def bvarsOn : (Nat → Prop) → Term → Prop
  | P, .bvar i => P i
  | _, .sort _ => True
  | _, .const _ _ => True
  | P, .app f a => bvarsOn P f ∧ bvarsOn P a
  | P, .lam A b => bvarsOn P A ∧ bvarsOn (shiftP P) b
  | P, .pi A B => bvarsOn P A ∧ bvarsOn (shiftP P) B
  | P, .eqE a b => bvarsOn P a ∧ bvarsOn P b
  | P, .fst e => bvarsOn P e
  | P, .snd e => bvarsOn P e
  | _, .prf => True

/-- Weakening the position predicate weakens the claim. -/
theorem bvarsOn_mono : ∀ {v : Term} {P Q : Nat → Prop}, (∀ i, P i → Q i) →
    bvarsOn P v → bvarsOn Q v := by
  intro v
  induction v with
  | bvar i => intro P Q h hv; exact h i hv
  | sort _ => intros; trivial
  | const _ _ => intros; trivial
  | app f a ihf iha => intro P Q h hv; exact ⟨ihf h hv.1, iha h hv.2⟩
  | lam A b ihA ihb =>
    intro P Q h hv
    refine ⟨ihA h hv.1, ihb ?_ hv.2⟩
    intro i hi
    cases i with
    | zero => trivial
    | succ i => exact h i hi
  | pi A B ihA ihB =>
    intro P Q h hv
    refine ⟨ihA h hv.1, ihB ?_ hv.2⟩
    intro i hi
    cases i with
    | zero => trivial
    | succ i => exact h i hi
  | eqE a b iha ihb => intro P Q h hv; exact ⟨iha h hv.1, ihb h hv.2⟩
  | fst e ihe => intro P Q h hv; exact ihe h hv
  | snd e ihe => intro P Q h hv; exact ihe h hv
  | prf => intros; trivial

/-- `bvarsBelow` is `bvarsOn` at a prefix predicate. -/
theorem bvarsOn_of_bvarsBelow : ∀ (v : Term) (n : Nat), bvarsBelow n v → bvarsOn (· < n) v := by
  intro v
  induction v with
  | bvar i => intro n h; exact h
  | sort _ => intros; trivial
  | const _ _ => intros; trivial
  | app f a ihf iha => intro n h; exact ⟨ihf n h.1, iha n h.2⟩
  | lam A b ihA ihb =>
    intro n h
    refine ⟨ihA n h.1, bvarsOn_mono ?_ (ihb (n + 1) h.2)⟩
    intro i hi
    cases i with
    | zero => trivial
    | succ i => exact Nat.lt_of_succ_lt_succ hi
  | pi A B ihA ihB =>
    intro n h
    refine ⟨ihA n h.1, bvarsOn_mono ?_ (ihB (n + 1) h.2)⟩
    intro i hi
    cases i with
    | zero => trivial
    | succ i => exact Nat.lt_of_succ_lt_succ hi
  | eqE a b iha ihb => intro n h; exact ⟨iha n h.1, ihb n h.2⟩
  | fst e ihe => intro n h; exact ihe n h
  | snd e ihe => intro n h; exact ihe n h
  | prf => intros; trivial

/-- Closed: no loose de Bruijn variables at all. -/
abbrev Closed (v : Term) : Prop := bvarsBelow 0 v

theorem bvarsBelow.mono : ∀ {v : Term} {m n : Nat}, m ≤ n →
    bvarsBelow m v → bvarsBelow n v := by
  intro v
  induction v with
  | bvar i => intro m n hmn h; exact Nat.lt_of_lt_of_le h hmn
  | sort u => intro _ _ _ _; trivial
  | const c us => intro _ _ _ _; trivial
  | prf => intro _ _ _ _; trivial
  | app f a ihf iha => intro m n hmn h; exact ⟨ihf hmn h.1, iha hmn h.2⟩
  | lam A b ihA ihb =>
    intro m n hmn h; exact ⟨ihA hmn h.1, ihb (Nat.succ_le_succ hmn) h.2⟩
  | pi A B ihA ihB =>
    intro m n hmn h; exact ⟨ihA hmn h.1, ihB (Nat.succ_le_succ hmn) h.2⟩
  | eqE a b iha ihb =>
    intro m n hmn h; exact ⟨iha hmn h.1, ihb hmn h.2⟩
  | fst e ihe => intro m n hmn h; exact ihe hmn h
  | snd e ihe => intro m n hmn h; exact ihe hmn h

/-- Lifting at a cut a term is already below is a no-op. -/
theorem liftN_eq_self : ∀ {v : Term} {k : Nat}, bvarsBelow k v →
    ∀ n : Nat, liftN n v k = v := by
  intro v
  induction v with
  | bvar i => intro k h n; have h' : i < k := h; simp [liftN, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k h n; rw [liftN_app, ihf h.1, iha h.2]
  | lam A b ihA ihb =>
    intro k h n; rw [liftN_lam, ihA h.1, ihb h.2]
  | pi A B ihA ihB =>
    intro k h n; rw [liftN_pi, ihA h.1, ihB h.2]
  | eqE a b iha ihb =>
    intro k h n; rw [liftN_eqE, iha h.1, ihb h.2]
  | fst e ihe => intro k h n; rw [liftN_fst, ihe h]
  | snd e ihe => intro k h n; rw [liftN_snd, ihe h]

/-- Instantiating at a cut a term is already below is a no-op. -/
theorem inst_eq_self : ∀ {v : Term} {k : Nat}, bvarsBelow k v →
    ∀ a : Term, inst v a k = v := by
  intro v
  induction v with
  | bvar i => intro k h a; have h' : i < k := h; simp [inst, h']
  | sort u => intro _ _ _; rfl
  | const c us => intro _ _ _; rfl
  | prf => intro _ _ _; rfl
  | app f b ihf ihb =>
    intro k h a; rw [inst_app, ihf h.1, ihb h.2]
  | lam A b ihA ihb =>
    intro k h a; rw [inst_lam, ihA h.1, ihb h.2]
  | pi A B ihA ihB =>
    intro k h a; rw [inst_pi, ihA h.1, ihB h.2]
  | eqE b c ihb ihc =>
    intro k h a; rw [inst_eqE, ihb h.1, ihc h.2]
  | fst e ihe => intro k h a; rw [inst_fst, ihe h]
  | snd e ihe => intro k h a; rw [inst_snd, ihe h]

/-- A closed term is invariant under lifting at any cut. -/
theorem liftN_eq_self_of_closed {v : Term} (h : Closed v) (n k : Nat) :
    liftN n v k = v :=
  liftN_eq_self (bvarsBelow.mono (Nat.zero_le k) h) n

/-- A closed term is invariant under instantiation at any cut. -/
theorem inst_eq_self_of_closed {v : Term} (h : Closed v) (a : Term)
    (k : Nat) : inst v a k = v :=
  inst_eq_self (bvarsBelow.mono (Nat.zero_le k) h) a

end Term
end ConLeche.Term
