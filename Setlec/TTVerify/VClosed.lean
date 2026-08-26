import Setlec.TT.Subst

/-!
# Closed `VExpr`s

`bvarsBelow n v` — `v` mentions no de Bruijn index `≥ n` — with the two
facts the bridge consumes: a term closed at the cut is invariant under
lifting and under instantiation *at that cut*.

## Why the bridge needs this and the set model does not

This is the exact mirror image of the saving recorded in
`Setlec/TTVerify/Denote.lean`.  There, the free-variable valuation `ρ`
disappeared because the opened binder *is* a variable, so `denote`
needs no valuation parameter where `interpExpr` needs one.  Here we pay
for the same fact: `VExpr` has variables and `V` does not, so a
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
`Setlec/TT/DESIGN.md` §6), and like `Setlec/TTVerify/Inversion.lean`
they live on the bridge side so that they stay marked as a bridge need.
-/

namespace Setlec.TT
namespace VExpr

/-- `v` mentions no de Bruijn index `≥ n`. -/
def bvarsBelow : Nat → VExpr → Prop
  | n, .bvar i => i < n
  | _, .sort _ => True
  | _, .const _ _ => True
  | n, .app f a => bvarsBelow n f ∧ bvarsBelow n a
  | n, .lam A b => bvarsBelow n A ∧ bvarsBelow (n + 1) b
  | n, .pi A B => bvarsBelow n A ∧ bvarsBelow (n + 1) B
  | n, .letE T v b => bvarsBelow n T ∧ bvarsBelow n v ∧ bvarsBelow (n + 1) b
  | n, .eqE T a b => bvarsBelow n T ∧ bvarsBelow n a ∧ bvarsBelow n b
  | n, .proj _ e => bvarsBelow n e
  | _, .prf => True

/-- Closed: no loose de Bruijn variables at all. -/
abbrev Closed (v : VExpr) : Prop := bvarsBelow 0 v

theorem bvarsBelow.mono : ∀ {v : VExpr} {m n : Nat}, m ≤ n →
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
  | letE T v b ihT ihv ihb =>
    intro m n hmn h
    exact ⟨ihT hmn h.1, ihv hmn h.2.1, ihb (Nat.succ_le_succ hmn) h.2.2⟩
  | eqE T a b ihT iha ihb =>
    intro m n hmn h; exact ⟨ihT hmn h.1, iha hmn h.2.1, ihb hmn h.2.2⟩
  | proj i e ihe => intro m n hmn h; exact ihe hmn h

/-- Lifting at a cut a term is already below is a no-op. -/
theorem liftN_eq_self : ∀ {v : VExpr} {k : Nat}, bvarsBelow k v →
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
  | letE T v b ihT ihv ihb =>
    intro k h n; rw [liftN_letE, ihT h.1, ihv h.2.1, ihb h.2.2]
  | eqE T a b ihT iha ihb =>
    intro k h n; rw [liftN_eqE, ihT h.1, iha h.2.1, ihb h.2.2]
  | proj i e ihe => intro k h n; rw [liftN_proj, ihe h]

/-- Instantiating at a cut a term is already below is a no-op. -/
theorem inst_eq_self : ∀ {v : VExpr} {k : Nat}, bvarsBelow k v →
    ∀ a : VExpr, inst v a k = v := by
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
  | letE T v b ihT ihv ihb =>
    intro k h a; rw [inst_letE, ihT h.1, ihv h.2.1, ihb h.2.2]
  | eqE T b c ihT ihb ihc =>
    intro k h a; rw [inst_eqE, ihT h.1, ihb h.2.1, ihc h.2.2]
  | proj i e ihe => intro k h a; rw [inst_proj, ihe h]

/-- A closed term is invariant under lifting at any cut. -/
theorem liftN_eq_self_of_closed {v : VExpr} (h : Closed v) (n k : Nat) :
    liftN n v k = v :=
  liftN_eq_self (bvarsBelow.mono (Nat.zero_le k) h) n

/-- A closed term is invariant under instantiation at any cut. -/
theorem inst_eq_self_of_closed {v : VExpr} (h : Closed v) (a : VExpr)
    (k : Nat) : inst v a k = v :=
  inst_eq_self (bvarsBelow.mono (Nat.zero_le k) h) a

end VExpr
end Setlec.TT
