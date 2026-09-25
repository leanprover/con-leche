module

public import ConLeche.Kernel.ExprOps

public section

/-!
# Bulk instantiation equals the `instantiate1` fold (task #50)

`Expr.instantiateList` substitutes a whole replacement list in one
traversal; these lemmas identify it **unconditionally** with the chains
of `instantiate1` the checker bodies fold over spines:

* `instantiateList_nil` / `instantiateList_cons` (in
  `ConLeche/Kernel/ExprOps.lean`, beside the definition: the
  `openPisAtFvars` `@[csimp]` in `ConLeche/Kernel/CheckerBase.lean`
  needs them) — the empty list is the identity; peeling the head is
  one `instantiate1` around the tail (the head is the substitution the
  fold applies *last*, at the outermost cursor `d`);
* `instantiateList_append_one` — peeling the last entry is one
  `instantiate1` *inside* (the substitution the fold applies *first*,
  at the innermost cursor `d + vs.length`);
* `instSpine_eq_instantiateList` — the telescope-context spine
  instantiation at descending cursors is bulk instantiation of the
  reversed spine.

With these, every claim about a folded call site transports to its
bulk form by rewriting — the Model/Verify layers keep seeing the fold.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Expr

/-- Bulk instantiation at or above the loose-bvar bound is the
identity (task #72's scope shortcut). -/
theorem instantiateList_eq_self {vs : List Expr} :
    ∀ {e : Expr} {d : Nat}, looseBVarsBounded d e = true →
      e.instantiateList vs d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d hb
    have h1 : i < d := by
      simpa [looseBVarsBounded] using hb
    simp [instantiateList, h1]
  | _ =>
    intro d hb <;>
    simp_all [looseBVarsBounded, instantiateList, Bool.and_eq_true]

theorem instantiateList_append_one :
    ∀ (vs : List Expr) (e v : Expr) (d : Nat),
      e.instantiateList (vs ++ [v]) d
        = (e.instantiate1 v (d + vs.length)).instantiateList vs d
  | [], e, v, d => by
    simp [instantiateList_cons, instantiateList_nil]
  | w :: ws, e, v, d => by
    rw [List.cons_append, instantiateList_cons,
      instantiateList_append_one ws e v (d + 1), ← instantiateList_cons]
    congr 2
    simp
    omega

theorem instSpine_eq_instantiateList :
    ∀ (as : List Expr) (t : Nat) (e : Expr), as.length = t + 1 →
      Expr.instSpine as t e = e.instantiateList as.reverse 0
  | a :: as, t, e, hlen => by
    rw [instSpine]
    cases t with
    | zero =>
      have : as = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst this
      simp [instSpine, instantiateList_cons, instantiateList_nil]
    | succ t' =>
      have hlen' : as.length = t' + 1 := by simpa using hlen
      rw [show t' + 1 - 1 = t' from rfl,
        instSpine_eq_instantiateList as t' _ hlen',
        List.reverse_cons, instantiateList_append_one]
      congr 2
      simp [hlen']

end ConLeche.Expr
