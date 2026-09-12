module

public section

/-!
# Peeling `Except` binds

The one generic lemma the checker's do-block inversions share.  It
lived in `ConLeche/Verify/ProjPinInv.lean` until that module — the
pinned pair entries' install-time invariant — was retired with the
`PSigma'` pin (task #175 W6, 2026-09-05); relocated verbatim.
-/

namespace ConLeche

/-- Peel one `Except` bind.  Peeling rather than inlining the whole
do-block is what keeps these inversions cheap: `simp only [bind,
Except.bind]` materialises the entire nested block and `split`'s
internal `simp` then exceeds its step budget on the larger checkers. -/
theorem exceptBind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- An `Except` that is no error is an `ok`.  The main corollary's
`… matches .error _` splits into the two cases, and this is what the
second one hands the argument: the environment the chain would have
returned. -/
theorem Except.exists_ok {ε α : Type} {x : Except ε α} (h : ∀ e, x ≠ .error e) :
    ∃ a, x = .ok a := by
  cases x with
  | error e => exact absurd rfl (h e)
  | ok a => exact ⟨a, rfl⟩

end ConLeche
