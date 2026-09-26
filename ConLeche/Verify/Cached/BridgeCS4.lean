module

public import ConLeche.Verify.Cached.BridgeCS3
public import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.Extend.Recs
import ConLeche.Kernel.Checker
import ConLeche.Verify.Abstract
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst

public section

/-!
# Cached shared-state checker: the per-declaration composition

Port of `ConLeche/Verify/BridgeS4.lean` for the cached tier.  Composes
the single-environment walks (`ConLeche/Verify/Cached/BridgeCS*.lean`)
along the thin phase drivers of `ConLeche/Cached/CheckerC.lean` into the
per-declaration bridge: a successful `checkDeclSF` run over a
well-formed environment is reproduced by the pure fueled checker.

The environment changes between phases; the state fact threaded across
a transition is the environment-free residue `CSOKF` — each phase
starts with `flushC`, which re-establishes `CSOK` for the phase's
environment (`flushC_csok`).  The `EnvWF` facts for the intermediate
environments are derived from the pure runs exactly as the interned
original does (the small `ConstWF` derivations are replicated here; the
heavy machinery — inversions, `ProvFacts`, `RulesChain` — is the same
public kit, and is `Expr`-level).

Against `BridgeS4` the systematic deletions of the tier carry through:
there is no arena, hence no `Ext` conjunct in any run-level statement,
no `tierOffE` transport and no tier-flag side condition; `ISOKF`
becomes `CSOKF`, whose `residue` needs no flag witness.  Every pure
comparand — the `(fueledOpsM mode)` runs, the `_datF` conversions, the
`EnvWF` conclusions — is byte-identical to the interned original's.
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## Run-level toolkit -/

/-- Dissect a successful `CheckCM` bind. -/
theorem bindC_ok {α β : Type} {x : CheckCM α} {k : α → CheckCM β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok pr =>
    obtain ⟨a, s₁⟩ := pr
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

theorem pureC_ok {α : Type} {a : α} {s₀ : CState} {v : α} {s' : CState}
    (h : (pure a : CheckCM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h

/-- Upgrade a fueled run (subject inferred from the hypothesis). -/
theorem FueledM.up {α : Type} {x : FueledM α} {F F' : Nat} {v : α}
    (hle : F ≤ F') (h : x.val F = .ok v) : x.val F' = .ok v :=
  x.property hle h

/-! ## `ConstWF` derivations (replicated from `BridgeWF`'s private
helpers, over the public inversions) -/

/-! ## The member fold -/

/-! ## The recursor group -/

/-- A `CheckCM` throw composed with anything never succeeds. -/
theorem throwC_bind_ok {α β : Type} {e : CheckError} {k : α → CheckCM β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : ((throw e : CheckCM α) >>= k) s₀ = .ok (v, s')) : False := by
  exact nomatch h

/-! ## The projection phases -/

end ConLeche.Cached
