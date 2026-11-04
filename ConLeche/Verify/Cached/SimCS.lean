module

public import ConLeche.Verify.Cached.KnotC
public import ConLeche.Verify.BridgeDecl
import ConLeche.Cached.CheckerC

public section

/-!
# Cached checker: the per-declaration faithfulness kit (task #163)

The cached core simulation (`CSOK`/`SimC`, `ConLeche/Verify/Cached/SimC.lean`, knotted in
`ConLeche/Verify/Cached/KnotC.lean`) is stated for *arbitrary* initial
states, so extending the cache lifetime from one entry call to one
declaration needs no new state invariant: this file provides the shared
entry points' triples (`opE_infer_spec`, `opE_whnf_spec`, `opB_spec`,
`opS_spec`) — a successful shared-state operation run from any `CSOK`
state preserves the invariant and answers what the pure fueled family
answers — and the same triples at the `sharedOpsC` projections a generic
checker function calls (`inferS_spec`, `whnfS_spec`, `defeqS_spec`,
`sortS_spec`: `vcgen` finds a spec by the program's head, and a triple
about `opB …` is not found for `(sharedOpsC …).isDefEq …`).

Two facts the kit relies on live elsewhere:

* `push_mkFEnv` (`ConLeche/Verify/CheckerF.lean`) is `Expr`-level — the
  index of a cons-extended environment is one insert, with no reference
  to any state representation;
* `flushC_csok` (`ConLeche/Verify/Cached/SimC.lean`): after a flush the
  state satisfies `CSOK` for *any* environment, which is what makes the
  driver-directed flush at environment transitions sound.

The runners pass their argument through, so a fabricated node is a
plain `pure` and the `opE` result relation stays on `Expr` and is
state-free.

The driver-level walks composing these are in
`ConLeche/Verify/Cached/BridgeCS*.lean`.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## Shared entry points simulate the fueled families -/

section Runners

variable {env : Env} {s₀ : CState}

/-- Shared `inferType` simulates the fueled family. -/
theorem opE_infer_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {e : Expr} (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opE mode (mkFEnv env) (·.infer) d e
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  ((ssimC hμ env henv checkFuel).infer hs rfl hw).triple relEC_inv

/-- Shared `whnf` simulates the fueled family. -/
theorem opE_whnf_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {e : Expr} (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opE mode (mkFEnv env) (·.whnf) d e
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).whnf env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  ((ssimC hμ env henv checkFuel).whnf hs rfl hw).triple relEC_inv

/-- Shared `isDefEq` simulates the fueled family. -/
theorem opB_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {a b : Expr}
    (hs : CSOK mode false env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ opB mode (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).isDefEq env d a b) v; ⊤⦄ :=
  ((ssimC hμ env henv checkFuel).defeq hs rfl rfl hwa hwb).tripleVC

/-- Shared `ensureSort` simulates the fueled family: the body walk's
answer at the fueled helper is the shared operation's (`ensureSort_def`). -/
theorem opS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opS mode (mkFEnv env) d e
    ⦃fun u s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).ensureSort env d e) u; ⊤⦄ :=
  triple_iff_run.mpr fun u s' hr => by
    obtain ⟨hs', F, h⟩ :=
      triple_iff_run.mp (ensureSortC_spec (ssimC hμ env henv checkFuel) hs hw) u s' hr
    rw [ensureSort_atF, ensureSort_def] at h
    exact ⟨hs', F, h⟩

/-! The shared operations as triples at the `sharedOpsC` projections, the
form a walk calls them in (`vcgen` finds a spec by the program's head). -/

theorem inferS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).inferType env d e
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opE_infer_spec hμ henv hs hw

theorem whnfS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).whnf env d e
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).whnf env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opE_whnf_spec hμ henv hs hw

theorem defeqS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {a b : Expr} {s₀ : CState} (hs : CSOK mode false env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).isDefEq env d a b
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).isDefEq env d a b) v; ⊤⦄ :=
  opB_spec hμ henv hs hwa hwb

theorem sortS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC mode (mkFEnv env)).ensureSort env d e
    ⦃fun v s' => CSOK mode false env s' ∧ Runs ((fueledOpsM mode).ensureSort env d e) v; ⊤⦄ :=
  opS_spec hμ henv hs hw

end Runners

end ConLeche.Cached
