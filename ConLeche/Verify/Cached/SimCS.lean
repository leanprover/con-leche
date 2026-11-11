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
entry points' triples (`opI_spec`, `opW_spec`, `opB_spec`,
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
plain `pure` and the `opI`/`opW` result relation stays on `Expr` and is
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
theorem opI_spec (henv : EnvWF env) {d : Nat}
    {e : Expr} (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opI .verified (mkFEnv env) d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  ((ssimC env henv checkFuel).infer hs rfl hw).triple relEC_inv

/-- Shared `whnf` simulates the fueled family. -/
theorem opW_spec (henv : EnvWF env) {d : Nat}
    {e : Expr} (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opW .verified (mkFEnv env) d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).whnf env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  ((ssimC env henv checkFuel).whnf hs rfl hw).triple relEC_inv

/-- Shared `isDefEq` simulates the fueled family. -/
theorem opB_spec (henv : EnvWF env) {d : Nat} {a b : Expr}
    (hs : CSOK .verified false env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ opB .verified (mkFEnv env) d a b
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).isDefEq env d a b) v; ⊤⦄ :=
  ((ssimC env henv checkFuel).defeq hs rfl rfl hwa hwb).tripleVC

/-- Shared `ensureSort` simulates the fueled family: the body walk's
answer at the fueled helper is the shared operation's (`ensureSort_def`). -/
theorem opS_spec (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ opS .verified (mkFEnv env) d e
    ⦃fun u s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).ensureSort env d e) u; ⊤⦄ :=
  triple_iff_run.mpr fun u s' hr => by
    obtain ⟨hs', F, h⟩ :=
      triple_iff_run.mp (ensureSortC_spec (ssimC env henv checkFuel) hs hw) u s' hr
    rw [ensureSort_atF, ensureSort_def] at h
    exact ⟨hs', F, h⟩

/-! The shared operations as triples at the `sharedOpsC` projections, the
form a walk calls them in (`vcgen` finds a spec by the program's head). -/

theorem inferS_spec (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).inferType env d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).inferType env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opI_spec henv hs hw

theorem whnfS_spec (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).whnf env d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).whnf env d e) v ∧
      Expr.WScoped d v; ⊤⦄ :=
  opW_spec henv hs hw

theorem defeqS_spec (henv : EnvWF env) {d : Nat}
    {a b : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).isDefEq env d a b
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).isDefEq env d a b) v; ⊤⦄ :=
  opB_spec henv hs hwa hwb

theorem sortS_spec (henv : EnvWF env) {d : Nat} {e : Expr}
    {s₀ : CState} (hs : CSOK .verified false env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).ensureSort env d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).ensureSort env d e) v; ⊤⦄ :=
  opS_spec henv hs hw

end Runners

end ConLeche.Cached
