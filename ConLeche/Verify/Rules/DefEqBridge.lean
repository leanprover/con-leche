module

public import ConLeche.Verify.Rules.Certs

public section

/-!
# The definitional-equality bridge (task #305, lane B3)

`isDefEqCore` at `fuel + 1` from the five bridges at `fuel`: one
`defeqStep` under a bridged continuation is a derivation, the loop
follows by induction on its budget, the body is the loop at
`defeqLoopFuel`.

There is no `defeqStep_inv` in the tree (the model tier's
`defeqStep_claim`, `Model/Steps/DefEq.lean:514`, inverts the step
inline against its continuation contract `DefEqCont`); the lane writes
the inversion as that proof does it, one `exceptBind_ok` per bind, and
lands each exit on its rule:

| exit (`Core.lean`) | rule |
|---|---|
| `a == b` (`:2431`) | `DefEq.refl` |
| the `Bool.true` shortcut (`:2432-2433`) | `boolTrueShortcut_bridge` |
| `whnfCore` both, `a' == b'` (`:2434-2436`) | `DefEq.redBoth` + `refl` |
| `propIrrel` (`:2455-2457`) | `redBoth` + `propIrrel_bridge` |
| `reduceNat` left / right (`:2493-2497`) | `redBoth` + `redL (reduceNat_bridge)` / `redR` + continuation |
| lazy δ, one side / both (`:2510-2545`) | `redBoth` + `deltaL` / `deltaR` / `deltaBoth` + continuation |
| same-head short-circuit (`:2528-2533`) | `redBoth` + `defeqSpine_bridge` |
| sorts / literals / fvars / consts (`:2554-2594`) | `sort` / `lit` / `fvar` / `const`, else `stuckIrrel_bridge` |
| `lit` vs `Nat.zero` / `Nat.succ` (`:2559-2574`) | `natZero`(`R`) / `natSucc`(`R`) with the continuation |
| string literal vs `String.ofList` (`:2578-2585`) | `strLitL` / `strLitR` with the continuation |
| ∀ / λ congruence (`:2595-2619`) | `forallE` / `lam` |
| stuck applications (`:2620-2647`) | `spine` (head + `defEqList_bridge`), else `stuckIrrel_bridge` |
| stuck projections (`:2648-2657`) | `proj`, else `stuckIrrel_bridge` |
| one-sided λ (`:2659-2664`) | `etaCert_bridge` / `etaR`, else `stuckIrrel_bridge` |
| distinct heads (`:2668`) | `stuckIrrel_bridge` |

all under the `redBoth` of the two `whnfCore` reducts.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- One `defeqStep` under a bridged continuation. -/
theorem defeqStep_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} {k : Bool → Expr → Expr → CheckM Bool}
    (hk : ∀ {pi : Bool} {a b : Expr}, k pi a b = .ok true → DefEq env d a b)
    {pi : Bool} {a b : Expr}
    (h : defeqStep .verified (pureFns .verified env fuel) env d k pi a b = .ok true) :
    DefEq env d a b := by
  sorry

/-- The loop at every budget. -/
theorem defeqLoop_bridge (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel)
    {d : Nat} : ∀ (n : Nat) {pi : Bool} {a b : Expr},
      defeqLoop .verified (pureFns .verified env fuel) env d n pi a b = .ok true →
      DefEq env d a b
  | 0, _, _, _, h => by
    simp [defeqLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, _, _, _, h =>
    defeqStep_bridge hwc hw hd hio (defeqLoop_bridge hwc hw hd hio n) h

/-- **`isDefEqCore` at `fuel + 1`**: the loop at its budget. -/
theorem defeq_bridge_succ (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel) :
    DefEqBridge env (fuel + 1) := by
  intro d a b h
  rw [isDefEqCore_succ] at h
  exact defeqLoop_bridge hwc hw hd hio _ h

end ConLeche.Rules
