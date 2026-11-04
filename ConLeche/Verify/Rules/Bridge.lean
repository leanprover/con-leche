module

public import ConLeche.Verify.Rules.Defs
import ConLeche.Verify.Rules.RedBridge
import ConLeche.Verify.Rules.DefEqBridge
import ConLeche.Verify.Rules.InferBridge

public section

/-!
# The bridge, closed (task #305)

The five bridges at every fuel: one mutual fuel induction, the shape
of `checkSoundAtP5`'s (`Model/Rules/Recompose.lean`), with the zero cases
from `Defs` and the step from the three lane files.  The step's
λ-congruence and η arms wait for the checker's body-type runs (task #342
S4, L-ck; the S4 ledger).
-/

namespace ConLeche.Rules

variable {env : Env}

/-- **The bridge**: an accepting run of any of the five entry points
of a pure knot that runs the verified checks, on or off the eager
tower (task #353), at any fuel, yields a derivation.  The induction is
over both flags at once: the full-grade application rule compares an
`eagerReduce _ _` argument at `eager := true`. -/
theorem bridgeAt (env : Env) :
    ∀ (fuel : Nat) (eager : Bool),
      WhnfCoreBridge .verified eager env fuel ∧ WhnfBridge .verified eager env fuel ∧
        DefEqBridge .verified eager env fuel ∧ InferBridge .verified eager env fuel ∧
          InferIOBridge .verified eager env fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro _
    exact ⟨whnfCore_bridge_zero, whnf_bridge_zero, defeq_bridge_zero,
      infer_bridge_zero, inferIO_bridge_zero⟩
  | succ fuel ih =>
    intro eager
    obtain ⟨hwc, hw, hd, hi, hio⟩ := ih eager
    have hdE : DefEqBridge .verified true env fuel := (ih true).2.2.1
    exact ⟨whnfCore_bridge_succ hwc hw hd hi hio, whnf_bridge_succ hwc hw,
      defeq_bridge_succ hwc hw hd hi hio, infer_bridge_succ hw hd hdE hi,
      inferIO_bridge_succ hw hio⟩

/-- The bridge at the `--verified` mode. -/
theorem bridge (env : Env) (fuel : Nat) :
    WhnfCoreBridge .verified false env fuel ∧ WhnfBridge .verified false env fuel ∧
      DefEqBridge .verified false env fuel ∧ InferBridge .verified false env fuel ∧
        InferIOBridge .verified false env fuel :=
  bridgeAt env fuel false

theorem whnfCore_bridge {fuel d : Nat} {e e' : Expr}
    (h : whnfCore .verified false env fuel d e = .ok e') : Red env d e e' :=
  (bridge env fuel).1 h

theorem whnf_bridge {fuel d : Nat} {e e' : Expr}
    (h : whnf .verified false env fuel d e = .ok e') : Red env d e e' :=
  (bridge env fuel).2.1 h

theorem isDefEqCore_bridge {fuel d : Nat} {a b : Expr}
    (h : isDefEqCore .verified false env fuel d a b = .ok true) : DefEq env d a b :=
  (bridge env fuel).2.2.1 h

theorem inferTypeCore_bridge {fuel d : Nat} {e t : Expr}
    (h : inferTypeCore .verified false env fuel d e = .ok t) : Infer env .full d e t :=
  (bridge env fuel).2.2.2.1 h

theorem inferTypeCoreIO_bridge {fuel d : Nat} {e t : Expr}
    (h : inferTypeCoreIO .verified false env fuel d e = .ok t) : Infer env .io d e t :=
  (bridge env fuel).2.2.2.2 h

end ConLeche.Rules
