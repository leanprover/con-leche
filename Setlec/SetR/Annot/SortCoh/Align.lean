import Setlec.SetR.Annot.SortCoh.SubstSim

/-!
# The alignment engine (E4, R1-ratified): the map

The core-dichotomy statement per the ratified R1: aligning a
gate-free trace's endpoint against the ACTUAL (gated, deterministic)
run's result — `aligned ∨ DeadCore ∨ seam`, the seams carried as
evidence packs with progress markers (the `NatSplitOut` precedent)
for routed consumers with more facts.  Divergence taxonomy sealed in
DESIGN ("STOP-FINDING at E4"): gate refusals are dead-shaped and
refutable; K fires always agree; the residual seams are the iota
fire divergence (the eta field segment) and the nat-arg grind.

Budget note (the both-fuel-bounds axiom): the aligned disjuncts'
runs feed det-reads and universally-budgeted walk premises, never
measure slots — plain existentials, per the recorded justification.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

section Discharge
variable {μ : CheckMode} {env : Env}

/-- **Dead head-normal shapes** — the gate-refusal outputs.  Shape
only: as an app/proj head each kills the outer (`iotaRec` shape/
length refusals), and at a sort-demanding top the consumer's own
run plus these shapes force a non-sort exit (`loop_dead_exit` for
the non-const heads; `unfoldDefinition_none_of_recInfo` plus the
nat-guard disjointness for the recursor spines). -/
def DeadCore (env : Env) (W : Expr) : Prop :=
  (∃ n ty b m, W.getAppFn = Expr.lam n ty b m ∧
    W.getAppArgs ≠ []) ∨
  (∃ sn i e₀, W.getAppFn = Expr.proj sn i e₀) ∨
  (∃ c us cv mI rP rules, W.getAppFn = Expr.const c us ∧
    env.find? c = some (.recInfo cv mI rP rules) ∧
    mI + 1 ≤ W.getAppArgs.length)

/-- **The literal residue** (loop-tier): the actual run parked at a
literal while the trace continues through its conversion (the
conversions live in `litMajorToCtor`/`projLitToCtor`, AFTER the
actual's whnf) — the consumer re-runs its own conversion (same
literal, determinism) and continues along the residue. -/
def LitResidue (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  (∃ n, W = Expr.lit (.natVal n) ∧
    RawReach μ env d G (Setlec.litToCtorIfNat env W) f') ∨
  (∃ s t g, W = Expr.lit (.strVal s) ∧
    Setlec.strLitSupported env = true ∧ g ≤ G ∧
    whnf μ env g d (Setlec.strLitToConstructor s) = .ok t ∧
    RawReach μ env d G t f')

/-- **The iota fire seam** (the eta field segment, defensively
general): both sides fire at the same recursor node with DIFFERENT
results — the claimed fire's provenance, the actual's fire as a
run, the remaining claimed trace, the actual's continuation, and
the inequality as the progress marker. -/
def IotaFireSeam (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  ∃ (S M e''c e''a : Expr) (c : Name) (us : List Level)
    (cv : Setlec.ConstantVal) (mI rP : Nat)
    (rules : List Setlec.RecRule) (g g₂ : Nat),
    S.getAppFn = Expr.const c us ∧
    env.find? c = some (.recInfo cv mI rP rules) ∧
    S.getAppArgs.length = mI + 1 ∧
    RawReach μ env d G (S.getAppArgs.getD mI (.bvar 0)) M ∧
    RawReach μ env d G e''c f' ∧
    Setlec.iotaRec μ (Setlec.pureFns μ env g) env d S
      = .ok (some e''a) ∧
    whnfCore μ env g₂ d e''a = .ok W ∧
    e''c ≠ e''a

/-- **The nat grind seam**: a claimed nat fire whose image argument
the actual run parked at a dead shape — the actual `reduceNat`
declines and the guard-guaranteed stored definition unfolds and
grinds.  Both arities in one pack (the unary rows set `y := none`).
The actual's continuation from the unfolding is carried whole. -/
def NatGrindSeam (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  ∃ (S u res : Expr) (c : Name) (g gl l : Nat),
    (S.getAppFn = Expr.const c []) ∧
    RawReach μ env d G res f' ∧
    (∃ x Wx gx lx, x ∈ S.getAppArgs ∧
      Setlec.whnfLoop (Setlec.pureFns μ env gx) env d lx x
        = .ok Wx ∧
      DeadCore env Wx) ∧
    Setlec.reduceNat (Setlec.pureFns μ env g) env d S
      = .ok none ∧
    Setlec.unfoldDefinition env S = some u ∧
    Setlec.whnfLoop (Setlec.pureFns μ env gl) env d l u = .ok W

/-- The core-tier alignment conclusion. -/
def CoreAlignOut (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  (∃ g₂, whnfCore μ env g₂ d f' = .ok W) ∨
  DeadCore env W ∨
  IotaFireSeam μ env d G f' W ∨
  NatGrindSeam μ env d G f' W

/-- The loop-tier alignment conclusion (adds the literal residue —
loop outputs may park at literals whose conversions the trace
already took). -/
def LoopAlignOut (μ : CheckMode) (env : Env) (d G : Nat)
    (f' W : Expr) : Prop :=
  (∃ g₂ l₂, Setlec.whnfLoop (Setlec.pureFns μ env g₂) env d l₂ f'
    = .ok W) ∨
  DeadCore env W ∨
  LitResidue μ env d G f' W ∨
  IotaFireSeam μ env d G f' W ∨
  NatGrindSeam μ env d G f' W

/-- **The core alignment claim**: a gate-free trace against the
actual `whnfCore` run — aligned, dead, or a routed seam. -/
def CoreAlignF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {d G g : Nat} {f f' W : Expr},
    RawReach μ env d G f f' →
    whnfCore μ env g d f = .ok W →
    CoreAlignOut μ env d G f' W

/-- **The loop alignment claim**: a gate-free trace against the
actual explicit-budget loop run. -/
def LoopAlignF (μ : CheckMode) (env : Env) : Prop :=
  ∀ {d G g l : Nat} {f f' W : Expr},
    RawReach μ env d G f f' →
    Setlec.whnfLoop (Setlec.pureFns μ env g) env d l f = .ok W →
    LoopAlignOut μ env d G f' W

end Discharge

end Setlec.SetR.Interp2
