import Setlec.SetR.Interp2.CtxOkPKit
import Setlec.SetR.Annot.BitLemmas
import Setlec.SetR.Interp2.Step2.DefEqRun

/-!
# The definitional-equality quarter, P currency (task #161, P3 batch 5)

The D generation of `Step2/DefEqRun.lean` — `DefEqCont2D` through
`defEqStep2D_of` — transposed to the validated-annotation reading.
The systematic deltas are the P tier's, uniformly:

* `denote2 μ m.acval env φ F d e` becomes `denoteP m.acval env φ d e`:
  **no fuel anywhere**, so no `∃ F' ≥ F` slack, no `denote2_fuelMono`,
  no `CtxOk2D.fuelMono`.  Where the D lane reconciled two readings by
  raising both to `max Fa Fb`, the P lane reconciles them with
  `Option.some.inj` — there is only one reading to have.
* `AnnotOk2` becomes `AnnotOkP` in every grading premise, `CtxOk2D`
  becomes `CtxOkP`.
* `BinderSortAgree2A` — residue 9 — is **deleted**.  See below.

## Residue 9 dissolves

`defeqStuck_claim2D` takes `hbs : BinderSortAgree2A` and spends it in
exactly two places: `obtain rfl : v₁ = v₂ := hbs.1 hbd hv₁ hv₂` in the
∀-congruence case and `obtain rfl : v₁ = v₂ := hbs.2 hbd hv₁ hv₂` in
the λ-congruence case, where `v₁`/`v₂` are the two sides'
`sortOfE`/`lamSortE` numerals and `deqStep2_piCong`/`deqStep2_lamCong`
demand one shared numeral.

In the P currency those numerals are `pwBit φ m₁.pw` and
`pwBit φ m₂.pw` — read off each side's *own* validated annotation
(`denoteP_forallE_inv`/`denoteP_lam_inv`), no run involved.  And the
binder arms of `defeqStep` (`Kernel/Core.lean`) end with the task-#161
check

```
    if mode.verified && !(m₁.pw.equiv m₂.pw) then
      throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
    pure true
```

so a run that reached `.ok true` at `μ.verified = true` **certifies**
`m₁.pw.equiv m₂.pw`, and `pwBit_eq_of_equiv` turns that into equal
numerals.  The obligation an outside supplier used to owe is now a
fact the run itself hands over: the quarter takes `hμ : μ.verified =
true` (a hypothesis of the *stuck claim* and of the *step*, never of
the claims, which stay mode-generic) and no `hbs` at all.

## What the P currency owes instead

Two obligations that the D lane got for free, because `Claims2D`
*produced* annotations and `Claims2P` (dual success, frozen text) does
not:

* `WhnfCoreReductExistsP` — the `whnfCore` reduct annotates.  This is
  `WhnfCoreExists2E`'s P transpose, and it is routed for the same
  reason generation six routes it: no claim in the family concludes
  definedness of anything.
* `DenotePDeltaP` — unfolding a definition head does not move the
  reading (`Denote2Delta2A` without the fuel bump).

Both are flagged in the report as kept-routed.

## Naming

The kernel already owns `Setlec.proofIrrelP` and `Setlec.stuckIrrelP`,
so the two residues that mirror `ProofIrrel2D`/`StuckIrrel2D` are
`ProofIrrelPQ`/`StuckIrrelPQ`.  `ReduceNat2D`'s mirror is
`ReduceNatStepPQ` (the whnf quarter owns `ReduceNatStep…`).  The two
package helpers carry a `dq_` prefix so that the concurrently-written
whnf quarter can keep the unprefixed names.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode CheckM Env Expr Name Level PropWhen isDefEqCore
  whnfCore defeqStep defeqLoop defeqBody defeqLoopFuel pureFns)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `denoteP` at the two `Nat` constructors

`denote2_natZeroConst`/`denote2_natSuccConst`, fuel-free. -/

/-- `Nat.zero`, in the validated reading. -/
theorem denoteP_natZeroConst {acval : Name → (Name → Nat) → AVExpr}
    (hg : Setlec.natLitSupported env = true) {d : Nat} :
    denoteP acval env φ d (.const Setlec.natZeroName [])
      = some (acval Setlec.natZeroName (Level.substFn φ [] [])) := by
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? Setlec.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [Setlec.natZeroOk, Bool.and_eq_true] at h2
        simpa [Setlec.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [Setlec.natZeroOk] at h2
    rw [denoteP_const hf (by simp [hlp]), hlp]

/-- `Nat.succ`, in the validated reading. -/
theorem denoteP_natSuccConst {acval : Name → (Name → Nat) → AVExpr}
    (hg : Setlec.natLitSupported env = true) {d : Nat} :
    denoteP acval env φ d (.const Setlec.natSuccName [])
      = some (acval Setlec.natSuccName (Level.substFn φ [] [])) := by
  simp only [Setlec.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? Setlec.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [Setlec.natSuccOk, Bool.and_eq_true] at h3
        simpa [Setlec.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [Setlec.natSuccOk] at h3
    rw [denoteP_const hf (by simp [hlp]), hlp]

/-! ## The `AnnotOkP` hoist kit

`AnnotOk2.hoist_pi`/`hoist_lam`/`hoist_proj`/`hoist_app`
(`Step2/Dispatch.lean`) at the merged currency.  Private: they are
plumbing, and the concurrently-written quarters may want the public
names. -/

private theorem hoistP_pi {Δa : List AVExpr} {u v : Nat} {A B : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOkP V ρ B) := by
  obtain ⟨h1, h2⟩ := AnnotOk2.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValidV_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValidV_pi V _ u v A B) ▸
      (h _ (Sat2_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

private theorem hoistP_lam {Δa : List AVExpr} {v : Nat} {A b : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ A) ∧
      (∀ ρ : Nat → V, Sat2 V (A :: Δa) ρ → AnnotOkP V ρ b) := by
  obtain ⟨h1, h2⟩ := AnnotOk2.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValidV_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValidV_lam V _ v A b) ▸
      (h _ (Sat2_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

private theorem hoistP_proj {Δa : List AVExpr} {i : Nat} {e : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.proj i e)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ e := fun ρ hρ =>
  ⟨AnnotOk2.hoist_proj (V := V) (fun σ hσ => (h σ hσ).1) ρ hρ,
    (AnnotValidV_proj V ρ i e) ▸ (h ρ hρ).2⟩

private theorem hoistP_app_arg {Δa : List AVExpr} {f a : AVExpr}
    (h : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ (.app f a)) :
    ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ a := fun ρ hρ =>
  ⟨(AnnotOk2.hoist_app (V := V) (fun σ hσ => (h σ hσ).1)).2 ρ hρ,
    ((AnnotValidV_app V ρ f a) ▸ (h ρ hρ).2).2⟩

/-! ## T1 — the routed definitions -/

/-- The continuation's contract, P currency. -/
def DefEqContP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AVExpr}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **One iteration of the lazy-delta loop**, P currency. -/
def DefEqStepAtP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Expr → Expr → CheckM Bool},
    DefEqContP m φ d k →
    ∀ {a b : Expr} {Δa : List AVExpr},
      defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      ∀ {aa ba : AVExpr},
        CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
        denoteP m.acval env φ d a = some aa →
        denoteP m.acval env φ d b = some ba →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 3 — proof irrelevance**, P currency.  (`ProofIrrelP`
would clash with the kernel's `Setlec.proofIrrelP`.) -/
def ProofIrrelPQ {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.proofIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 4 — the literal acceleration**, P currency.  The
existential is over the reduct's *reading* alone: there is no fuel to
raise. -/
def ReduceNatStepPQ {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr} {ea : AVExpr},
    Setlec.reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOkP m φ d Δa e →
    denoteP m.acval env φ d e = some ea →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
    ∃ ea₂,
      denoteP m.acval env φ d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea₂) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOkP m φ d Δa e₂

/-- **Residue 5 — the same-head spine short-circuit**, P currency. -/
def DefEqSpineP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.defeqSpineP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **The stuck configuration**, P currency.  `hμ : μ.verified = true`
is *not* here: it is a hypothesis of the theorem that discharges this
Prop, so the routed shape stays mode-generic. -/
def DefEqStuckP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {k : Expr → Expr → CheckM Bool}
    {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k a b = .ok true →
    (a == b) = false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    Setlec.proofIrrelP μ env fuel d a' b' = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      Setlec.reduceNatP μ env fuel d b' else pure none) = .ok none →
    Setlec.unfoldableHead env a' = false →
    Setlec.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    ∀ {aa' ba' : AVExpr},
      CtxOkP m φ d Δa a' → CtxOkP m φ d Δa b' →
      denoteP m.acval env φ d a' = some aa' →
      denoteP m.acval env φ d b' = some ba' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa') →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba') →
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa' = interp2 V ρ ba'

/-- **Residue 6 — `stuckIrrel`**, P currency.  (`StuckIrrelP` would
clash with the kernel's `Setlec.stuckIrrelP`.) -/
def StuckIrrelPQ {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    Setlec.stuckIrrelP μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 10 — the stuck spine congruence**, P currency. -/
def AppCongrStuckP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AVExpr},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    Setlec.defEqListP μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa a → CtxOkP m φ d Δa b →
      denoteP m.acval env φ d a = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 11 — the η certificate**, P currency. -/
def EtaCertStepP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {n : Name} {ty bd b : Expr} {mb : Setlec.BinderMeta}
    {Δa : List AVExpr},
    Setlec.etaCertP μ env fuel d n ty bd mb b = .ok true →
    Expr.WScoped d (.lam n ty bd mb) →
    (Expr.lam n ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AVExpr},
      CtxOkP m φ d Δa (.lam n ty bd mb) →
      CtxOkP m φ d Δa b →
      denoteP m.acval env φ d (.lam n ty bd mb) = some aa →
      denoteP m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ba) →
      ∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ aa = interp2 V ρ ba

/-- **Residue 7 — the string-literal expansion**, P currency
(`Denote2StrLit2A`, fuel-free). -/
def DenotePStrLit {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (st : String) {sa : AVExpr},
    Setlec.strLitSupported env = true →
    denoteP m.acval env φ d (.lit (.strVal st)) = some sa →
    denoteP m.acval env φ d
        (Setlec.strLitToConstructor st) = some sa ∧
      Expr.WScoped d (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Setlec.strLitToConstructor st) ∧
      (Setlec.strLitToConstructor st).fvarLeaves = []

/-- **Residue 2 — the delta identity**, P currency: unfolding a
definition head does not move the validated reading.  Fuel-free, so
`Denote2Delta2A`'s `∃ F' ≥ F` collapses to an equation. -/
def DenotePDeltaP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {x y : Expr} {xa : AVExpr},
    Setlec.unfoldDefinition env x = some y →
    denoteP m.acval env φ d x = some xa →
    denoteP m.acval env φ d y = some xa

/-- **The dual-success existence factor** the P currency owes: a
`whnfCore` reduct annotates.  `WhnfCoreExists2E`'s transpose, routed
for the same reason — no claim of the family concludes definedness. -/
def WhnfCoreReductExistsP {env : Env} (m : EnvS2UM V μ env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      ∃ ea', denoteP m.acval env φ d e' = some ea'

/-! ## T2 — the loop plumbing -/

/-- The loop satisfies the contract at every budget. -/
theorem defeqLoop_contP {m : EnvS2UM V μ env} {fuel : Nat}
    (hstep : DefEqStepAtP m φ fuel) :
    ∀ (budget d : Nat),
      DefEqContP m φ d
        (defeqLoop μ (pureFns μ env fuel) env d budget) := by
  intro budget
  induction budget with
  | zero =>
    intro d a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d a b Δa h
    rw [defeqLoop] at h
    exact hstep (ih d) h

/-- **`DefEqClaims2P` at `fuel + 1`**, modulo the step. -/
theorem defeq_claimsP {m : EnvS2UM V μ env} {fuel : Nat}
    (hstep : DefEqStepAtP m φ fuel) :
    DefEqClaims2P μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
  rw [Setlec.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_contP hstep defeqLoopFuel d h hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb

/-- The `whnfCore` reduct's package, P currency.  `whnfCore_package2D`
with the fuel bump gone and the annotation's *existence* taken from
the routed factor instead of from the claim. -/
theorem dq_whnfCore_packageP (m : EnvS2UM V μ env) {fuel d : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa : AVExpr}
    (hex : WhnfCoreReductExistsP m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkP m φ d Δa a)
    (haa : denoteP m.acval env φ d a = some aa)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) :
    ∃ aa', denoteP m.acval env φ d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa') ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOkP m φ d Δa a' := by
  obtain ⟨aa', haa'⟩ := hex hw hws hb hLb hC haa hok
  obtain ⟨hok', heq⟩ := ihwc hw hws hb hLb hC haa haa' hok
  exact ⟨aa', haa', hok', heq,
    whnfCore_WScoped m.base.wf fuel hw hws,
    whnfCore_looseBVars m.base.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.base.wf fuel hw l hl),
    hC.of_subset (whnfCore_fvarLeaves m.base.wf fuel hw)⟩

/-- The δ package, P currency: neither the annotation nor the fuel
moves, so only the frame conditions and one `of_subset` remain. -/
theorem dq_delta_packageP {m : EnvS2UM V μ env}
    (hdel : DenotePDeltaP m φ)
    {d : Nat} {Δa : List AVExpr} {x y : Expr} {xa : AVExpr}
    (hu : Setlec.unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x) (hC : CtxOkP m φ d Δa x)
    (hx : denoteP m.acval env φ d x = some xa) :
    denoteP m.acval env φ d y = some xa ∧
      Expr.WScoped d y ∧ y.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded y ∧ CtxOkP m φ d Δa y :=
  ⟨hdel hu hx, unfoldDefinition_WScoped m.base.wf hu hws,
    unfoldDefinition_looseBVars m.base.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.base.wf hu l hl),
    hC.of_subset (unfoldDefinition_fvarLeaves m.base.wf hu)⟩

end Setlec.SetR.Interp2
