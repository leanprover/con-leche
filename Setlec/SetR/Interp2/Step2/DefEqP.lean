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

/-! ## T3 — the step dispatcher

`defeqStep_claim2D`'s transpose.  Every `denote2_fuelMono` and every
`CtxOk2D.fuelMono` in the original had exactly one job — reconciling
two readings taken at two fuels — and in the P currency there is one
reading, so all of them disappear together with the `max Fa Fb` join.
What is left is the checker's own case tree. -/

/-- **`DefEqStepAtP`**, modulo the routed obligations. -/
theorem defeqStep_claimP {m : EnvS2UM V μ env} {fuel : Nat}
    (hex : WhnfCoreReductExistsP m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    (hdel : DenotePDeltaP m φ)
    (hnat : ReduceNatStepPQ m φ fuel) (hpi : ProofIrrelPQ m φ fuel)
    (hstk : DefEqStuckP m φ fuel)
    (hspine : DefEqSpineP m φ fuel) :
    DefEqStepAtP m φ fuel := by
  intro d k hk a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb
    hda hdb hokA hokB ρ hρ
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, Setlec.whnfCore_def,
    Setlec.proofIrrel_fold, Setlec.reduceNat_fold,
    Setlec.defeqSpine_fold, Setlec.stuckIrrel_fold,
    Setlec.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · cases hwca : whnfCore μ env fuel d a with
    | error err => rw [hwca] at h; exact nomatch h
    | ok a' =>
    rw [hwca] at h
    dsimp only at h
    cases hwcb : whnfCore μ env fuel d b with
    | error err => rw [hwcb] at h; exact nomatch h
    | ok b' =>
    rw [hwcb] at h
    dsimp only at h
    obtain ⟨aa', hda', hokA', hEa, hwa', hba', hLa', hCa'⟩ :=
      dq_whnfCore_packageP m hex ihwc hwca hwa hba hLa hCa hda hokA
    obtain ⟨ba', hdb', hokB', hEb, hwb', hbb', hLb', hCb'⟩ :=
      dq_whnfCore_packageP m hex ihwc hwcb hwb hbb hLb hCb hdb hokB
    have hEA := hEa ρ hρ
    have hEB := hEb ρ hρ
    -- from here every verdict is the middle equation
    suffices hmid : interp2 V ρ aa' = interp2 V ρ ba' from
      (hEA.trans hmid).trans hEB.symm
    clear hEA hEB hEa hEb hda hdb hokA hokB hCa hCb
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · cases hir : Setlec.proofIrrelP μ env fuel d a' b' with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        exact hpi hir hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' hokA' hokB' ρ hρ
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : Setlec.reduceNatP μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨w, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda' hokA'
          exact (hEw ρ hρ).trans
            (hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw hdb' hokw
              hokB' ρ hρ)
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            Setlec.reduceNatP μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : Setlec.reduceNatP μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨w, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb' hokB'
          exact (hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hw
            hokA' hokw ρ hρ).trans (hEw ρ hρ).symm
        | none, hnb, h =>
        cases hha : Setlec.unfoldableHead env a' <;>
          cases hhb : Setlec.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hwca
            hwcb (by simpa using ‹¬(a' == b') = true›) hir hna hnb
            hha hhb hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
            hdb' hokA' hokB' ρ hρ
        · cases hub : Setlec.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              dq_delta_packageP hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hd2
              hokA' hokB' ρ hρ
        · cases hua : Setlec.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              dq_delta_packageP hdel hua hwa' hba' hLa' hCa' hda'
            exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hdb'
              hokA' hokB' ρ hρ
        · have hboth : ∀ {x : CheckM Bool},
              (match Setlec.unfoldDefinition env a',
                  Setlec.unfoldDefinition env b' with
                | some a₂, some b₂ => k a₂ b₂
                | _, _ => pure false) = .ok true →
              interp2 V ρ aa' = interp2 V ρ ba' := by
            intro x hbb2
            cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : Setlec.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨hdA, hwA, hbA, hLA, hCA⟩ :=
                dq_delta_packageP hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨hdB, hwB, hbB, hLB, hCB⟩ :=
                dq_delta_packageP hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk hbb2 hwA hbA hLA hwB hbB hLB hCA hCB hdA hdB
                hokA' hokB' ρ hρ
          cases hlt1 : Setlec.ReducibilityHint.lt
              (Setlec.headHint env b') (Setlec.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : Setlec.ReducibilityHint.lt
                (Setlec.headHint env a') (Setlec.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (Setlec.ReducibilityHint.sameRegular
                    (Setlec.headHint env a') (Setlec.headHint env b') &&
                  Setlec.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : Setlec.defeqSpineP μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' hokA' hokB' ρ hρ
                | false => exact hboth (x := pure false) h
            · cases hub : Setlec.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                  dq_delta_packageP hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda'
                  hd2 hokA' hokB' ρ hρ
          · cases hua : Setlec.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                dq_delta_packageP hdel hua hwa' hba' hLa' hCa' hda'
              exact hk h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
                hdb' hokA' hokB' ρ hρ

/-! ## T4 — the binder congruence's two premises -/

/-- An application's argument frame, P currency (`frame_appArg2D`). -/
private theorem dq_frame_appArgP {m : EnvS2UM V μ env} {d : Nat}
    {Δa : List AVExpr} {f x : Expr}
    (hws : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f x))
    (hC : CtxOkP m φ d Δa (.app f x)) :
    Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2,
    fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]), hC.app_arg⟩

/-- **The binder congruence's two premises, P currency.**
`binder_congr2D` verbatim modulo the currency: the opened contexts are
`CtxOkP.openS` on the left (its own domain) and `CtxOkP.openCongC` on
the right (the *left* domain, across the domains' semantic agreement),
and `hdom` — `ihd`'s own conclusion — is computed once and used for
both the congruence's first component and `openCongC`'s transport.

The gradings come in at `AnnotOkP`, which is what `CtxOkP`'s leaf
package and `DefEqClaims2P`'s premises both speak. -/
theorem binder_congrP {m : EnvS2UM V μ env} {fuel : Nat}
    (ihd : DefEqClaims2P μ m φ fuel)
    {d : Nat} {Δa : List AVExpr} {n₁ n₂ : Name}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AVExpr}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁))
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOkP m φ d Δa ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOkP m φ d Δa bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOkP m φ d Δa ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOkP m φ d Δa bd₂)
    (hta₁ : denoteP m.acval env φ d ty₁ = some ta₁)
    (hva₁ : denoteP m.acval env φ (d + 1)
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) = some ba₁)
    (hta₂ : denoteP m.acval env φ d ty₂ = some ta₂)
    (hva₂ : denoteP m.acval env φ (d + 1)
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) = some ba₂)
    (hoT₁ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ ta₁)
    (hoT₂ : ∀ σ : Nat → V, Sat2 V Δa σ → AnnotOkP V σ ta₂)
    (hoB₁ : ∀ σ : Nat → V, Sat2 V (ta₁ :: Δa) σ → AnnotOkP V σ ba₁)
    (hoB₂ : ∀ σ : Nat → V, Sat2 V (ta₂ :: Δa) σ → AnnotOkP V σ ba₂)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ta₁ = interp2 V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp2 V ρ ta₁ →
        interp2 V (cons x ρ) ba₁ = interp2 V (cons x ρ) ba₂ := by
  have hdom : ∀ σ : Nat → V, Sat2 V Δa σ →
      interp2 V σ ta₁ = interp2 V σ ta₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      hoT₁ hoT₂
  have hLo₁ : Expr.LeavesBounded
      (bd₁.instantiate1 (.fvar d n₁ ty₁)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bd₁ 0 hl with h2 | h2
    · exact hLb₁ l h2
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbt₁
      · exact hLt₁ l h3
  have hLo₂ : Expr.LeavesBounded
      (bd₂.instantiate1 (.fvar d n₂ ty₂)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bd₂ 0 hl with h2 | h2
    · exact hLb₂ l h2
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbt₂
      · exact hLt₂ l h3
  refine ⟨hdom ρ hρ, ?_⟩
  intro x hx
  exact ihd (Δa := ta₁ :: Δa) hdd
    (Expr.WScoped.instantiate1 hwt₁ 0 hwb₁)
    (Setlec.looseBVarsBounded_instantiate1 bd₁ 0 hbb₁) hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (Setlec.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) hLo₂
    (CtxOkP.openS hCt₁ hCb₁ hta₁ hoT₁)
    (CtxOkP.openCongC hCb₂ hCt₂ hta₂ hoT₂ hdom)
    hva₁ hva₂ hoB₁
    (fun σ hσ => hoB₂ σ (Sat2.head_congr hdom hσ)) (cons x ρ)
    (Sat2_cons V hρ hx)

end Setlec.SetR.Interp2
