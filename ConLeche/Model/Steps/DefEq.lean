module

public import ConLeche.Model.CtxOkKit
public import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Model.Annot.BitRename
public import ConLeche.Semantics.DefEqStep
public import ConLeche.Semantics.Hoist
public import ConLeche.Model.Steps.ProjAVKit

@[expose] public section

/-!
# The definitional-equality quarter, P currency (task #161, P3 batch 5)

The D generation of `Steps/DefEqRun.lean` — `DefEqCont2D` through
`defEqStep2D_of` — transposed to the validated-annotation reading.
The systematic deltas are the P tier's, uniformly:

* `denoteAnnot μ m.acval env φ F d e` becomes `denoteMeta m.acval env φ d e`:
  **no fuel anywhere**, so no `∃ F' ≥ F` slack, no `denote2_fuelMono`,
  no `CtxOk2D.fuelMono`.  Where the D lane reconciled two readings by
  raising both to `max Fa Fb`, the P lane reconciles them with
  `Option.some.inj` — there is only one reading to have.
* `WellDenoted` becomes `WellDenotedV` in every grading premise, `CtxOk2D`
  becomes `CtxOk`.
* `BinderSortAgree2A` — residue 9 — is **deleted**.  See below.

## Residue 9 dissolves

`defeqStuck_claim2D` takes `hbs : BinderSortAgree2A` and spends it in
exactly two places: `obtain rfl : v₁ = v₂ := hbs.1 hbd hv₁ hv₂` in the
∀-congruence case and `obtain rfl : v₁ = v₂ := hbs.2 hbd hv₁ hv₂` in
the λ-congruence case, where `v₁`/`v₂` are the two sides'
`sortOfE`/`lamSortE` numerals and `deqStep_piCong`/`deqStep_lamCong`
demand one shared numeral.

In the P currency those numerals are `pwBit φ m₁.pw` and
`pwBit φ m₂.pw` — read off each side's *own* validated annotation
(`denoteMeta_forallE_inv`/`denoteMeta_lam_inv`), no run involved.  And the
binder arms of `defeqStep` (`Kernel/Core.lean`) end with the task-#161
check

```
    if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
      throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
    pure true
```

so a run that reached `.ok true` at `μ.verifiedChecks = true` **certifies**
`m₁.pw == m₂.pw`, i.e. `m₁.pw = m₂.pw`, hence equal
numerals by rewriting.  The obligation an outside supplier used to owe is now a
fact the run itself hands over: the quarter takes `hμ : μ.verifiedChecks =
true` (a hypothesis of the *stuck claim* and of the *step*, never of
the claims, which stay mode-generic) and no `hbs` at all.

## What the P currency owes instead

Two obligations that the D lane got for free, because `Claims2D`
*produced* annotations and `Claims` (dual success, frozen text) does
not:

* `WhnfCoreReductExists` — the `whnfCore` reduct annotates.  This is
  `WhnfCoreExists2E`'s P transpose, and it is routed for the same
  reason generation six routes it: no claim in the family concludes
  definedness of anything.
* `DenoteMetaDelta` — unfolding a definition head does not move the
  reading (`Denote2Delta2A` without the fuel bump).

Both are flagged in the report as kept-routed.

## Naming

The kernel already owns `ConLeche.proofIrrelFueled` and `ConLeche.stuckIrrelFueled`,
so the two residues that mirror `ProofIrrel2D`/`StuckIrrel2D` are
`ProofIrrelPQ`/`StuckIrrelPQ`.  `ReduceNat2D`'s mirror is
`ReduceNatStepPQ` (the whnf quarter owns `ReduceNatStep…`).  The two
package helpers carry a `dq_` prefix so that the concurrently-written
whnf quarter can keep the unprefixed names.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode CheckM Env Expr Name Level PropWhen isDefEqCore
  whnfCore defeqStep defeqLoop defeqBody defeqLoopFuel pureFns)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `denoteMeta` at the two `Nat` constructors

`denote2_natZeroConst`/`denote2_natSuccConst`, fuel-free. -/

/-- `Nat.zero`, in the validated reading. -/
theorem denoteMeta_natZeroConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natZeroName [])
      = some (acval ConLeche.natZeroName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, -⟩ := hg
  cases hf : env.find? ConLeche.natZeroName with
  | none => rw [hf] at h2; exact nomatch h2
  | some ci =>
    rw [hf] at h2
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h2
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h2.1
      | _ => simp [ConLeche.natZeroOk] at h2
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-- `Nat.succ`, in the validated reading. -/
theorem denoteMeta_natSuccConst {acval : Name → (Name → Nat) → AnnotTerm}
    (hg : ConLeche.natLitSupported env = true) {d : Nat} :
    denoteMeta acval env φ d (.const ConLeche.natSuccName [])
      = some (acval ConLeche.natSuccName (Level.substFn φ [] [])) := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨-, h3⟩ := hg
  cases hf : env.find? ConLeche.natSuccName with
  | none => rw [hf] at h3; exact nomatch h3
  | some ci =>
    rw [hf] at h3
    have hlp : ci.toConstantVal.levelParams = [] := by
      cases ci with
      | ctorInfo cv p q =>
        simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h3
        simpa [ConLeche.ConstantInfo.toConstantVal, List.isEmpty_iff]
          using h3.1
      | _ => simp [ConLeche.natSuccOk] at h3
    rw [denoteMeta_const hf (by simp [hlp]), hlp]

/-! ## The `WellDenotedV` hoist kit

`WellDenoted.hoist_pi`/`hoist_lam`/`hoist_fst`/`hoist_snd`/`hoist_app`
(`Steps/Dispatch.lean`) at the merged currency.  Private: they are
plumbing, and the concurrently-written quarters may want the public
names. -/

private theorem hoist_pi {Δa : List AnnotTerm} {u v : Nat} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.pi u v A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenotedV V ρ B) := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_pi (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_pi V ρ u v A B) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_pi V _ u v A B) ▸
      (h _ (Sat_tail hρ)).2).2.1 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

private theorem hoist_lam {Δa : List AnnotTerm} {v : Nat} {A b : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.lam v A b)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenotedV V ρ b) := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_lam (V := V) (fun ρ hρ => (h ρ hρ).1)
  refine ⟨fun ρ hρ => ⟨h1 ρ hρ, ?_⟩, fun ρ hρ => ⟨h2 ρ hρ, ?_⟩⟩
  · exact ((AnnotValid_lam V ρ v A b) ▸ (h ρ hρ).2).1
  · have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
      funext i; cases i with | zero => rfl | succ i => rfl
    have := ((AnnotValid_lam V _ v A b) ▸
      (h _ (Sat_tail hρ)).2).2 (ρ 0) (hρ 0 A rfl)
    rwa [hcons] at this

private theorem hoist_fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.fst e)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ e := fun ρ hρ =>
  ⟨WellDenoted.hoist_fst (V := V) (fun σ hσ => (h σ hσ).1) ρ hρ,
    (AnnotValid_fst V ρ e) ▸ (h ρ hρ).2⟩

private theorem hoist_snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ (.snd e)) :
    ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ e := fun ρ hρ =>
  ⟨WellDenoted.hoist_snd (V := V) (fun σ hσ => (h σ hσ).1) ρ hρ,
    (AnnotValid_snd V ρ e) ▸ (h ρ hρ).2⟩

/-! ## T1 — the routed definitions -/

/-- The continuation's contract, P currency. -/
def DefEqCont {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (d : Nat)
    (k : Expr → Expr → CheckM Bool) : Prop :=
  ∀ {a b : Expr} {Δa : List AnnotTerm}, k a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **One iteration of the lazy-delta loop**, P currency. -/
def DefEqStepAt (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {k : Bool → Expr → Expr → CheckM Bool},
    (∀ pi : Bool, DefEqCont m φ d (k pi)) →
    ∀ (pi : Bool) {a b : Expr} {Δa : List AnnotTerm},
      defeqStep μ (pureFns μ env fuel) env d k pi a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      ∀ {aa ba : AnnotTerm},
        CtxOk m φ d Δa a → CtxOk m φ d Δa b →
        denoteMeta m.acval env φ d a = some aa →
        denoteMeta m.acval env φ d b = some ba →
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ aa = interp V ρ ba

/-- **Residue 3 — proof irrelevance**, P currency.  (`ProofIrrelP`
would clash with the kernel's `ConLeche.proofIrrelFueled`.) -/
def ProofIrrelPQ (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.proofIrrelFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 3′ — the hoisted `Prop`-branch test** (task #168, Option
U), P currency: `defeqStep`'s hoist runs `propIrrel` — the `Prop`
branch with the head-symbol fast arms; the unit-like branch stays with
`stuckIrrel`'s `proofIrrel`. -/
def PropIrrelPQ (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.propIrrelFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 4 — the literal acceleration**, P currency.  The
existential is over the reduct's *reading* alone: there is no fuel to
raise. -/
def ReduceNatStepPQ (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AnnotTerm} {ea : AnnotTerm},
    ConLeche.reduceNatFueled μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
    ∃ ea₂,
      denoteMeta m.acval env φ d e₂ = some ea₂ ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea₂) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea = interp V ρ ea₂) ∧
      Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₂ ∧ CtxOk m φ d Δa e₂

/-- **Residue 5 — the same-head spine short-circuit**, P currency. -/
def DefEqSpine (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.defeqSpineFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **The stuck configuration**, P currency.  `hμ : μ.verifiedChecks = true`
is *not* here: it is a hypothesis of the theorem that discharges this
Prop, so the routed shape stays mode-generic. -/
def DefEqStuck (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AnnotTerm} {k : Bool → Expr → Expr → CheckM Bool}
    {pi : Bool} {a b a' b' : Expr},
    defeqStep μ (pureFns μ env fuel) env d k pi a b = .ok true →
    (a == b) = false →
    (if pi && b.isBoolTrue && !a.hasFvar then
      ConLeche.boolTrueShortcutFueled μ env fuel d a else pure false) = .ok false →
    whnfCore μ env fuel d a = .ok a' →
    whnfCore μ env fuel d b = .ok b' →
    (a' == b') = false →
    (if pi && !a'.quickPair b' then ConLeche.propIrrelFueled μ env fuel d a' b'
      else pure false) = .ok false →
    (if !a'.hasFvar && !b'.hasFvar then
      ConLeche.reduceNatFueled μ env fuel d a' else pure none) = .ok none →
    (if !a'.hasFvar && !b'.hasFvar then
      ConLeche.reduceNatFueled μ env fuel d b' else pure none) = .ok none →
    ConLeche.unfoldableHead env a' = false →
    ConLeche.unfoldableHead env b' = false →
    Expr.WScoped d a' → a'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a' →
    Expr.WScoped d b' → b'.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b' →
    ∀ {aa' ba' : AnnotTerm},
      CtxOk m φ d Δa a' → CtxOk m φ d Δa b' →
      denoteMeta m.acval env φ d a' = some aa' →
      denoteMeta m.acval env φ d b' = some ba' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa') →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba') →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa' = interp V ρ ba'

/-- **Residue 6 — `stuckIrrel`**, P currency.  (`StuckIrrelP` would
clash with the kernel's `ConLeche.stuckIrrelFueled`.) -/
def StuckIrrelPQ (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    ConLeche.stuckIrrelFueled μ env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 10 — the stuck spine congruence**, P currency. -/
def AppCongrStuck (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr} {Δa : List AnnotTerm},
    isDefEqCore μ env fuel d a.getAppFn b.getAppFn = .ok true →
    ConLeche.defEqListFueled μ env fuel d a.getAppArgs b.getAppArgs
      = .ok true →
    a.getAppArgs.length = b.getAppArgs.length →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a → CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 11 — the η certificate**, P currency. -/
def EtaCertStep (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {ty bd b : Expr} {mb : ConLeche.BinderMeta}
    {Δa : List AnnotTerm},
    ConLeche.etaCertFueled μ env fuel d ty bd mb b = .ok true →
    Expr.WScoped d (.lam ty bd mb) →
    (Expr.lam ty bd mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam ty bd mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa (.lam ty bd mb) →
      CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d (.lam ty bd mb) = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ aa = interp V ρ ba

/-- **Residue 7 — the string-literal expansion**, P currency
(`Denote2StrLit2A`, fuel-free). -/
def DenotePStrLit {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (st : String) {sa : AnnotTerm},
    ConLeche.strLitSupported env = true →
    denoteMeta m.acval env φ d (.lit (.strVal st)) = some sa →
    denoteMeta m.acval env φ d
        (ConLeche.strLitToConstructor st) = some sa ∧
      Expr.WScoped d (ConLeche.strLitToConstructor st) ∧
      (ConLeche.strLitToConstructor st).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (ConLeche.strLitToConstructor st) ∧
      (ConLeche.strLitToConstructor st).fvarLeaves = []

/-- **Residue 2 — the delta identity**, P currency: unfolding a
definition head does not move the validated reading.  Fuel-free, so
`Denote2Delta2A`'s `∃ F' ≥ F` collapses to an equation. -/
def DenoteMetaDelta {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {x y : Expr} {xa : AnnotTerm},
    ConLeche.unfoldDefinition env x = some y →
    denoteMeta m.acval env φ d x = some xa →
    denoteMeta m.acval env φ d y = some xa

/-- **The dual-success existence factor** the P currency owes: a
`whnfCore` reduct annotates.  `WhnfCoreExists2E`'s transpose, routed
for the same reason — no claim of the family concludes definedness. -/
def WhnfCoreReductExists (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AnnotTerm},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      ∃ ea', denoteMeta m.acval env φ d e' = some ea'

/-! ## T2 — the loop plumbing -/

/-- The loop satisfies the contract at every budget. -/
theorem defeqLoop_cont {m : EnvModel V env} {fuel : Nat}
    (hstep : DefEqStepAt μ m φ fuel) :
    ∀ (budget d : Nat) (pi : Bool),
      DefEqCont m φ d
        (defeqLoop μ (pureFns μ env fuel) env d budget pi) := by
  intro budget
  induction budget with
  | zero =>
    intro d pi a b Δa h
    rw [defeqLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d pi a b Δa h
    rw [defeqLoop] at h
    exact hstep (fun pi' => ih d pi') pi h

/-- **`DefEqClaim` at `fuel + 1`**, modulo the step. -/
theorem defeq_claims {m : EnvModel V env} {fuel : Nat}
    (hstep : DefEqStepAt μ m φ fuel) :
    DefEqClaim μ m φ (fuel + 1) := by
  intro d a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb hda hdb
  rw [ConLeche.isDefEqCore_succ, defeqBody] at h
  exact defeqLoop_cont hstep defeqLoopFuel d true h hwa hba hLa hwb
    hbb hLb hCa hCb hda hdb

/-- The `whnfCore` reduct's package, P currency.  `whnfCore_package2D`
with the fuel bump gone and the annotation's *existence* taken from
the routed factor instead of from the claim. -/
theorem dq_whnfCore_package (m : EnvModel V env) {fuel d : Nat}
    {Δa : List AnnotTerm} {a a' : Expr} {aa : AnnotTerm}
    (hex : WhnfCoreReductExists μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOk m φ d Δa a)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) :
    ∃ aa', denoteMeta m.acval env φ d a' = some aa' ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa') ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa = interp V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOk m φ d Δa a' := by
  obtain ⟨aa', haa'⟩ := hex hw hws hb hLb hC haa hok
  obtain ⟨hok', heq⟩ := ihwc hw hws hb hLb hC haa haa' hok
  exact ⟨aa', haa', hok', heq,
    whnfCore_WScoped m.wf fuel hw hws,
    whnfCore_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.wf fuel hw l hl),
    hC.of_subset (whnfCore_fvarLeaves m.wf fuel hw)⟩

/-- The δ package, P currency: neither the annotation nor the fuel
moves, so only the frame conditions and one `of_subset` remain. -/
theorem dq_delta_package {m : EnvModel V env}
    (hdel : DenoteMetaDelta m φ)
    {d : Nat} {Δa : List AnnotTerm} {x y : Expr} {xa : AnnotTerm}
    (hu : ConLeche.unfoldDefinition env x = some y)
    (hws : Expr.WScoped d x) (hb : x.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded x) (hC : CtxOk m φ d Δa x)
    (hx : denoteMeta m.acval env φ d x = some xa) :
    denoteMeta m.acval env φ d y = some xa ∧
      Expr.WScoped d y ∧ y.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded y ∧ CtxOk m φ d Δa y :=
  ⟨hdel hu hx, unfoldDefinition_WScoped m.wf hu hws,
    unfoldDefinition_looseBVars m.wf hu hb,
    fun l hl => hLb l (unfoldDefinition_fvarLeaves m.wf hu l hl),
    hC.of_subset (unfoldDefinition_fvarLeaves m.wf hu)⟩

/-! ## T3 — the step dispatcher

`defeqStep_claim2D`'s transpose.  Every `denote2_fuelMono` and every
`CtxOk2D.fuelMono` in the original had exactly one job — reconciling
two readings taken at two fuels — and in the P currency there is one
reading, so all of them disappear together with the `max Fa Fb` join.
What is left is the checker's own case tree. -/

/-- `Expr.isBoolTrue` reads exactly the constant `Bool.true`. -/
private theorem isBoolTrue_iff {e : Expr} :
    e.isBoolTrue = true ↔ e = .const ConLeche.boolTrueName [] := by
  cases e <;> (try cases ‹List Level›) <;> simp [Expr.isBoolTrue]

/-- **`DefEqStepAt`**, modulo the routed obligations. -/
theorem defeqStep_claim {m : EnvModel V env} {fuel : Nat}
    (hex : WhnfCoreReductExists μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel)
    (ihw : WhnfClaim μ m φ fuel)
    (hdel : DenoteMetaDelta m φ)
    (hnat : ReduceNatStepPQ μ m φ fuel) (hpi : PropIrrelPQ μ m φ fuel)
    (hstk : DefEqStuck μ m φ fuel)
    (hspine : DefEqSpine μ m φ fuel) :
    DefEqStepAt μ m φ fuel := by
  intro d k hk pi a b Δa h hwa hba hLa hwb hbb hLb aa ba hCa hCb
    hda hdb hokA hokB ρ hρ
  have h0 := h
  simp only [defeqStep, Bind.bind, Except.bind, ConLeche.whnfCore_def,
    ConLeche.propIrrel_fold, ConLeche.reduceNat_fold,
    ConLeche.boolTrueShortcut_fold,
    ConLeche.defeqSpine_fold, ConLeche.stuckIrrel_fold,
    ConLeche.defeq_def] at h
  split at h
  · -- the syntactic fast path
    next hab =>
    obtain rfl : a = b := eq_of_beq hab
    obtain rfl : aa = ba := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  · -- the eq-true shortcut (E2): a `true` verdict is `whnf a = Bool.true
    -- = b`, closed by the whnf claim at the reduct's own reading (`b`'s)
    cases hbt : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcutFueled μ env fuel d a else pure false) with
    | error err => rw [hbt] at h; exact nomatch h
    | ok rbt =>
    rw [hbt] at h
    dsimp only at h
    cases rbt with
    | true =>
      have hbt' : ConLeche.boolTrueShortcutFueled μ env fuel d a = .ok true ∧
          b.isBoolTrue = true := by
        split at hbt
        · next hc =>
          simp only [Bool.and_eq_true] at hc
          exact ⟨hbt, hc.1.2⟩
        · exact nomatch hbt
      obtain ⟨hsc, hbtrue⟩ := hbt'
      simp only [ConLeche.boolTrueShortcutFueled, ConLeche.boolTrueShortcut, Bind.bind,
        Except.bind, ConLeche.whnf_def] at hsc
      cases hw : ConLeche.whnf μ env fuel d a with
      | error err => rw [hw] at hsc; exact nomatch hsc
      | ok w =>
      rw [hw] at hsc
      simp only [pure, Except.pure, Except.ok.injEq] at hsc
      obtain rfl : w = b := by
        rw [isBoolTrue_iff] at hsc hbtrue
        rw [hsc, hbtrue]
      exact (ihw hw hwa hba hLa hCa hda hdb hokA).2 ρ hρ
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hwca : whnfCore μ env fuel d a with
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
      dq_whnfCore_package m hex ihwc hwca hwa hba hLa hCa hda hokA
    obtain ⟨ba', hdb', hokB', hEb, hwb', hbb', hLb', hCb'⟩ :=
      dq_whnfCore_package m hex ihwc hwcb hwb hbb hLb hCb hdb hokB
    have hEA := hEa ρ hρ
    have hEB := hEb ρ hρ
    -- from here every verdict is the middle equation
    suffices hmid : interp V ρ aa' = interp V ρ ba' from
      (hEA.trans hmid).trans hEB.symm
    clear hEA hEB hEa hEb hda hdb hokA hokB hCa hCb
    split at h
    · next hab' =>
      obtain rfl : a' = b' := eq_of_beq hab'
      obtain rfl : aa' = ba' := by
        rw [hda'] at hdb'; exact Option.some.inj hdb'
      rfl
    · -- proof irrelevance, once per entry (the audit's D3): the gate is
      -- `pi`, and only a `true` verdict is consumed
      cases hir : (if pi && !a'.quickPair b' then
          ConLeche.propIrrelFueled μ env fuel d a' b' else pure false) with
      | error err => rw [hir] at h; exact nomatch h
      | ok r =>
      rw [hir] at h
      dsimp only at h
      cases r with
      | true =>
        have hir' : ConLeche.propIrrelFueled μ env fuel d a' b' = .ok true := by
          split at hir
          · exact hir
          · exact nomatch hir
        exact hpi hir' hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
          hdb' hokA' hokB' ρ hρ
      | false =>
        cases hna : (if !a'.hasFvar && !b'.hasFvar then
            ConLeche.reduceNatFueled μ env fuel d a' else pure none) with
        | error err => rw [hna] at h; exact nomatch h
        | ok o₁ =>
        rw [hna] at h
        dsimp only at h
        match o₁, hna, h with
        | some a₂, hna, h =>
          have hred : ConLeche.reduceNatFueled μ env fuel d a'
              = .ok (some a₂) := by
            split at hna
            · exact hna
            · exact nomatch hna
          obtain ⟨w, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwa' hba' hLa' hCa' hda' hokA'
          exact (hEw ρ hρ).trans
            (hk true h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hw hdb' hokw
              hokB' ρ hρ)
        | none, hna, h =>
        dsimp only at h
        cases hnb : (if !a'.hasFvar && !b'.hasFvar then
            ConLeche.reduceNatFueled μ env fuel d b' else pure none) with
        | error err => rw [hnb] at h; exact nomatch h
        | ok o₂ =>
        rw [hnb] at h
        dsimp only at h
        match o₂, hnb, h with
        | some b₂, hnb, h =>
          have hred : ConLeche.reduceNatFueled μ env fuel d b'
              = .ok (some b₂) := by
            split at hnb
            · exact hnb
            · exact nomatch hnb
          obtain ⟨w, hw, hokw, hEw, hw2, hb2, hL2, hC2⟩ :=
            hnat hred hwb' hbb' hLb' hCb' hdb' hokB'
          exact (hk true h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hw
            hokA' hokw ρ hρ).trans (hEw ρ hρ).symm
        | none, hnb, h =>
        cases hha : ConLeche.unfoldableHead env a' <;>
          cases hhb : ConLeche.unfoldableHead env b' <;>
          rw [hha, hhb] at h <;> dsimp only at h
        · -- neither head unfolds: the stuck configuration
          exact hstk h0 (by simpa using ‹¬(a == b) = true›) hbt hwca
            hwcb (by simpa using ‹¬(a' == b') = true›) hir hna hnb
            hha hhb hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hda'
            hdb' hokA' hokB' ρ hρ
        · cases hub : ConLeche.unfoldDefinition env b' with
          | none => rw [hub] at h; exact nomatch h
          | some b₂ =>
            rw [hub] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              dq_delta_package hdel hub hwb' hbb' hLb' hCb' hdb'
            exact hk false h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda' hd2
              hokA' hokB' ρ hρ
        · cases hua : ConLeche.unfoldDefinition env a' with
          | none => rw [hua] at h; exact nomatch h
          | some a₂ =>
            rw [hua] at h
            obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
              dq_delta_package hdel hua hwa' hba' hLa' hCa' hda'
            exact hk false h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2 hdb'
              hokA' hokB' ρ hρ
        · have hboth : ∀ {x : CheckM Bool},
              (match ConLeche.unfoldDefinition env a',
                  ConLeche.unfoldDefinition env b' with
                | some a₂, some b₂ => k false a₂ b₂
                | _, _ => pure false) = .ok true →
              interp V ρ aa' = interp V ρ ba' := by
            intro x hbb2
            cases hua : ConLeche.unfoldDefinition env a' with
            | none => rw [hua] at hbb2; exact nomatch hbb2
            | some a₂ =>
            cases hub : ConLeche.unfoldDefinition env b' with
            | none => rw [hua, hub] at hbb2; exact nomatch hbb2
            | some b₂ =>
              rw [hua, hub] at hbb2
              obtain ⟨hdA, hwA, hbA, hLA, hCA⟩ :=
                dq_delta_package hdel hua hwa' hba' hLa' hCa' hda'
              obtain ⟨hdB, hwB, hbB, hLB, hCB⟩ :=
                dq_delta_package hdel hub hwb' hbb' hLb' hCb' hdb'
              exact hk false hbb2 hwA hbA hLA hwB hbB hLB hCA hCB hdA hdB
                hokA' hokB' ρ hρ
          cases hlt1 : ConLeche.ReducibilityHint.lt
              (ConLeche.headHint env b') (ConLeche.headHint env a') <;>
            rw [hlt1] at h
          · cases hlt2 : ConLeche.ReducibilityHint.lt
                (ConLeche.headHint env a') (ConLeche.headHint env b') <;>
              rw [hlt2] at h
            · cases hsr : (ConLeche.ReducibilityHint.sameRegular
                    (ConLeche.headHint env a') (ConLeche.headHint env b') &&
                  ConLeche.sameConstHeads a' b') <;> rw [hsr] at h
              · exact hboth (x := pure false) h
              · cases hsp : ConLeche.defeqSpineFueled μ env fuel d a' b' with
                | error err => rw [hsp] at h; exact nomatch h
                | ok r' =>
                rw [hsp] at h
                dsimp only at h
                cases r' with
                | true =>
                  exact hspine hsp hwa' hba' hLa' hwb' hbb' hLb'
                    hCa' hCb' hda' hdb' hokA' hokB' ρ hρ
                | false => exact hboth (x := pure false) h
            · cases hub : ConLeche.unfoldDefinition env b' with
              | none => rw [hub] at h; exact nomatch h
              | some b₂ =>
                rw [hub] at h
                obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                  dq_delta_package hdel hub hwb' hbb' hLb' hCb' hdb'
                exact hk false h hwa' hba' hLa' hw2 hb2 hL2 hCa' hC2 hda'
                  hd2 hokA' hokB' ρ hρ
          · cases hua : ConLeche.unfoldDefinition env a' with
            | none => rw [hua] at h; exact nomatch h
            | some a₂ =>
              rw [hua] at h
              obtain ⟨hd2, hw2, hb2, hL2, hC2⟩ :=
                dq_delta_package hdel hua hwa' hba' hLa' hCa' hda'
              exact hk false h hw2 hb2 hL2 hwb' hbb' hLb' hC2 hCb' hd2
                hdb' hokA' hokB' ρ hρ

/-! ## T4 — the binder congruence's two premises -/

/-- An application's argument frame, P currency (`frame_appArg2D`). -/
private theorem dq_frame_appArg {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {f x : Expr}
    (hws : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f x))
    (hC : CtxOk m φ d Δa (.app f x)) :
    Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2,
    fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]), hC.app_arg⟩

/-- **The binder congruence's two premises, P currency.**
`binder_congr2D` verbatim modulo the currency: the opened contexts are
`CtxOk.openS` on the left (its own domain) and `CtxOk.openCongC` on
the right (the *left* domain, across the domains' semantic agreement),
and `hdom` — `ihd`'s own conclusion — is computed once and used for
both the congruence's first component and `openCongC`'s transport.

The gradings come in at `WellDenotedV`, which is what `CtxOk`'s leaf
package and `DefEqClaim`'s premises both speak. -/
theorem binder_congr {m : EnvModel V env} {fuel : Nat}
    (ihd : DefEqClaim μ m φ fuel)
    {d : Nat} {Δa : List AnnotTerm}
    {ty₁ bd₁ ty₂ bd₂ : Expr} {ta₁ ba₁ ta₂ ba₂ : AnnotTerm}
    (hdt : isDefEqCore μ env fuel d ty₁ ty₂ = .ok true)
    (hdd : isDefEqCore μ env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d ty₂))
      (bd₂.instantiate1 (.fvar d ty₂)) = .ok true)
    (hwt₁ : Expr.WScoped d ty₁) (hbt₁ : ty₁.looseBVarsBounded 0 = true)
    (hLt₁ : Expr.LeavesBounded ty₁)
    (hCt₁ : CtxOk m φ d Δa ty₁)
    (hwb₁ : Expr.WScoped d bd₁) (hbb₁ : bd₁.looseBVarsBounded 1 = true)
    (hLb₁ : Expr.LeavesBounded bd₁)
    (hCb₁ : CtxOk m φ d Δa bd₁)
    (hwt₂ : Expr.WScoped d ty₂) (hbt₂ : ty₂.looseBVarsBounded 0 = true)
    (hLt₂ : Expr.LeavesBounded ty₂)
    (hCt₂ : CtxOk m φ d Δa ty₂)
    (hwb₂ : Expr.WScoped d bd₂) (hbb₂ : bd₂.looseBVarsBounded 1 = true)
    (hLb₂ : Expr.LeavesBounded bd₂)
    (hCb₂ : CtxOk m φ d Δa bd₂)
    (hta₁ : denoteMeta m.acval env φ d ty₁ = some ta₁)
    (hva₁ : denoteMeta m.acval env φ (d + 1)
      (bd₁.instantiate1 (.fvar d ty₁)) = some ba₁)
    (hta₂ : denoteMeta m.acval env φ d ty₂ = some ta₂)
    (hva₂ : denoteMeta m.acval env φ (d + 1)
      (bd₂.instantiate1 (.fvar d ty₂)) = some ba₂)
    (hoT₁ : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ ta₁)
    (hoT₂ : ∀ σ : Nat → V, Sat V Δa σ → WellDenotedV V σ ta₂)
    (hoB₁ : ∀ σ : Nat → V, Sat V (ta₁ :: Δa) σ → WellDenotedV V σ ba₁)
    (hoB₂ : ∀ σ : Nat → V, Sat V (ta₂ :: Δa) σ → WellDenotedV V σ ba₂)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ ta₁ = interp V ρ ta₂ ∧
      ∀ x, x ∈ˢ interp V ρ ta₁ →
        interp V (cons x ρ) ba₁ = interp V (cons x ρ) ba₂ := by
  have hdom : ∀ σ : Nat → V, Sat V Δa σ →
      interp V σ ta₁ = interp V σ ta₂ :=
    ihd hdt hwt₁ hbt₁ hLt₁ hwt₂ hbt₂ hLt₂ hCt₁ hCt₂ hta₁ hta₂
      hoT₁ hoT₂
  -- The run opens BOTH bodies with the right binder's local (official
  -- `is_def_eq_binding`, task #201); the left body's denotation is
  -- read off its own opening — `denoteMeta` reads an fvar's index only.
  have hva₁' : denoteMeta m.acval env φ (d + 1)
      (bd₁.instantiate1 (.fvar d ty₂)) = some ba₁ := by
    rw [denoteMeta_erasedEq (Expr.ErasedEq.instantiate1
      (Expr.ErasedEq.rfl bd₁)
      (show Expr.ErasedEq (.fvar d ty₂) (.fvar d ty₁) from rfl))]
    exact hva₁
  have hLo₁ : Expr.LeavesBounded
      (bd₁.instantiate1 (.fvar d ty₂)) := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bd₁ 0 hl with h2 | h2
    · exact hLb₁ l h2
    · rw [Expr.fvarLeaves] at h2
      rcases List.mem_cons.mp h2 with rfl | h3
      · exact hbt₂
      · exact hLt₂ l h3
  have hLo₂ : Expr.LeavesBounded
      (bd₂.instantiate1 (.fvar d ty₂)) := by
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
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₁)
    (ConLeche.looseBVarsBounded_instantiate1 bd₁ 0 hbb₁) hLo₁
    (Expr.WScoped.instantiate1 hwt₂ 0 hwb₂)
    (ConLeche.looseBVarsBounded_instantiate1 bd₂ 0 hbb₂) hLo₂
    (CtxOk.openCongC hCb₁ hCt₂ hta₂ hoT₂ hdom)
    (CtxOk.openCongC hCb₂ hCt₂ hta₂ hoT₂ hdom)
    hva₁' hva₂ hoB₁
    (fun σ hσ => hoB₂ σ (Sat.head_congr hdom hσ)) (cons x ρ)
    (Sat_cons V hρ hx)

/-! ## T5 — the stuck configuration, seventeen cases

`AcvalParams2` mentions no reading at all (it is a statement about
`m.acval` and two valuations), so it is consumed with its body
verbatim — only its carrier moves, to `AcvalParams`/`acvalParams`
over `EnvModel` (`Annot/EnvModel.lean`, batch 8).  Its consumer
moves too. -/

/-- The same constant at level-equivalent instantiations has one
validated reading (`acval_const_congr2`, fuel-free). -/
theorem acval_const_congr {m : EnvModel V env} (hap : AcvalParams m)
    {d : Nat} {n : Name} {us us' : List Level} {aa ba : AnnotTerm}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denoteMeta m.acval env φ d (.const n us) = some aa)
    (hdb : denoteMeta m.acval env φ d (.const n us') = some ba) :
    aa = ba := by
  rw [denoteMeta] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine hap n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-- **`DefEqStuck`** — the seventeen cases, P currency.

`hbs : BinderSortAgree2A` is **gone**.  Its two uses were the
`obtain rfl : v₁ = v₂` lines in cases 11 and 12; each is replaced by
the run's own certificate, extracted from the ok-true tail of the
binder arm at `hμ : μ.verifiedChecks = true` and turned into an equation by
`eq_of_beq`.  Nothing else in the block changes shape. -/
theorem defeqStuck_claim {m : EnvModel V env} {fuel : Nat}
    (hμ : μ.verifiedChecks = true)
    (ihd : DefEqClaim μ m φ fuel) (hsi : StuckIrrelPQ μ m φ fuel)
    (hstr : DenotePStrLit m φ) (hap : AcvalParams m)
    (happ : AppCongrStuck μ m φ fuel) (heta : EtaCertStep μ m φ fuel) :
    DefEqStuck μ m φ fuel := by
  intro d Δa _k _pi a b a' b' h hab hbt hwca hwcb hab' hir hna hnb hha hhb
    hwa hba hLa hwb hbb hLb aa' ba' hCa hCb hda hdb hokA hokB ρ hρ
  simp only [defeqStep, Bind.bind, Except.bind, ConLeche.whnfCore_def,
    ConLeche.propIrrel_fold, ConLeche.reduceNat_fold,
    ConLeche.boolTrueShortcut_fold,
    ConLeche.defeqSpine_fold, ConLeche.stuckIrrel_fold, ConLeche.defeq_def,
    ConLeche.defEqList_fold, ConLeche.etaCert_fold] at h
  rw [if_neg (by simpa using hab), hbt] at h
  dsimp only at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [hwca] at h
  dsimp only at h
  rw [hwcb] at h
  dsimp only at h
  rw [if_neg (by simpa using hab'), hir] at h
  dsimp only at h
  rw [hna] at h
  dsimp only at h
  rw [hnb] at h
  dsimp only at h
  rw [hha, hhb] at h
  simp only [Bool.false_eq_true, if_false] at h
  have hfall : ConLeche.stuckIrrelFueled μ env fuel d a' b' = .ok true →
      interp V ρ aa' = interp V ρ ba' := fun hs =>
    hsi hs hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA hokB ρ hρ
  clear hab hbt hwca hwcb hab' hir hna hnb hha hhb hsi
  split at h
  -- 1: sort/sort
  · rename_i u v
    rw [denoteMeta_sort] at hda hdb
    obtain rfl : aa' = AnnotTerm.sort (u.eval φ) :=
      (Option.some.inj hda).symm
    obtain rfl : ba' = AnnotTerm.sort (v.eval φ) :=
      (Option.some.inj hdb).symm
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; exact nomatch h
    | some r =>
      rw [hle] at h
      dsimp only [ConLeche.liftFueled] at h
      cases r with
      | false => exact nomatch h
      | true => rw [Level.isEquiv_sound hle φ]
  -- 2: lit/lit
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    obtain rfl : aa' = ba' := by
      rw [hda] at hdb; exact Option.some.inj hdb
    rfl
  -- 3: `lit 0` against `Nat.zero`
  · rename_i n c us
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv hda
      rw [denoteMeta_natZeroConst hg] at hdb
      obtain rfl : ba' = m.acval ConLeche.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 4: `Nat.zero` against `lit 0`
  · rename_i c us n
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl⟩ := hcond
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv hdb
      rw [denoteMeta_natZeroConst hg] at hda
      obtain rfl : aa' = m.acval ConLeche.natZeroName
        (Level.substFn φ [] []) := (Option.some.inj hda).symm
      rfl
    · exact hfall h
  -- 5: `lit (k+1)` against a `Nat.succ` application
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv hda
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denoteMeta_app_inv hdb
        rw [denoteMeta_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval ConLeche.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := dq_frame_appArg hwb hbb hLb hCb
        refine deqStep_appCong rfl
          (ihd h (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hwx hbx hLx
            (CtxOk.of_fvarLeaves_nil hCa.length
              (by simp [Expr.fvarLeaves]))
            hCx (denoteMeta_natLit hg) hxa (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA1 := (hokA σ hσ).1
          have hA2 := (hokA σ hσ).2
          simp only [natLitAV, WellDenoted_app] at hA1
          simp only [natLitAV, AnnotValid_app] at hA2
          exact ⟨hA1.2.1, hA2.2⟩
        · have hB1 := (hokB σ hσ).1
          have hB2 := (hokB σ hσ).2
          rw [WellDenoted_app] at hB1
          rw [AnnotValid_app] at hB2
          exact ⟨hB1.2.1, hB2.2⟩
      · exact hfall h
    · exact hfall h
  -- 6: a `Nat.succ` application against `lit (k+1)`
  · split at h
    · split at h
      · next hc =>
        subst hc
        obtain ⟨hg, rfl⟩ := denoteMeta_natLit_inv hdb
        obtain ⟨fa, xa, hfa, hxa, rfl⟩ := denoteMeta_app_inv hda
        rw [denoteMeta_natSuccConst hg] at hfa
        obtain rfl : fa = m.acval ConLeche.natSuccName
          (Level.substFn φ [] []) := (Option.some.inj hfa).symm
        obtain ⟨hwx, hbx, hLx, hCx⟩ := dq_frame_appArg hwa hba hLa hCa
        refine deqStep_appCong rfl
          (ihd h hwx hbx hLx (Expr.WScoped.of_not_hasFvar rfl) rfl
            (Expr.LeavesBounded.of_not_hasFvar rfl) hCx
            (CtxOk.of_fvarLeaves_nil hCb.length
              (by simp [Expr.fvarLeaves]))
            hxa (denoteMeta_natLit hg) (fun σ hσ => ?_)
            (fun σ hσ => ?_) ρ hρ)
        · have hA1 := (hokA σ hσ).1
          have hA2 := (hokA σ hσ).2
          rw [WellDenoted_app] at hA1
          rw [AnnotValid_app] at hA2
          exact ⟨hA1.2.1, hA2.2⟩
        · have hB1 := (hokB σ hσ).1
          have hB2 := (hokB σ hσ).2
          simp only [natLitAV, WellDenoted_app] at hB1
          simp only [natLitAV, AnnotValid_app] at hB2
          exact ⟨hB1.2.1, hB2.2⟩
      · exact hfall h
    · exact hfall h
  -- 7: a string literal against a `String.ofList` application
  · rename_i st cO usO x
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr d st hg hda
      exact ihd h hwc hbc hLc hwb hbb hLb
        (CtxOk.of_fvarLeaves_nil hCa.length hnil) hCb hdc hdb
        hokA hokB ρ hρ
    · exact hfall h
  -- 8: a `String.ofList` application against a string literal
  · rename_i cO usO x st
    split at h
    · next hcond =>
      obtain ⟨rfl, rfl, hg⟩ := hcond
      obtain ⟨hdc, hwc, hbc, hLc, hnil⟩ := hstr d st hg hdb
      exact ihd h hwa hba hLa hwc hbc hLc hCa
        (CtxOk.of_fvarLeaves_nil hCb.length hnil) hda hdc hokA
        hokB ρ hρ
    · exact hfall h
  -- 9: the same de Bruijn level
  · rename_i i t₁ j t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      rw [denoteMeta_fvar] at hda hdb
      obtain rfl : aa' = AnnotTerm.bvar (d - 1 - i) :=
        (Option.some.inj hda).symm
      obtain rfl : ba' = AnnotTerm.bvar (d - 1 - i) :=
        (Option.some.inj hdb).symm
      rfl
    · exact hfall h
  -- 10: the same constant at level-equivalent instantiations
  · rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [ConLeche.liftFueled] at h
        cases r with
        | false => exact hfall h
        | true =>
          obtain rfl : aa' = ba' := acval_const_congr hap hle hda hdb
          rfl
    · exact hfall h
  -- 11: ∀-congruence
  · rename_i ty₁ bd₁ mb₁ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_forallE_inv hda
      obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_forallE_inv hdb
      have hbd : isDefEqCore μ env fuel (d + 1)
          (bd₁.instantiate1 (Expr.fvar d ty₂))
          (bd₂.instantiate1 (Expr.fvar d ty₂)) = .ok true := by
        revert h
        cases hbd0 : isDefEqCore μ env fuel (d + 1)
            (bd₁.instantiate1 (Expr.fvar d ty₂))
            (bd₂.instantiate1 (Expr.fvar d ty₂)) with
        | error err => intro h; exact nomatch h
        | ok rb =>
          intro h
          dsimp only at h
          cases rb with
          | false => simp [pure, Except.pure] at h
          | true => rfl
      -- THE KEY DELTA: the run's own certificate, in place of `hbs.1`
      have hq : (mb₁.pw == mb₂.pw) = true := by
        by_cases hq0 : (mb₁.pw == mb₂.pw) = true
        · exact hq0
        · exfalso
          have hq1 : (mb₁.pw == mb₂.pw) = false := by
            simpa using hq0
          rw [hbd] at h
          dsimp only at h
          rw [hμ, hq1] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      have hpw : pwBit φ mb₁.pw = pwBit φ mb₂.pw := by
        rw [eq_of_beq hq]
      obtain ⟨hoT₁, hoB₁⟩ := hoist_pi hokA
      obtain ⟨hoT₂, hoB₂⟩ := hoist_pi hokB
      obtain ⟨hDA, hDB⟩ := binder_congr ihd hdt hbd
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.forallE_ty
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.forallE_body
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.forallE_ty
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.forallE_body
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      rw [hpw]
      exact deqStep_piCong hDA hDB
  -- 12: λ-congruence
  · rename_i ty₁ bd₁ mb₁ ty₂ bd₂ mb₂
    cases hdt : isDefEqCore μ env fuel d ty₁ ty₂ with
    | error err => rw [hdt] at h; exact nomatch h
    | ok r =>
    rw [hdt] at h
    cases r with
    | false => exact nomatch h
    | true =>
      dsimp only at h
      simp only [Expr.WScoped] at hwa hwb
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba hbb
      obtain ⟨ta₁, ba₁, hta₁, hva₁, rfl⟩ := denoteMeta_lam_inv hda
      obtain ⟨ta₂, ba₂, hta₂, hva₂, rfl⟩ := denoteMeta_lam_inv hdb
      have hbd : isDefEqCore μ env fuel (d + 1)
          (bd₁.instantiate1 (Expr.fvar d ty₂))
          (bd₂.instantiate1 (Expr.fvar d ty₂)) = .ok true := by
        revert h
        cases hbd0 : isDefEqCore μ env fuel (d + 1)
            (bd₁.instantiate1 (Expr.fvar d ty₂))
            (bd₂.instantiate1 (Expr.fvar d ty₂)) with
        | error err => intro h; exact nomatch h
        | ok rb =>
          intro h
          dsimp only at h
          cases rb with
          | false => simp [pure, Except.pure] at h
          | true => rfl
      -- THE KEY DELTA: the run's own certificate, in place of `hbs.2`
      have hq : (mb₁.pw == mb₂.pw) = true := by
        by_cases hq0 : (mb₁.pw == mb₂.pw) = true
        · exact hq0
        · exfalso
          have hq1 : (mb₁.pw == mb₂.pw) = false := by
            simpa using hq0
          rw [hbd] at h
          dsimp only at h
          rw [hμ, hq1] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      have hpw : pwBit φ mb₁.pw = pwBit φ mb₂.pw := by
        rw [eq_of_beq hq]
      obtain ⟨hoT₁, hoB₁⟩ := hoist_lam hokA
      obtain ⟨hoT₂, hoB₂⟩ := hoist_lam hokB
      obtain ⟨hDA, hDB⟩ := binder_congr ihd hdt hbd
        hwa.1 hba.1 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.lam_ty
        hwa.2 hba.2 (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
        hCa.lam_body
        hwb.1 hbb.1 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.lam_ty
        hwb.2 hbb.2 (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
        hCb.lam_body
        hta₁ hva₁ hta₂ hva₂ hoT₁ hoT₂ hoB₁ hoB₂ ρ hρ
      rw [hpw]
      exact deqStep_lamCong hDA hDB
  -- 13: the stuck spine congruence
  · rename_i f₁ a₁ f₂ a₂
    split at h
    · next hlen =>
      cases hhd : isDefEqCore μ env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : ConLeche.defEqListFueled μ env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true =>
          exact happ hhd hls hlen hwa hba hLa hwb hbb hLb hCa hCb
            hda hdb hokA hokB ρ hρ
    · exact hfall h
  -- 14: the stuck projection congruence
  · rename_i s₁ i₁ e₁ s₂ i₂ e₂
    split at h
    · next hii =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hii
      obtain ⟨rfl, rfl⟩ := hii
      cases hde : isDefEqCore μ env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok r =>
      rw [hde] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        -- both nodes carry the same struct name and index (the W5
        -- congruence guard), so both readings take the same entry
        -- kind: `.fst`/`.snd` at a pair-backed entry, `projAV i` at a
        -- tower-backed one — each a congruence in the subject's value
        obtain ⟨ia₁, he₁, hrd₁⟩ := denoteMeta_proj_inv hda
        obtain ⟨ia₂, he₂, hrd₂⟩ := denoteMeta_proj_inv hdb
        simp only [Expr.WScoped] at hwa hwb
        simp only [Expr.looseBVarsBounded] at hba hbb
        rcases hrd₁ with ⟨entry, hfe, rfl⟩ | ⟨hnt, hdec₁⟩
        · rcases hrd₂ with ⟨entry', hfe', rfl⟩ | ⟨hnt', -⟩
          · obtain rfl : entry = entry' := Option.some.inj (hfe.symm.trans hfe')
            exact interp_projAV_congr (ihd hde hwa hba
              (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
              hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
              hCa.proj_arg hCb.proj_arg he₁ he₂
              (fun σ hσ => WellDenotedV_projAV_hoist (hokA σ hσ))
              (fun σ hσ => WellDenotedV_projAV_hoist (hokB σ hσ)) ρ hρ)
          · rw [hnt'] at hfe; exact nomatch hfe
        · rcases hrd₂ with ⟨entry', hfe', -⟩ | ⟨-, hdec₂⟩
          · rw [hnt] at hfe'; exact nomatch hfe'
          · rcases AnnotTerm.projPair?_cases₂ hdec₁ hdec₂ with
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact deqStep_fstCong (ihd hde hwa hba
                (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                hCa.proj_arg hCb.proj_arg
                he₁ he₂ (hoist_fst hokA) (hoist_fst hokB) ρ hρ)
            · exact deqStep_sndCong (ihd hde hwa hba
                (fun l hl => hLa l (by simp [Expr.fvarLeaves, hl]))
                hwb hbb (fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]))
                hCa.proj_arg hCb.proj_arg
                he₁ he₂ (hoist_snd hokA) (hoist_snd hokB) ρ hρ)
    · exact hfall h
  -- 15: one-sided λ on the left
  · rename_i ty₁ bd₁ mb₁ hnl
    cases he : ConLeche.etaCertFueled μ env fuel d ty₁ bd₁ mb₁ b' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact heta he hwa hba hLa hwb hbb hLb hCa hCb hda hdb hokA
        hokB ρ hρ
    | false => exact hfall h
  -- 16: one-sided λ on the right
  · rename_i ty₂ bd₂ mb₂ hnl
    cases he : ConLeche.etaCertFueled μ env fuel d ty₂ bd₂ mb₂ a' with
    | error err => rw [he] at h; exact nomatch h
    | ok r =>
    rw [he] at h
    dsimp only at h
    cases r with
    | true =>
      exact (heta he hwb hbb hLb hwa hba hLa hCb hCa hdb hda hokB
        hokA ρ hρ).symm
    | false => exact hfall h
  -- 17: distinct stuck heads
  · exact hfall h

/-! ## T6 — the quarter

`defEqStep2D_of`'s transpose.  Two things move.

* The ten routed residues are bundled into `DefEqInputs` rather than
  spelled as ten hypotheses: at this width the list is the noise and
  the structure is the signal, and a consumer that discharges one
  residue can update one field.
* `μ.verifiedChecks = true` is a hypothesis of the **step**, not of the
  claims.  `DefEqClaim` stays mode-generic — it must, it is frozen
  text — and the mode pin sits exactly where the validation conjuncts
  are read, which is `defeqStuck_claim`'s two binder cases.  This is
  the same discipline the infer quarter's `infer_forallE_claim`
  already follows.

`hap : AcvalParams` is kept in the structure for symmetry with the D
lane's hypothesis list even though `acvalParams` discharges it
outright from the `EnvModelU` field. -/

/-- The quarter's deliverable: the four P claims at `fuel` give the
defeq claim at `fuel + 1`. -/
def DefEqStep (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    DefEqClaim μ m φ (fuel + 1)

/-- **The quarter's routed inputs**, one field per residue.  Eight are
the D lane's own list transposed; two — `hex` and `hdel` — are the
dual-success currency's price (see the module docstring). -/
structure DefEqInputs (μ : CheckMode) (V : Type w) [SetTheory V] :
    Prop where
  /-- **New at the P tier.**  The `whnfCore` reduct annotates. -/
  hex : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), WhnfCoreReductExists μ m φ fuel
  /-- Residue 2 — the delta identity, fuel-free. -/
  hdel : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat),
    DenoteMetaDelta m φ
  /-- Residue 4 — the literal acceleration. -/
  hnat : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), ReduceNatStepPQ μ m φ fuel
  /-- Residue 3 — proof irrelevance at the hoist: the `Prop` branch
  (task #168, Option U). -/
  hpi : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), PropIrrelPQ μ m φ fuel
  /-- Residue 5 — the same-head spine short-circuit. -/
  hspine : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), DefEqSpine μ m φ fuel
  /-- Residue 6 — `stuckIrrel`. -/
  hsi : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), StuckIrrelPQ μ m φ fuel
  /-- Residue 7 — the string-literal expansion. -/
  hstr : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat),
    DenotePStrLit m φ
  /-- Residue 8 — the canonical valuation is level-insensitive.
  Discharged by `acvalParams`; kept for symmetry. -/
  hap : ∀ (env : Env) (m : EnvModel V env), AcvalParams m
  /-- Residue 10 — the stuck spine congruence. -/
  happ : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), AppCongrStuck μ m φ fuel
  /-- Residue 11 — the η certificate. -/
  heta : ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), EtaCertStep μ m φ fuel

/-- **The defeq quarter, P currency.**  Ten routed residues and one
mode pin; **no `BinderSortAgree`** — residue 9's successor is the run's
own `==` certificate, read at `hμ` inside `defeqStuck_claim`. -/
theorem defEqStep_of (hμ : μ.verifiedChecks = true)
    (hin : DefEqInputs μ V) : DefEqStep μ V := by
  intro env m φ fuel ihwc ihw ihd _ihi
  exact defeq_claims
    (defeqStep_claim (hin.hex env m φ fuel) ihwc ihw (hin.hdel env m φ)
      (hin.hnat env m φ fuel) (hin.hpi env m φ fuel)
      (defeqStuck_claim hμ ihd (hin.hsi env m φ fuel)
        (hin.hstr env m φ) (hin.hap env m) (hin.happ env m φ fuel)
        (hin.heta env m φ fuel))
      (hin.hspine env m φ fuel))

end ConLeche.Model
