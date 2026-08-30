import Setlec.SetR.Interp2.Claims2E
import Setlec.SetR.Interp2.Step2.Fuel

/-!
# Generation six against generation five — the exact factorisation

**The finding this file mechanizes.**  `Claims2E` is `Claims2D` with
the produced annotation moved into the premises.  That move is exactly
a *factorisation*, and the factor it removes has a name:

```
    Claims2D  ⟺  Claims2E  ∧  Exists2E
```

Both directions are proved below, at each of the four claims.  So
generation six does not weaken the family and does not strengthen it:
it **splits** it, into *agreement* (the `…2E` claims, dual success)
and *existence* (`…Exists2E`, the existential half alone).

## Why the split is the whole story

Seal 29 predicted that under dual success "existence is localized and
agreement is distributed".  The distribution half is true and is the
content of `…2E`.  **The localization half is not delivered by
`Denote2Total`**, and the three `Exists2E` residues below are where
the shortfall becomes a signature one can read:

* `InferExists2E` concludes an annotation for the **inferred type**
  `t`.  `Denote2Total`'s conclusion is about the run's **subject** `e`
  (`t` is bound in its statement and does not occur in its
  conclusion).  Those are different terms, and at the `.app` clause
  the subject's annotation is already a premise — it is the *result*
  that is missing.
* `WhnfCoreExists2E`/`WhnfExists2E` conclude an annotation for a
  **reduct**.  No run-conditioned statement supplies it: at the
  application clause the checker computes neither `sortOfE` of the
  ∀'s domain nor `sortOfE` of its opened body (`Kernel/Core.lean`'s
  `.app` branch runs `infer`, `whnf`, `infer`, `defeq` and nothing
  else), while `denote2`'s `.pi` clause needs both.

Consequently the three residues below are *not* discharged here and
are not claimed to be discharged anywhere: within the induction they
are proved by the generation-five quarters, which is where the
existential halves live today.

## What that buys, honestly

The capstone (`Capstone2E.lean`) needs **none** of them: generation
five's own induction (`checkSound2D`) already proves the `…2D` claims
at every fuel, so the `…2E` claims follow at every fuel by the
weakening direction alone.  The residues are needed only by the
*per-quarter* route, and that is the measurement: generation six's
decomposition costs three existence residues per quarter and saves
none of generation five's fifteen.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- `denote2` is a **function** wherever it answers: two fuels that
both compute an annotation compute the same one.  This is what makes
the weakening direction free — generation six's dropped fuel ordering
is the same observation (seal 31). -/
theorem denote2_crossFuel {acval : Name → (Name → Nat) → AVExpr}
    {F G d : Nat} {e : Expr} {ea ea' : AVExpr}
    (h1 : denote2 μ acval env φ F d e = some ea)
    (h2 : denote2 μ acval env φ G d e = some ea') : ea = ea' := by
  have h1' := denote2_fuelMono (Nat.le_add_right F G) d e h1
  have h2' := denote2_fuelMono (Nat.le_add_left G F) d e h2
  rw [h1'] at h2'
  exact Option.some.inj h2'

/-! ## The existence factor, stated at each claim

Each is its `…2D` claim with the two semantic conjuncts deleted: the
existential half, alone. -/

/-- The head-normalisation existence factor. -/
def WhnfCoreExists2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnfCore μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea'

/-- The reduction-loop existence factor. -/
def WhnfExists2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {Δa : List AVExpr},
    whnf μ env fuel d e = .ok e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ea) →
      ∃ F' ea', F ≤ F' ∧
        denote2 μ m.acval env φ F' d e' = some ea'

/-- The inference existence factor — **the inferred type annotates**.
This is the shape `Denote2Total` was priced to supply and does not:
its conclusion names `e`, this one names `t`. -/
def InferExists2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {F : Nat} {ea : AVExpr},
      CtxOk2D m μ φ F d Δa e →
      denote2 μ m.acval env φ F d e = some ea →
      ∃ F' ta, F ≤ F' ∧
        denote2 μ m.acval env φ F' d t = some ta

/-- The three factors, bundled — defeq needs none, because
`DefEqClaims2D` never produced an annotation (seal 31). -/
def Exists2E (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  WhnfCoreExists2E μ m φ fuel ∧ WhnfExists2E μ m φ fuel ∧
    InferExists2E μ m φ fuel

/-! ## `Denote2Total`, and the one-word repair

`Denote2Total` (`Interp2/EnvLaws2.lean`) reads

```
    ∀ F d e t, inferTypeCore μ env F d e = .ok t →
      ∃ F' ea, denote2 μ m.acval env φ F' d e = some ea
```

— its conclusion names **`e`**, the run's *subject*; `t` is bound and
does not occur in it.  Every consumer generation six has needs the
run's *result*.  The two are independent statements: neither implies
the other, because no term is both, and **no claim in the family
concludes definedness of a subject's annotation** — all four take it
as a premise.  So `Denote2Total` as frozen has no consumer in this
family.

`Denote2TotalR` below is the repair, and it is one word: `e ↦ t`.  It
discharges the inference existence factor outright
(`inferExists2E_of_totalR`).  It does **not** discharge the two
reduction factors, and nothing of this shape can: at the `.app`
clause the missing `.pi` annotation needs `sortOfE` at the ∀'s domain
and at its opened body, and the checker's application branch runs no
sort computation on either, so there is no run to condition on. -/

/-- **The repair**: `Denote2Total` with its conclusion moved from the
run's subject to the run's result. -/
def Denote2TotalR (μ : CheckMode) {env : Env} (m : EnvS2 V env)
    (φ : Name → Nat) : Prop :=
  ∀ (F d : Nat) (e t : Expr),
    inferTypeCore μ env F d e = .ok t →
    ∃ F' ta, denote2 μ m.acval env φ F' d t = some ta

/-- The repaired law **does** discharge the inference existence
factor — the fuel ordering `F ≤ F'` is bought by `denote2_fuelMono`,
so the law needs no fuel bookkeeping of its own. -/
theorem inferExists2E_of_totalR {m : EnvS2 V env}
    (h : Denote2TotalR μ m φ) : InferExists2E μ m φ fuel := by
  intro d e t Δa hrun _ _ _ F ea _ _
  obtain ⟨F', ta, hta⟩ := h fuel d e t hrun
  exact ⟨F + F', ta, Nat.le_add_right F F',
    denote2_fuelMono (Nat.le_add_left F' F) d t hta⟩

/-! ## Direction 1 — the weakening: `…2D → …2E`

Free at every claim, and it needs nothing but `denote2_crossFuel`. -/

theorem whnfCoreClaims2E_of_2D {m : EnvS2 V env}
    (h : WhnfCoreClaims2D μ m φ fuel) :
    WhnfCoreClaims2E μ m φ fuel := by
  intro d e e' Δa hrun hws hb hLb F F' ea ea' hC hea hea' hok
  obtain ⟨F1, ea1, _, hden, hok1, heq⟩ := h hrun hws hb hLb hC hea hok
  obtain rfl : ea1 = ea' := denote2_crossFuel hden hea'
  exact ⟨hok1, heq⟩

theorem whnfClaims2E_of_2D {m : EnvS2 V env}
    (h : WhnfClaims2D μ m φ fuel) : WhnfClaims2E μ m φ fuel := by
  intro d e e' Δa hrun hws hb hLb F F' ea ea' hC hea hea' hok
  obtain ⟨F1, ea1, _, hden, hok1, heq⟩ := h hrun hws hb hLb hC hea hok
  obtain rfl : ea1 = ea' := denote2_crossFuel hden hea'
  exact ⟨hok1, heq⟩

/-- Defeq's weakening is the **fuel split** and nothing else: the two
context hypotheses and the two annotations are lifted to a common
fuel, where generation five's claim applies verbatim.  This is the
one claim that was already dual-success. -/
theorem defEqClaims2E_of_2D {m : EnvS2 V env}
    (h : DefEqClaims2D μ m φ fuel) : DefEqClaims2E μ m φ fuel := by
  intro d a b Δa hrun hwa hba hLa hwb hbb hLb F F' aa ba hCa hCb
    hden hden' hoka hokb
  exact h hrun hwa hba hLa hwb hbb hLb
    (CtxOk2D.fuelMono (Nat.le_add_right F F') hCa)
    (CtxOk2D.fuelMono (Nat.le_add_left F' F) hCb)
    (denote2_fuelMono (Nat.le_add_right F F') d a hden)
    (denote2_fuelMono (Nat.le_add_left F' F) d b hden')
    hoka hokb

theorem inferClaims2E_of_2D {m : EnvS2 V env}
    (h : InferClaims2D μ m φ fuel) : InferClaims2E μ m φ fuel := by
  intro d e t Δa hrun hws hb hLb F F' ea ta hC hea hta
  obtain ⟨F1, ta1, _, hden, hokE, hokT, hmem⟩ :=
    h hrun hws hb hLb hC hea
  obtain rfl : ta1 = ta := denote2_crossFuel hden hta
  exact ⟨hokE, hokT, hmem⟩

/-! ## Direction 2 — the recovery: `…2E ∧ Exists2E → …2D`

The existence factor supplies the witness; the dual-success claim
supplies everything said about it. -/

theorem whnfCoreClaims2D_of_2E {m : EnvS2 V env}
    (hex : WhnfCoreExists2E μ m φ fuel)
    (h : WhnfCoreClaims2E μ m φ fuel) :
    WhnfCoreClaims2D μ m φ fuel := by
  intro d e e' Δa hrun hws hb hLb F ea hC hea hok
  obtain ⟨F', ea', hle, hden⟩ := hex hrun hws hb hLb hC hea hok
  obtain ⟨hok', heq⟩ := h hrun hws hb hLb hC hea hden hok
  exact ⟨F', ea', hle, hden, hok', heq⟩

theorem whnfClaims2D_of_2E {m : EnvS2 V env}
    (hex : WhnfExists2E μ m φ fuel)
    (h : WhnfClaims2E μ m φ fuel) : WhnfClaims2D μ m φ fuel := by
  intro d e e' Δa hrun hws hb hLb F ea hC hea hok
  obtain ⟨F', ea', hle, hden⟩ := hex hrun hws hb hLb hC hea hok
  obtain ⟨hok', heq⟩ := h hrun hws hb hLb hC hea hden hok
  exact ⟨F', ea', hle, hden, hok', heq⟩

/-- Defeq recovers with **no existence factor at all** — the fuel
split is instantiated at `F' := F`. -/
theorem defEqClaims2D_of_2E {m : EnvS2 V env}
    (h : DefEqClaims2E μ m φ fuel) : DefEqClaims2D μ m φ fuel := by
  intro d a b Δa hrun hwa hba hLa hwb hbb hLb F aa ba hCa hCb
    hden hden' hoka hokb
  exact h hrun hwa hba hLa hwb hbb hLb hCa hCb hden hden' hoka hokb

theorem inferClaims2D_of_2E {m : EnvS2 V env}
    (hex : InferExists2E μ m φ fuel)
    (h : InferClaims2E μ m φ fuel) : InferClaims2D μ m φ fuel := by
  intro d e t Δa hrun hws hb hLb F ea hC hea
  obtain ⟨F', ta, hle, hta⟩ := hex hrun hws hb hLb hC hea
  obtain ⟨hokE, hokT, hmem⟩ := h hrun hws hb hLb hC hea hta
  exact ⟨F', ta, hle, hta, hokE, hokT, hmem⟩

/-- The existence factor is a *factor*: generation five's claims imply
it, so `Claims2D ⟺ Claims2E ∧ Exists2E` is an equivalence and the
split loses nothing. -/
theorem exists2E_of_claims2D {m : EnvS2 V env}
    (hwc : WhnfCoreClaims2D μ m φ fuel) (hw : WhnfClaims2D μ m φ fuel)
    (hi : InferClaims2D μ m φ fuel) : Exists2E μ m φ fuel := by
  refine ⟨?_, ?_, ?_⟩
  · intro d e e' Δa hrun hws hb hLb F ea hC hea hok
    obtain ⟨F', ea', hle, hden, -, -⟩ := hwc hrun hws hb hLb hC hea hok
    exact ⟨F', ea', hle, hden⟩
  · intro d e e' Δa hrun hws hb hLb F ea hC hea hok
    obtain ⟨F', ea', hle, hden, -, -⟩ := hw hrun hws hb hLb hC hea hok
    exact ⟨F', ea', hle, hden⟩
  · intro d e t Δa hrun hws hb hLb F ea hC hea
    obtain ⟨F', ta, hle, hta, -, -, -⟩ := hi hrun hws hb hLb hC hea
    exact ⟨F', ta, hle, hta⟩

/-- **The four claims, recovered together** — the form the quarters
consume. -/
theorem claims2D_of_2E {m : EnvS2 V env} (hex : Exists2E μ m φ fuel)
    (hwc : WhnfCoreClaims2E μ m φ fuel) (hw : WhnfClaims2E μ m φ fuel)
    (hd : DefEqClaims2E μ m φ fuel) (hi : InferClaims2E μ m φ fuel) :
    WhnfCoreClaims2D μ m φ fuel ∧ WhnfClaims2D μ m φ fuel ∧
      DefEqClaims2D μ m φ fuel ∧ InferClaims2D μ m φ fuel :=
  ⟨whnfCoreClaims2D_of_2E hex.1 hwc, whnfClaims2D_of_2E hex.2.1 hw,
    defEqClaims2D_of_2E hd, inferClaims2D_of_2E hex.2.2 hi⟩

end Setlec.SetR.Interp2
