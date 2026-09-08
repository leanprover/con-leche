module

import ConLeche.Verify.InferIOLeaves
public import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Annot.BitInstall
public import ConLeche.Model.Steps.BitLevels
import ConLeche.Semantics.Sat
public import ConLeche.Semantics.WhnfCoreLeaf
public import ConLeche.Model.ClaimsIO

public section

/-!
# The two head-normalisation quarters, P currency (task #161, P3.4)

The `…D` generation of `Steps/Whnf.lean` — `whnfCore_claims2D`,
`whnfLoop_claim2D` and the residues they consume — transposed to the
P tier: `denoteMeta` for `denoteAnnot`, `WellDenotedV` for `WellDenoted`, `CtxOk`
for `CtxOk2D`.  The systematic deltas, and what each buys:

* **the annotation fuel vanishes.**  `denoteAnnot … F d e` becomes
  `denoteMeta … d e`; with it go `denote2_fuelMono`, the `∃ F' ≥ F`
  slack, and every `CtxOk2D.fuelMono` call.  Two readings of the same
  term are now literally the same run, so reconciling them is
  `Option.some.inj` — the move this file makes a dozen times where the
  `…D` lane moved a fuel.
* **`Denote2Inst1B` is retired.**  The ζ and β clauses' substitution
  law is `denoteMeta_beta` (`Annot/BitInst.lean`), a *theorem*, so the
  quarter's routed-input list is one shorter than the `…D` lane's.
  Its two leaf premises are discharged here: `hacl` is the environment
  structure's own `acval_closed` field, and `hainst` is
  `acval_inst_self` below (`AnnotTerm.inst_eq_self` at the erasure's
  closedness — `EnvS.cval_closed` composed with `acval_erase`).
* **`Delta2B`'s level crossing is paid.**  `delta2B_of` routes
  `AcvalDefnInst`, whose statement bakes in `instantiateLevelParams`
  because the canonical reading's level crossing is two open checker
  metatheorems.  `denotePInstLevels` is an unconditional *equality*,
  so `AcvalDefnInst` is stated at the **uninstantiated** value (the
  shape `EnvModelU.acval_defn` already has, minus the fuel) and the
  instantiated form is derived — `acvalDefnInst_subst`.

## The existence factor, and why it is routed

`Claims` is **dual success** (`Claims.lean`): the reduct's
annotation is a premise, not a conclusion.  `Dual2E.lean` measured
what that costs a reduction quarter — `Claims2D ⟺ Claims2E ∧ Exists2E`
— and the measurement transposes verbatim: `whnfCore`'s application
clause reduces the *head* first, and nothing in the dual-success claim
says the head's reduct annotates.  So this quarter is handed the
existence factor back, exactly as `whnfCoreStep2E_of` is:
`WhnfCoreExists` (the head's reduct) and `InferExists` (the β
certificate's inferred type) are routed inputs, bundled with the three
clause residues in `WhnfInputs`.

`IotaStep` and `ReduceNatStep` are kept in their `…D` *producing*
shape for the same reason: both feed a continuation (`ihwc`, and the
loop's own induction) whose subject is the residue's output, so a
dual-success transpose of either would have no supplier for its own
premise.  `ProjStep` **is** dual-success — it is the claim's `.proj`
clause entire, nothing continues past it, and the weaker shape is
therefore the right obligation to route.

## Mode

`WhnfCoreStep`/`WhnfStep` carry `μ.verifiedChecks = true` for assembly
uniformity with the infer quarter (`Steps/Infer.lean`'s docstring
records why the step proofs are verified-only).  **Neither quarter's
proof reads it** — flagged here rather than dropped, because the
capstone binds the four steps at one mode hypothesis.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level BinderMeta Literal whnf
  whnfCore whnfBody whnfLoop whnfStep whnfLoopFuel pureFns
  inferTypeCore iotaRecFueled reduceNatFueled unfoldDefinition ConstantInfo
  ConstantVal ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The two leaf premises of `denoteMeta_beta`

`hacl` is a structure field; `hainst` is one composition away from
another, and is proved here once so that no clause carries it. -/

/-- `denoteMeta` has no clause for a loose `bvar` — `denote2_bvar`'s
mirror, and the `.bvar` case of the dispatcher entire. -/
theorem denoteMeta_bvar {acval : Name → (Name → Nat) → AnnotTerm}
    (d i : Nat) : denoteMeta acval env φ d (.bvar i) = none := by
  rw [denoteMeta.eq_def]

/-! ## The currency's reduction steps

`WellDenoted_zeta` / `WellDenoted_beta_pos` / `WellDenoted_beta_zero`
(`Annot/WellDenoted.lean`) are currency-level and reused verbatim for the
`WellDenoted` half.  The `AnnotValid` half rides `AnnotValid_inst0`,
whose premise is the substituend's own validity — available at each
site — and whose *transport* needs the argument's domain membership.
At kind `0` that membership is the β certificate's business
(`WellDenotedV_beta_zero` takes it, as `WellDenoted_beta_zero` does); at a
positive kind it is derivable from the subject's `WellDenoted` alone, and
`wellDenoted_beta_dom_pos` below is `WellDenoted_beta_pos`'s own derivation
of it, isolated so the P step can read it. -/

/-- **The argument is in the λ's domain**, at a positive kind, from
the application's `WellDenoted` alone.  Extracted from
`WellDenoted_beta_pos`'s proof (rigidity: the slot's product cannot be
`pt`, so `piR_dom_unique` pins its domain to the λ's own). -/
theorem wellDenoted_beta_dom_pos {v : Nat} (hv : v ≠ 0) {A b a : AnnotTerm}
    {ρ : Nat → V} (h : WellDenoted V ρ (.app (.lam v A b) a)) :
    interp V ρ a ∈ˢ interp V ρ A := by
  rw [WellDenoted_app] at h
  obtain ⟨hlam, -, v', A', B', hslot, hmem, -⟩ := h
  rw [WellDenoted_lam] at hlam
  obtain ⟨-, -, B, hfib, -⟩ := hlam
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    have h1 := eq_pt_of_mem_piR_zero hslot
    rw [interp_lam] at h1
    exact lamR_ne_pt hv h1
  have hown : interp V ρ (.lam v A b)
      ∈ˢ piR v (interp V ρ A) B := by
    rw [interp_lam]
    exact lamR_mem hfib
  rw [piR_dom_unique hv hv' hown hslot]
  exact hmem

/-- A λ's domain annotation is graded when the λ is — the fact the β
site's certificate premise reads (`WellDenoted.hoist_lam`'s P mirror, at
one valuation). -/
theorem WellDenotedV.lam_dom {v : Nat} {A b : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.lam v A b)) : WellDenotedV V ρ A := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1; rw [WellDenoted_lam] at h1; exact h1.1
  · have h2 := h.2; rw [AnnotValid_lam] at h2; exact h2.1


/-- **The graded β step at a positive kind, P currency.** -/
theorem WellDenotedV_beta_pos {v : Nat} (hv : v ≠ 0) {A b a : AnnotTerm}
    {ρ : Nat → V} (h : WellDenotedV V ρ (.app (.lam v A b) a)) :
    interp V ρ (.app (.lam v A b) a) = interp V ρ (b.inst a) ∧
      WellDenotedV V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := WellDenoted_beta_pos V hv h.1
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValid_app, AnnotValid_lam] at hv2
  exact (AnnotValid_inst0 V hv2.2).mpr
    (hv2.1.2 _ (wellDenoted_beta_dom_pos hv h.1))

/-- **The graded β step at kind `0`, P currency** — the domain
membership is the β certificate's, exactly as at `WellDenoted`. -/
theorem WellDenotedV_beta_zero {A b a : AnnotTerm} {ρ : Nat → V}
    (h : WellDenotedV V ρ (.app (.lam 0 A b) a))
    (hmem : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (.app (.lam 0 A b) a) = interp V ρ (b.inst a) ∧
      WellDenotedV V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := WellDenoted_beta_zero V h.1 hmem
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValid_app, AnnotValid_lam] at hv2
  exact (AnnotValid_inst0 V hv2.2).mpr (hv2.1.2 _ hmem)

/-! # T1 — the routed clause residues, fuel-free

`IotaStep2D`, `ProjStep2D`, `ReduceNatStep2D` and `Delta2B`
transposed.  All four stay routed: the install and iota tiers
discharge them. -/

/-- `IotaStep2D` in the P currency.  Kept **producing** (see the module
docstring): the app clause's ι branch continues into `ihwc` at the
fired rule's RHS, so the residue must supply that reduct's reading. -/
@[expose] def IotaStep (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e'' : Expr} {Δa : List AnnotTerm},
    iotaRecFueled μ env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      ∃ ea', denoteMeta m.acval env φ d e'' = some ea' ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea = interp V ρ ea') ∧
        Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e'' ∧ CtxOk m φ d Δa e''

/-- `ProjStep2D` in the P currency, **dual success**: the clause is the
whole of the dispatcher's `.proj` case and nothing continues past it,
so the reduct's reading is a premise here as it is in the claim. -/
@[expose] def ProjStep (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {sn : Name} {i : Nat} {pe e' : Expr}
    {Δa : List AnnotTerm},
    whnfCore μ env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    ∀ {ea ea' : AnnotTerm},
      CtxOk m φ d Δa (.proj sn i pe) →
      denoteMeta m.acval env φ d (.proj sn i pe) = some ea →
      denoteMeta m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea = interp V ρ ea'

/-- `ReduceNatStep2D` in the P currency.  Producing, for the loop's
sake (the budget induction continues at `e₂`). -/
@[expose] def ReduceNatStep (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AnnotTerm},
    reduceNatFueled μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      ∃ ea', denoteMeta m.acval env φ d e₂ = some ea' ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
        (∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea = interp V ρ ea') ∧
        Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₂ ∧ CtxOk m φ d Δa e₂

/-- `Delta2B` in the P currency: the annotation does not move, and now
neither does anything else — there is no fuel left to step. -/
@[expose] def Delta {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ea : AnnotTerm},
    unfoldDefinition env e = some e' →
    denoteMeta m.acval env φ d e = some ea →
    denoteMeta m.acval env φ d e' = some ea

/-! # T2 — the delta exit, discharged from one obligation

`AcvalDefnInst`'s statement carries `instantiateLevelParams` because
`Denote2InstLevels` is a residue.  `denotePInstLevels` is a theorem —
an unconditional equality — so the P-tier obligation is stated at the
*uninstantiated* value, which is `EnvModelU.acval_defn`'s own shape with
the fuel and the mode-conditioned direction removed. -/

/-- **The unfolding supplier the P-tier delta exit consumes**: a stored
value's validated annotation *is* the constant's own leaf, at every
level assignment.  Both unfoldable kinds in one premise, as
`unfoldDefinition`'s two branches differ only in the field that
supplies the value.

Routed.  The install tier discharges it; `acvalDefnInst_noParams`
(`Steps/Whnf.lean`) is the canonical tier's evidence that the shape is
inhabited well beyond vacuity, and the P shape asks for *less* than
that one (no `us`, no instantiation). -/
@[expose] def AcvalDefnInst {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
    ((∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) →
    denoteMeta m.acval env ψ 0 value = some (m.acval cv.name ψ)

/-- **The instantiated form, derived.**  This is the whole of what the
canonical lane routes as `Denote2InstLevels`, and it is one rewrite.
Note that the arity premise `us.length = cv.levelParams.length` — which
`AcvalDefnInst` carries — is *not needed*: `denotePInstLevels` is
unconditional. -/
theorem acvalDefnInst_subst {m : EnvModel V env}
    (hdi : AcvalDefnInst m) (φ : Name → Nat) {cv : ConstantVal}
    {value : Expr} {us : List Level}
    (hmem : (∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) :
    denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval cv.name (Level.substFn φ cv.levelParams us)) := by
  rw [denotePInstLevels m φ cv.levelParams us 0 value]
  exact hdi _ cv value hmem

/-- The shared core of `unfoldDefinition`'s two branches, P currency —
`delta2B_core` with the fuel move deleted. -/
private theorem delta_core (m : EnvModel V env)
    {d : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea : AnnotTerm}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : denoteMeta m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval ci.name (Level.substFn φ cv.levelParams us)))
    (hea : denoteMeta m.acval env φ d e = some ea) :
    denoteMeta m.acval env φ d
        (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs) = some ea := by
  obtain rfl : ci.name = n := by
    rw [Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    Expr.mkAppN_getApp e
  rw [← he] at hea
  refine denoteMeta_mkAppN_swap e.getAppArgs ?_ hea
  intro fa hfa
  rw [hfn, denoteMeta, hfind] at hfa
  simp only [hcvt] at hfa
  rw [if_pos hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  exact denoteMeta_depth_of_closed m.acval_closed
    (by rw [Expr.hasFvar_instantiateLevelParams]; exact hnofv)
    (fun k => m.acval_closed _ _ k) hval d

/-- **`Delta`, discharged** from `AcvalDefnInst`.  `delta2B_of`'s
mirror; the spine (`denoteMeta_mkAppN_swap`), the depth
(`denoteMeta_depth_of_closed`) and now the *level crossing*
(`denotePInstLevels`, through `acvalDefnInst_subst`) are all
theorems. -/
theorem delta_of (m : EnvModel V env) (hdi : AcvalDefnInst m) :
    Delta m φ := by
  intro d e e' ea hud hea
  rw [unfoldDefinition] at hud
  split at hud
  · next n us hfn =>
    split at hud
    · next cv value hint hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact delta_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ :=
                m.wf _ (find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (acvalDefnInst_subst hdi φ
            (Or.inl ⟨hint, find?_mem hfind⟩)) hea
      · exact nomatch hud
    · next cv value hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact delta_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, -, -, ht, -⟩ :=
                m.wf _ (find?_mem hfind)
              exact (ht cv value rfl).1)
          (acvalDefnInst_subst hdi φ (Or.inr (find?_mem hfind))) hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud

/-! # The existence factors, routed

`Dual2E.lean`'s `WhnfCoreExists2E`/`InferExists2E`, fuel-free.  See
the module docstring: the dual-success claims say nothing about a
reduct annotating, and this quarter reduces the head of an application
before it can say anything about the application. -/

/-- The head-normalisation existence factor, P currency. -/
@[expose] def WhnfCoreExists (μ : CheckMode) {env : Env} (m : EnvModel V env)
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

/-- The inference existence factor, P currency — what the β
certificate needs and `InferClaim`, being dual success, does not
give. -/
@[expose] def InferExists (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      ∃ ta, denoteMeta m.acval env φ d t = some ta

/-- `InferExists` at the io slot (task #172 B4): the totality factor
for a converted call site's inferred type. -/
@[expose] def InferExistsIOS (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    ConLeche.inferTypeIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      ∃ ta, denoteMeta m.acval env φ d t = some ta

/-! # T4a — the β certificate -/

/-- `BetaCert2D` in the P currency. -/
def BetaCert (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AnnotTerm} {a ty ta : Expr} {aa tya : AnnotTerm},
    ConLeche.inferTypeIO μ env fuel d a = .ok ta →
    ConLeche.isDefEqCore μ env fuel d ta ty = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    CtxOk m φ d Δa a →
    CtxOk m φ d Δa ty →
    denoteMeta m.acval env φ d a = some aa →
    denoteMeta m.acval env φ d ty = some tya →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ tya) →
    ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ aa ∈ˢ interp V ρ tya

/-- **The β certificate, discharged** — `betaCert2D_of_claims`'s
mirror.  The two context obligations are kit moves (`CtxOk.of_subset`
along `inferTypeCore_fvarLeaves`; the ascribed type keeps its own, with
no fuel to raise it to), and the one new input is the inference
existence factor the dual-success claim withholds. -/
theorem betaCert_of_claims (m : EnvModel V env) {fuel : Nat}
    (hexi : InferExistsIOS μ m φ fuel)
    (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel) :
    BetaCert μ m φ fuel := by
  intro d Δa a ty ta aa tya hta hde hwa hba hLa hwty hbty hLty
    hCa hCty haa htya hoka hoktya ρ hρ
  have hwta : Expr.WScoped d ta :=
    ConLeche.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hsub := ConLeche.inferTypeIO_fvarLeaves m.wf fuel hta hwa
  have hLta : Expr.LeavesBounded ta := fun l hl => hLa l (hsub l hl)
  have hCta : CtxOk m φ d Δa ta := hCa.of_subset hsub
  obtain ⟨ta', hta'⟩ := hexi hta hwa hba hLa hCa haa
  obtain ⟨hokta, hcon⟩ := ihis hta hwa hba hLa hCa haa hta' hoka
  have heq := ihd hde hwta hbta hLta hwty hbty hLty hCta hCty hta'
    htya hokta hoktya ρ hρ
  exact heq ▸ hcon ρ hρ

/-! # T3/T5 — the eleven cases -/

/-- `whnfCore_package2D`'s mirror.  There is no fuel to mediate, so the
reduct's reading is a premise (dual success) and the package's job is
the frames and the restricted context. -/
theorem whnfCore_package (m : EnvModel V env) {fuel d : Nat}
    {Δa : List AnnotTerm} {a a' : Expr} {aa aa' : AnnotTerm}
    (ihwc : WhnfCoreClaim μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOk m φ d Δa a)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (haa' : denoteMeta m.acval env φ d a' = some aa')
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa') ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa = interp V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOk m φ d Δa a' := by
  obtain ⟨hok', heq⟩ := ihwc hw hws hb hLb hC haa haa' hok
  exact ⟨hok', heq, whnfCore_WScoped m.wf fuel hw hws,
    whnfCore_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.wf fuel hw l hl),
    hC.of_subset (whnfCore_fvarLeaves m.wf fuel hw)⟩

/-- **The `.bvar` clause.**  Vacuous on the annotation side. -/
theorem whnfCore_bvar_claim (m : EnvModel V env) {d i : Nat}
    {ea : AnnotTerm}
    (hea : denoteMeta m.acval env φ d (.bvar i) = some ea) : False := by
  rw [denoteMeta_bvar] at hea; exact nomatch hea

/-- **The six leaf clauses**, at the P claim's own shape: the reduct is
the subject, so its reading is the subject's (`Option.some.inj`) and
both conjuncts are reflexivity. -/
theorem whnfCore_leaf_claim (m : EnvModel V env) {fuel d : Nat}
    {e e' : Expr} {Δa : List AnnotTerm} {ea ea' : AnnotTerm}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx ty, e = .fvar idx ty) ∨
      (∃ ty body bi, e = .forallE ty body bi) ∨
      (∃ ty body mb, e = .lam ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore μ env (fuel + 1) d e = .ok e')
    (hea : denoteMeta m.acval env φ d e = some ea)
    (hea' : denoteMeta m.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea = interp V ρ ea' := by
  have he : e' = e := by
    rcases hleaf with ⟨u, rfl⟩ | ⟨idx, ty, rfl⟩ |
      ⟨n, ty, body, bi, rfl⟩ | ⟨n, ty, body, mb, rfl⟩ |
      ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
      simp only [whnfCore_leaf_sort, whnfCore_leaf_fvar, whnfCore_leaf_forallE,
        whnfCore_leaf_lam, whnfCore_leaf_const, whnfCore_leaf_lit,
        Except.ok.injEq] at h <;>
      exact h.symm
  subst he
  obtain rfl : ea = ea' := Option.some.inj (hea.symm.trans hea')
  exact ⟨hok, fun _ _ => rfl⟩

/-- **The `.app` clause, P currency.**  The β kind split is verbatim
the `…D` lane's — `Nat.eq_zero_or_pos` on the λ's stored numeral, which
in this currency is `pwBit φ mb.pw` — and the two arms are
`WellDenotedV_beta_zero`/`WellDenotedV_beta_pos`.  The head's reduct reading
comes from the routed existence factor; every other reading in the
proof is inverted out of a premise. -/
theorem whnfCore_app_claim (m : EnvModel V env) {fuel : Nat}
    (hex : WhnfCoreExists μ m φ fuel)
    (hcert : BetaCert μ m φ fuel) (hiota : IotaStep μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel)
    {d : Nat} {f a e' : Expr} {Δa : List AnnotTerm}
    (h : whnfCore μ env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    {ea ea' : AnnotTerm}
    (hC : CtxOk m φ d Δa (.app f a))
    (hea : denoteMeta m.acval env φ d (.app f a) = some ea)
    (hea' : denoteMeta m.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ ea = interp V ρ ea' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOk m φ d Δa f := hC.app_fn
  have hCa : CtxOk m φ d Δa a := hC.app_arg
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  have hokf : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ fa := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have h1 := hx.1; rw [WellDenoted_app] at h1; exact h1.1
    · have h2 := hx.2; rw [AnnotValid_app] at h2; exact h2.1
  have hoka : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have h1 := hx.1; rw [WellDenoted_app] at h1; exact h1.2.1
    · have h2 := hx.2; rw [AnnotValid_app] at h2; exact h2.2
  obtain ⟨f', hwf, hcase⟩ := ConLeche.whnf_app_inv h
  obtain ⟨fa', hfa'⟩ := hex hwf hws.1 hb.1 hLf hCf hfa hokf
  obtain ⟨hokf', heqf, hwf', hbf', hLf', hCf'⟩ :=
    whnfCore_package m ihwc hwf hws.1 hb.1 hLf hCf hfa hfa' hokf
  have hiapp : denoteMeta m.acval env φ d (.app f' a)
      = some (.app fa' aa) := by rw [denoteMeta, hfa', haa]; rfl
  have hokapp : ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V ρ (.app fa' aa) := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have hx1 := hx.1
      rw [WellDenoted_app] at hx1
      obtain ⟨-, hoka1, v', A, B, h1, h2, h3⟩ := hx1
      rw [WellDenoted_app]
      exact ⟨(hokf' ρ hρ).1, hoka1, v', A, B, (heqf ρ hρ) ▸ h1, h2, h3⟩
    · rw [AnnotValid_app]
      exact ⟨(hokf' ρ hρ).2, (hoka ρ hρ).2⟩
  have heqapp : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ (.app fa aa) = interp V ρ (.app fa' aa) := by
    intro ρ hρ
    rw [interp_app, interp_app, heqf ρ hρ]
  have hwapp : Expr.WScoped d (.app f' a) := by
    simp only [Expr.WScoped]; exact ⟨hwf', hws.2⟩
  have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hbf', hb.2⟩
  have hLapp : Expr.LeavesBounded (.app f' a) := fun l hl => by
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hLf' l hl
    · exact hLa l hl
  have hCapp : CtxOk m φ d Δa (.app f' a) := CtxOk.app hCf' hCa
  rcases hcase with ⟨ty, body, mm, rfl, hbeta, hcertOr⟩ |
    ⟨e'', hio, hwe''⟩ | rfl
  · -- β
    obtain ⟨tya, ba, htya, hbb, rfl⟩ := denoteMeta_lam_inv hfa'
    simp only [Expr.WScoped] at hwf'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLf' l (by simp [Expr.fvarLeaves, hl])
    have hCty : CtxOk m φ d Δa ty := hCf'.lam_ty
    have hwred : Expr.WScoped d (body.instantiate1 a) :=
      Expr.WScoped.instantiate1_gen hws.2 0 hwf'.2
    have hbred : (body.instantiate1 a).looseBVarsBounded 0 = true :=
      Expr.looseBVarsBounded_instantiate1_gen hb.2 hbf'.2
    have hsubred : ∀ l ∈ (body.instantiate1 a).fvarLeaves,
        l ∈ (Expr.app (.lam ty body mm) a).fvarLeaves := by
      intro l hl
      rcases Expr.fvarLeaves_instantiate1 body 0 hl with h2 | h2
      · simp [Expr.fvarLeaves, h2]
      · simp [Expr.fvarLeaves, h2]
    have hLred : Expr.LeavesBounded (body.instantiate1 a) :=
      fun l hl => hLapp l (hsubred l hl)
    have hstep : ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ (.app (.lam (pwBit φ mm.pw) tya ba) aa)
            = interp V ρ (ba.inst aa) ∧
          WellDenotedV V ρ (ba.inst aa) := by
      intro ρ hρ
      by_cases hz : pwBit φ mm.pw = 0
      · -- task #161: the zero-kind arm is the one that consumes a
        -- certificate, and it is exactly the arm a **fired β gate**
        -- cannot reach — the asymmetry fence, discharged here rather
        -- than assumed (`gate_zero_kind_unreachable`, `GateP.lean`,
        -- is this same composition packaged).
        rcases hcertOr with hfired | ⟨ta, hta, hde⟩
        · exact absurd hz
            (pwBit_ne_zero_of_isNever (isNever_of_betaGateFires hfired) φ)
        · rw [hz] at hokapp ⊢
          exact WellDenotedV_beta_zero (hokapp ρ hρ)
            (hcert hta hde hws.2 hb.2 hLa hwf'.1 hbf'.1 hLty hCa
              hCty haa htya hoka
              (fun ρ' hρ' => WellDenotedV.lam_dom (hokf' ρ' hρ'))
              ρ hρ)
      · -- the positive arm consumes no certificate at all: this is
        -- the branch a fired gate always lands in (`WellDenotedV_beta_gate`)
        exact WellDenotedV_beta_pos hz (hokapp ρ hρ)
    have hred : denoteMeta m.acval env φ d (body.instantiate1 a)
        = some (ba.inst aa) := by
      rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
        (ty := ty) hwf'.2.fvarsBelow hws.2 hb.2 haa 0, hbb]
      rfl
    obtain ⟨hok', heq'⟩ :=
      ihwc hbeta hwred hbred hLred (hCapp.of_subset hsubred) hred hea'
        (fun ρ hρ => (hstep ρ hρ).2)
    exact ⟨hok', fun ρ hρ => by
      rw [heqapp ρ hρ, (hstep ρ hρ).1, heq' ρ hρ]⟩
  · -- ι
    obtain ⟨ea₂, hea₂, hok₂, heq₂, hwe, hbe, hLe, hCe⟩ :=
      hiota hio hwapp hbapp hLapp hCapp hiapp hokapp
    obtain ⟨hok', heq'⟩ := ihwc hwe'' hwe hbe hLe hCe hea₂ hea' hok₂
    exact ⟨hok',
      interpC_trans (interpC_trans heqapp heq₂) heq'⟩
  · -- stuck
    obtain rfl : (AnnotTerm.app fa' aa) = ea' :=
      Option.some.inj (hiapp.symm.trans hea')
    exact ⟨hokapp, heqapp⟩

/-- **`WhnfCoreClaim` at `fuel + 1`** — the eleven shapes. -/
theorem whnfCore_claims (m : EnvModel V env) {fuel : Nat}
    (hex : WhnfCoreExists μ m φ fuel)
    (hcert : BetaCert μ m φ fuel) (hiota : IotaStep μ m φ fuel)
    (hproj : ProjStep μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel) :
    WhnfCoreClaim μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb ea ea' hC hea hea' hok
  match e with
  | .sort u =>
    exact whnfCore_leaf_claim m (Or.inl ⟨u, rfl⟩) h hea hea' hok
  | .fvar idx ty =>
    exact whnfCore_leaf_claim m (Or.inr (Or.inl ⟨idx, ty, rfl⟩))
      h hea hea' hok
  | .forallE ty body bi =>
    exact whnfCore_leaf_claim m
      (Or.inr (Or.inr (Or.inl ⟨ty, body, bi, rfl⟩))) h hea hea' hok
  | .lam ty body mb =>
    exact whnfCore_leaf_claim m
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨ty, body, mb, rfl⟩))))
      h hea hea' hok
  | .const n us =>
    exact whnfCore_leaf_claim m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩)))))
      h hea hea' hok
  | .lit l =>
    exact whnfCore_leaf_claim m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))))
      h hea hea' hok
  | .bvar i => exact (whnfCore_bvar_claim m hea).elim
  | .letE tt vv bb =>
    exact (ConLeche.whnfCore_letE_inv h).elim
  | .app f a =>
    exact whnfCore_app_claim m hex hcert hiota ihwc h hws hb hLb hC
      hea hea' hok
  | .proj sn i pe => exact hproj h hws hb hLb hC hea hea' hok

/-- **The budget induction, P currency.**  `Delta` is now an equality
between two readings of the *same* annotation, so the δ branch neither
moves a fuel nor raises a context. -/
theorem whnfLoop_claim (m : EnvModel V env) {fuel : Nat}
    (hex : WhnfCoreExists μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel)
    (hnat : ReduceNatStep μ m φ fuel) (hdelta : Delta m φ) :
    ∀ (budget : Nat) {d : Nat} {Δa : List AnnotTerm} {e e' : Expr},
      whnfLoop (pureFns μ env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∀ {ea ea' : AnnotTerm},
        CtxOk m φ d Δa e →
        denoteMeta m.acval env φ d e = some ea →
        denoteMeta m.acval env φ d e' = some ea' →
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea') ∧
          ∀ ρ : Nat → V, Sat V Δa ρ →
            interp V ρ ea = interp V ρ ea' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δa e e' h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δa e e' h hws hb hLb ea ea' hC hea hea' hok
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, ConLeche.whnfCore_def] at h
    cases hwc : whnfCore μ env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨ea₁, hea₁⟩ := hex hwc hws hb hLb hC hea hok
    obtain ⟨hok₁, heq₁, hws₁, hb₁, hLb₁, hC₁⟩ :=
      whnfCore_package m ihwc hwc hws hb hLb hC hea hea₁ hok
    cases hrn : reduceNatFueled μ env fuel d e₁ with
    | error err =>
      rw [ConLeche.reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [ConLeche.reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨ea₂, hea₂, hok₂, heq₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hea₁ hok₁
      obtain ⟨hok', heq'⟩ :=
        ih h hws₂ hb₂ hLb₂ hC₂ hea₂ hea' hok₂
      exact ⟨hok', interpC_trans (interpC_trans heq₁ heq₂) heq'⟩
    | none, h =>
      dsimp only at h
      cases hud : unfoldDefinition env e₁ with
      | none =>
        rw [hud] at h
        obtain rfl : e₁ = e' := Except.ok.inj h
        obtain rfl : ea₁ = ea' :=
          Option.some.inj (hea₁.symm.trans hea')
        exact ⟨hok₁, heq₁⟩
      | some e₂ =>
        rw [hud] at h
        dsimp only at h
        obtain ⟨hok', heq'⟩ :=
          ih h (unfoldDefinition_WScoped m.wf hud hws₁)
            (unfoldDefinition_looseBVars m.wf hud hb₁)
            (fun l hl => hLb₁ l
              (unfoldDefinition_fvarLeaves m.wf hud l hl))
            (hC₁.of_subset
              (unfoldDefinition_fvarLeaves m.wf hud))
            (hdelta hud hea₁) hea' hok₁
        exact ⟨hok', interpC_trans heq₁ heq'⟩

/-- **`WhnfClaim` at `fuel + 1`.** -/
theorem whnf_claims (m : EnvModel V env) {fuel : Nat}
    (hex : WhnfCoreExists μ m φ fuel)
    (ihwc : WhnfCoreClaim μ m φ fuel)
    (hnat : ReduceNatStep μ m φ fuel) (hdelta : Delta m φ) :
    WhnfClaim μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb ea ea' hC hea hea' hok
  rw [ConLeche.whnf_succ, whnfBody] at h
  exact whnfLoop_claim m hex ihwc hnat hdelta whnfLoopFuel h hws hb
    hLb hC hea hea' hok

/-! # T5 — the quarters -/

/-- The head-normalisation quarter, P currency. -/
def WhnfCoreStep (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    InferClaimIO μ m φ fuel →
    WhnfCoreClaim μ m φ (fuel + 1)

/-- The reduction-loop quarter, P currency. -/
def WhnfStep (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvModel V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaim μ m φ fuel → WhnfClaim μ m φ fuel →
    DefEqClaim μ m φ fuel → InferClaim μ m φ fuel →
    InferClaimIO μ m φ fuel →
    WhnfClaim μ m φ (fuel + 1)

/-- **The two quarters' routed inputs.**  Six fields where the `…D`
lane's `whnfCoreStep2E_of`/`whnfStep2E_of` between them take five
(`hex` bundling three, `hinst`, `hiota`, `hproj`, `hnat`, `hdelta`):
`Denote2Inst1B` is gone (`denoteMeta_beta`), `Delta2B` is replaced by the
strictly weaker `AcvalDefnInst` (`delta_of` discharges it), and the
existence factor is split into the two components these quarters
actually read — defeq's is empty and `whnf`'s is unused here. -/
structure WhnfInputs (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- the head reduct annotates (`WhnfCoreExists2E`'s transpose) -/
  core_exists : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), WhnfCoreExists μ m φ fuel
  /-- the inferred type annotates (`InferExists2E`'s transpose), at
  the io slot (task #172 B4 — the β certificate's inference is a
  converted call site) -/
  infer_exists : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), InferExistsIOS μ m φ fuel
  /-- the ι clause -/
  iota : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), IotaStep μ m φ fuel
  /-- the projection clause -/
  proj : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), ProjStep μ m φ fuel
  /-- the `Nat`-literal reduction clause.  It takes the whnf claims at
  the same fuel: `reduceNat` head-normalises its arguments before
  reading them as literals, so the row's own `interp` equality needs
  whnf soundness there (the collapse lane's `reduceNat_stepR` takes the
  same IH).  `whnfStep_of` was already holding — and discarding —
  exactly this argument. -/
  nat : ∀ {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (fuel : Nat), WhnfClaim μ m φ fuel → ReduceNatStep μ m φ fuel
  /-- the δ exit's single obligation -/
  defn : ∀ {env : Env} (m : EnvModel V env), AcvalDefnInst m

/-- **`whnfCoreStep_of` — the head-normalisation quarter, P
currency.**  `hμ` is *unused* (flagged in the module docstring); it is
carried so the four quarters assemble under one mode hypothesis. -/
theorem whnfCoreStep_of (_hμ : μ.verifiedChecks = true)
    (hin : WhnfInputs V μ) : WhnfCoreStep μ V :=
  fun _env m φ fuel ihwc _ ihd ihi ihio =>
    whnfCore_claims m (hin.core_exists m φ fuel)
      (betaCert_of_claims m (hin.infer_exists m φ fuel) ihd
        (inferClaimIOS_of ihi ihio))
      (hin.iota m φ fuel) (hin.proj m φ fuel) ihwc

/-- **`whnfStep_of` — the reduction loop, P currency.**  `hμ` unused,
as above. -/
theorem whnfStep_of (_hμ : μ.verifiedChecks = true)
    (hin : WhnfInputs V μ) : WhnfStep μ V :=
  fun _env m φ fuel ihwc ihw _ _ _ =>
    whnf_claims m (hin.core_exists m φ fuel) ihwc
      (hin.nat m φ fuel ihw) (delta_of m (hin.defn m))

end ConLeche.Model
