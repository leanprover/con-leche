import Lech.Verify.InferIOLeaves
import Lech.SetP.CtxOkPKit
import Lech.SetP.Annot.BitInst
import Lech.SetP.Annot.BitInstall
import Lech.SetP.Step2.BitLevels
import Lech.Semantics.Sat2
import Lech.Semantics.WhnfCoreLeaf
import Lech.SetP.Claims2PIO

/-!
# The two head-normalisation quarters, P currency (task #161, P3.4)

The `…D` generation of `Step2/Whnf.lean` — `whnfCore_claims2D`,
`whnfLoop_claim2D` and the residues they consume — transposed to the
P tier: `denoteP` for `denote2`, `AnnotOkP` for `AnnotOk2`, `CtxOkP`
for `CtxOk2D`.  The systematic deltas, and what each buys:

* **the annotation fuel vanishes.**  `denote2 … F d e` becomes
  `denoteP … d e`; with it go `denote2_fuelMono`, the `∃ F' ≥ F`
  slack, and every `CtxOk2D.fuelMono` call.  Two readings of the same
  term are now literally the same run, so reconciling them is
  `Option.some.inj` — the move this file makes a dozen times where the
  `…D` lane moved a fuel.
* **`Denote2Inst1B` is retired.**  The ζ and β clauses' substitution
  law is `denoteP_beta` (`Annot/BitInst.lean`), a *theorem*, so the
  quarter's routed-input list is one shorter than the `…D` lane's.
  Its two leaf premises are discharged here: `hacl` is the environment
  structure's own `acval_closed` field, and `hainst` is
  `acval_inst_self` below (`AVExpr.inst_eq_self` at the erasure's
  closedness — `EnvS.cval_closed` composed with `acval_erase`).
* **`Delta2B`'s level crossing is paid.**  `delta2B_of` routes
  `AcvalDefnInst`, whose statement bakes in `instantiateLevelParams`
  because the canonical reading's level crossing is two open checker
  metatheorems.  `denotePInstLevels` is an unconditional *equality*,
  so `AcvalDefnInstP` is stated at the **uninstantiated** value (the
  shape `EnvS2U.acval_defn` already has, minus the fuel) and the
  instantiated form is derived — `acvalDefnInstP_subst`.

## The existence factor, and why it is routed

`Claims2P` is **dual success** (`Claims2P.lean`): the reduct's
annotation is a premise, not a conclusion.  `Dual2E.lean` measured
what that costs a reduction quarter — `Claims2D ⟺ Claims2E ∧ Exists2E`
— and the measurement transposes verbatim: `whnfCore`'s application
clause reduces the *head* first, and nothing in the dual-success claim
says the head's reduct annotates.  So this quarter is handed the
existence factor back, exactly as `whnfCoreStep2E_of` is:
`WhnfCoreExistsP` (the head's reduct) and `InferExistsP` (the β
certificate's inferred type) are routed inputs, bundled with the three
clause residues in `WhnfInputsP`.

`IotaStepP` and `ReduceNatStepP` are kept in their `…D` *producing*
shape for the same reason: both feed a continuation (`ihwc`, and the
loop's own induction) whose subject is the residue's output, so a
dual-success transpose of either would have no supplier for its own
premise.  `ProjStepP` **is** dual-success — it is the claim's `.proj`
clause entire, nothing continues past it, and the weaker shape is
therefore the right obligation to route.

## Mode

`WhnfCoreStepP`/`WhnfStepP` carry `μ.verifiedChecks = true` for assembly
uniformity with the infer quarter (`Step2/InferP.lean`'s docstring
records why the step proofs are verified-only).  **Neither quarter's
proof reads it** — flagged here rather than dropped, because the
capstone binds the four steps at one mode hypothesis.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level BinderMeta Literal whnf
  whnfCore whnfBody whnfLoop whnfStep whnfLoopFuel pureFns
  inferTypeCore iotaRecP reduceNatP unfoldDefinition ConstantInfo
  ConstantVal ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The two leaf premises of `denoteP_beta`

`hacl` is a structure field; `hainst` is one composition away from
another, and is proved here once so that no clause carries it. -/

/-- `denoteP` has no clause for a loose `bvar` — `denote2_bvar`'s
mirror, and the `.bvar` case of the dispatcher entire. -/
theorem denoteP_bvar {acval : Name → (Name → Nat) → AVExpr}
    (d i : Nat) : denoteP acval env φ d (.bvar i) = none := by
  rw [denoteP.eq_def]

/-! ## The currency's reduction steps

`AnnotOk2_zeta` / `AnnotOk2_beta_pos` / `AnnotOk2_beta_zero`
(`Annot/Ok2.lean`) are currency-level and reused verbatim for the
`AnnotOk2` half.  The `AnnotValidV` half rides `AnnotValidV_inst0`,
whose premise is the substituend's own validity — available at each
site — and whose *transport* needs the argument's domain membership.
At kind `0` that membership is the β certificate's business
(`AnnotOkP_beta_zero` takes it, as `AnnotOk2_beta_zero` does); at a
positive kind it is derivable from the subject's `AnnotOk2` alone, and
`annotOk2_beta_dom_pos` below is `AnnotOk2_beta_pos`'s own derivation
of it, isolated so the P step can read it. -/

/-- **The argument is in the λ's domain**, at a positive kind, from
the application's `AnnotOk2` alone.  Extracted from
`AnnotOk2_beta_pos`'s proof (rigidity: the slot's product cannot be
`pt`, so `piR_dom_unique` pins its domain to the λ's own). -/
theorem annotOk2_beta_dom_pos {v : Nat} (hv : v ≠ 0) {A b a : AVExpr}
    {ρ : Nat → V} (h : AnnotOk2 V ρ (.app (.lam v A b) a)) :
    interp2 V ρ a ∈ˢ interp2 V ρ A := by
  rw [AnnotOk2_app] at h
  obtain ⟨hlam, -, v', A', B', hslot, hmem, -⟩ := h
  rw [AnnotOk2_lam] at hlam
  obtain ⟨-, -, B, hfib, -⟩ := hlam
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    have h1 := eq_pt_of_mem_piR_zero hslot
    rw [interp2_lam] at h1
    exact lamR_ne_pt hv h1
  have hown : interp2 V ρ (.lam v A b)
      ∈ˢ piR v (interp2 V ρ A) B := by
    rw [interp2_lam]
    exact lamR_mem hfib
  rw [piR_dom_unique hv hv' hown hslot]
  exact hmem

/-- A λ's domain annotation is graded when the λ is — the fact the β
site's certificate premise reads (`AnnotOk2.hoist_lam`'s P mirror, at
one valuation). -/
theorem AnnotOkP.lam_dom {v : Nat} {A b : AVExpr} {ρ : Nat → V}
    (h : AnnotOkP V ρ (.lam v A b)) : AnnotOkP V ρ A := by
  refine ⟨?_, ?_⟩
  · have h1 := h.1; rw [AnnotOk2_lam] at h1; exact h1.1
  · have h2 := h.2; rw [AnnotValidV_lam] at h2; exact h2.1

/-- **The graded ζ step, P currency.** -/
theorem AnnotOkP_zeta {T v b : AVExpr} {ρ : Nat → V}
    (h : AnnotOkP V ρ (.letE T v b)) :
    interp2 V ρ (.letE T v b) = interp2 V ρ (b.inst v) ∧
      AnnotOkP V ρ (b.inst v) := by
  obtain ⟨heq, hok2⟩ := AnnotOk2_zeta V h.1
  refine ⟨heq, hok2, ?_⟩
  have hv := h.2
  rw [AnnotValidV_letE] at hv
  exact (AnnotValidV_inst0 V hv.2.1).mpr hv.2.2

/-- **The graded β step at a positive kind, P currency.** -/
theorem AnnotOkP_beta_pos {v : Nat} (hv : v ≠ 0) {A b a : AVExpr}
    {ρ : Nat → V} (h : AnnotOkP V ρ (.app (.lam v A b) a)) :
    interp2 V ρ (.app (.lam v A b) a) = interp2 V ρ (b.inst a) ∧
      AnnotOkP V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := AnnotOk2_beta_pos V hv h.1
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValidV_app, AnnotValidV_lam] at hv2
  exact (AnnotValidV_inst0 V hv2.2).mpr
    (hv2.1.2 _ (annotOk2_beta_dom_pos hv h.1))

/-- **The graded β step at kind `0`, P currency** — the domain
membership is the β certificate's, exactly as at `AnnotOk2`. -/
theorem AnnotOkP_beta_zero {A b a : AVExpr} {ρ : Nat → V}
    (h : AnnotOkP V ρ (.app (.lam 0 A b) a))
    (hmem : interp2 V ρ a ∈ˢ interp2 V ρ A) :
    interp2 V ρ (.app (.lam 0 A b) a) = interp2 V ρ (b.inst a) ∧
      AnnotOkP V ρ (b.inst a) := by
  obtain ⟨heq, hok2⟩ := AnnotOk2_beta_zero V h.1 hmem
  refine ⟨heq, hok2, ?_⟩
  have hv2 := h.2
  rw [AnnotValidV_app, AnnotValidV_lam] at hv2
  exact (AnnotValidV_inst0 V hv2.2).mpr (hv2.1.2 _ hmem)

/-! # T1 — the routed clause residues, fuel-free

`IotaStep2D`, `ProjStep2D`, `ReduceNatStep2D` and `Delta2B`
transposed.  All four stay routed: the install and iota tiers
discharge them. -/

/-- `IotaStep2D` in the P currency.  Kept **producing** (see the module
docstring): the app clause's ι branch continues into `ihwc` at the
fired rule's RHS, so the residue must supply that reduct's reading. -/
def IotaStepP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e'' : Expr} {Δa : List AVExpr},
    iotaRecP μ env fuel d e = .ok (some e'') →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      ∃ ea', denoteP m.acval env φ d e'' = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea') ∧
        Expr.WScoped d e'' ∧ e''.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e'' ∧ CtxOkP m φ d Δa e''

/-- `ProjStep2D` in the P currency, **dual success**: the clause is the
whole of the dispatcher's `.proj` case and nothing continues past it,
so the reduct's reading is a premise here as it is in the claim. -/
def ProjStepP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {sn : Name} {i : Nat} {pe e' : Expr}
    {Δa : List AVExpr},
    whnfCore μ env (fuel + 1) d (.proj sn i pe) = .ok e' →
    Expr.WScoped d (.proj sn i pe) →
    (Expr.proj sn i pe).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.proj sn i pe) →
    ∀ {ea ea' : AVExpr},
      CtxOkP m φ d Δa (.proj sn i pe) →
      denoteP m.acval env φ d (.proj sn i pe) = some ea →
      denoteP m.acval env φ d e' = some ea' →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
        ∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea'

/-- `ReduceNatStep2D` in the P currency.  Producing, for the loop's
sake (the budget induction continues at `e₂`). -/
def ReduceNatStepP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e e₂ : Expr} {Δa : List AVExpr},
    reduceNatP μ env fuel d e = .ok (some e₂) →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
      ∃ ea', denoteP m.acval env φ d e₂ = some ea' ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
        (∀ ρ : Nat → V, Sat2 V Δa ρ →
          interp2 V ρ ea = interp2 V ρ ea') ∧
        Expr.WScoped d e₂ ∧ e₂.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded e₂ ∧ CtxOkP m φ d Δa e₂

/-- `Delta2B` in the P currency: the annotation does not move, and now
neither does anything else — there is no fuel left to step. -/
def DeltaP {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) : Prop :=
  ∀ {d : Nat} {e e' : Expr} {ea : AVExpr},
    unfoldDefinition env e = some e' →
    denoteP m.acval env φ d e = some ea →
    denoteP m.acval env φ d e' = some ea

/-! # T2 — the delta exit, discharged from one obligation

`AcvalDefnInst`'s statement carries `instantiateLevelParams` because
`Denote2InstLevels` is a residue.  `denotePInstLevels` is a theorem —
an unconditional equality — so the P-tier obligation is stated at the
*uninstantiated* value, which is `EnvS2U.acval_defn`'s own shape with
the fuel and the mode-conditioned direction removed. -/

/-- **The unfolding supplier the P-tier delta exit consumes**: a stored
value's validated annotation *is* the constant's own leaf, at every
level assignment.  Both unfoldable kinds in one premise, as
`unfoldDefinition`'s two branches differ only in the field that
supplies the value.

Routed.  The install tier discharges it; `acvalDefnInst_noParams`
(`Step2/Whnf.lean`) is the canonical tier's evidence that the shape is
inhabited well beyond vacuity, and the P shape asks for *less* than
that one (no `us`, no instantiation). -/
def AcvalDefnInstP {env : Env} (m : EnvS2Core V env) : Prop :=
  ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
    ((∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) →
    denoteP m.acval env ψ 0 value = some (m.acval cv.name ψ)

/-- **The instantiated form, derived.**  This is the whole of what the
canonical lane routes as `Denote2InstLevels`, and it is one rewrite.
Note that the arity premise `us.length = cv.levelParams.length` — which
`AcvalDefnInst` carries — is *not needed*: `denotePInstLevels` is
unconditional. -/
theorem acvalDefnInstP_subst {m : EnvS2Core V env}
    (hdi : AcvalDefnInstP m) (φ : Name → Nat) {cv : ConstantVal}
    {value : Expr} {us : List Level}
    (hmem : (∃ hint : ReducibilityHint,
        ConstantInfo.defnInfo cv value hint ∈ env.consts) ∨
      ConstantInfo.thmInfo cv value ∈ env.consts) :
    denoteP m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval cv.name (Level.substFn φ cv.levelParams us)) := by
  rw [denotePInstLevels m φ cv.levelParams us 0 value]
  exact hdi _ cv value hmem

/-- The shared core of `unfoldDefinition`'s two branches, P currency —
`delta2B_core` with the fuel move deleted. -/
private theorem deltaP_core (m : EnvS2Core V env)
    {d : Nat} {e : Expr} {n : Name} {us : List Level}
    {ci : ConstantInfo} {cv : ConstantVal} {value : Expr}
    {ea : AVExpr}
    (hfn : e.getAppFn = .const n us)
    (hfind : env.find? n = some ci)
    (hcvt : ci.toConstantVal = cv)
    (hlen : us.length = cv.levelParams.length)
    (hnofv : value.hasFvar = false)
    (hval : denoteP m.acval env φ 0
        (value.instantiateLevelParams cv.levelParams us)
      = some (m.acval ci.name (Level.substFn φ cv.levelParams us)))
    (hea : denoteP m.acval env φ d e = some ea) :
    denoteP m.acval env φ d
        (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs) = some ea := by
  obtain rfl : ci.name = n := by
    rw [Env.find?] at hfind
    have := List.find?_some hfind
    simpa using this
  have he : Expr.mkAppN e.getAppFn e.getAppArgs = e :=
    Expr.mkAppN_getApp e
  rw [← he] at hea
  refine denoteP_mkAppN_swap e.getAppArgs ?_ hea
  intro fa hfa
  rw [hfn, denoteP, hfind] at hfa
  simp only [hcvt] at hfa
  rw [if_pos hlen] at hfa
  obtain rfl : fa = m.acval ci.name
      (Level.substFn φ cv.levelParams us) := (Option.some.inj hfa).symm
  exact denoteP_depth_of_closed m.acval_closed
    (by rw [Expr.hasFvar_instantiateLevelParams]; exact hnofv)
    (fun k => m.acval_closed _ _ k) hval d

/-- **`DeltaP`, discharged** from `AcvalDefnInstP`.  `delta2B_of`'s
mirror; the spine (`denoteP_mkAppN_swap`), the depth
(`denoteP_depth_of_closed`) and now the *level crossing*
(`denotePInstLevels`, through `acvalDefnInstP_subst`) are all
theorems. -/
theorem deltaP_of (m : EnvS2Core V env) (hdi : AcvalDefnInstP m) :
    DeltaP m φ := by
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
        exact deltaP_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, hd, -⟩ :=
                m.wf _ (find?_mem hfind)
              exact (hd cv value hint rfl).1)
          (acvalDefnInstP_subst hdi φ
            (Or.inl ⟨hint, find?_mem hfind⟩)) hea
      · exact nomatch hud
    · next cv value hfind =>
      split at hud
      · next hlen =>
        obtain rfl : e' = Expr.mkAppN
            (value.instantiateLevelParams cv.levelParams us)
            e.getAppArgs := (Option.some.inj hud).symm
        exact deltaP_core m hfn hfind rfl hlen
          (by obtain ⟨-, -, -, -, -, -, ht, -⟩ :=
                m.wf _ (find?_mem hfind)
              exact (ht cv value rfl).1)
          (acvalDefnInstP_subst hdi φ (Or.inr (find?_mem hfind))) hea
      · exact nomatch hud
    · exact nomatch hud
  · exact nomatch hud

/-! # The existence factors, routed

`Dual2E.lean`'s `WhnfCoreExists2E`/`InferExists2E`, fuel-free.  See
the module docstring: the dual-success claims say nothing about a
reduct annotating, and this quarter reduces the head of an application
before it can say anything about the application. -/

/-- The head-normalisation existence factor, P currency. -/
def WhnfCoreExistsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
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

/-- The inference existence factor, P currency — what the β
certificate needs and `InferClaims2P`, being dual success, does not
give. -/
def InferExistsP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    inferTypeCore μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      ∃ ta, denoteP m.acval env φ d t = some ta

/-- `InferExistsP` at the io slot (task #172 B4): the totality factor
for a converted call site's inferred type. -/
def InferExistsIOSP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AVExpr},
    Lech.inferTypeIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea : AVExpr},
      CtxOkP m φ d Δa e →
      denoteP m.acval env φ d e = some ea →
      ∃ ta, denoteP m.acval env φ d t = some ta

/-! # T4a — the β certificate -/

/-- `BetaCert2D` in the P currency. -/
def BetaCertP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {a ty ta : Expr} {aa tya : AVExpr},
    Lech.inferTypeIO μ env fuel d a = .ok ta →
    Lech.isDefEqCore μ env fuel d ta ty = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    CtxOkP m φ d Δa a →
    CtxOkP m φ d Δa ty →
    denoteP m.acval env φ d a = some aa →
    denoteP m.acval env φ d ty = some tya →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ tya) →
    ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ aa ∈ˢ interp2 V ρ tya

/-- **The β certificate, discharged** — `betaCert2D_of_claims`'s
mirror.  The two context obligations are kit moves (`CtxOkP.of_subset`
along `inferTypeCore_fvarLeaves`; the ascribed type keeps its own, with
no fuel to raise it to), and the one new input is the inference
existence factor the dual-success claim withholds. -/
theorem betaCertP_of_claims (m : EnvS2Core V env) {fuel : Nat}
    (hexi : InferExistsIOSP μ m φ fuel)
    (ihd : DefEqClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel) :
    BetaCertP μ m φ fuel := by
  intro d Δa a ty ta aa tya hta hde hwa hba hLa hwty hbty hLty
    hCa hCty haa htya hoka hoktya ρ hρ
  have hwta : Expr.WScoped d ta :=
    Lech.inferTypeIO_WScoped m.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    Lech.inferTypeIO_looseBVars m.wf fuel hta hwa hba hLa
  have hsub := Lech.inferTypeIO_fvarLeaves m.wf fuel hta hwa
  have hLta : Expr.LeavesBounded ta := fun l hl => hLa l (hsub l hl)
  have hCta : CtxOkP m φ d Δa ta := hCa.of_subset hsub
  obtain ⟨ta', hta'⟩ := hexi hta hwa hba hLa hCa haa
  obtain ⟨hokta, hcon⟩ := ihis hta hwa hba hLa hCa haa hta' hoka
  have heq := ihd hde hwta hbta hLta hwty hbty hLty hCta hCty hta'
    htya hokta hoktya ρ hρ
  exact heq ▸ hcon ρ hρ

/-! # T3/T5 — the eleven cases -/

/-- `whnfCore_package2D`'s mirror.  There is no fuel to mediate, so the
reduct's reading is a premise (dual success) and the package's job is
the frames and the restricted context. -/
theorem whnfCore_packageP (m : EnvS2Core V env) {fuel d : Nat}
    {Δa : List AVExpr} {a a' : Expr} {aa aa' : AVExpr}
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    (hw : whnfCore μ env fuel d a = .ok a')
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkP m φ d Δa a)
    (haa : denoteP m.acval env φ d a = some aa)
    (haa' : denoteP m.acval env φ d a' = some aa')
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa') ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ aa = interp2 V ρ aa') ∧
      Expr.WScoped d a' ∧ a'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a' ∧ CtxOkP m φ d Δa a' := by
  obtain ⟨hok', heq⟩ := ihwc hw hws hb hLb hC haa haa' hok
  exact ⟨hok', heq, whnfCore_WScoped m.wf fuel hw hws,
    whnfCore_looseBVars m.wf fuel hw hb,
    fun l hl => hLb l (whnfCore_fvarLeaves m.wf fuel hw l hl),
    hC.of_subset (whnfCore_fvarLeaves m.wf fuel hw)⟩

/-- **The `.bvar` clause.**  Vacuous on the annotation side. -/
theorem whnfCore_bvar_claimP (m : EnvS2Core V env) {d i : Nat}
    {ea : AVExpr}
    (hea : denoteP m.acval env φ d (.bvar i) = some ea) : False := by
  rw [denoteP_bvar] at hea; exact nomatch hea

/-- **The six leaf clauses**, at the P claim's own shape: the reduct is
the subject, so its reading is the subject's (`Option.some.inj`) and
both conjuncts are reflexivity. -/
theorem whnfCore_leaf_claimP (m : EnvS2Core V env) {fuel d : Nat}
    {e e' : Expr} {Δa : List AVExpr} {ea ea' : AVExpr}
    (hleaf : (∃ u, e = .sort u) ∨ (∃ idx ty, e = .fvar idx ty) ∨
      (∃ n ty body bi, e = .forallE ty body bi) ∨
      (∃ n ty body mb, e = .lam ty body mb) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l))
    (h : whnfCore μ env (fuel + 1) d e = .ok e')
    (hea : denoteP m.acval env φ d e = some ea)
    (hea' : denoteP m.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea' := by
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

/-- **The ζ clause, P currency.**  Where the `…D` lane consumed
`Denote2Inst1B` (a routed residue with a fuel move), this reads
`denoteP_beta` — a theorem, and an equality. -/
theorem whnfCore_letE_claimP (m : EnvS2Core V env) {fuel : Nat}
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    {d : Nat} {nn : Name} {tt vv bb e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.letE tt vv bb) = .ok e')
    (hws : Expr.WScoped d (.letE tt vv bb))
    (hb : (Expr.letE tt vv bb).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.letE tt vv bb))
    {ea ea' : AVExpr}
    (hC : CtxOkP m φ d Δa (.letE tt vv bb))
    (hea : denoteP m.acval env φ d (.letE tt vv bb) = some ea)
    (hea' : denoteP m.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea' := by
  rw [Lech.whnfCore_succ] at h
  simp only [Lech.whnfCoreBody, Lech.whnfCore_def] at h
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  rw [denoteP] at hea
  rcases hta : denoteP m.acval env φ d tt with _ | ta
  · rw [hta] at hea; exact nomatch hea
  rw [hta] at hea
  rcases hva : denoteP m.acval env φ d vv with _ | va
  · rw [hva] at hea; exact nomatch hea
  rw [hva] at hea
  rcases hba : denoteP m.acval env φ (d + 1)
      (bb.instantiate1 (.fvar d tt)) with _ | ba
  · rw [hba] at hea; exact nomatch hea
  rw [hba] at hea
  obtain rfl : ea = .letE ta va ba := (Option.some.inj hea).symm
  have hsubred : ∀ l ∈ (bb.instantiate1 vv).fvarLeaves,
      l ∈ (Expr.letE tt vv bb).fvarLeaves := by
    intro l hl
    rcases Expr.fvarLeaves_instantiate1 bb 0 hl with h2 | h2
    · simp [Expr.fvarLeaves, h2]
    · simp [Expr.fvarLeaves, h2]
  have hwred : Expr.WScoped d (bb.instantiate1 vv) :=
    Expr.WScoped.instantiate1_gen hws.2.1 0 hws.2.2
  have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
    Expr.looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
  have hLred : Expr.LeavesBounded (bb.instantiate1 vv) :=
    fun l hl => hLb l (hsubred l hl)
  have hred : denoteP m.acval env φ d (bb.instantiate1 vv)
      = some (ba.inst va) := by
    rw [denoteP_beta m.acval_closed (acval_inst_self m)
      (n := nn) (ty := tt) hws.2.2.fvarsBelow hws.2.1 hb.1.2 hva 0,
      hba]
    rfl
  obtain ⟨hok', heq'⟩ :=
    ihwc h hwred hbred hLred (hC.of_subset hsubred) hred hea'
      (fun ρ hρ => (AnnotOkP_zeta (hok ρ hρ)).2)
  exact ⟨hok', fun ρ hρ =>
    ((AnnotOkP_zeta (hok ρ hρ)).1).trans (heq' ρ hρ)⟩

/-- **The `.app` clause, P currency.**  The β kind split is verbatim
the `…D` lane's — `Nat.eq_zero_or_pos` on the λ's stored numeral, which
in this currency is `pwBit φ mb.pw` — and the two arms are
`AnnotOkP_beta_zero`/`AnnotOkP_beta_pos`.  The head's reduct reading
comes from the routed existence factor; every other reading in the
proof is inverted out of a premise. -/
theorem whnfCore_app_claimP (m : EnvS2Core V env) {fuel : Nat}
    (hex : WhnfCoreExistsP μ m φ fuel)
    (hcert : BetaCertP μ m φ fuel) (hiota : IotaStepP μ m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    {d : Nat} {f a e' : Expr} {Δa : List AVExpr}
    (h : whnfCore μ env (fuel + 1) d (.app f a) = .ok e')
    (hws : Expr.WScoped d (.app f a))
    (hb : (Expr.app f a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app f a))
    {ea ea' : AVExpr}
    (hC : CtxOkP m φ d Δa (.app f a))
    (hea : denoteP m.acval env φ d (.app f a) = some ea)
    (hea' : denoteP m.acval env φ d e' = some ea')
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ ea = interp2 V ρ ea' := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  have hLf : Expr.LeavesBounded f := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hLa : Expr.LeavesBounded a := fun l hl =>
    hLb l (by simp [Expr.fvarLeaves, hl])
  have hCf : CtxOkP m φ d Δa f := hC.app_fn
  have hCa : CtxOkP m φ d Δa a := hC.app_arg
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv hea
  have hokf : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ fa := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have h1 := hx.1; rw [AnnotOk2_app] at h1; exact h1.1
    · have h2 := hx.2; rw [AnnotValidV_app] at h2; exact h2.1
  have hoka : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have h1 := hx.1; rw [AnnotOk2_app] at h1; exact h1.2.1
    · have h2 := hx.2; rw [AnnotValidV_app] at h2; exact h2.2
  obtain ⟨f', hwf, hcase⟩ := Lech.whnf_app_inv h
  obtain ⟨fa', hfa'⟩ := hex hwf hws.1 hb.1 hLf hCf hfa hokf
  obtain ⟨hokf', heqf, hwf', hbf', hLf', hCf'⟩ :=
    whnfCore_packageP m ihwc hwf hws.1 hb.1 hLf hCf hfa hfa' hokf
  have hiapp : denoteP m.acval env φ d (.app f' a)
      = some (.app fa' aa) := by rw [denoteP, hfa', haa]; rfl
  have hokapp : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      AnnotOkP V ρ (.app fa' aa) := by
    intro ρ hρ
    have hx := hok ρ hρ
    refine ⟨?_, ?_⟩
    · have hx1 := hx.1
      rw [AnnotOk2_app] at hx1
      obtain ⟨-, hoka1, v', A, B, h1, h2, h3⟩ := hx1
      rw [AnnotOk2_app]
      exact ⟨(hokf' ρ hρ).1, hoka1, v', A, B, (heqf ρ hρ) ▸ h1, h2, h3⟩
    · rw [AnnotValidV_app]
      exact ⟨(hokf' ρ hρ).2, (hoka ρ hρ).2⟩
  have heqapp : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ (.app fa aa) = interp2 V ρ (.app fa' aa) := by
    intro ρ hρ
    rw [interp2_app, interp2_app, heqf ρ hρ]
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
  have hCapp : CtxOkP m φ d Δa (.app f' a) := CtxOkP.app hCf' hCa
  rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, hcertOr⟩ |
    ⟨e'', hio, hwe''⟩ | rfl
  · -- β
    obtain ⟨tya, ba, htya, hbb, rfl⟩ := denoteP_lam_inv hfa'
    simp only [Expr.WScoped] at hwf'
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbf'
    have hLty : Expr.LeavesBounded ty := fun l hl =>
      hLf' l (by simp [Expr.fvarLeaves, hl])
    have hCty : CtxOkP m φ d Δa ty := hCf'.lam_ty
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
    have hstep : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ (.app (.lam (pwBit φ mm.pw) tya ba) aa)
            = interp2 V ρ (ba.inst aa) ∧
          AnnotOkP V ρ (ba.inst aa) := by
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
          exact AnnotOkP_beta_zero (hokapp ρ hρ)
            (hcert hta hde hws.2 hb.2 hLa hwf'.1 hbf'.1 hLty hCa
              hCty haa htya hoka
              (fun ρ' hρ' => AnnotOkP.lam_dom (hokf' ρ' hρ'))
              ρ hρ)
      · -- the positive arm consumes no certificate at all: this is
        -- the branch a fired gate always lands in (`AnnotOkP_beta_gate`)
        exact AnnotOkP_beta_pos hz (hokapp ρ hρ)
    have hred : denoteP m.acval env φ d (body.instantiate1 a)
        = some (ba.inst aa) := by
      rw [denoteP_beta m.acval_closed (acval_inst_self m)
        (n := n) (ty := ty) hwf'.2.fvarsBelow hws.2 hb.2 haa 0, hbb]
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
      interp2C_trans (interp2C_trans heqapp heq₂) heq'⟩
  · -- stuck
    obtain rfl : (AVExpr.app fa' aa) = ea' :=
      Option.some.inj (hiapp.symm.trans hea')
    exact ⟨hokapp, heqapp⟩

/-- **`WhnfCoreClaims2P` at `fuel + 1`** — the eleven shapes. -/
theorem whnfCore_claimsP (m : EnvS2Core V env) {fuel : Nat}
    (hex : WhnfCoreExistsP μ m φ fuel)
    (hcert : BetaCertP μ m φ fuel) (hiota : IotaStepP μ m φ fuel)
    (hproj : ProjStepP μ m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel) :
    WhnfCoreClaims2P μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb ea ea' hC hea hea' hok
  match e with
  | .sort u =>
    exact whnfCore_leaf_claimP m (Or.inl ⟨u, rfl⟩) h hea hea' hok
  | .fvar idx ty =>
    exact whnfCore_leaf_claimP m (Or.inr (Or.inl ⟨idx, ty, rfl⟩))
      h hea hea' hok
  | .forallE ty body bi =>
    exact whnfCore_leaf_claimP m
      (Or.inr (Or.inr (Or.inl ⟨n, ty, body, bi, rfl⟩))) h hea hea' hok
  | .lam ty body mb =>
    exact whnfCore_leaf_claimP m
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, ty, body, mb, rfl⟩))))
      h hea hea' hok
  | .const n us =>
    exact whnfCore_leaf_claimP m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, us, rfl⟩)))))
      h hea hea' hok
  | .lit l =>
    exact whnfCore_leaf_claimP m
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))))
      h hea hea' hok
  | .bvar i => exact (whnfCore_bvar_claimP m hea).elim
  | .letE tt vv bb =>
    exact whnfCore_letE_claimP m ihwc h hws hb hLb hC hea hea' hok
  | .app f a =>
    exact whnfCore_app_claimP m hex hcert hiota ihwc h hws hb hLb hC
      hea hea' hok
  | .proj sn i pe => exact hproj h hws hb hLb hC hea hea' hok

/-- **The budget induction, P currency.**  `DeltaP` is now an equality
between two readings of the *same* annotation, so the δ branch neither
moves a fuel nor raises a context. -/
theorem whnfLoop_claimP (m : EnvS2Core V env) {fuel : Nat}
    (hex : WhnfCoreExistsP μ m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    (hnat : ReduceNatStepP μ m φ fuel) (hdelta : DeltaP m φ) :
    ∀ (budget : Nat) {d : Nat} {Δa : List AVExpr} {e e' : Expr},
      whnfLoop (pureFns μ env fuel) env d budget e = .ok e' →
      Expr.WScoped d e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      ∀ {ea ea' : AVExpr},
        CtxOkP m φ d Δa e →
        denoteP m.acval env φ d e = some ea →
        denoteP m.acval env φ d e' = some ea' →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) →
        (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea') ∧
          ∀ ρ : Nat → V, Sat2 V Δa ρ →
            interp2 V ρ ea = interp2 V ρ ea' := by
  intro budget
  induction budget with
  | zero =>
    intro d Δa e e' h
    rw [whnfLoop] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ budget ih =>
    intro d Δa e e' h hws hb hLb ea ea' hC hea hea' hok
    rw [whnfLoop, whnfStep] at h
    simp only [Bind.bind, Except.bind, Lech.whnfCore_def] at h
    cases hwc : whnfCore μ env fuel d e with
    | error err => rw [hwc] at h; exact nomatch h
    | ok e₁ =>
    rw [hwc] at h
    dsimp only at h
    obtain ⟨ea₁, hea₁⟩ := hex hwc hws hb hLb hC hea hok
    obtain ⟨hok₁, heq₁, hws₁, hb₁, hLb₁, hC₁⟩ :=
      whnfCore_packageP m ihwc hwc hws hb hLb hC hea hea₁ hok
    cases hrn : reduceNatP μ env fuel d e₁ with
    | error err =>
      rw [Lech.reduceNat_fold] at h; rw [hrn] at h; exact nomatch h
    | ok o =>
    rw [Lech.reduceNat_fold] at h
    rw [hrn] at h
    dsimp only at h
    match o, h with
    | some e₂, h =>
      obtain ⟨ea₂, hea₂, hok₂, heq₂, hws₂, hb₂, hLb₂, hC₂⟩ :=
        hnat hrn hws₁ hb₁ hLb₁ hC₁ hea₁ hok₁
      obtain ⟨hok', heq'⟩ :=
        ih h hws₂ hb₂ hLb₂ hC₂ hea₂ hea' hok₂
      exact ⟨hok', interp2C_trans (interp2C_trans heq₁ heq₂) heq'⟩
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
        exact ⟨hok', interp2C_trans heq₁ heq'⟩

/-- **`WhnfClaims2P` at `fuel + 1`.** -/
theorem whnf_claimsP (m : EnvS2Core V env) {fuel : Nat}
    (hex : WhnfCoreExistsP μ m φ fuel)
    (ihwc : WhnfCoreClaims2P μ m φ fuel)
    (hnat : ReduceNatStepP μ m φ fuel) (hdelta : DeltaP m φ) :
    WhnfClaims2P μ m φ (fuel + 1) := by
  intro d e e' Δa h hws hb hLb ea ea' hC hea hea' hok
  rw [Lech.whnf_succ, whnfBody] at h
  exact whnfLoop_claimP m hex ihwc hnat hdelta whnfLoopFuel h hws hb
    hLb hC hea hea' hok

/-! # T5 — the quarters -/

/-- The head-normalisation quarter, P currency. -/
def WhnfCoreStepP (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2Core V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2P μ m φ fuel → WhnfClaims2P μ m φ fuel →
    DefEqClaims2P μ m φ fuel → InferClaims2P μ m φ fuel →
    InferClaimsIO2P μ m φ fuel →
    WhnfCoreClaims2P μ m φ (fuel + 1)

/-- The reduction-loop quarter, P currency. -/
def WhnfStepP (μ : CheckMode) (V : Type w) [SetTheory V] : Prop :=
  ∀ (env : Env) (m : EnvS2Core V env) (φ : Name → Nat) (fuel : Nat),
    WhnfCoreClaims2P μ m φ fuel → WhnfClaims2P μ m φ fuel →
    DefEqClaims2P μ m φ fuel → InferClaims2P μ m φ fuel →
    InferClaimsIO2P μ m φ fuel →
    WhnfClaims2P μ m φ (fuel + 1)

/-- **The two quarters' routed inputs.**  Six fields where the `…D`
lane's `whnfCoreStep2E_of`/`whnfStep2E_of` between them take five
(`hex` bundling three, `hinst`, `hiota`, `hproj`, `hnat`, `hdelta`):
`Denote2Inst1B` is gone (`denoteP_beta`), `Delta2B` is replaced by the
strictly weaker `AcvalDefnInstP` (`deltaP_of` discharges it), and the
existence factor is split into the two components these quarters
actually read — defeq's is empty and `whnf`'s is unused here. -/
structure WhnfInputsP (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop where
  /-- the head reduct annotates (`WhnfCoreExists2E`'s transpose) -/
  core_exists : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), WhnfCoreExistsP μ m φ fuel
  /-- the inferred type annotates (`InferExists2E`'s transpose), at
  the io slot (task #172 B4 — the β certificate's inference is a
  converted call site) -/
  infer_exists : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), InferExistsIOSP μ m φ fuel
  /-- the ι clause -/
  iota : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), IotaStepP μ m φ fuel
  /-- the projection clause -/
  proj : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), ProjStepP μ m φ fuel
  /-- the `Nat`-literal reduction clause.  It takes the whnf claims at
  the same fuel: `reduceNat` head-normalises its arguments before
  reading them as literals, so the row's own `interp2` equality needs
  whnf soundness there (the collapse lane's `reduceNat_stepR` takes the
  same IH).  `whnfStepP_of` was already holding — and discarding —
  exactly this argument. -/
  nat : ∀ {env : Env} (m : EnvS2Core V env) (φ : Name → Nat)
    (fuel : Nat), WhnfClaims2P μ m φ fuel → ReduceNatStepP μ m φ fuel
  /-- the δ exit's single obligation -/
  defn : ∀ {env : Env} (m : EnvS2Core V env), AcvalDefnInstP m

/-- **`whnfCoreStepP_of` — the head-normalisation quarter, P
currency.**  `hμ` is *unused* (flagged in the module docstring); it is
carried so the four quarters assemble under one mode hypothesis. -/
theorem whnfCoreStepP_of (_hμ : μ.verifiedChecks = true)
    (hin : WhnfInputsP V μ) : WhnfCoreStepP μ V :=
  fun _env m φ fuel ihwc _ ihd ihi ihio =>
    whnfCore_claimsP m (hin.core_exists m φ fuel)
      (betaCertP_of_claims m (hin.infer_exists m φ fuel) ihd
        (inferClaimsIOS2P_of ihi ihio))
      (hin.iota m φ fuel) (hin.proj m φ fuel) ihwc

/-- **`whnfStepP_of` — the reduction loop, P currency.**  `hμ` unused,
as above. -/
theorem whnfStepP_of (_hμ : μ.verifiedChecks = true)
    (hin : WhnfInputsP V μ) : WhnfStepP μ V :=
  fun _env m φ fuel ihwc ihw _ _ _ =>
    whnf_claimsP m (hin.core_exists m φ fuel) ihwc
      (hin.nat m φ fuel ihw) (deltaP_of m (hin.defn m))

end Lech.SetP
