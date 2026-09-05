import Setlec.SetBase.Bridge.Irrel

/-!
# `Tele` from `iotaCerts` (task #148, T3, shared by batches d/e/g)

`certs_teleR` — the transpose of `certs_typed`
(`Setlec/TTVerify/Certs.lean`) and of `certs_fit`
(`Setlec/Model/Core/Certs.lean`): a successful `iotaCerts` run builds a
`Tele` derivation for the certified spine.

**This is the `iotaCerts` prediction discharged on the premise-exact
side.**  `Tele.cons` is `Infer Δ a ta → DefEq Δ ta A → Tele (B.inst a)
as rest`, and `iotaCerts`'s step is `infer arg` then `defeq ta dom` —
*the same pair, in the same order*.  So each step of the walk is the two
induction hypotheses and the constructor, with no conversion in
between: unlike every other consumer of the inference claim, this one
needs no `inferShapeR`, because the rule already asks for the pair the
slack produces.

Consumed by D10/D11 (the eta and unit certificates' telescopes), by R11
(the recursor's and the constructor's telescopes), by R12–R14 (the
task-#71 synthetic-spine certificates) and by R6 (the constructor-spine
certificate T4's second amendment exposed).
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- `DenoteSpine` is deterministic: the same expression spine has one
denotation.  Needed wherever a clause obtains its spine twice — once
from `denote_mkAppN_inv` on the subject and once from `certs_teleR`. -/
theorem DenoteSpine.det {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} : ∀ {as : List Expr} {vs ws : List VExpr},
      DenoteSpine cval env φ d as vs → DenoteSpine cval env φ d as ws →
      vs = ws := by
  intro as
  induction as with
  | nil => intro vs ws h1 h2; cases h1; cases h2; rfl
  | cons a as ih =>
    intro vs ws h1 h2
    cases h1 with | cons hv h1' => ?_
    cases h2 with | cons hw h2' => ?_
    obtain rfl : _ = _ := Option.some.inj (hv.symm.trans hw)
    rw [ih h1' h2']

/-- **A certified spine is a `Tele`.**  The spine's denotation is
existential (the inference claim *produces* it), as on the TT lane. -/
theorem certs_teleR {env : Env} (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (hg : mode.betaGate = false)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsR mode m φ fuel) (ihi : InferClaimsR mode m φ fuel) :
    ∀ {d : Nat} {Δ : List VExpr} (ty : Expr) (args : List Expr) (T : VExpr),
      iotaCertsP mode env fuel d false ty args = .ok true →
      Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty →
      CtxOkR mode m.cval env φ d Δ ty →
      denote m.cval env φ d ty = some T →
      (∀ x ∈ args, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkR mode m.cval env φ d Δ x) →
      ∃ vs rest, DenoteSpine m.cval env φ d args vs ∧
        Tele mode env m.cval φ Δ T vs rest := by
  intro d Δ ty args
  induction args generalizing ty with
  | nil =>
    intro T _ _ _ _ _ _ _
    exact ⟨[], T, DenoteSpine.nil, Tele.nil⟩
  | cons a as ih =>
    intro T hc hwty hbty hLbty hCty hity hargs
    match ty, hc with
    | .bvar _, hc => exact nomatch hc
    | .fvar _ _ _, hc => exact nomatch hc
    | .sort _, hc => exact nomatch hc
    | .const _ _, hc => exact nomatch hc
    | .app _ _, hc => exact nomatch hc
    | .lam _ _ _ _, hc => exact nomatch hc
    | .letE _ _ _ _, hc => exact nomatch hc
    | .lit _, hc => exact nomatch hc
    | .proj _ _ _, hc => exact nomatch hc
    | .forallE n dom body mt, hc =>
    obtain ⟨ta, hta, hde, hrest⟩ := iotaCerts_step_inv hc
    rw [Setlec.inferTypeIO_off hg] at hta
    obtain ⟨haw, hab, haLb, haC⟩ := hargs a List.mem_cons_self
    obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d dom ∧ Expr.WScoped d body := by
      simpa [Expr.WScoped] using hwty
    obtain ⟨hdomb, hbodyb⟩ :
        dom.looseBVarsBounded 0 = true ∧
          Expr.looseBVarsBounded 1 body = true := by
      simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
    have hCdom : CtxOkR mode m.cval env φ d Δ dom :=
      CtxOkR.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCty
    rw [denote_forallE] at hity
    split at hity
    · exact nomatch hity
    · next A hidom =>
      split at hity
      · exact nomatch hity
      · next B hibody =>
        obtain rfl : T = .pi A B := (Option.some.inj hity).symm
        -- the argument's inferred type, and its certificate against the
        -- domain: `Tele.cons`'s two premises, in the checker's order
        obtain ⟨x, tv, hix, hita, TX, hXI, hXD⟩ := ihi hta haw hab haLb haC
        obtain ⟨hwta, hbta, hLbta, hCta⟩ := frame_inferR m.wf hta haw hab haLb haC
        have hLbdom : Expr.LeavesBounded dom := fun l hl =>
          hLbty l (by simp [Expr.fvarLeaves, hl])
        have hDeq : DefEq mode env m.cval φ Δ tv A :=
          ihd hde hwta hbta hLbta hdomw hdomb hLbdom hCta hCdom hita hidom
        -- the instantiated residual denotes, by `denote_beta`
        have hfb : Expr.fvarsBelow d body := hbodyw.fvarsBelow
        have hibody' :
            denote m.cval env φ d (body.instantiate1 a) =
              some (VExpr.inst B x) := by
          rw [denote_beta (n := n) (ty := dom) hcl hfb haw hab hix 0, hibody]
          rfl
        have hwbody : Expr.WScoped d (body.instantiate1 a) :=
          Expr.WScoped.instantiate1_gen haw 0 hbodyw
        have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true :=
          Expr.looseBVarsBounded_instantiate1_gen hab hbodyb
        have hLbbody : Expr.LeavesBounded (body.instantiate1 a) := by
          intro l hl
          rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
          · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
          · exact haLb l hl'
        have hCbody : CtxOkR mode m.cval env φ d Δ (body.instantiate1 a) := by
          refine ⟨hCty.1, fun l hl => ?_⟩
          rcases Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
          · exact hCty.2 l (by simp [Expr.fvarLeaves, hl'])
          · exact haC.2 l hl'
        obtain ⟨xs, rest, hsp, hfit⟩ :=
          ih (body.instantiate1 a) (VExpr.inst B x) hrest hwbody hbbody
            hLbbody hCbody hibody'
            (fun y hy => hargs y (List.mem_cons_of_mem a hy))
        exact ⟨x :: xs, rest, DenoteSpine.cons hix hsp,
          Tele.cons hXI (hXD.trans hDeq) hfit⟩

/-- The denotation of a stored declaration's type at a level
instantiation, at the ambient depth: the three moves the `.const`
inference clause and the delta step use, packaged for the certificate
clauses that need a stored telescope's `VExpr` **and** its closedness
(deviation D1). -/
theorem denote_declTypeR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ)) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (us : List Level) (d : Nat) :
    ∃ T, denoteClosed m.cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some T ∧
      VExpr.Closed T ∧
      denote m.cval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some T := by
  obtain ⟨t, ht⟩ :=
    m.ty_denotes ci (find?_mem hf)
      (Level.substFn φ ci.toConstantVal.levelParams us)
  obtain ⟨hnf, -, -, hbd, -⟩ := m.wf ci (find?_mem hf)
  have hcls : VExpr.Closed t := denote_closed hcl hnf hbd ht
  have h0 : denoteClosed m.cval env φ
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some t := by
    rw [denoteClosed, denote_instLevels m.val_params]
    exact ht
  refine ⟨t, h0, hcls, ?_⟩
  rw [denote_instLevels m.val_params,
    denote_lift hcl (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow d
      (Nat.zero_le d)]
  rw [denoteClosed] at ht
  rw [ht]
  simp only [Option.map_some, Nat.sub_zero, VExpr.liftN_eq_self_of_closed hcls]

/-- The frame conditions of a stored declaration's instantiated type:
closed, so all four are free. -/
theorem frame_declTypeR {cval : TConstVal} {φ : Name → Nat} {env : Env}
    (hwf : EnvWF env) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (us : List Level) (d : Nat)
    {Δ : List VExpr} (hlen : Δ.length = d) :
    Expr.WScoped d (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) ∧
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) ∧
      CtxOkR mode cval env φ d Δ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) := by
  obtain ⟨hnf, -, -, hbd, -⟩ := hwf ci (find?_mem hf)
  have hnf' : (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]
    exact hnf
  refine ⟨Expr.WScoped.of_not_hasFvar hnf', ?_,
    Expr.LeavesBounded.of_not_hasFvar hnf', ⟨hlen, fun l hl => ?_⟩⟩
  · rw [Expr.looseBVarsBounded_instantiateLevelParams]
    exact hbd
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf'] at hl
    exact nomatch hl

end Setlec.SetR
