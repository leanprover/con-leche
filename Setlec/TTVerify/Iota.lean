import Setlec.TTVerify.Certs

/-!
# Firing a modeled-inductive iota rule

The **assembly** half of the iota clause (`Setlec/TTVerify/DESIGN.md`
§7): turning the two certification runs the checker performs at a fire
site into the two `TeleTyped`s the fired contract wants, and applying
`EnvTT.rec_rules`.

The other half — bridging the redex *as written* to the redex with its
major in constructor form — is `majorToCtor` soundness, and is not
here.  This module is the part that was de-risked by scouting: every
piece existed, nothing needed invention.

**Where the §6 fact appears.**  `rec_rules` is hypothesised on one
typing premise per argument, at the domain the rule fires at, and the
only supplier is the checker's own `iotaCerts` — which computes exactly
that list (`certs_typed`).  The chain below is that claim end to end,
with no step drawing on anything ambient.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- **The fired instance.**  Given the two `iotaCertsP` runs that
`iotaRec` performs before reducing — one against the recursor's
telescope at the full spine, one against the constructor's at its own —
the stored rule's contract applies at this instantiation.

The scoping and context side conditions are hypotheses: they are
`Expr`-level facts about stored types and the checker's own guards, and
the eventual clause discharges them from `EnvTT.wf` and the reduction's
invariants, exactly as the set model's iota case does. -/
theorem rec_rules_fire {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr}
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {us usj : List Level} {args margs : List Expr}
    (hrec : env.find? n = some (.recInfo cv mI rP rules))
    (hrl : rl ∈ rules) (hfire : RecRule.fire rl ≠ .inert)
    (hctor : env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF))
    (hlenA : args.length = mI)
    (hlenM : margs.length = RecRule.ctorParams rl + RecRule.nfields rl)
    -- the recursor's telescope, certified at the full spine
    {TR : VExpr}
    (hcertR : iotaCertsP env fuel d
      (cv.type.instantiateLevelParams cv.levelParams us)
      (args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs]) = .ok true)
    (hwR : Expr.WScoped d (cv.type.instantiateLevelParams cv.levelParams us))
    (hbR : (cv.type.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0
      = true)
    (hCR : CtxOk m.cval env φ d Δ
      (cv.type.instantiateLevelParams cv.levelParams us))
    (hiR : denote m.cval env φ d
      (cv.type.instantiateLevelParams cv.levelParams us) = some TR)
    (hargsR : ∀ x ∈ args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        CtxOk m.cval env φ d Δ x)
    -- the constructor's telescope, certified at its own spine
    {TC : VExpr}
    (hcertC : iotaCertsP env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs = .ok true)
    (hwC : Expr.WScoped d (cvj.type.instantiateLevelParams cvj.levelParams usj))
    (hbC : (cvj.type.instantiateLevelParams cvj.levelParams usj).looseBVarsBounded 0
      = true)
    (hCC : CtxOk m.cval env φ d Δ
      (cvj.type.instantiateLevelParams cvj.levelParams usj))
    (hiC : denote m.cval env φ d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC)
    (hargsC : ∀ x ∈ margs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      CtxOk m.cval env φ d Δ x)
    -- the two sides denote
    {L R : VExpr}
    (hL : denote m.cval env φ d
      (Expr.mkAppN (.const n us)
        (args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs])) = some L)
    (hR : denote m.cval env φ d
      (Expr.mkAppN
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        (args.take rP ++ margs.drop (RecRule.ctorParams rl))) = some R) :
    Deq Δ L R := by
  -- the checker's two certification runs become the contract's two
  -- telescope-typing hypotheses; this is `certs_typed`, i.e. the
  -- `iotaCerts` prediction of DESIGN §6 in use
  obtain ⟨xs, restR, hfitR⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TR hcertR hwR hbR hCR hiR hargsR
  obtain ⟨ys, restC, hfitC⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TC hcertC hwC hbC hCC hiC hargsC
  exact m.rec_rules n cv mI rP rules hrec rl hrl hfire cvj cnP cnF hctor
    φ d Δ us usj args margs xs ys restR restC L R hlenA hlenM hfitR hfitC
    hL hR

end Setlec.TTVerify
