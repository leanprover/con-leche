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

/-! ## The stuck-major rescues

`majorToCtor` has two.  The **eta** rescue is below and proved.  The
**K** rescue is *blocked on a layer change*, not merely unwritten: its
certificate (`proofIrrel fab major`) identifies inhabitants of two
*different* `Prop`s — and in its unit-like branch, of `PUnit` at two
different *levels*, `isUnitLikeTy` matching `.const c _` — while
`HasType.proofIrrel` and `HasType.punitEta` each demand one type for
both subjects.  Both rules are over-constrained relative to their own
soundness proofs (`Setlec/TTVerify/DESIGN.md` §10.2).  Left blocked
rather than worked around, as `.proj` is.

## The stuck-major eta rescue

`majorToCtor`'s eta branch (`Setlec/Kernel/Core.lean`) replaces a major
that will not whnf to a constructor by the *fabrication*
`C p⃗ (proj₀ p⃗ b) … (proj_{n-1} p⃗ b)`, certified by
`structEtaCertWith`.  On the bridge side that replacement is
`EnvTT.caps_ok`'s eta law, and the lemma below is the consumer that
shows the field is shaped for it (house rule,
`Setlec/TT/DESIGN.md` §3.1).

**The two hypotheses are exactly the pre-registered ones.**
`structEtaCertWith` runs `iotaCerts` on `T`'s parameter telescope at
`wtb.getAppArgs`, which `certs_typed` turns into the `TeleTyped` below;
and `majorToCtor` computes `tmaj ← whnf (infer major)`, which the
inference and whnf claims turn into the subject's typing at `T p⃗`.
Recorded in `Setlec/TTVerify/DESIGN.md` §6 as a prediction *before*
`EtaLawTT` was written, and confirmed verbatim — so the field's shape
was fixed by the prediction rather than fitted to the code
afterwards. -/

/-- **The eta rescue.**  A stuck major and its fabricated constructor
form denote to `Deq`-equal terms. -/
theorem eta_rescue {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {d : Nat} {Δ : List VExpr}
    {T : Name} {cvT : ConstantVal} {caps : IndCaps} {ust : List Level}
    {major : Expr} {targs : List Expr} {xs : List VExpr} {rest : Expr}
    {B F : VExpr}
    (hT : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true)
    (hres : reservedBasisNames.contains T = false)
    (hfam : EtaFamilyStoredT env T caps)
    (hlen : targs.length = caps.etaParams)
    (hfit : TeleTyped m.cval env φ d Δ
      (cvT.type.instantiateLevelParams cvT.levelParams ust) targs xs rest)
    (hB : denote m.cval env φ d major = some B)
    (hBt : HasType Δ B
      (VExpr.mkAppN (m.cval T (Level.substFn φ cvT.levelParams ust)) xs))
    (hF : denote m.cval env φ d
      (Expr.mkAppN (.const caps.etaCtor ust)
        (etaFabArgs T ust targs major caps.etaFields)) = some F) :
    Deq Δ B F :=
  m.caps_ok.1 T cvT caps hT heta hres hfam φ d Δ ust targs major xs rest
    B F hlen hfit hB hBt hF

end Setlec.TTVerify
