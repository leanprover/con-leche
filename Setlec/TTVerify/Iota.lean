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

/-- The comparand level list does not read the recursor's arguments —
both branches of `recFireComparands` compute it from the levels alone,
so a law may quote it at any argument list. -/
theorem recFireComparands_levels (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args args' : List Expr)
    (rP rP' : Nat) :
    (recFireComparands rl lps us cvjLps args rP).1
      = (recFireComparands rl lps us cvjLps args' rP').1 := by
  unfold recFireComparands
  split <;> rfl

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
    (hlenR : us.length = cv.levelParams.length)
    (hlenJ : usj.length = cvj.levelParams.length)
    -- the fire site's level test, in the form the law consumes
    (hlev : Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1)
    -- the recursor's telescope, certified at the full spine
    {TR : VExpr}
    (hcertR : iotaCertsP env fuel d
      (cv.type.instantiateLevelParams cv.levelParams us)
      (args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs]) = .ok true)
    (hwR : Expr.WScoped d (cv.type.instantiateLevelParams cv.levelParams us))
    (hbR : (cv.type.instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0
      = true)
    (hLR : Expr.LeavesBounded
      (cv.type.instantiateLevelParams cv.levelParams us))
    (hCR : CtxOk m.cval env φ d Δ
      (cv.type.instantiateLevelParams cv.levelParams us))
    (hiR : denote m.cval env φ d
      (cv.type.instantiateLevelParams cv.levelParams us) = some TR)
    (hargsR : ∀ x ∈ args ++ [Expr.mkAppN (.const (RecRule.ctor rl) usj) margs],
      Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk m.cval env φ d Δ x)
    -- the constructor's telescope, certified at its own spine
    {TC : VExpr}
    (hcertC : iotaCertsP env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs = .ok true)
    (hwC : Expr.WScoped d (cvj.type.instantiateLevelParams cvj.levelParams usj))
    (hbC : (cvj.type.instantiateLevelParams cvj.levelParams
      usj).looseBVarsBounded 0
      = true)
    (hLC : Expr.LeavesBounded
      (cvj.type.instantiateLevelParams cvj.levelParams usj))
    (hCC : CtxOk m.cval env φ d Δ
      (cvj.type.instantiateLevelParams cvj.levelParams usj))
    (hiC : denote m.cval env φ d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TC)
    (hargsC : ∀ x ∈ margs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧ CtxOk m.cval env φ d Δ x)
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
  obtain ⟨zs, restR, hfitR⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TR hcertR hwR hbR hLR hCR hiR hargsR
  obtain ⟨ys, restC, hfitC⟩ :=
    certs_typed m φ hcl ihd ihi _ _ TC hcertC hwC hbC hLC hCC hiC hargsC
  -- the constructor's spine denotes elementwise, so the major premise's
  -- own denotation is its `VExpr` application
  have hspC : DenoteSpine m.cval env φ d margs ys := hfitC.spine
  have hmaj : denote m.cval env φ d
      (Expr.mkAppN (.const (RecRule.ctor rl) usj) margs) =
      some (VExpr.mkAppN
        (m.cval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj))
          ys) := by
    refine denote_mkAppN hspC ?_
    simp [denote_const, hctor, ConstantInfo.toConstantVal, hlenJ]
  -- split the recursor's spine at its last entry, the major premise
  obtain ⟨xs, y, rfl, hspR, hy⟩ := DenoteSpine.snoc_inv hfitR.spine
  obtain rfl : y = VExpr.mkAppN
      (m.cval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys := by
    rw [hmaj] at hy; exact (Option.some.inj hy).symm
  -- the two sides are the spines' `VExpr` applications
  obtain ⟨RVR, hvR, -⟩ := hfitR.toV hcl hiR
  obtain ⟨RVC, hvC, -⟩ := hfitC.toV hcl hiC
  obtain rfl : L = VExpr.mkAppN (m.cval n (Level.substFn φ cv.levelParams us))
      (xs ++ [VExpr.mkAppN
        (m.cval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj))
          ys]) := by
    rw [denote_mkAppN (vf := m.cval n (Level.substFn φ cv.levelParams us))
      (DenoteSpine.append hspR (.cons hy .nil))
      (by simp [denote_const, hrec, ConstantInfo.toConstantVal, hlenR])] at hL
    exact (Option.some.inj hL).symm
  -- the field *produces* the right-hand side's denotation (§12.9)
  obtain ⟨RH, hRH, hlaw⟩ :=
    (m.rec_rules n cv mI rP rules hrec rl hrl hfire).2 φ d us hlenR
  obtain rfl : R = VExpr.mkAppN RH
      (xs.take rP ++ ys.drop (RecRule.ctorParams rl)) := by
    rw [denote_mkAppN (DenoteSpine.append (hspR.take rP)
      (hspC.drop (RecRule.ctorParams rl))) hRH] at hR
    exact (Option.some.inj hR).symm
  refine hlaw cvj cnP cnF hctor Δ usj xs ys TR TC RVR RVC ?_ ?_ hlenJ hlev
    hiR hiC hvR hvC
  · have := hspR.length
    omega
  · have := hspC.length
    omega

/-! ## The stuck-major rescues

`majorToCtor` has two.  The **eta** rescue is below and proved.  The
**K** rescue is *blocked on a layer change*, not merely unwritten: its
certificate (`proofIrrel fab major`) identifies inhabitants of two
*different* `Prop`s — and in its unit-like branch, of `PUnit` at two
different *levels*, `isUnitLikeTy` matching `.const c _` — while
`HasType.proofIrrel` and `HasType.punitEta` each demand one type for
both subjects.  Both rules are over-constrained relative to their own
soundness proofs (`Setlec/TTVerify/DESIGN.md` §10.2).  **Unblocked**: the
  layer change
landed, both rules now read per side, and `proof_irrel_step` below is
the branch's content.

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
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr}
    {T : Name} {cvT : ConstantVal} {caps : IndCaps} {ust : List Level}
    {major : Expr} {targs : List Expr} {xs : List VExpr} {rest : Expr}
    {TV B : VExpr}
    (hT : env.find? T = some (.indInfo cvT caps))
    (heta : caps.eta = true)
    (hres : reservedBasisNames.contains T = false)
    (hfam : EtaFamilyStoredT env T caps)
    (hlen : targs.length = caps.etaParams)
    (hlenC : ust.length = (levelParamsAt env caps.etaCtor).length)
    (hlenP : ∀ j, j < caps.etaFields →
      ust.length = (levelParamsAt env (projFnName T j)).length)
    (hTV : denote m.cval env φ d
      (cvT.type.instantiateLevelParams cvT.levelParams ust) = some TV)
    (hfit : TeleTyped m.cval env φ d Δ
      (cvT.type.instantiateLevelParams cvT.levelParams ust) targs xs rest)
    (hB : denote m.cval env φ d major = some B)
    (hBt : HasType Δ B
      (VExpr.mkAppN (m.cval T (Level.substFn φ cvT.levelParams ust)) xs)) :
    ∃ F, denote m.cval env φ d
      (Expr.mkAppN (.const caps.etaCtor ust)
        (etaFabArgs T ust targs major caps.etaFields)) = some F ∧
      Deq Δ B F := by
  obtain ⟨hcres, ⟨cvC, hfC⟩, hfP⟩ := hfam
  obtain ⟨rest', hvfit, -⟩ := hfit.toV hcl hTV
  have hsp : DenoteSpine m.cval env φ d targs xs := hfit.spine
  -- every fabricated field denotes to the law's projection application
  have hproj : DenoteSpine m.cval env φ d
      ((List.range caps.etaFields).map fun j =>
        Expr.mkAppN (.const (projFnName T j) ust) (targs ++ [major]))
      ((List.range caps.etaFields).map fun j =>
        VExpr.mkAppN (m.cval (projFnName T j)
          (Level.substFn φ (levelParamsAt env (projFnName T j)) ust))
          (xs ++ [B])) := by
    refine DenoteSpine.map fun j hj => ?_
    obtain ⟨cvP, mI, rP, rules, hfPj⟩ := hfP j (List.mem_range.mp hj)
    refine denote_mkAppN (DenoteSpine.append hsp (.cons hB .nil)) ?_
    simp [denote_const, hfPj, levelParamsAt, ConstantInfo.toConstantVal,
      hlenP j (List.mem_range.mp hj)]
  refine ⟨VExpr.mkAppN (m.cval caps.etaCtor
      (Level.substFn φ (levelParamsAt env caps.etaCtor) ust))
      (xs ++ (List.range caps.etaFields).map fun j =>
        VExpr.mkAppN (m.cval (projFnName T j)
          (Level.substFn φ (levelParamsAt env (projFnName T j)) ust))
          (xs ++ [B])), ?_, ?_⟩
  · rw [etaFabArgs]
    refine denote_mkAppN (vf := m.cval caps.etaCtor
      (Level.substFn φ (levelParamsAt env caps.etaCtor) ust))
      (DenoteSpine.append hsp hproj) ?_
    simp [denote_const, hfC, levelParamsAt, ConstantInfo.toConstantVal, hlenC]
  · refine m.caps_ok.1 T cvT caps hT heta hres
      ⟨hcres, ⟨cvC, hfC⟩, hfP⟩ φ d Δ ust xs TV rest' B ?_ hTV hvfit hBt
    rw [hsp.length, hlen]

/-! ## The stuck-major K rescue

`majorToCtor`'s K branch fabricates the parameters-only constructor
application and certifies it with `proofIrrel fab major`, which checks
that **each side's inferred type is a `Prop`** — never that the two
agree.

This is the branch that motivated the layer change of
`Setlec/TTVerify/DESIGN.md` §10.2.  Before it, `HasType.proofIrrel`
demanded one `P` for both sides and this lemma could not be stated;
after it, the rule reads per side and the lemma is the certificate's
own facts handed straight to it.  Note that the proof below uses
`hTA` and `hTB` at *different* types — that is exactly the freedom the
generalization bought, and the reason the workaround (deriving through
`propext`, which needs binder weakening) was not worth paying for. -/

/-- **The K rescue's equation.**  Two expressions whose inferred types
are both `Prop`s denote to `Deq`-equal terms. -/
theorem proof_irrel_step {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} {d : Nat} {Δ : List VExpr}
    (ihw : WhnfClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {a b ta tb sta stb : Expr} {uT vT : Level}
    (hta : inferTypeCore env fuel d a = .ok ta)
    (hsta : inferTypeCore env fuel d ta = .ok sta)
    (hwa : whnf env fuel d sta = .ok (.sort uT)) (huT : uT.eval φ = 0)
    (htb : inferTypeCore env fuel d b = .ok tb)
    (hstb : inferTypeCore env fuel d tb = .ok stb)
    (hwb : whnf env fuel d stb = .ok (.sort vT)) (hvT : vT.eval φ = 0)
    (hCa : CtxOk m.cval env φ d Δ a) (hCb : CtxOk m.cval env φ d Δ b)
    (hwsa : Expr.WScoped d a) (hwsb : Expr.WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hLb : Expr.LeavesBounded b) :
    ∃ A B, denote m.cval env φ d a = some A ∧
      denote m.cval env φ d b = some B ∧ Deq Δ A B := by
  -- each side: its type is derivable, and that type is a `Prop`
  have side : ∀ {e t st : Expr} {u : Level},
      inferTypeCore env fuel d e = .ok t →
      inferTypeCore env fuel d t = .ok st →
      whnf env fuel d st = .ok (.sort u) → u.eval φ = 0 →
      CtxOk m.cval env φ d Δ e → Expr.WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      ∃ E T, denote m.cval env φ d e = some E ∧
        HasType Δ E T ∧ HasType Δ T (.sort 0) := by
    intro e t st u he ht hw hu hC hws hbe hLe
    obtain ⟨E, T, hE, hT, hEt⟩ := ihi he hws hbe hLe hC
    have hCt : CtxOk m.cval env φ d Δ t :=
      CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel he hws) hC
    have hwst : Expr.WScoped d t := inferTypeCore_WScoped m.wf fuel he hws
    have hbt : t.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel he hws hbe hLe
    have hLt : Expr.LeavesBounded t := fun l hl =>
      hLe l (inferTypeCore_fvarLeaves m.wf fuel he hws l hl)
    obtain ⟨T', S, hT', hS, hTs⟩ := ihi ht hwst hbt hLt hCt
    obtain rfl : T' = T := by rw [hT'] at hT; exact Option.some.inj hT
    have hCs : CtxOk m.cval env φ d Δ st :=
      CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel ht hwst) hCt
    have hwss : Expr.WScoped d st := inferTypeCore_WScoped m.wf fuel ht hwst
    have hbst : st.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel ht hwst hbt hLt
    have hLst : Expr.LeavesBounded st := fun l hl =>
      hLt l (inferTypeCore_fvarLeaves m.wf fuel ht hwst l hl)
    obtain ⟨S', hS', hDeq⟩ := ihw hw hwss hbst hLst hCs hS
    rw [denote_sort, hu] at hS'
    obtain rfl : S' = .sort 0 := (Option.some.inj hS').symm
    exact ⟨E, T', hE, hEt, Deq.conv hTs hDeq⟩
  obtain ⟨A, TA, hA, hAt, hTA⟩ := side hta hsta hwa huT hCa hwsa hba hLa
  obtain ⟨B, TB, hB, hBt, hTB⟩ := side htb hstb hwb hvT hCb hwsb hbb hLb
  -- the two sides sit at *different* types; this is the relaxed rule
  exact ⟨A, B, hA, hB, ⟨TA, HasType.proofIrrel hTA hTB hAt hBt⟩⟩

end Setlec.TTVerify
