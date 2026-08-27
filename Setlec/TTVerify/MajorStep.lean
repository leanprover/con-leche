import Setlec.TTVerify.LitCtorStep

/-!
# The stuck-major rescue

`MajorToCtorStepTT`, the last of `WhnfCoreClaimsTT`'s three chain
links.  `majorToCtor` either returns the major untouched — nothing to
prove, the reduct *is* the subject — or replaces it by a fabrication
certified in one of three ways:

| branch | certificate | bridge lemma |
| --- | --- | --- |
| K (`caps.ruleK`, zero fields) | `proofIrrel fab major` | `proofIrrel_stepTT` |
| structural η | `structEtaCertWith fab major tmaj` | `structEtaCertWith_stepTT` |
| zero-field η (pinned `PUnit`) | `proofIrrel fab major` | `proofIrrel_stepTT` |

All three are already discharged, so the work here is the *dispatch*
and the fabrication's own facts — its frame conditions and the fact
that it denotes at all.

Both are §8.4 again, and unusually cleanly.  The frame conditions are
literally the checker's own guard: `majorToCtor` runs

```
fab.wscopedB depth && fab.looseBVarsBounded 0 &&
  fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)
```

before it will use the fabrication, and those three Booleans are
`Expr.WScoped d fab`, the bound, and — with `CtxOk.of_subset` — the
context correspondence.  The denotation comes from the *other* guard:
`iotaCerts` on the constructor's telescope, whose `certs_typed`
transpose produces a `DenoteSpine` over exactly the fabrication's
argument list, and `denote_mkAppN` assembles it.

So the scope guard the checker added for its own verification
(`annotateProjElim`'s sibling) is the whole of the bridge's frame
obligation here, and the synthetic-spine certificate of task #71 is the
whole of its denotation obligation.
-/

namespace Setlec.TTVerify

/- Task #147: this file's lemmas are stated at the TT-lane mode — the
seven gated checks reduce definitionally at `.ttModel`, so the walks
below see the pre-#147 bodies (`CertifiedConfigTT` pins the running
mode to this value). -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- A fabricated constructor spine denotes, and carries the frame
conditions the checker's scope guard checked. -/
theorem fab_reduct {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel)
    {cj : Name} {cvj : ConstantVal} {cnP cnF : Nat} {ust : List Level}
    {L : List Expr}
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hlenU : cvj.levelParams.length = ust.length)
    (hcerts : iotaCertsP mode env fuel d
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      L = .ok true)
    (hws : Expr.WScoped d (Expr.mkAppN (.const cj ust) L))
    (hb : (Expr.mkAppN (.const cj ust) L).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (Expr.mkAppN (.const cj ust) L))
    (hC : CtxOk m.cval env φ d Δ
      (Expr.mkAppN (.const cj ust) L)) :
    ∃ w, denote m.cval env φ d
      (Expr.mkAppN (.const cj ust) L) = some w := by
  obtain ⟨TV, hTV⟩ := denote_declType m φ hfj hcl ust d
  obtain ⟨hwty, hbty, hLty, hCty⟩ := closed_frames (cval := m.cval)
    (env := env) (φ := φ) hC.1
    (by rw [Expr.hasFvar_instantiateLevelParams cvj.levelParams ust]
        exact (m.wf _ (find?_mem hfj)).1)
    (by
      rw [Expr.looseBVarsBounded_instantiateLevelParams cvj.levelParams ust]
      exact (m.wf _ (find?_mem hfj)).2.2.2.1)
  obtain ⟨xs, rest, hfit⟩ := certs_typed m φ hcl ihd ihi _ L
    TV hcerts hwty hbty hLty hCty hTV (fun x hx => by
      have hx' : x ∈ (Expr.mkAppN (Expr.const cj ust)
          L).getAppArgs := by
        rw [Expr.getAppArgs_mkAppN]; exact hx
      exact ⟨hws.getAppArgs x hx', looseBVarsBounded_getAppArgs hb x hx',
        fun l hl => hLb l (fvarLeaves_getAppArgs hx' l hl),
        CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx' l hl) hC⟩)
  exact ⟨VExpr.mkAppN (m.cval cj (Level.substFn φ cvj.levelParams ust)) xs,
    denote_mkAppN (vf := m.cval cj (Level.substFn φ cvj.levelParams ust))
      hfit.spine
      (by rw [denote_const, hfj]
          dsimp only
          rw [if_pos (show ust.length
            = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
            from hlenU.symm)]
          rfl)⟩

/-- **`MajorToCtorStepTT`, discharged.** -/
theorem majorToCtor_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) : MajorToCtorStepTT m φ fuel := by
  intro d Δ c rules e e' v h hws hb hLb hC hv
  rcases majorToCtor_inv h with rfl | ⟨hsc, hbf, hleaf, rl, cvj, cnP, cnF,
    tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfj, hpr, hfT, hinf,
    hwtm, hfnm, hbranch⟩
  · exact ⟨v, hv, Deq.refl, hws, hb, hLb, hC⟩
  -- the fabrication's frame conditions are the checker's scope guard
  have hwsF : Expr.WScoped d e' := Expr.WScoped.of_wscopedB hsc
  have hCF : CtxOk m.cval env φ d Δ e' :=
    CtxOk.of_subset (fun l hl => by
      have := List.all_eq_true.mp hleaf l hl
      simpa using this) hC
  have hLbF : Expr.LeavesBounded e' := fun l hl =>
    hLb l (by
      have := List.all_eq_true.mp hleaf l hl
      simpa using this)
  -- the major's reduced type, and its frames
  have hCtm : CtxOk m.cval env φ d Δ tmaj₀ :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hinf hws) hC
  have hwtm₀ : Expr.WScoped d tmaj₀ :=
    inferTypeCore_WScoped m.wf fuel hinf hws
  have hbtm : tmaj₀.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hinf hws hb hLb
  have hLtm : Expr.LeavesBounded tmaj₀ := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel hinf hws l hl)
  obtain ⟨vE, Tm, hvE, hTm, hEt⟩ := ihi hinf hws hb hLb hC
  obtain rfl : vE = v := by rw [hvE] at hv; exact Option.some.inj hv
  obtain ⟨W, hW, hDW⟩ := ihw hwtm hwtm₀ hbtm hLtm hCtm hTm
  rcases hbranch with ⟨-, -, hlenU, -, -, rfl, hcerts, -, hpi⟩ |
    ⟨-, hctor, -, -, -, -, hlenU, -, rfl, hcerts, hcase⟩
  · -- the K rescue: the fabrication is certified by proof irrelevance
    obtain ⟨w, hw⟩ := fab_reduct m φ hcl ihd ihi hfj hlenU
      hcerts hwsF hbf hLbF hCF
    exact ⟨w, hw,
      (proofIrrel_stepTT m φ ihw ihi hpi hwsF hbf hLbF hws hb hLb hCF hC
        hw hv).symm,
      hwsF, hbf, hLbF, hCF⟩
  · -- the eta rescue, or its zero-field (pinned `PUnit`) variant
    obtain ⟨w, hw⟩ := fab_reduct m φ hcl ihd ihi (hctor ▸ hfj) hlenU
      hcerts hwsF hbf hLbF hCF
    refine ⟨w, hw, ?_, hwsF, hbf, hLbF, hCF⟩
    rcases hcase with hse | ⟨-, -, hpi⟩
    · exact (structEtaCertWith_stepTT m φ hcl ihd ihi hse hwsF hbf hLbF hCF
        hws hb hLb hC (whnf_WScoped m.wf fuel hwtm hwtm₀)
        (whnf_looseBVars m.wf fuel hwtm hbtm)
        (fun l hl => hLtm l (whnf_fvarLeaves m.wf fuel hwtm l hl))
        (CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwtm) hCtm)
        hW (Deq.conv hEt hDW) hw hv).symm
    · exact (proofIrrel_stepTT m φ ihw ihi hpi hwsF hbf hLbF hws hb hLb hCF
        hC hw hv).symm

/-! ## `CheckStepTT`, assembled — with no outstanding obligation

All four quarters.  The last hypothesis, `PairEtaCertStepTT`, was
carried as a parameter while task #130 was in flight
(`Setlec/TTVerify/DESIGN.md` §13); #130 landed, `pairEtaCert_stepTT`
discharges it, and the parameter is gone.

`CheckStepTT` is the `succ` case of the fuel induction, so with
`checkSoundTT`'s `zero` case already proved this closes the four claim
families at every fuel — the whole of stage 2's per-expression half. -/

/-- **`CheckStepTT`, proved.** -/
theorem checkStepTT : CheckStepTT mode := by
  intro env m φ fuel ihwc ihw ihd ihi
  have hc : ∀ n ψ, VExpr.Closed (m.cval n ψ) := m.cval_closed
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact whnfCore_claimsTT_iota m φ hc (litMajorToCtor_stepTT m φ ihw)
      (majorToCtor_stepTT m φ hc ihw ihd ihi)
      (projLitToCtor_stepTT m φ ihw) ihwc ihw ihd ihi
  · exact whnf_claimsTT_closed m φ hc ihwc ihw
  · exact defeq_claimsTT_pairEta m φ hc ihwc ihw ihd ihi
      (pairEtaCert_stepTT m φ hc ihw ihd ihi)
  · exact infer_claimsTT_closed m φ hc ihw ihd ihi

/-- **The four claim families, at every fuel.** -/
theorem checkClaimsTT {env : Env} (m : EnvTT env) (φ : Name → Nat) :
    ∀ fuel : Nat, WhnfCoreClaimsTT mode m φ fuel ∧ WhnfClaimsTT mode m φ fuel ∧
      DefEqClaimsTT mode m φ fuel ∧ InferClaimsTT mode m φ fuel :=
  checkSoundTT checkStepTT m φ

end Setlec.TTVerify
