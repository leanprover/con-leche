import Setlec.TTVerify.EtaCertStep

/-!
# The stuck fallback

`StuckIrrelStepTT`: `stuckIrrel`'s verdict yields an equation.  The
function is a chain of five certificate calls with proof irrelevance
last, and every link is a *named* checker function, so §8.6's factoring
rule puts one obligation on each and the chain itself is a walk:

| link | obligation |
| --- | --- |
| `pairEtaCert a b`, `pairEtaCert b a` | `PairEtaCertStepTT` |
| `structEtaCert a b`, `structEtaCert b a` | `StructEtaCertStepTT` |
| `structUnitCert a b` | **discharged here** |
| `proofIrrel a b` | `proofIrrel_stepTT` — proved |

The two `b a` calls are the same obligation used with `Deq.symm`: the
checker is deliberately symmetric here, and the bridge pays for that
symmetry once.
-/

namespace Setlec.TTVerify

/- Task #147: this file's lemmas are stated at the TT-lane mode — the
seven gated checks reduce definitionally at `.ttModel`, so the walks
below see the pre-#147 bodies (`CertifiedConfigTT` pins the running
mode to this value). -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- `pairEtaCert`'s verdict yields an equation. -/
def PairEtaCertStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    pairEtaCertP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- `structEtaCert`'s verdict yields an equation. -/
def StructEtaCertStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    structEtaCertP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-! ## The unit-like certificate

`structUnitCert` is the *consumer side* of `CapsOkTT`'s unit law, and
it lines up with it clause for clause — which is the §8.4 observation
once more: the certificate checks exactly the facts the fired law asks
for, because both were written against the same telescope.

`iotaCerts` on the family's parameter telescope becomes `TeleTyped`
(`certs_typed`), the two subjects' inferred types are identified by the
`defeq` the certificate runs, and `UnitLawTT` closes it. -/

/-- The denotation of a stored declaration's type at a level
instantiation, available at any depth. -/
theorem denote_declType {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ)) (us : List Level) (d : Nat) :
    ∃ TV, denote m.cval env φ d
      (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) = some TV := by
  obtain ⟨hnf, -, -, hb, -⟩ := m.wf ci (find?_mem hf)
  obtain ⟨t, ht, -⟩ := m.has_type ci (find?_mem hf)
    (Level.substFn φ ci.toConstantVal.levelParams us)
  refine ⟨t, ?_⟩
  rw [denote_depth_closed hcl
      (by rw [Expr.hasFvar_instantiateLevelParams]; exact hnf)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hb),
    denoteClosed, denote_instLevels m.val_params φ 0]
  exact ht

/-- **`StructUnitCertStepTT`, discharged.** -/
theorem structUnitCert_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) :
    ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
      structUnitCertP mode env fuel d a b = .ok true →
      Expr.WScoped d a → a.looseBVarsBounded 0 = true →
      Expr.LeavesBounded a →
      Expr.WScoped d b → b.looseBVarsBounded 0 = true →
      Expr.LeavesBounded b →
      CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
      ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
        denote m.cval env φ d b = some vb → Deq Δ va vb := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨ta, wta, T, us', cvT, caps, tb, wtb, hta, hwta, hfn, hfT, hunit,
    hres, hlenA, hlenU, -, htb, hwtb, hdeq, hcerts⟩ := structUnitCert_inv h
  -- each subject is typed at its own reduced type
  obtain ⟨va', Ta, hva', hTa, haT⟩ := ihi hta hwa hba hLa hCa
  obtain rfl : va = va' := by rw [hva'] at hva; exact (Option.some.inj hva).symm
  obtain ⟨vb', Tb, hvb', hTb, hbT⟩ := ihi htb hwb hbb hLb hCb
  obtain rfl : vb = vb' := by rw [hvb'] at hvb; exact (Option.some.inj hvb).symm
  have hCta : CtxOk m.cval env φ d Δ ta :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hwa) hCa
  have hwta' : Expr.WScoped d ta := inferTypeCore_WScoped m.wf fuel hta hwa
  have hbta : ta.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel hta hwa hba hLa
  have hLta : Expr.LeavesBounded ta := fun l hl =>
    hLa l (inferTypeCore_fvarLeaves m.wf fuel hta hwa l hl)
  have hCtb : CtxOk m.cval env φ d Δ tb :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hCb
  have hwtb' : Expr.WScoped d tb := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb : tb.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLb
  have hLtb : Expr.LeavesBounded tb := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  obtain ⟨WA, hWA, hDA⟩ := ihw hwta hwta' hbta hLta hCta hTa
  obtain ⟨WB, hWB, hDB⟩ := ihw hwtb hwtb' hbtb hLtb hCtb hTb
  -- the reducts' frames
  have hwra : Expr.WScoped d wta := whnf_WScoped m.wf fuel hwta hwta'
  have hbra : wta.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hwta hbta
  have hLra : Expr.LeavesBounded wta := fun l hl =>
    hLta l (whnf_fvarLeaves m.wf fuel hwta l hl)
  have hCra : CtxOk m.cval env φ d Δ wta :=
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwta) hCta
  have hwrb : Expr.WScoped d wtb := whnf_WScoped m.wf fuel hwtb hwtb'
  have hbrb : wtb.looseBVarsBounded 0 = true :=
    whnf_looseBVars m.wf fuel hwtb hbtb
  have hLrb : Expr.LeavesBounded wtb := fun l hl =>
    hLtb l (whnf_fvarLeaves m.wf fuel hwtb l hl)
  have hCrb : CtxOk m.cval env φ d Δ wtb :=
    CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hCtb
  -- the two reduced types agree
  have hDW : Deq Δ WA WB :=
    ihd hdeq hwra hbra hLra hwrb hbrb hLrb hCra hCrb hWA hWB
  -- the family's telescope, certified
  obtain ⟨TV, hTV⟩ := denote_declType m φ hfT hcl us' d
  obtain ⟨hwty, hbty, hLty, hCty⟩ := closed_frames (cval := m.cval)
    (env := env) (φ := φ) hCa.1
    (by rw [Expr.hasFvar_instantiateLevelParams cvT.levelParams us']
        exact (m.wf _ (find?_mem hfT)).1)
    (by
      rw [Expr.looseBVarsBounded_instantiateLevelParams cvT.levelParams us']
      exact (m.wf _ (find?_mem hfT)).2.2.2.1)
  obtain ⟨xs, rest, hfit⟩ := certs_typed m φ hcl ihd ihi _ wta.getAppArgs
    TV hcerts hwty hbty hLty hCty hTV (fun x hx =>
      ⟨hwra.getAppArgs x hx, looseBVarsBounded_getAppArgs hbra x hx,
        fun l hl => hLra l (fvarLeaves_getAppArgs hx l hl),
        CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hCra⟩)
  obtain ⟨RV, hVfit, -⟩ := hfit.toV hcl hTV
  -- the reduced type is the family applied to the certified spine
  have hWA' : WA = VExpr.mkAppN
      (m.cval T (Level.substFn φ cvT.levelParams us')) xs := by
    have hmk : wta = Expr.mkAppN (.const T us') wta.getAppArgs := by
      rw [← hfn, Expr.mkAppN_getApp]
    have := denote_mkAppN (cval := m.cval) (env := env) (φ := φ) (d := d)
      (vf := m.cval T (Level.substFn φ cvT.levelParams us')) hfit.spine
      (by rw [denote_const, hfT]
          dsimp only
          rw [if_pos (show us'.length
            = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
            from hlenU)]
          rfl)
    rw [← hmk, hWA] at this
    exact Option.some.inj this
  refine m.caps_ok.2 T cvT caps hfT hunit hres φ d Δ us' xs TV RV va vb
    (by rw [hfit.spine.length, hlenA]) hTV hVfit ?_ ?_
  · rw [← hWA']; exact Deq.conv haT hDA
  · rw [← hWA']; exact Deq.conv (Deq.conv hbT hDB) hDW.symm

/-! ## The chain -/

/-- **`StuckIrrelStepTT`**, modulo the two remaining certificates. -/
theorem stuckIrrel_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT mode m φ fuel) (ihd : DefEqClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel)
    (hpe : PairEtaCertStepTT m φ fuel)
    (hse : StructEtaCertStepTT m φ fuel) : StuckIrrelStepTT m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  simp only [stuckIrrelP, stuckIrrel, Bind.bind, Except.bind,
    pairEtaCert_fold, structEtaCert_fold, structUnitCert_fold,
    proofIrrel_fold] at h
  cases h1 : pairEtaCertP mode env fuel d a b with
  | error err => rw [h1] at h; exact nomatch h
  | ok r1 =>
  rw [h1] at h
  dsimp only at h
  cases r1 with
  | true => exact hpe h1 hwa hba hLa hwb hbb hLb hCa hCb hva hvb
  | false =>
  simp only [Bool.false_eq_true, if_false] at h
  cases h2 : pairEtaCertP mode env fuel d b a with
  | error err => rw [h2] at h; exact nomatch h
  | ok r2 =>
  rw [h2] at h
  dsimp only at h
  cases r2 with
  | true => exact (hpe h2 hwb hbb hLb hwa hba hLa hCb hCa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, if_false] at h
  cases h3 : structEtaCertP mode env fuel d a b with
  | error err => rw [h3] at h; exact nomatch h
  | ok r3 =>
  rw [h3] at h
  dsimp only at h
  cases r3 with
  | true => exact hse h3 hwa hba hLa hwb hbb hLb hCa hCb hva hvb
  | false =>
  simp only [Bool.false_eq_true, if_false] at h
  cases h4 : structEtaCertP mode env fuel d b a with
  | error err => rw [h4] at h; exact nomatch h
  | ok r4 =>
  rw [h4] at h
  dsimp only at h
  cases r4 with
  | true => exact (hse h4 hwb hbb hLb hwa hba hLa hCb hCa hvb hva).symm
  | false =>
  simp only [Bool.false_eq_true, if_false] at h
  cases h5 : structUnitCertP mode env fuel d a b with
  | error err => rw [h5] at h; exact nomatch h
  | ok r5 =>
  rw [h5] at h
  dsimp only at h
  cases r5 with
  | true =>
    exact structUnitCert_stepTT m φ hcl ihw ihd ihi h5 hwa hba hLa hwb hbb
      hLb hCa hCb hva hvb
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    exact proofIrrel_stepTT m φ ihw ihi h hwa hba hLa hwb hbb hLb hCa hCb
      hva hvb

end Setlec.TTVerify
