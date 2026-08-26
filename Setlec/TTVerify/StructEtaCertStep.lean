import Setlec.TTVerify.StuckIrrelStep

/-!
# The structural-eta certificate

`StructEtaCertStepTT`: `structEtaCert`'s verdict yields an equation.

Unlike `pairEtaCert` (§13), this certificate is **self-sufficient**: it
runs `iotaCerts` on the family's parameter telescope and
`structEtaProjCerts` on each projection function's, so everything
`EtaLawTT` asks for is certified on the spot.  The proof is therefore
`eta_rescue` — already proved for `majorToCtor`'s stuck-major branch —
plus a spine congruence, and the *only* new work is turning
`structEtaCertWith`'s two half-`defEqList`s into one over the
fabrication's argument list.

That the same lemma serves both consumers is the §6 prediction paying
off a second time: `eta_rescue` was written against the shape
`structEtaCertWith` produces, and `structEtaCert` is `structEtaCertWith`
with the stuck side's type reduced by the caller instead of by the
caller's caller.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- Two certified argument lists concatenate. -/
theorem defEqList_append {env : Env} {fuel d : Nat} :
    ∀ {as as' bs bs' : List Expr},
      defEqList (pureFns env fuel) env d as as' = .ok true →
      defEqList (pureFns env fuel) env d bs bs' = .ok true →
      defEqList (pureFns env fuel) env d (as ++ bs) (as' ++ bs')
        = .ok true := by
  intro as
  induction as with
  | nil =>
    intro as' bs bs' h1 h2
    cases as' with
    | nil => exact h2
    | cons _ _ => simp [defEqList, pure, Except.pure] at h1
  | cons a as ih =>
    intro as' bs bs' h1 h2
    cases as' with
    | nil => simp [defEqList, pure, Except.pure] at h1
    | cons a' as' =>
      rw [List.cons_append, List.cons_append]
      simp only [defEqList, Bind.bind, Except.bind, defeq_def] at h1 ⊢
      cases hde : isDefEqCore env fuel d a a' with
      | error err => rw [hde] at h1; exact nomatch h1
      | ok r =>
        rw [hde] at h1
        cases r with
        | false => simp [pure, Except.pure] at h1
        | true =>
          simp only [if_true] at h1 ⊢
          exact ih h1 h2

/-- The frame conditions of one fabricated projection application. -/
theorem etaFab_frames {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr}
    (hwt : ∀ x ∈ targs, Expr.WScoped d x)
    (hbt : ∀ x ∈ targs, x.looseBVarsBounded 0 = true)
    (hLt : ∀ x ∈ targs, Expr.LeavesBounded x)
    (hCt : ∀ x ∈ targs, CtxOk cval env φ d Δ x)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b) (hCb : CtxOk cval env φ d Δ b)
    (j : Nat) :
    Expr.WScoped d
        (Expr.mkAppN (.const (projFnName T j) us') (targs ++ [b])) ∧
      (Expr.mkAppN (.const (projFnName T j) us')
        (targs ++ [b])).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded
        (Expr.mkAppN (.const (projFnName T j) us') (targs ++ [b])) ∧
      CtxOk cval env φ d Δ
        (Expr.mkAppN (.const (projFnName T j) us') (targs ++ [b])) := by
  have hmem : ∀ x ∈ targs ++ [b], (Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true) ∧
      (Expr.LeavesBounded x ∧ CtxOk cval env φ d Δ x) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact ⟨⟨hwt x h, hbt x h⟩, hLt x h, hCt x h⟩
    · obtain rfl : x = b := by simpa using h
      exact ⟨⟨hwb, hbb⟩, hLb, hCb⟩
  refine ⟨Expr.WScoped.mkAppN (by simp [Expr.WScoped])
      (fun x hx => (hmem x hx).1.1),
    looseBVarsBounded_mkAppN rfl (fun x hx => (hmem x hx).1.2), ?_, ?_⟩
  · intro l hl
    rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at h
    · exact (hmem x hx).2.1 l hlx
  · refine ⟨hCb.1, fun l hl => ?_⟩
    rcases fvarLeaves_mkAppN hl with h | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at h
    · exact (hmem x hx).2.2.2 l hlx

/-- **The certificate against a given reduced type.**  Stated at
`structEtaCertWith` rather than at `structEtaCert` because that is
where the checker factors: `majorToCtor`'s eta rescue calls it with
the major's already-reduced type, and `structEtaCert` calls it with a
type it reduces itself.  Both consumers get the same lemma. -/
theorem structEtaCertWith_stepTT {env : Env} (m : EnvTT env)
    (φ : Name → Nat) {fuel : Nat}
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    {d : Nat} {Δ : List VExpr} {a b wtb : Expr} {va vb W : VExpr}
    (hcert : structEtaCertWithP env fuel d a b wtb = .ok true)
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a) (hCa : CtxOk m.cval env φ d Δ a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b) (hCb : CtxOk m.cval env φ d Δ b)
    (hwr : Expr.WScoped d wtb) (hbr : wtb.looseBVarsBounded 0 = true)
    (hLr : Expr.LeavesBounded wtb) (hCr : CtxOk m.cval env φ d Δ wtb)
    (hW : denote m.cval env φ d wtb = some W) (hbT : HasType Δ vb W)
    (hva : denote m.cval env φ d a = some va)
    (hvb : denote m.cval env φ d b = some vb) : Deq Δ va vb := by
  obtain ⟨c, us, cvc, cnP, cnF, T, us', cvT, caps, hfn, hfc, hlenA, hfnb,
    hfT, heta, hctor, hpP, hpF, hresT, hresC, hlenT, hlenU, hlps, _,
    hlev, hcerts, hprojs, hd1, hd2⟩ := structEtaCertWith_inv hcert
  -- the family's telescope, certified
  obtain ⟨TV, hTV⟩ := denote_declType m φ hfT hcl us' d
  obtain ⟨hwty, hbty, hLty, hCty⟩ := closed_frames (cval := m.cval)
    (env := env) (φ := φ) hCr.1
    (by rw [Expr.hasFvar_instantiateLevelParams cvT.levelParams us']
        exact (m.wf _ (find?_mem hfT)).1)
    (by
      rw [Expr.looseBVarsBounded_instantiateLevelParams cvT.levelParams us']
      exact (m.wf _ (find?_mem hfT)).2.2.2.1)
  have hargs : ∀ x ∈ wtb.getAppArgs, Expr.WScoped d x ∧
      x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
      CtxOk m.cval env φ d Δ x := fun x hx =>
    ⟨hwr.getAppArgs x hx, looseBVarsBounded_getAppArgs hbr x hx,
      fun l hl => hLr l (fvarLeaves_getAppArgs hx l hl),
      CtxOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hCr⟩
  obtain ⟨xs, rest, hfit⟩ := certs_typed m φ hcl ihd ihi _ wtb.getAppArgs
    TV hcerts hwty hbty hLty hCty hTV hargs
  -- the stuck side is typed at the family applied to that spine
  have hWeq : W = VExpr.mkAppN
      (m.cval T (Level.substFn φ cvT.levelParams us')) xs := by
    have hmk : wtb = Expr.mkAppN (.const T us') wtb.getAppArgs := by
      rw [← hfnb, Expr.mkAppN_getApp]
    have := denote_mkAppN (cval := m.cval) (env := env) (φ := φ) (d := d)
      (vf := m.cval T (Level.substFn φ cvT.levelParams us')) hfit.spine
      (by rw [denote_const, hfT]
          dsimp only
          rw [if_pos (show us'.length
            = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
            from hlenU)]
          rfl)
    rw [← hmk, hW] at this
    exact Option.some.inj this
  have hBt : HasType Δ vb (VExpr.mkAppN
      (m.cval T (Level.substFn φ cvT.levelParams us')) xs) := hWeq ▸ hbT
  -- the family is complete: constructor and projection functions stored
  have hfam : EtaFamilyStoredT env T caps := by
    refine ⟨by rw [hctor]; exact hresC, ⟨cvc, ?_⟩, fun j hj => ?_⟩
    · rw [hctor, hpP, hpF]; exact hfc
    · obtain ⟨cvp, mIp, rPp, rulesp, hfp, _, _, _⟩ :=
        structEtaProjCerts_inv (List.range cnF) hprojs j
          (List.mem_range.mpr (hpF ▸ hj))
      exact ⟨cvp, mIp, rPp, rulesp, hfp⟩
  -- the eta law, fired at the fabrication
  obtain ⟨F, hF, hDF⟩ := eta_rescue m φ hcl hfT heta hresT hfam
    (by rw [hlenT, hpP])
    (by rw [hctor, levelParamsAt, hfc]
        dsimp only [ConstantInfo.toConstantVal]
        rw [hlps]; exact hlenU)
    (fun j hj => by
      obtain ⟨cvp, _, _, _, hfp, hlpp, _, _⟩ :=
        structEtaProjCerts_inv (List.range cnF) hprojs j
          (List.mem_range.mpr (hpF ▸ hj))
      rw [levelParamsAt, hfp]
      dsimp only [ConstantInfo.toConstantVal]
      rw [hlpp]; exact hlenU)
    hTV hfit hvb hBt
  -- and the constructor application agrees with the fabrication
  have hea : a = Expr.mkAppN (.const c us) a.getAppArgs := by
    rw [← hfn, Expr.mkAppN_getApp]
  have hfab : Expr.mkAppN (.const caps.etaCtor us')
      (etaFabArgs T us' wtb.getAppArgs b caps.etaFields) =
      Expr.mkAppN (.const c us')
        (wtb.getAppArgs ++ (List.range cnF).map fun j =>
          Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
      := by rw [hctor, etaFabArgs, hpF]
  rw [hfab] at hF
  rw [hea] at hva
  obtain ⟨vfa, vas, hvfa, hspa, rfl⟩ := denote_mkAppN_inv hva
  obtain ⟨vfb, vbs, hvfb, hspb, rfl⟩ := denote_mkAppN_inv hF
  obtain rfl : vfa = vfb := denote_const_congr m φ hlev hvfa hvfb
  have hga : (Expr.mkAppN (Expr.const c us')
      (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))).getAppArgs =
      wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]) := Expr.getAppArgs_mkAppN _ _
  rw [← hga] at hspb
  refine Deq.trans ?_ hDF.symm
  refine spine_congr m φ ihd ?_ hwa hba hLa hCa ?_ ?_ ?_ ?_ hspa hspb
    Deq.refl
  · rw [hga, ← List.take_append_drop cnP a.getAppArgs]
    exact defEqList_append hd1 hd2
  · exact Expr.WScoped.mkAppN (by simp [Expr.WScoped]) (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact (hargs x h).1
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
        exact (etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j).1)
  · exact looseBVarsBounded_mkAppN rfl (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact (hargs x h).2.1
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
        exact (etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j).2.1)
  · intro l hl
    rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at hl'
    · rcases List.mem_append.mp hx with h | h
      · exact (hargs x h).2.2.1 l hlx
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
        exact (etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j).2.2.1 l hlx
  · refine ⟨hCr.1, fun l hl => ?_⟩
    rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at hl'
    · rcases List.mem_append.mp hx with h | h
      · exact (hargs x h).2.2.2.2 l hlx
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp h
        exact ((etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j).2.2.2).2 l hlx

/-- **`StructEtaCertStepTT`, discharged.** -/
theorem structEtaCert_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT m φ fuel) (ihd : DefEqClaimsTT m φ fuel)
    (ihi : InferClaimsTT m φ fuel) : StructEtaCertStepTT m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨tb, wtb, htb, hwtb, hcert⟩ := structEtaCert_inv h
  obtain ⟨vb', Tb, hvb', hTb, hbT⟩ := ihi htb hwb hbb hLb hCb
  obtain rfl : vb = vb' := by
    rw [hvb'] at hvb; exact (Option.some.inj hvb).symm
  have hCtb : CtxOk m.cval env φ d Δ tb :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htb hwb) hCb
  have hwtb' : Expr.WScoped d tb := inferTypeCore_WScoped m.wf fuel htb hwb
  have hbtb : tb.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel htb hwb hbb hLb
  have hLtb : Expr.LeavesBounded tb := fun l hl =>
    hLb l (inferTypeCore_fvarLeaves m.wf fuel htb hwb l hl)
  obtain ⟨W, hW, hDW⟩ := ihw hwtb hwtb' hbtb hLtb hCtb hTb
  exact structEtaCertWith_stepTT m φ hcl ihd ihi hcert hwa hba hLa hCa
    hwb hbb hLb hCb
    (whnf_WScoped m.wf fuel hwtb hwtb')
    (whnf_looseBVars m.wf fuel hwtb hbtb)
    (fun l hl => hLtb l (whnf_fvarLeaves m.wf fuel hwtb l hl))
    (CtxOk.of_subset (whnf_fvarLeaves m.wf fuel hwtb) hCtb)
    hW (Deq.conv hbT hDW) hva hvb

/-! ## The chain, closed but for one link

Everything `stuckIrrel` calls is now discharged except `pairEtaCert`,
whose obligation is blocked on task #130 (`Setlec/TTVerify/DESIGN.md`
§13): the certificate does not establish that the pair type's two
arguments are types, and `HasType.psigmaEta` needs exactly that.  When
#130 lands, `projEntry_tele_premises` turns its verdict into the two
premises and this hypothesis goes away. -/

/-- `StuckIrrelStepTT` with the structural certificates discharged. -/
theorem stuckIrrel_stepTT_closed {env : Env} (m : EnvTT env)
    (φ : Name → Nat) {fuel : Nat}
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihw : WhnfClaimsTT m φ fuel) (ihd : DefEqClaimsTT m φ fuel)
    (ihi : InferClaimsTT m φ fuel) (hpe : PairEtaCertStepTT m φ fuel) :
    StuckIrrelStepTT m φ fuel :=
  stuckIrrel_stepTT m φ hcl ihw ihd ihi hpe
    (structEtaCert_stepTT m φ hcl ihw ihd ihi)

/-- **`DefEqClaimsTT` at `fuel + 1`, modulo `PairEtaCertStepTT` alone.**
The third quarter of `CheckStepTT` is closed down to the single
blocked certificate. -/
theorem defeq_claimsTT_pairEta {env : Env} (m : EnvTT env)
    (φ : Name → Nat) {fuel : Nat}
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT m φ fuel) (ihw : WhnfClaimsTT m φ fuel)
    (ihd : DefEqClaimsTT m φ fuel) (ihi : InferClaimsTT m φ fuel)
    (hpe : PairEtaCertStepTT m φ fuel) : DefEqClaimsTT m φ (fuel + 1) :=
  defeq_claimsTT_stuck m φ hcl ihwc ihw ihd ihi
    (stuckIrrel_stepTT_closed m φ hcl ihw ihd ihi hpe)
    (etaCert_stepTT m φ hcl ihw ihd ihi)

end Setlec.TTVerify
