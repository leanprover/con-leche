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

/-- Denotation spines are unique: `denote` is a function. -/
theorem DenoteSpine.unique {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List VExpr},
      DenoteSpine cval env φ d as vs →
      DenoteSpine cval env φ d as vs' → vs = vs' := by
  intro as
  induction as with
  | nil => intro vs vs' h h'; cases h; cases h'; rfl
  | cons a as ih =>
    intro vs vs' h h'
    cases h with
    | cons hv hs =>
      cases h' with
      | cons hv' hs' =>
        cases hv.symm.trans hv'
        rw [ih hs hs']

private theorem map_range_getD' {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun k => l.getD k default) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD, List.getElem?_eq_getElem h2]

private theorem instSeq_const' : ∀ (args : List Expr) (t : Nat)
    (n : Name) (ls : List Level),
    Expr.instSeq args t (.const n ls) = .const n ls
  | [], _, _, _ => rfl
  | _ :: as, t, n, ls => instSeq_const' as (t - 1) n ls

/-- `piResidual` through a full-depth strip: the tower consumed by
exactly its depth is the stripped body under the argument spine.
(Task #119 §16.3: the residual-pin consumer's bridge from
`TeleTyped.rest_eq` to the pinned `directFam`.) -/
theorem piResidual_of_stripPis :
    ∀ (args : List Expr) {e : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      e.stripPis args.length = some (bs, body) →
      piResidual e args
        = some (Expr.instSeq args (args.length - 1) body) := by
  intro args
  induction args with
  | nil =>
    intro e bs body h
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  | cons a as ih =>
    intro e bs body h
    match e, h with
    | .forallE n dm b m, h =>
      simp only [List.length_cons, Expr.stripPis] at h
      cases hstrip : b.stripPis as.length with
      | none => rw [hstrip] at h; exact nomatch h
      | some q =>
        obtain ⟨bs0, body0⟩ := q
        rw [hstrip] at h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have hsome : ((b.instantiate1 a 0).stripPis as.length).isSome :=
          Expr.stripPis_instantiate1_isSome as.length 0
            (by rw [hstrip]; rfl)
        obtain ⟨bs1, body1, hstrip1⟩ : ∃ bs1 body1,
            (b.instantiate1 a 0).stripPis as.length = some (bs1, body1) := by
          cases hq : (b.instantiate1 a 0).stripPis as.length with
          | none => rw [hq] at hsome; exact nomatch hsome
          | some q => exact ⟨q.1, q.2, rfl⟩
        obtain ⟨hbody1, -⟩ :=
          Expr.stripPis_instantiate1_eq as.length 0 hstrip hstrip1
        show piResidual (b.instantiate1 a) as = _
        rw [ih hstrip1, hbody1]
        simp only [Nat.zero_add]
        rfl

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
    hlev, hcerts, hprojs, hd1, hcertsC, hd2⟩ := structEtaCertWith_inv hcert
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
  -- **task #119 §16.3: the law's premise** — the fabrication is typed
  -- at `T p⃗`, from task #137's constructor-telescope certificate plus
  -- the stored residual pin (`EnvTT.ctor_residual`)
  have hprojs' : ∀ j, j < cnF → ∃ cvp mIp rPp rulesp,
      env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp) ∧
      cvp.levelParams = cvT.levelParams := fun j hj => by
    obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ :=
      structEtaProjCerts_inv (List.range cnF) hprojs j
        (List.mem_range.mpr hj)
    exact ⟨cvp, mIp, rPp, rulesp, hfp, hlpp⟩
  have hprojDen : DenoteSpine m.cval env φ d
      ((List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))
      ((List.range cnF).map fun j =>
        VExpr.mkAppN (m.cval (projFnName T j)
          (Level.substFn φ (levelParamsAt env (projFnName T j)) us'))
          (xs ++ [vb])) := by
    refine DenoteSpine.map fun j hj => ?_
    obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp⟩ :=
      hprojs' j (List.mem_range.mp hj)
    refine denote_mkAppN (DenoteSpine.append hfit.spine
      (.cons hvb .nil)) ?_
    simp [denote_const, hfp, levelParamsAt, ConstantInfo.toConstantVal,
      hlpp, hlenU]
  -- the constructor's stored type denotes, and types its constant
  have hcname : cvc.name = c := by
    rw [Env.find?] at hfc
    have := List.find?_some hfc
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
  obtain ⟨hnfC, -, -, hbdC, -⟩ := m.wf _ (find?_mem hfc)
  obtain ⟨tv0, htv0, hct⟩ := m.has_type _ (find?_mem hfc)
    (Level.substFn φ cvc.levelParams us)
  dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal]
    at hnfC hbdC htv0 hct
  rw [hcname] at hct
  have hTVc : denote m.cval env φ d
      (cvc.type.instantiateLevelParams cvc.levelParams us)
      = some tv0 := by
    rw [denote_depth_closed hcl
        (by rw [Expr.hasFvar_instantiateLevelParams]; exact hnfC)
        (by rw [Expr.looseBVarsBounded_instantiateLevelParams]
            exact hbdC) d,
      denoteClosed, denote_instLevels m.val_params φ 0]
    exact htv0
  obtain ⟨hwtyC, hbtyC, hLtyC, hCtyC⟩ := closed_frames (cval := m.cval)
    (env := env) (φ := φ) hCr.1
    (by rw [Expr.hasFvar_instantiateLevelParams cvc.levelParams us]
        exact hnfC)
    (by
      rw [Expr.looseBVarsBounded_instantiateLevelParams cvc.levelParams us]
      exact hbdC)
  -- the certificate's telescope walk over the fabricated spine
  obtain ⟨zsC, restC, hfitC⟩ := certs_typed m φ hcl ihd ihi _
    (wtb.getAppArgs ++ (List.range cnF).map fun j =>
      Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
    tv0 hcertsC hwtyC hbtyC hLtyC hCtyC hTVc (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact hargs x h
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
        exact etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j)
  obtain rfl : zsC = xs ++ (List.range cnF).map fun j =>
      VExpr.mkAppN (m.cval (projFnName T j)
        (Level.substFn φ (levelParamsAt env (projFnName T j)) us'))
        (xs ++ [vb]) :=
    hfitC.spine.unique (DenoteSpine.append hfit.spine hprojDen)
  -- the stored constructor's residual is the pinned family application
  have hfcC : env.find? caps.etaCtor
      = some (.ctorInfo cvc caps.etaParams caps.etaFields) := by
    rw [hctor, hpP, hpF]; exact hfc
  obtain ⟨bsR, hstripR⟩ := m.ctor_residual T cvT caps cvc hfT heta hresT
    hfam.1 hfcC
  rw [hpP, hpF] at hstripR
  -- the walked residual, syntactically: the pin under the spine
  have hlenF : (wtb.getAppArgs ++ (List.range cnF).map fun j =>
      Expr.mkAppN (.const (projFnName T j) us')
        (wtb.getAppArgs ++ [b])).length = cnP + cnF := by
    simp [hlenT]
  have hsomeU : ((cvc.type.instantiateLevelParams cvc.levelParams
      us).stripPis (cnP + cnF)).isSome :=
    Expr.stripPis_instantiateLevelParams_isSome cvc.levelParams us
      (cnP + cnF) (by rw [hstripR]; rfl)
  obtain ⟨bsU, bodyU, hstripU⟩ : ∃ bsU bodyU,
      (cvc.type.instantiateLevelParams cvc.levelParams us).stripPis
        (cnP + cnF) = some (bsU, bodyU) := by
    cases hq : (cvc.type.instantiateLevelParams cvc.levelParams
        us).stripPis (cnP + cnF) with
    | none => rw [hq] at hsomeU; exact nomatch hsomeU
    | some q => exact ⟨q.1, q.2, rfl⟩
  obtain ⟨hbodyU, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvc.levelParams us (cnP + cnF) hstripR hstripU
  have hresidC := hfitC.rest_eq
  have hresid2 := piResidual_of_stripPis
    (wtb.getAppArgs ++ (List.range cnF).map fun j =>
      Expr.mkAppN (.const (projFnName T j) us') (wtb.getAppArgs ++ [b]))
    (by rw [hlenF]; exact hstripU)
  rw [hresidC, hlenF] at hresid2
  obtain rfl : restC = Expr.instSeq
      (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))
      (cnP + cnF - 1) bodyU := Option.some.inj hresid2
  -- the pin's body, level-instantiated
  have hbodyC : bodyU = Expr.mkAppN
      (.const T ((cvT.levelParams.map Level.param).map
        (Level.subst cvc.levelParams us)))
      ((List.range cnP).map fun k => Expr.bvar (cnF + cnP - 1 - k)) := by
    rw [hbodyU]
    show (Expr.mkAppN (.const T (cvT.levelParams.map Level.param))
      ((List.range cnP).map fun k =>
        Expr.bvar (cnF + cnP - 1 - k))).instantiateLevelParams
        cvc.levelParams us = _
    rw [instantiateLevelParams_mkAppN]
    refine congrArg (Expr.mkAppN _) ?_
    rw [List.map_map]
    rfl
  -- ... and consumed by the spine: `T` at the family's arguments
  have hrestSyn : Expr.instSeq
      (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))
      (cnP + cnF - 1) bodyU
      = Expr.mkAppN
        (.const T ((cvT.levelParams.map Level.param).map
          (Level.subst cvc.levelParams us)))
        wtb.getAppArgs := by
    rw [hbodyC, Expr.instSeq_mkAppN, instSeq_const']
    refine congrArg (Expr.mkAppN _) ?_
    rw [List.map_map]
    have hrhs := (map_range_getD' wtb.getAppArgs).symm
    rw [hlenT] at hrhs
    conv => rhs; rw [hrhs]
    refine List.map_congr_left fun k hk => ?_
    have hklt : k < cnP := List.mem_range.mp hk
    have hbcl : ∀ a ∈ wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]), a.looseBVarsBounded 0 = true := by
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact (hargs a h).2.1
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
        exact (etaFab_frames (cval := m.cval) (Δ := Δ)
          (fun y hy => (hargs y hy).1) (fun y hy => (hargs y hy).2.1)
          (fun y hy => (hargs y hy).2.2.1)
          (fun y hy => (hargs y hy).2.2.2) hwb hbb hLb hCb j).2.1
    have hhit := Expr.instSeq_bvar
      (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))
      (cnP + cnF - 1) (cnF + cnP - 1 - k) hbcl (by omega)
      (by rw [hlenF]; omega)
    have hidx : cnP + cnF - 1 - (cnF + cnP - 1 - k) = k := by omega
    rw [hidx] at hhit
    have hk2 : k < (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b])).length := by rw [hlenF]; omega
    rw [List.getElem?_eq_getElem hk2] at hhit
    have hgetk : (wtb.getAppArgs ++ (List.range cnF).map fun j =>
        Expr.mkAppN (.const (projFnName T j) us')
          (wtb.getAppArgs ++ [b]))[k] = wtb.getAppArgs.getD k default := by
      rw [List.getElem_append_left (by rw [hlenT]; omega)]
      simp [List.getD, List.getElem?_eq_getElem
        (show k < wtb.getAppArgs.length from by rw [hlenT]; omega)]
    rw [hgetk] at hhit
    exact (Option.some.inj hhit).symm
  -- the walked residual denotes to the law's type slot
  obtain ⟨RVc, hvfitC, hrestVC⟩ := hfitC.toV hcl hTVc
  rw [hrestSyn] at hrestVC
  have hrestDen : denote m.cval env φ d
      (Expr.mkAppN
        (.const T ((cvT.levelParams.map Level.param).map
          (Level.subst cvc.levelParams us)))
        wtb.getAppArgs)
      = some (VExpr.mkAppN
        (m.cval T (Level.substFn φ cvT.levelParams us')) xs) := by
    refine denote_mkAppN hfit.spine ?_
    rw [denote_const, hfT]
    dsimp only
    rw [if_pos (show ((cvT.levelParams.map Level.param).map
        (Level.subst cvc.levelParams us)).length
        = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from by simp [ConstantInfo.toConstantVal])]
    refine congrArg some ?_
    refine m.val_params T _ hfT _ _ ?_
    intro p hp
    dsimp only [ConstantInfo.toConstantVal] at hp ⊢
    rw [Level.substFn_map_subst (by simp) hp, ← hlps,
      Level.substFn_map_param, hlps,
      Level.substFn_congr (Level.isEquivList_sound hlev φ)]
  rw [hrestVC] at hrestDen
  obtain rfl : RVc = VExpr.mkAppN
      (m.cval T (Level.substFn φ cvT.levelParams us')) xs :=
    Option.some.inj hrestDen
  -- assembled: the fabrication's typing, in the law's spelling
  have hheads : m.cval caps.etaCtor
      (Level.substFn φ (levelParamsAt env caps.etaCtor) us')
      = m.cval c (Level.substFn φ cvc.levelParams us) := by
    rw [hctor, levelParamsAt, hfc]
    dsimp only [ConstantInfo.toConstantVal]
    rw [Level.substFn_congr (Level.isEquivList_sound hlev φ)]
  have hfabT : HasType Δ
      (VExpr.mkAppN (m.cval caps.etaCtor
          (Level.substFn φ (levelParamsAt env caps.etaCtor) us'))
        (xs ++ (List.range caps.etaFields).map fun j =>
          VExpr.mkAppN (m.cval (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us'))
            (xs ++ [vb])))
      (VExpr.mkAppN (m.cval T
        (Level.substFn φ cvT.levelParams us')) xs) := by
    rw [hheads, hpF]
    exact hvfitC.appN (HasType.weakenNil hct Δ)
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
    hTV hfit hvb hBt hfabT
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
