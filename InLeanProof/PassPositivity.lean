module

public import InLeanProof.PassNestWalk
public import InLeanProof.PassCtors
public import InLeanProof.DeclGuards
import ConLeche.Verify.Cached.BridgeCS3
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-positivity: the block's positivity against master's (task #451, lane O7-positivity)

* `allLevelParamsDefinedI_run`: InLean's level-parameter guard through the
  annotations (`withAnnotations`: the term and the interned types of the ids
  its variables reach) is master's on the reading, whose free variables carry
  their types: an id's reading is closed under the reach (`idLpd`).
* `checkAbsCtorSortsI_run`, `checkAbsCtorSortsAllI_run`: the fields' sorts
  of the root frame's normal forms, as `PassCtors.lean`'s fields.
* `checkBlockPositivityI_run`: the context, the uniform-occurrence check, the
  root frame and the fields' sorts.
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-! ## The level-parameter guard through the annotations -/

/-- **A reading's level parameters**: the closed reading's guard holds and every
occurring id's reading passes it, so the reading passes it. -/
theorem allLPD_toExpr {g : FVarId → Option ConLeche.Expr} (ps : List ConLeche.Name) :
    ∀ {e : Expr} {c : ConLeche.Expr}, toExpr g e = some c →
      (trC e).allLevelParamsDefined ps = true →
      (∀ x c', OccF x e → g x = some c' → c'.allLevelParamsDefined ps = true) →
      c.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar => intro c h _ _; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | lit => intro c h _ _; simp only [toExpr, Option.some.injEq] at h; subst h; rfl
  | mvar => intro c h; simp [toExpr] at h
  | fvar id => intro c h _ hid; exact hid id c rfl h
  | sort u =>
    intro c h ht _
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cu, hu, rfl⟩ := h
    rw [toLevel_eq_trL hu]
    exact ht
  | const n us =>
    intro c h ht _
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cus, hus, rfl⟩ := h
    rw [toLevels_eq_map hus]
    exact ht
  | app f a ihf iha | lam _ f a _ ihf iha | forallE _ f a _ ihf iha =>
    intro c h ht hid
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨cf, hf, ca, ha, rfl⟩ := h
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at ht ⊢
    exact ⟨ihf hf ht.1 fun x c' hx => hid x c' (.inl hx),
      iha ha ht.2 fun x c' hx => hid x c' (.inr hx)⟩
  | letE _ t v b _ iht ihv ihb =>
    intro c h ht hid
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ct, htt, cv, hv, cb, hb, rfl⟩ := h
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined, Bool.and_eq_true] at ht ⊢
    exact ⟨⟨iht htt ht.1.1 fun x c' hx => hid x c' (.inl hx),
      ihv hv ht.1.2 fun x c' hx => hid x c' (.inr (.inl hx))⟩,
      ihb hb ht.2 fun x c' hx => hid x c' (.inr (.inr hx))⟩
  | mdata _ x ih => intro c h ht hid; exact ih h ht hid
  | proj _ _ x ih =>
    intro c h ht hid
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨cx, hx, rfl⟩ := h
    simp only [trC, trE, ConLeche.Expr.allLevelParamsDefined] at ht ⊢
    exact ih hx ht hid

/-- An id reaching another reaches what that one reaches. -/
theorem RReach.of_succ {tys : Array Expr} {x y z : FVarId} (hs : y ∈ succIds tys x)
    (h : RReach tys (fun w => y = w) z) : RReach tys (fun w => x = w) z := by
  induction h with
  | base hp => subst hp; exact .step (.base rfl) hs
  | step _ hs' ih => exact .step ih hs'

/-- **An id's reading passes the guard** when every interned type it reaches
does (closed reading). -/
theorem idLpd {s : InLean.CState} (hfv : FVTableOK s) (ps : List ConLeche.Name) :
    ∀ (n d : Nat), (∀ y ty, RReach s.fvTys (fun z => fvId d n = z) y → fvTyOf s.fvTys y = some ty →
      (trC ty).allLevelParamsDefined ps = true) →
    ∀ c, fvT s (fvId d n) = some c → c.allLevelParamsDefined ps = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro d H c hc
    have htn : (tableOf s).transNum d n = some c := by
      simpa [fvT, FVarTable.trans, fvParts_fvId] using hc
    obtain ⟨-, ty, cty, hty', hcty, rfl⟩ := FVarTable.transNum_some htn
    have hty : s.fvTys[n]? = some ty := by simpa [tableOf] using hty'
    have hr : Expr.RangeOk ty := hfv.range n ty hty
    simp only [ConLeche.Expr.allLevelParamsDefined]
    refine allLPD_toExpr ps hcty (H (fvId d n) ty (.base rfl) (by simp [fvTyOf, fvParts_fvId, hty]))
      fun x c' hx hx' => ?_
    obtain ⟨d', m, rfl, hm, htm⟩ := FVarTable.inner_some hx'
    have hsucc : fvId d' m ∈ succIds s.fvTys (fvId d n) := by
      simp only [succIds, fvParts_fvId, hty]
      rw [Array.mem_toList_iff, mem_fvarIds hr]; exact hx
    exact ih m hm d' (fun y ty' hy hy' => H y ty' (RReach.of_succ hsucc hy) hy') c'
      (by simpa [fvT, FVarTable.trans, fvParts_fvId] using htm)

/-- **InLean's level-parameter guard** (`allLevelParamsDefined`, through the
annotations) reads no state, and its pass is master's on the reading. -/
theorem allLevelParamsDefinedI_run {s s' : InLean.CState} {lps : List Name} {e : Expr} {b : Bool}
    (hfv : FVTableOK s) (he : OkS s e = true)
    (h : InLean.allLevelParamsDefined lps e s = .ok (b, s')) :
    s' = s ∧ (b = true → (TrS s e).allLevelParamsDefined (lps.map toName) = true) := by
  have hre := RangeOk_of_OkS he
  have hte : toExpr (fvT s) e = some (TrS s e) := TransS_of_ok he
  let f : Expr → Bool := fun t => !t.hasLevelParam || (EO.levelParams t).all lps.contains
  have hf : ∀ t, Expr.RangeOk t → f t = true →
      (trC t).allLevelParamsDefined (lps.map toName) = true := by
    intro t hr ht
    refine allLevelParamsDefined_of_guard hr fun hl => ?_
    simpa [f, hl] using ht
  unfold InLean.allLevelParamsDefined InLean.withAnnotations InLean.fvarClosureM at h
  by_cases hn : (!e.hasFVar) = true
  · simp only [hn, ↓reduceIte] at h
    obtain ⟨l, s₁, h1, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h1
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨rfl, fun hb => ?_⟩
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hb
    have hfs : fvarS e = false := by
      rw [← Expr.hasFVar_eq hre]; simpa using hn
    exact allLPD_toExpr _ hte (hf e hre hb) fun x _ hx _ => absurd hx (not_occF_of_fvarS hfs)
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨l, s₁, h1, h⟩ := bind_run h
    obtain ⟨tys, s₂, h2, h1⟩ := bind_run h1
    simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨ids, s₃, h3, h1⟩ := bind_run h1
    obtain ⟨tys', s₄, h4, h3⟩ := bind_run h3
    simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    obtain ⟨rfl, rfl⟩ := pure_run h3
    obtain ⟨rfl, rfl⟩ := pure_run h1
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨rfl, fun hb => ?_⟩
    simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine allLPD_toExpr _ hte (hf e hre hb1) fun x c' hx hx' => ?_
    obtain ⟨d, n, rfl, -⟩ := FVarTable.trans_some hx'
    refine idLpd hfv _ n d (fun y ty hy hy' => ?_) c' hx'
    have hyc : (leafGuardM.closure s.fvTys s.fvTys.size (EO.fvarIds e).toList ∅ ∅).contains y =
        true := by
      rw [closure_contains_iff]
      exact hy.mono fun z hz => by
        subst hz; rw [Array.mem_toList_iff, mem_fvarIds hre]; exact hx
    have hmem : ty ∈ (leafGuardM.closure s.fvTys s.fvTys.size (EO.fvarIds e).toList ∅ ∅).toList.filterMap
        (fvTyOf s.fvTys) :=
      List.mem_filterMap.2 ⟨y, Std.HashSet.mem_toList.2 (Std.HashSet.mem_iff_contains.2 hyc), hy'⟩
    have hrt : Expr.RangeOk ty := by
      unfold fvTyOf at hy'
      split at hy'
      · exact hfv.range _ ty hy'
      · cases hy'
    exact hf ty hrt (hb2 ty hmem)

/-! ## The fields' sorts at the holes -/

/-- **One member's fields' sorts** (`checkAbsCtorSorts`): each normal form's
level parameters, its fields opened at the holes' context, their sorts;
master's on the readings. -/
theorem checkAbsCtorSortsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} :
    ∀ (cs : List (Lean.ConstantVal × Nat)) (os : List (List InLean.NestFieldKind × Lean.Expr))
      {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → (∀ o ∈ os, OutOk s₀ (ctx.hiAt 0) o) →
      InLean.checkAbsCtorSorts (sharedOpsC .verified fe) fe ctx cs os s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkAbsCtorSorts (ConLeche.fueledOpsM .verified) L cctx (trCtorL cs)
          (trOuts s₀ os)) ()
  | [], os, s₀, s', u, hs, _, _, h => by
    unfold InLean.checkAbsCtorSorts at h
    obtain ⟨-, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    unfold ConLeche.checkAbsCtorSorts
    exact Runs.pure _
  | c :: cs, [], s₀, s', u, hs, _, _, h => by
    unfold InLean.checkAbsCtorSorts at h
    obtain ⟨-, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    unfold ConLeche.checkAbsCtorSorts
    exact Runs.pure _
  | c :: cs, o :: os, s₀, s', u, hs, hW, hos, h => by
    obtain ⟨hok, hwo, hco⟩ := hos o List.mem_cons_self
    unfold InLean.checkAbsCtorSorts at h
    obtain ⟨b, s₁, h1, h⟩ := bind_run h
    obtain ⟨rfl, hb⟩ := allLevelParamsDefinedI_run hs.fv hok h1
    cases b with
    | false =>
      simp only at h
      obtain ⟨_, _, h', -⟩ := bind_run h
      exact (throw_run h').elim
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨r, s₂, h2, h⟩ := bind_run h
    unfold InLean.openPisAtFvars at h2
    obtain ⟨hs₂, ht₂, hR2⟩ := openPisAtFvarsI_run c.2 (ctx.hiAt 0) hs hok hco h2
    obtain ⟨xq0, s₃, h3, h⟩ := bind_run h
    cases r with
    | none => simp only [InLean.unwrapOr] at h3; exact (throw_run h3).elim
    | some xq =>
    simp only [InLean.unwrapOr] at h3
    obtain ⟨rfl, rfl⟩ := pure_run h3
    obtain ⟨hokx, hokxb, hmX⟩ := hR2 xq.1 xq.2 rfl
    rw [ConLeche.Cached.openPisAtFvarsC_eq] at hmX
    have hfvX : ∀ (i : Nat) (x : ConLeche.Expr), (TrSL s₂ xq.1)[i]? = some x →
        (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (ctx.hiAt 0 + i) x.fvarTypeD ∧
          x.fvarTypeD.looseBVarsBounded 0 = true := by
      intro i x hx
      refine ⟨?_, openers_fvarTypeD_WScoped hmX hwo hx,
        (ConLeche.Verify.openPisAtFvars_bounded c.2 hmX hco).2 x (List.mem_of_getElem? hx)⟩
      obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index c.2 _ _ hmX i x hx
      exact ⟨_, _, rfl⟩
    obtain ⟨_, s₄, h4, h⟩ := bind_run h
    obtain ⟨hs₄, ht₄, hR4⟩ := checkStructFieldSortsIFI_run hJ.ops hW.sortOk hfvX c.2 hs₂ hokx
      rfl rfl rfl h4
    have ht04 := ht₂.trans ht₄
    obtain ⟨hos₄, htr₄⟩ := OutOk.mono ht04 (fun o' ho' => hos o' (List.mem_cons_of_mem _ ho'))
    obtain ⟨hs', ht', hR'⟩ := checkAbsCtorSortsI_run hJ cs os hs₄ (hW.mono ht04) hos₄ h
    refine ⟨hs', ht04.trans ht', ?_⟩
    rw [htr₄] at hR'
    unfold ConLeche.checkAbsCtorSorts
    simp only [trCtorL, trOuts, List.map_cons] at hR' ⊢
    simp only [hW.canon.lps, hb rfl, ↓reduceIte, hiAt_rel hW.canon,
      hmX, ConLeche.unwrapOr, hW.sort, isEquiv_zero_tr hW.sortOk]
    exact Runs.bind (Runs.pure _) (Runs.bind hR4 hR')

/-- **Every member's fields' sorts** (`checkAbsCtorSortsAll`). -/
theorem checkAbsCtorSortsAllI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {ctx : InLean.NestCtx} {cctx : ConLeche.NestCtx} :
    ∀ (css : List (List (Lean.ConstantVal × Nat)))
      (oss : List (List (List InLean.NestFieldKind × Lean.Expr))) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx →
      (∀ os ∈ oss, ∀ o ∈ os, OutOk s₀ (ctx.hiAt 0) o) →
      InLean.checkAbsCtorSortsAll (sharedOpsC .verified fe) fe ctx css oss s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkAbsCtorSortsAll (ConLeche.fueledOpsM .verified) L cctx
          (css.map trCtorL) (oss.map (trOuts s₀))) ()
  | [], oss, s₀, s', u, hs, _, _, h => by
    unfold InLean.checkAbsCtorSortsAll at h
    obtain ⟨-, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    unfold ConLeche.checkAbsCtorSortsAll
    exact Runs.pure _
  | cs :: css, [], s₀, s', u, hs, _, _, h => by
    unfold InLean.checkAbsCtorSortsAll at h
    obtain ⟨-, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, ?_⟩
    unfold ConLeche.checkAbsCtorSortsAll
    exact Runs.pure _
  | cs :: css, os :: oss, s₀, s', u, hs, hW, hoss, h => by
    unfold InLean.checkAbsCtorSortsAll at h
    obtain ⟨_, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hR1⟩ := checkAbsCtorSortsI_run hJ cs os hs hW (hoss os List.mem_cons_self) h1
    have hmono : ∀ os' ∈ oss, (∀ o ∈ os', OutOk s₁ (ctx.hiAt 0) o) ∧ trOuts s₁ os' = trOuts s₀ os' :=
      fun os' ho' => OutOk.mono ht₁ (hoss os' (List.mem_cons_of_mem _ ho'))
    obtain ⟨hs', ht', hR'⟩ := checkAbsCtorSortsAllI_run hJ css oss hs₁ (hW.mono ht₁)
      (fun os' ho' => (hmono os' ho').1) h
    refine ⟨hs', ht₁.trans ht', ?_⟩
    rw [List.map_congr_left (fun os' ho' => (hmono os' ho').2)] at hR'
    unfold ConLeche.checkAbsCtorSortsAll
    simp only [List.map_cons]
    exact Runs.bind hR1 hR'

/-! ## The block's positivity -/

theorem trShape_memberCtors (p : InLean.BlockShape) :
    (trShape p).memberCtors = p.memberCtors.map trCtorL := by
  simp [ConLeche.BlockShape.memberCtors, InLean.BlockShape.memberCtors, trShape, trMember, trCtorL,
    trCtor]

theorem trShape_nIdxs (p : InLean.BlockShape) : (trShape p).nIdxs = p.nIdxs := by
  simp [ConLeche.BlockShape.nIdxs, InLean.BlockShape.nIdxs, trShape, trMember]

theorem trSt_empty (s : InLean.CState) : trSt s {} = {} := by
  simp [trSt]

theorem StOk_empty (s : InLean.CState) : StOk s {} := by
  unfold StOk
  simp

/-- **The block's positivity** (`checkBlockPositivity`): the walk's context and
holes, official's uniform-occurrence check, the root frame from the empty
state, the fields' sorts; master's at the translated shape, on the readings. -/
theorem checkBlockPositivityI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hRF : ReducedFormerSimI) {p : InLean.BlockShape} {s₀ s' : InLean.CState}
    {v : List (List (List InLean.NestFieldKind × Lean.Expr)) × InLean.NestState}
    (hs : CSOKI .verified false L s₀)
    (hok : ∀ ms ∈ p.members, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true)
    (hct : ∀ cs ∈ p.memberCtors, ∀ c ∈ cs, CtorOkI c) (hsort : okL p.resSort = true)
    (h : InLean.checkBlockPositivity (sharedOpsC .verified fe) fe p s₀ = .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      (∀ os ∈ v.1, ∀ o ∈ os, OutOk s' (p.nP + p.memberNames.length) o) ∧ StOk s' v.2 ∧
      Runs (ConLeche.checkBlockPositivity (ConLeche.fueledOpsM .verified) L L.find? (trShape p))
        (v.1.map (trOuts s'), trSt s' v.2) := by
  unfold InLean.checkBlockPositivity at h
  obtain ⟨⟨ctx, holes⟩, s₁, h1, h⟩ := bind_run h
  obtain ⟨hs₁, ht₁, fvs, rfl, hokf, hokh, hclf, hwf, hholes, hR1⟩ :=
    blockNestCtxI_run L.find? hs hok h1
  simp only at h
  generalize hc : (trShape p).nestCtx (TrSL s₁ fvs) L.find? = cctx at hholes hR1
  have hR : CanonRel (p.nestCtx fvs fe) cctx := by
    subst hc
    exact ⟨trShape_memberNames p, trShape_lps p, rfl⟩
  have hW : WalkRel fe L s₁ (p.nestCtx fvs fe) cctx := by
    subst hc
    exact { canon := hR, fe := rfl, find := rfl, sort := rfl, sortOk := hsort,
            nIdxs := trShape_nIdxs p, params := rfl, paramsOk := hokf, paramsCl := hclf }
  -- the holes, scoped and closed at the frame
  have hctxOk : ConLeche.NestCtxOk cctx := by
    subst hc
    refine ⟨fun n ci hf => (hJ.wf.consts ci (List.mem_of_find?_eq_some hf)).1, fun cv hcv => ?_⟩
    simp only [ConLeche.BlockShape.nestCtx, trShape, List.map_map, List.mem_map] at hcv
    obtain ⟨ms, -, rfl⟩ := hcv
    exact trC_hasFvar _
  have hpar : ∀ x ∈ cctx.params, ConLeche.Expr.WScoped cctx.nP x := by
    subst hc
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hwf a ha
  have hHok := ConLeche.nestHoles_ok hctxOk hpar hholes
  have hhT : ∀ a ∈ holes, TOk s₁ ((p.nestCtx fvs fe).hiAt 0) a := by
    intro a ha
    obtain ⟨hw, i, ty, he⟩ := hHok (TrS s₁ a) (List.mem_map_of_mem ha)
    refine ⟨by simp only [OkSL, List.all_eq_true] at hokh; exact hokh a ha, ?_, ?_⟩
    · rw [← hiAt_rel hR]; exact hw
    · rw [he]; simp [ConLeche.Expr.looseBVarsBounded]
  have hpW : ∀ a ∈ (p.nestCtx fvs fe).params, ConLeche.Expr.WScoped ((p.nestCtx fvs fe).hiAt 0)
      (TrS s₁ a) := by
    intro a ha
    exact ConLeche.Expr.WScoped.mono (by simp [InLean.NestCtx.hiAt, InLean.BlockShape.nestCtx])
      (hwf a ha)
  have hlen : (p.nestCtx fvs fe).names.length ≤ holes.length := by
    have := ConLeche.nestHoles_length hholes
    rw [hR.names] at this
    simp [TrSL] at this
    omega
  -- the uniform-occurrence check
  obtain ⟨_, s₂, h2, h⟩ := bind_run h
  obtain ⟨hs₂, ht₂, hR2⟩ := nestUniformI_run hR (fun cs hcs c hc' => (hct cs hcs c hc').1) hs₁ h2
  -- the root frame
  obtain ⟨⟨outs, st⟩, s₃, h3, h⟩ := bind_run h
  simp only at h
  obtain ⟨hs₃, ht₃, hos, hst, hR3⟩ := nestRootI_run hJ hRF holes p.memberCtors {} hs₂
    (hW.mono ht₂) (StOk_empty _) (okSL_of_tabLe ht₂ hokh) (TOk_all_mono ht₂ hhT)
    (fun a ha => by
      rw [TrS_of_tabLe ht₂ (by
        simp only [InLean.BlockShape.nestCtx, OkSL, List.all_eq_true] at hokf ha
        exact hokf a ha)]
      exact hpW a ha)
    hlen hct h3
  -- the fields' sorts
  obtain ⟨_, s₄, h4, h⟩ := bind_run h
  obtain ⟨hs₄, ht₄, hR4⟩ := checkAbsCtorSortsAllI_run hJ p.memberCtors outs hs₃
    ((hW.mono ht₂).mono ht₃) hos h4
  obtain ⟨rfl, rfl⟩ := pure_run h
  have hmono : ∀ os ∈ outs, (∀ o ∈ os, OutOk s₄ ((p.nestCtx fvs fe).hiAt 0) o) ∧
      trOuts s₄ os = trOuts s₃ os := fun os hos' => OutOk.mono ht₄ (hos os hos')
  refine ⟨hs₄, ht₁.trans (ht₂.trans (ht₃.trans ht₄)), fun os hos' => (hmono os hos').1,
    (hst.mono ht₄).1, ?_⟩
  rw [(hst.mono ht₄).2, List.map_congr_left (fun os hos' => (hmono os hos').2)]
  rw [TrSL_of_tabLe ht₂ hokh, trSt_empty] at hR3
  unfold ConLeche.checkBlockPositivity
  refine Runs.bind hR1 ?_
  simp only [trShape_memberCtors]
  refine Runs.bind hR2 ?_
  refine Runs.bind hR3 ?_
  refine Runs.bind hR4 ?_
  exact Runs.pure _

end InLeanProof
