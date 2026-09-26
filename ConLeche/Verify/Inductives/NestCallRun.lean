module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The calls' run facts at a nested stage (lane NESTIND, session 27)

The run facts the calls' landing reads off the install, beside
`RecCheckRun.lean` and `PositivityInv.lean`:

* every checked major records the walk's normal forms at its class
  (`targetRecTys_nfs`: `TargetMajor.nfs = targetMajorNfs aux …`);
* every call's typing ran (`targetCallsOk_each`);
* the positivity run's normal forms have the constructors' shape, and the
  members' own entries are recorded (`checkBlockPositivity_memberEntry`).
-/

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-! ## A checked major's recorded normal forms -/

/-- **Stage (b) at one recursor: the major records its class's normal
forms** (`targetMajorOf_nfs` through the stage). -/
theorem targetRecTy_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape}
    {F : Nat} {cvRi : ConstantVal} {M : TargetMajor} {u : Level}
    (h : targetRecTy (fueledOps mode F) fe p nested aux cvTas ctorsAs rc
      = .ok (cvRi, M, u)) :
    M.nfs = targetMajorNfs aux M.lvls M.ds := by
  unfold targetRecTy at h
  obtain ⟨cvRi', hcv, h⟩ := exceptBind_ok h
  by_cases hroom : p.nP ≤ rc.rP
  case neg => rw [if_neg hroom] at h; close_throw h
  rw [if_pos hroom] at h
  by_cases hle : rc.rP ≤ rc.mI
  case neg => rw [if_neg hle] at h; close_throw h
  rw [if_pos hle] at h
  obtain ⟨x1, hx1, h⟩ := exceptBind_ok h
  obtain ⟨fvs, concl⟩ := x1
  obtain ⟨maj, hmaj, h⟩ := exceptBind_ok h
  obtain ⟨M', hM', h⟩ := exceptBind_ok h
  suffices hMM : M' = M by subst hMM; exact targetMajorOf_nfs hM'
  by_cases htgt : (M'.member.all (· == rc.tgt)) = true
  case neg => rw [if_neg htgt] at h; close_throw h
  rw [if_pos htgt] at h
  obtain ⟨u0, hpinTys, h⟩ := exceptBind_ok h
  obtain ⟨cvTP, hcvTP, h⟩ := exceptBind_ok h
  obtain ⟨x2, hx2, h⟩ := exceptBind_ok h
  obtain ⟨ud, hud, h⟩ := exceptBind_ok h
  by_cases hmI : (rc.mI == rc.rP + M'.nIdx) = true
  case neg => rw [if_neg hmI] at h; close_throw h
  rw [if_pos hmI] at h
  by_cases hargs : (maj.fvarTypeD.getAppArgs.length == M'.nPc + M'.nIdx &&
      maj.fvarTypeD.getAppArgs.drop M'.nPc == (fvs.drop rc.rP).take (rc.mI - rc.rP)) = true
  case neg => rw [if_neg hargs] at h; close_throw h
  rw [if_pos hargs] at h
  obtain ⟨idoms, hidoms, h⟩ := exceptBind_ok h
  obtain ⟨ui, hui, h⟩ := exceptBind_ok h
  obtain ⟨sty, hsty, h⟩ := exceptBind_ok h
  obtain ⟨u', hu', h⟩ := exceptBind_ok h
  by_cases hlarge : blockLargeElimAllowed p nested = true
  case pos =>
    rw [if_pos hlarge] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.1
  case neg =>
    rw [if_neg hlarge] at h
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    by_cases hbt : b = true
    case neg => rw [if_neg hbt] at h; close_throw h
    rw [if_pos hbt] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.1

/-- **Stage (b): every major records its class's normal forms.** -/
theorem targetRecTys_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {aux : NestNodes}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat} :
    ∀ {recs : List RecShape} {tys : List (ConstantVal × TargetMajor × Level)},
      targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs recs = .ok tys →
      ∀ t ∈ tys, t.2.1.nfs = targetMajorNfs aux t.2.1.lvls t.2.1.ds
  | [], tys, h => by
    simp only [targetRecTys, pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro t ht; exact nomatch ht
  | rc :: rcs, tys, h => by
    unfold targetRecTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    obtain ⟨ts, hts, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · obtain ⟨cvRi, M, u⟩ := t'
      exact targetRecTy_nfs ht
    · exact targetRecTys_nfs hts t' ht'

/-- **Every stored major records its class's normal forms**, at a run of
the target check against the walk's classes `aux`. -/
theorem targetRecRun_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {F : Nat} (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ∀ t ∈ out, t.2.1.nfs = targetMajorNfs R.aux t.2.1.lvls t.2.1.ds := by
  intro t ht
  have h0 := targetRecRun_out_fst R
  have hm : (t.1, t.2.1) ∈ R.tys.map (fun t => (t.1, t.2.1)) := by
    rw [← h0]; exact List.mem_map_of_mem ht
  obtain ⟨t', ht', he⟩ := List.mem_map.mp hm
  have := targetRecTys_nfs R.htys t' ht'
  have e2 : t'.2.1 = t.2.1 := (Prod.mk.inj he).2
  rw [← e2]; exact this

/-! ## Every call's typing ran -/

/-- **Every call's typing ran**, one by one. -/
theorem targetCallsOk_each {env : Env} {cn : Name} {fam : TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k F : Nat} {pw : PropWhen} {fwss : List (List Expr)} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k pw fwss ihs
        = .ok () →
      ∀ ih ∈ ihs, targetCallOk (fueledOps mode F) env cn fam fvsPref fvsF fnorm teles absM base k
        pw fwss ih = .ok ()
  | [], _, ih, hih => nomatch hih
  | ih0 :: ihs, h, ih, hih => by
    unfold targetCallsOk at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hih with rfl | hih
    · cases u; exact hu
    · exact targetCallsOk_each h ih hih

/-! ## The members' recorded normal forms -/

theorem nestMemberCtors_shape {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {cs : List (ConstantVal × Nat)} {st : NestState} {kss : List (List NestFieldKind)}
      {nss : List Expr} {st' : NestState},
      nestMemberCtors ops env ctx holes cs st = .ok (kss, nss, st') → nss.length = cs.length
  | [], st, kss, nss, st', h => by
    simp only [nestMemberCtors, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    rfl
  | c :: cs, st, kss, nss, st', h => by
    simp only [nestMemberCtors, bind, Except.bind] at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    split at h
    · simp at h
    rename_i r hr
    obtain ⟨kss', nss', st''⟩ := r
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    simp [nestMemberCtors_shape hr]

theorem nestBlockCtors_shape {ops : CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {holes : List Expr} :
    ∀ {css : List (List (ConstantVal × Nat))} {st : NestState}
      {ksss : List (List (List NestFieldKind))} {nsss : List (List Expr)} {st' : NestState},
      nestBlockCtors ops env ctx holes css st = .ok (ksss, nsss, st') →
      ∀ (c : Nat) (cs : List (ConstantVal × Nat)), css[c]? = some cs →
        ∃ ns, nsss[c]? = some ns ∧ ns.length = cs.length
  | [], st, ksss, nsss, st', _, c, cs, hc => by simp at hc
  | cs₀ :: css, st, ksss, nsss, st', h, c, cs, hc => by
    simp only [nestBlockCtors, bind, Except.bind] at h
    split at h
    · simp at h
    rename_i r₁ hr₁
    obtain ⟨kss, nss, st₁⟩ := r₁
    simp only at h
    split at h
    · simp at h
    rename_i r₂ hr₂
    obtain ⟨ksss₂, nsss₂, st₂⟩ := r₂
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    cases c with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨nss, rfl, nestMemberCtors_shape hr₁⟩
    | succ c =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact nestBlockCtors_shape hr₂ c cs hc

theorem mem_nestMemberNfs {ctx : NestCtx} :
    ∀ {css : List (List (ConstantVal × Nat))} {nfs : List (List Expr)} {m j : Nat}
      {cs : List (ConstantVal × Nat)} {cA : ConstantVal × Nat} {ns : List Expr} {n : Expr},
      css[m]? = some cs → cs[j]? = some cA → nfs[m]? = some ns → ns[j]? = some n →
      (⟨cA.1.name, ctx.lps.map .param, ctx.params, n.replaceFVars (nestHoleConst ctx [])⟩ :
        NestCtorNf) ∈ nestMemberNfs ctx css nfs := by
  intro css nfs m j cs cA ns n hcs hcA hns hn
  unfold nestMemberNfs
  refine List.mem_flatMap.mpr ⟨(cs, ns), ?_, ?_⟩
  · exact List.mem_iff_getElem?.mpr ⟨m, by rw [List.getElem?_zip_eq_some]; exact ⟨hcs, hns⟩⟩
  · refine List.mem_map.mpr ⟨(cA, n), ?_, rfl⟩
    exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨hcA, hn⟩⟩

/-- **A member constructor's walked normal form is recorded** (K.53′'s
node-`0` entries, `nestMemberNfs`): at the positivity run, the entry of
member `m`'s constructor `j` at the block's own levels and parameters,
its normal form (the run's `nfs`) read back. -/
theorem checkBlockPositivity_memberEntry {ops : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {nodes : NestNodes}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, nodes)) :
    ∃ cvTa0 fvsP rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[m]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
          (⟨cA.1.name, (p.nestCtx fvsP find? consts).lps.map .param,
            (p.nestCtx fvsP find? consts).params,
            ((nfs.getD m []).getD j default).replaceFVars
              (nestHoleConst (p.nestCtx fvsP find? consts) [])⟩ : NestCtorNf) ∈ nodes.ctors := by
  simp only [checkBlockPositivity, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i cvTa0 hcv
  have hcv' : cvTas.head? = some cvTa0 := unwrapOr_ok hcv
  split at h
  · simp at h
  rename_i pq hpq
  have hpq' : openPisAtFvars p.nP cvTa0.type 0 = some pq := unwrapOr_ok hpq
  split at h
  · simp at h
  rename_i holes hholes
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨kinds', normals, st⟩ := r
  simp only at h
  split at h
  · simp at h
  rename_i u hA
  cases u
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨cvTa0, pq.1, pq.2, hcv', hpq', fun m cs hcs j cA hj => ?_⟩
  obtain ⟨ns, hns, hlen⟩ := nestBlockCtors_shape hr m cs hcs
  have hjl : j < ns.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  refine List.mem_append_left _ ?_
  have hn : ns[j]? = some ((normals.getD m []).getD j default) := by
    rw [List.getD_eq_getElem?_getD (l := normals), hns, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
  exact mem_nestMemberNfs hcs hj hns hn

end ConLeche
