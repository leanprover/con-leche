module

public import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.PositivityInv

public section

/-!
# The calls' run facts at a nested stage

The run facts the calls' landing reads off the install, beside
`RecCheckRun.lean` and `PositivityInv.lean`:

* every checked major records the walk's normal forms its class matches
  (`TargetRecRun.nfsRun`: `targetMajorNfs … = .ok TargetMajor.nfs`);
* every call's typing ran (`targetCallsOk_each`);
* the positivity run's normal forms have the constructors' shape, and the
  members' own entries are recorded (`checkBlockPositivity_memberEntry`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## A checked major's recorded normal forms -/

/-- **Every stored major records its class's normal forms**, at a run of
the target check (its table `R.tbl`). -/
theorem targetRecRun_nfs {fe : FEnv} {p : BlockShape} {nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {F : Nat} (R : TargetRecRun mode F fe p nested block cvTas ctorsAs out) :
    ∀ t ∈ out, targetMajorNfs (fueledOps mode F) fe.env p (cvTas.map (·.type)) t.2.1.pfvs
      t.2.1.lvls t.2.1.ds t.2.1.ctors R.tbl = .ok t.2.1.nfs := by
  intro t ht
  have h0 := targetRecRun_out_fst R
  have hm : (t.1, t.2.1) ∈ R.tys.map (fun t => (t.1, t.2.1)) := by
    rw [← h0]; exact List.mem_map_of_mem ht
  obtain ⟨t', ht', he⟩ := List.mem_map.mp hm
  have := R.nfsRun t' ht'
  have e2 : t'.2.1 = t.2.1 := (Prod.mk.inj he).2
  rw [← e2]; exact this

/-! ## Every call's typing ran -/

/-- **Every call's typing ran**, one by one. -/
theorem targetCallsOk_each {env : Env} {p : BlockShape} {formerTys : List Expr} {cn : Name}
    {fam : TargetFamily}
    {fvsPref fvsF : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM mvF : Expr → Expr} {base k dA F : Nat} {pw : PropWhen} {fwss : List (List Expr)} :
    ∀ {ihs : List TargetIh},
      targetCallsOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles absM mvF base k
        dA pw fwss ihs = .ok () →
      ∀ ih ∈ ihs, targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles
        absM mvF base k dA pw fwss ih = .ok ()
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
      (⟨cA.1.name, ctx.lps.map .param, ctx.params, n.replaceFVars (nestHoleConst ctx []), []⟩ :
        NestCtorNf) ∈ nestMemberNfs ctx css nfs := by
  intro css nfs m j cs cA ns n hcs hcA hns hn
  unfold nestMemberNfs
  refine List.mem_flatMap.mpr ⟨(cs, ns), ?_, ?_⟩
  · exact List.mem_iff_getElem?.mpr ⟨m, by rw [List.getElem?_zip_eq_some]; exact ⟨hcs, hns⟩⟩
  · refine List.mem_map.mpr ⟨(cA, n), ?_, rfl⟩
    exact List.mem_iff_getElem?.mpr ⟨j, by rw [List.getElem?_zip_eq_some]; exact ⟨hcA, hn⟩⟩

/-- **A member constructor's walked normal form is recorded** (K.53′'s
node-`0` entries, `nestMemberNfs`): at the positivity run and the
recursor check's seeds after it, the table holds the entry of member
`m`'s constructor `j` at the block's own levels and parameters, its
normal form (the run's `nfs`) read back. -/
theorem checkBlockPositivity_memberEntry {ops ops' : CheckerOps CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos st : NestState}
    {tys : List (ConstantVal × TargetMajor × Level)} {tbl : List NestCtorNf}
    (h : checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs = .ok (kinds, nfs, pos))
    (hs : checkBlockSeeds ops' env₁ find? consts p.toBlockShape cvTas ctorsAs nfs st tys
      = .ok tbl) :
    ∃ cvTa0 fvsP rest, cvTas.head? = some cvTa0 ∧
      openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
      ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[m]? = some cs →
        ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
          (⟨cA.1.name, (p.nestCtx fvsP find? consts).lps.map .param,
            (p.nestCtx fvsP find? consts).params,
            ((nfs.getD m []).getD j default).replaceFVars
              (nestHoleConst (p.nestCtx fvsP find? consts) []), []⟩ : NestCtorNf) ∈ tbl := by
  simp only [checkBlockPositivity, bind, Except.bind] at h
  split at h
  · simp at h
  rename_i r₀ hr₀
  obtain ⟨ctx, holes⟩ := r₀
  obtain ⟨cvTa0, fvsP, rest, hcv', hpq', rfl, -⟩ := blockNestCtx_inv hr₀
  simp only at h
  split at h
  · simp at h
  rename_i r hr
  obtain ⟨kinds', normals, st'⟩ := r
  simp only at h
  split at h
  · simp at h
  rename_i u hA
  cases u
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  simp only [checkBlockSeeds, bind, Except.bind] at hs
  split at hs
  · simp at hs
  rename_i r₁ hr₁
  obtain ⟨ctx', holes'⟩ := r₁
  obtain ⟨cvTa0', fvsP', rest', hcv'', hpq'', rfl, -⟩ := blockNestCtx_inv hr₁
  rw [hcv'] at hcv''
  obtain rfl := Option.some.inj hcv''
  rw [hpq'] at hpq''
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hpq''
  simp only at hs
  split at hs
  · simp at hs
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  subst hs
  refine ⟨cvTa0, fvsP, rest, hcv', hpq', fun m cs hcs j cA hj => ?_⟩
  obtain ⟨ns, hns, hlen⟩ := nestBlockCtors_shape hr m cs hcs
  have hjl : j < ns.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1
  refine List.mem_append_left _ ?_
  have hn : ns[j]? = some ((normals.getD m []).getD j default) := by
    rw [List.getD_eq_getElem?_getD (l := normals), hns, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
  exact mem_nestMemberNfs hcs hj hns hn

end ConLeche
