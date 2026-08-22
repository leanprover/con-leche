import Setlec.Model.Extend.Modeled

/-!
# Ind — split out of `Setlec.Model.Extend`

Soundness of the `checkIndDecl` member fold: `BlockInstalled`,
`checkIndMember_sound` and `checkIndFold_sound`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- One `checkIndMember` step preserves having a model together with
the fold invariant. -/
theorem checkIndMember_sound {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁)
    (hpins : ∀ cv caps₂, ci = .indInfo cv caps₂ →
      EtaPins env' cv.name cv.levelParams caps)
    (hbn : blockNames.contains ci.name = true)
    (m : EnvModel V env') (hI : BlockInstalled blockNames env' m.val) :
    ∃ m₁ : EnvModel V env₁, BlockInstalled blockNames env₁ m₁.val := by
  obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
    checkIndMember_inv h
  obtain ⟨hfind0, hnres0, hpshape0, hnd, hlb, hfv, tyA, stype, u, hann,
    hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
  have hnameA : cvA.name = ci.name := by rw [hcvA]; rfl
  have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by
    rw [hcvA]
  have htypeA : cvA.type = tyA := by rw [hcvA]
  have hfind' : env'.find? cvA.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres0
  have hshapeA : cvA.name.isProjFnShape = false := by
    rw [hnameA]; exact hpshape0
  have hprojRef : ∀ (T : Name) (j : Nat), cvA.name = projFnName T j →
      ∀ {p : Prop}, p := by
    intro T j hh
    rw [hh] at hshapeA
    exact nomatch hshapeA
  have hbnA : blockNames.contains cvA.name = true := by
    rw [hnameA]; exact hbn
  have htyf : cvA.type.hasFvar = false := by
    rw [htypeA]
    exact not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann (WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvA.type.looseBVarsBounded 0 = true := by
    rw [htypeA]
    exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvA.type.allLevelParamsDefined cvA.levelParams = true := by
    rw [htypeA, hlpsA]; exact hlp
  have htres : cvA.type.constsResolve env' = true := by
    rw [htypeA]; exact hres
  -- the block renaming and its semantic pruning
  obtain ⟨fb, hfb⟩ : ∃ fb : Name → Name, fb = fun n =>
      if blockNames.contains n then n.str "_model" else n := ⟨_, rfl⟩
  rw [← hfb] at hrenf
  obtain ⟨fS, hfS⟩ : ∃ fS : Name → Name, fS = fun n =>
      if (env'.find? n).isSome then fb n else n := ⟨_, rfl⟩
  have hfSfound : ∀ n, (env'.find? n).isSome = true → fS n = fb n := by
    intro n hn
    rw [hfS]; simp only [hn, if_true]
  have hfSnone : ∀ n, env'.find? n = none → fS n = n := by
    intro n hn
    rw [hfS]; simp [hn]
  have hroS : RenameOk m.val env' fS := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ci₂ hf₂
      have hsome : (env'.find? n).isSome = true := by rw [hf₂]; rfl
      rw [hfSfound n hsome, hfb]
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -⟩ := hI n hc ci₂ hf₂
        exact ⟨.defnInfo cvm₂ mval₂ hm₂, hfm₂, hlps₂⟩
      · rw [if_neg hc]
        exact ⟨ci₂, hf₂, rfl⟩
    · intro n hf₂
      rw [hfSnone n hf₂]
      exact hf₂
    · intro n ψ
      cases hf₂ : env'.find? n with
      | none => rw [hfSnone n hf₂]
      | some ci₂ =>
        have hsome : (env'.find? n).isSome = true := by rw [hf₂]; rfl
        rw [hfSfound n hsome, hfb]
        dsimp only
        by_cases hc : blockNames.contains n = true
        · rw [if_pos hc]
          obtain ⟨cvm₂, mval₂, hm₂, -, -, hv₂⟩ := hI n hc ci₂ hf₂
          exact (hv₂ ψ).symm
        · rw [if_neg hc]
  have hrenS : Expr.eqUpToNames (cvA.type.renameConsts fS) cvm.type =
      true := by
    rw [htypeA, ← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) tyA hres]
    rw [← htypeA]
    exact hrenf
  have hannT : ∀ ψ : Name → Nat,
      AnnotOk V m.val env' ψ 0 (rho0 V) cvA.type := by
    intro ψ
    rw [htypeA]
    exact annotate_sound m _ hann (WScoped.of_not_hasFvar hfv) hlb
      (Expr.LeavesBounded.of_not_hasFvar hfv) (rho0 V)
      (FvarsOk.of_not_hasFvar hfv)
  rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
  · -- inductive type former
    have hwf : ConstWF ⟨.indInfo cvA caps :: env'.consts⟩
        (.indInfo cvA caps) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.indInfo cvA caps) fS (cvA.name.str "_model") hfind' hnres hwf htres
      (Or.inl ⟨_, _, rfl⟩) hfm hlps hrenS hannT hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j _ _ _ _ hh _ => hprojRef T j hh)
      (fun cv₂ caps₂ heq hcape _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE,
          ⟨cvmC, mvalC, hmC, hCmE, hCmlpsE⟩, hPjE, heqfE, hS_stripE,
          hTm_stripE, hsdomsE, hxdomE, hsbodyE⟩ :=
          hpinsA.1 hcape
        obtain ⟨rfl, rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT ∧ hmcvm = hmT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1, by injection h1⟩
        refine ⟨by rw [hCmE]; rfl, ?_, ?_⟩
        · intro j hj
          obtain ⟨cvmj, mvalj, hmj, hfj, -⟩ := hPjE j hj
          show (env'.find? (projModelName cvA.name j)).isSome = true
          rw [hfj]
          rfl
        · intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
          obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
            Expr.ErasedEq.stripPis_inv caps.etaParams
              (Expr.ErasedEq.of_eqUpToNames hrenS) hTm_stripE
          obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
            Expr.stripPis_renameConsts_inv (f := fS) caps.etaParams
              hstripR
          have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
              k < caps.etaParams →
              sbinders[k]? = some b → tbinders[k]? = some b' →
              RenEq fS b'.2.1 b.2.1 := by
            intro k b b' hk hb hb'
            have hbR : bsR[k]? =
                some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
              rw [hbsmap, List.getElem?_map, hb']
              rfl
            have hklt : k < tbindersM.length := by
              have h1 : bsR[k]?.isSome = true := by rw [hbR]; rfl
              simp at h1
              omega
            have hbm : tbindersM[k]? = some tbindersM[k] :=
              List.getElem?_eq_getElem hklt
            have hrel := (hdomsR k _ _ hbR hbm).1
            have hpin : b.2.1 = tbindersM[k].2.1 :=
              hsdomsE k b _ hk hb hbm
            show Expr.ErasedEq ((b'.2.1).renameConsts fS) b.2.1
            rw [hpin]
            exact hrel
          have hcvp : ConstValParams m.val env' :=
            fun n ci₂ hf ψ₁ ψ₂ hψ => m.val_params n ci₂ hf ψ₁ ψ₂ hψ
          have heqval : ∀ ψ'' : Name → Nat,
              m.val eqName ψ'' = eqVal V ψ'' := by
            intro ψ''
            obtain ⟨-, hpv⟩ :=
              m.ind_ok.2.2.2.1 eqName eqA heqfE (by rfl) (by decide)
            rw [hpv ψ'']
            simp [pinnedVal]
          have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
              interpClosed V m.val env' ψ'' tcv.type = some Pv ∧
              m.val tcv.name ψ'' ∈ˢ Pv := by
            intro ψ''
            obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE) ψ''
            exact ⟨P, hP, hmem⟩
          have hSw : tcv.type.hasFvar = false := by
            obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE)
            exact h1
          have hthm_annot : ∀ ψ'' : Name → Nat,
              AnnotOk V m.val env' ψ'' 0 (rho0 V) tcv.type :=
            fun ψ'' => (m.annot_ok _ (find?_mem hthmE) ψ'').1
          exact eta_rule_fold hroS hcvp hTmE hTmlpsE
            (cimC := .defnInfo cvmC mvalC hmC) hCmE hCmlpsE
            (fun j hj => by
              obtain ⟨cvmj, mvalj, hmj, hfj, hjlps⟩ := hPjE j hj
              exact ⟨.defnInfo cvmj mvalj hmj, hfj, hjlps⟩)
            heqfE heqval hthm_mem hthm_annot hSw hS_stripE hT_strip
            hsdomsF hxdomE hsbodyE htyf hlen hx hfit)
      (fun cv₂ caps₂ heq hcapu _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE, heqfE,
          hS_stripE, hTm_stripE, hsdomsE, hxdomE, hydomE, hsbodyE⟩ :=
          hpinsA.2 hcapu
        obtain ⟨rfl, rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT ∧ hmcvm = hmT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1, by injection h1⟩
        intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
        obtain ⟨bsR, bodyR, hstripR, hlenR, hdomsR, -⟩ :=
          Expr.ErasedEq.stripPis_inv caps.unitParams
            (Expr.ErasedEq.of_eqUpToNames hrenS) hTm_stripE
        obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
          Expr.stripPis_renameConsts_inv (f := fS) caps.unitParams
            hstripR
        have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
            k < caps.unitParams →
            sbinders[k]? = some b → tbinders[k]? = some b' →
            RenEq fS b'.2.1 b.2.1 := by
          intro k b b' hk hb hb'
          have hbR : bsR[k]? =
              some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
            rw [hbsmap, List.getElem?_map, hb']
            rfl
          have hklt : k < tbindersM.length := by
            have h1 : bsR[k]?.isSome = true := by rw [hbR]; rfl
            simp at h1
            omega
          have hbm : tbindersM[k]? = some tbindersM[k] :=
            List.getElem?_eq_getElem hklt
          have hrel := (hdomsR k _ _ hbR hbm).1
          have hpin : b.2.1 = tbindersM[k].2.1 :=
            hsdomsE k b _ hk hb hbm
          show Expr.ErasedEq ((b'.2.1).renameConsts fS) b.2.1
          rw [hpin]
          exact hrel
        have hcvp : ConstValParams m.val env' :=
          fun n ci₂ hf ψ₁ ψ₂ hψ => m.val_params n ci₂ hf ψ₁ ψ₂ hψ
        have heqval : ∀ ψ'' : Name → Nat,
            m.val eqName ψ'' = eqVal V ψ'' := by
          intro ψ''
          obtain ⟨-, hpv⟩ :=
            m.ind_ok.2.2.2.1 eqName eqA heqfE (by rfl) (by decide)
          rw [hpv ψ'']
          simp [pinnedVal]
        have hthm_mem : ∀ ψ'' : Name → Nat, ∃ Pv,
            interpClosed V m.val env' ψ'' tcv.type = some Pv ∧
            m.val tcv.name ψ'' ∈ˢ Pv := by
          intro ψ''
          obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthmE) ψ''
          exact ⟨P, hP, hmem⟩
        have hSw : tcv.type.hasFvar = false := by
          obtain ⟨h1, -⟩ := m.wf _ (find?_mem hthmE)
          exact h1
        have hthm_annot : ∀ ψ'' : Name → Nat,
            AnnotOk V m.val env' ψ'' 0 (rho0 V) tcv.type :=
          fun ψ'' => (m.annot_ok _ (find?_mem hthmE) ψ'').1
        exact unit_rule_fold hroS hcvp hTmE hTmlpsE heqfE heqval
          hthm_mem hthm_annot hSw hS_stripE hT_strip hsdomsF hxdomE
          hydomE hsbodyE htyf hlen hx hy hfit)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hval₁ hpres₁⟩
  · -- constructor
    have hwf : ConstWF ⟨.ctorInfo cvA nP nF :: env'.consts⟩
        (.ctorInfo cvA nP nF) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.ctorInfo cvA nP nF) fS (cvA.name.str "_model")
      hfind' hnres hwf htres
      (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) hfm hlps hrenS hannT hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j _ _ _ _ hh _ => hprojRef T j hh)
      (fun cv₂ caps₂ hcon => nomatch hcon)
      (fun cv₂ caps₂ hcon => nomatch hcon)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hval₁ hpres₁⟩

/-- A successful fold's members were all fresh at their own step, hence
already fresh at any earlier point. -/
theorem checkIndMember_fold_names {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, env'.find? ci.name = none
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -⟩ := checkConstantVal_inv hccv
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · exact hfind0
    · have hnone₁ := checkIndMember_fold_names rest env₁ env₂ h ci hci
      have henv₁ : ∃ ci₁, env₁ = (⟨ci₁ :: env'.consts⟩ : Env) := by
        rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      obtain ⟨ci₁, rfl⟩ := henv₁
      rw [Env.find?_cons] at hnone₁
      split at hnone₁
      · exact nomatch hnone₁
      · exact hnone₁

/-- The fold of `checkIndDecl` preserves having a model together with
the block-install invariant. -/
theorem checkIndFold_sound {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    (∀ cv caps₂,
      (ConstantInfo.indInfo cv caps₂) ∈ rest →
      EtaPins env' cv.name cv.levelParams caps) →
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ m : EnvModel V env', BlockInstalled blockNames env' m.val →
    ∃ m₂ : EnvModel V env₂, BlockInstalled blockNames env₂ m₂.val
  | [], env', env₂, hns, _hp, h, m, hI => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hI⟩
  | ci :: rest, env', env₂, hns, hp, h, m, hI => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨m₁, hI₁⟩ := checkIndMember_sound hstep
      (fun cv caps₂ heq => hp cv caps₂
        (by rw [← heq]; exact List.mem_cons_self))
      (hns ci (by simp)) m hI
    obtain ⟨cvA', cvm', mval', hm', hccv', -, -, -, -, hkind'⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0', -, -, -, -, -, tyA', stype', u', -, -, -, -, -,
      hcvA'⟩ := checkConstantVal_inv hccv'
    have hnameA' : cvA'.name = ci.name := by
      rw [hcvA']
      rfl
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA'.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind' with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    have hfresh₁ : env'.find? ci₁.name = none := by
      rw [hname₁, hnameA']
      exact hfind0'
    exact checkIndFold_sound rest _ env₂
      (fun ci' hci' => hns ci' (by simp [hci']))
      (fun cv caps₂ hmem => EtaPins.step
        (hp cv caps₂ (List.mem_cons_of_mem _ hmem)) hfresh₁)
      h m₁ hI₁


/-- The member fold only extends the environment: stored lookups stay
stored. -/
theorem checkIndFold_mono {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' =
      .ok env₂ →
    ∀ n, (env'.find? n).isSome = true → (env₂.find? n).isSome = true
  | [], _, _, h, n, hn => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hn
  | ci :: rest, env', env₂, h, n, hn => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env'
        ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, -, -, -, -, hkind⟩ :=
      checkIndMember_inv hstep
    have henv₁ : ∃ ci₁ : ConstantInfo, env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨ci₁, rfl⟩ := henv₁
    refine checkIndFold_mono rest _ env₂ h n ?_
    rw [Env.find?_cons]
    by_cases hh : ci₁.name = n
    · rw [if_pos hh]
      rfl
    · rw [if_neg hh]
      exact hn

/-- After the member fold every folded member is stored. -/
theorem checkIndFold_stored {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' =
      .ok env₂ →
    ∀ ci ∈ rest, (env₂.find? ci.name).isSome = true
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env'
        ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, -, -, -, -, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
      checkConstantVal_inv hccv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    rcases List.mem_cons.mp hci with rfl | hci
    · refine checkIndFold_mono rest _ env₂ h ci.name ?_
      rw [Env.find?_cons, if_pos (by rw [hname₁, hnameA])]
      rfl
    · exact checkIndFold_stored rest _ env₂ h ci hci

end Setlec
