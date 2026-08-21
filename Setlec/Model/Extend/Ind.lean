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

/-- The fold invariant of `checkIndDecl`: every installed block member
has its `_model` companion stored (as a definition with the same level
parameters) and is interpreted by it. -/
def BlockInstalled (blockNames : List Name) (env' : Env)
    (val : ConstVal V) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval, env'.find? (n.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ

omit [SetTheory V] in
/-- Installing one member with its model's value preserves the fold
invariant. -/
theorem BlockInstalled.step {blockNames : List Name} {env' : Env}
    {val val₁ : ConstVal V} {ci₁ : ConstantInfo} {cvm : ConstantVal}
    {mval : Expr}
    (hI : BlockInstalled blockNames env' val)
    (hms : ci₁.name.isModelSuffix = false)
    (hfm : env'.find? (ci₁.name.str "_model") = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hval₁ : ∀ ψ, val₁ ci₁.name ψ = val (ci₁.name.str "_model") ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → val₁ n ψ = val n ψ) :
    BlockInstalled blockNames ⟨ci₁ :: env'.consts⟩ val₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, ?_, hlps, ?_⟩
    · rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci₁.name "_model" h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (Name.str_ne ci₁.name "_model")]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, ?_, hlps₂, ?_⟩
    · rw [Env.find?_cons, if_neg (show ¬ci₁.name = n.str "_model" from
        fun h => Name.str_model_ne hms h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm),
        hpres₁ _ ψ (fun h => Name.str_model_ne hms h),
        hv₂ ψ]

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
  obtain ⟨cvA, cvm, mval, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
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
  rw [← hfb] at hrenf hkind
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
        obtain ⟨cvm₂, mval₂, hfm₂, hlps₂, -⟩ := hI n hc ci₂ hf₂
        exact ⟨.defnInfo cvm₂ mval₂, hfm₂, hlps₂⟩
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
          obtain ⟨cvm₂, mval₂, -, -, hv₂⟩ := hI n hc ci₂ hf₂
          exact (hv₂ ψ).symm
        · rw [if_neg hc]
  have hrenS : cvA.type.renameConsts fS = cvm.type := by
    rw [htypeA, ← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) tyA hres]
    rw [← htypeA]
    exact hrenf
  rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩ |
    ⟨cv, nP, nm, ni, rules, rules', rfl, hall, heqf, hcir, rfl⟩
  · -- inductive type former
    have hwf : ConstWF ⟨.indInfo cvA caps :: env'.consts⟩
        (.indInfo cvA caps) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.indInfo cvA caps) fS (cvA.name.str "_model") hfind' hnres hwf htres
      (Or.inl ⟨_, _, rfl⟩) hfm hlps hrenS hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j hh => hprojRef T j hh)
      (fun cv₂ caps₂ heq hcape _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE,
          ⟨cvmC, mvalC, hCmE, hCmlpsE⟩, hPjE, heqfE, hS_stripE,
          hTm_stripE, hsdomsE, hxdomE, hsbodyE⟩ :=
          hpinsA.1 hcape
        obtain ⟨rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1⟩
        refine ⟨by rw [hCmE]; rfl, ?_, ?_⟩
        · intro j hj
          obtain ⟨cvmj, mvalj, hfj, -⟩ := hPjE j hj
          show (env'.find? (projModelName cvA.name j)).isSome = true
          rw [hfj]
          rfl
        · intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
          obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
            Expr.stripPis_renameConsts_inv (f := fS) caps.etaParams
              (by rw [hrenS]; exact hTm_stripE)
          have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
              k < caps.etaParams →
              sbinders[k]? = some b → tbinders[k]? = some b' →
              b.2.1 = (b'.2.1).renameConsts fS := by
            intro k b b' hk hb hb'
            have hbm : tbindersM[k]? =
                some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
              rw [hbsmap, List.getElem?_map, hb']
              rfl
            exact hsdomsE k b _ hk hb hbm
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
            (cimC := .defnInfo cvmC mvalC) hCmE hCmlpsE
            (fun j hj => by
              obtain ⟨cvmj, mvalj, hfj, hjlps⟩ := hPjE j hj
              exact ⟨.defnInfo cvmj mvalj, hfj, hjlps⟩)
            heqfE heqval hthm_mem hthm_annot hSw hS_stripE hT_strip
            hsdomsF hxdomE hsbodyE htyf hlen hx hfit)
      (fun cv₂ caps₂ heq hcapu _hres' => by
        injection heq with hcv hcaps
        subst hcv
        subst hcaps
        have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
          rw [hnameA, hlpsA]
          exact hpins cv caps' rfl
        obtain ⟨tcv, tval, cvmT, mvalT, sbinders, tbindersM, sbody,
          tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE, heqfE,
          hS_stripE, hTm_stripE, hsdomsE, hxdomE, hydomE, hsbodyE⟩ :=
          hpinsA.2 hcapu
        obtain ⟨rfl, rfl⟩ : cvm = cvmT ∧ mval = mvalT := by
          rw [hfm] at hTmE
          have h1 := Option.some.inj hTmE
          exact ⟨by injection h1, by injection h1⟩
        intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
        obtain ⟨tbinders, tbody, hT_strip, hbsmap, -⟩ :=
          Expr.stripPis_renameConsts_inv (f := fS) caps.unitParams
            (by rw [hrenS]; exact hTm_stripE)
        have hsdomsF : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
            k < caps.unitParams →
            sbinders[k]? = some b → tbinders[k]? = some b' →
            b.2.1 = (b'.2.1).renameConsts fS := by
          intro k b b' hk hb hb'
          have hbm : tbindersM[k]? =
              some (b'.1, (b'.2.1).renameConsts fS, b'.2.2) := by
            rw [hbsmap, List.getElem?_map, hb']
            rfl
          exact hsdomsE k b _ hk hb hbm
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
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.ctorInfo cvA nP nF) fS (cvA.name.str "_model")
      hfind' hnres hwf htres
      (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) hfm hlps hrenS hroS
      (fun _ => ⟨show (env'.find? (cvA.name.str "_model")).isSome = true
        by rw [hfm]; rfl, fun ψ => rfl⟩)
      (fun T j hh => hprojRef T j hh)
      (fun cv₂ caps₂ hcon => nomatch hcon)
      (fun cv₂ caps₂ hcon => nomatch hcon)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hval₁ hpres₁⟩
  · -- recursor
    have hfself : fb cvA.name = cvA.name.str "_model" := by
      rw [hfb]; dsimp only; rw [if_pos hbnA]
    have hfnot : ∀ n, fb n ≠ cvA.name := by
      intro n
      rw [hfb]
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        exact Name.str_model_ne hms
      · rw [if_neg hc]
        intro hn
        rw [hn] at hc
        exact hc hbnA
    have hff₀ : ∀ n, n ≠ cvA.name → fb n = fS n := by
      intro n hn
      cases hf₂ : env'.find? n with
      | some ci₂ =>
        exact (hfSfound n (by rw [hf₂]; rfl)).symm
      | none =>
        rw [hfSnone n hf₂, hfb]
        have hnc : ¬blockNames.contains n = true := by
          intro hc
          have hmem : n ∈ blockNames := by
            simpa using hc
          have hor := List.all_eq_true.mp hall n hmem
          simp only [Bool.or_eq_true, beq_iff_eq] at hor
          rcases hor with h1 | h1
          · exact hn h1
          · rw [hf₂] at h1; exact nomatch h1
        dsimp only
        rw [if_neg hnc]
    have heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'' := by
      intro ψ''
      obtain ⟨-, hpv⟩ :=
        m.ind_ok.2.2.2.1 eqName eqA heqf (by rfl) (by decide)
      rw [hpv ψ'']
      simp [pinnedVal]
    have hwf : ConstWF ⟨.recInfo cvA nP 1 nm ni rules' :: env'.consts⟩
        (.recInfo cvA nP 1 nm ni rules') := by
      have hiso : ∀ n,
          ((⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩ : Env).find? n).isSome
          =
          ((⟨.recInfo cvA nP 1 nm ni rules' ::
            env'.consts⟩ : Env).find? n).isSome := by
        intro n
        rw [Env.find?_cons, Env.find?_cons]
        by_cases hh : cvA.name = n
        · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
              []).name = n from hh),
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
              rules').name = n from hh)]
          rfl
        · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
              []).name = n from hh),
            if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
              rules').name = n from hh)]
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_⟩
      · intro cv2 v2 heq; exact nomatch heq
      · intro cv2 nP' nM' nm' ni' rules'' heq r hr
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          -, -, -, -, -, hrf, hrb', -, -, -, -, -, -, -, -, -, -, -,
          hrlp, hrres⟩ :=
          checkIotaRules_inv 0 rules rules' hcir r hr
        refine ⟨hrf, by rw [← e1]; exact hrlp, ?_, hrb'⟩
        rw [← Expr.constsResolve_congr hiso]
        exact hrres
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_rec m cvA nP nm ni rules'
      fb hfind' hnres hshapeA hwf htres hfm hlps hrenf
      fS hroS hff₀ hfself hfnot heqf heqval
      (checkIotaRules_inv 0 rules rules' hcir)
    exact ⟨m₁, BlockInstalled.step
      (ci₁ := .recInfo cvA nP 1 nm ni rules') hI hms hfm hlps hval₁ hpres₁⟩

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
    obtain ⟨cvA, cvm, mval, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -⟩ := checkConstantVal_inv hccv
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · exact hfind0
    · have hnone₁ := checkIndMember_fold_names rest env₁ env₂ h ci hci
      have henv₁ : ∃ ci₁, env₁ = (⟨ci₁ :: env'.consts⟩ : Env) := by
        rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩ |
          ⟨cv, nP, nm, rules, rules', -, -, -, -, -, rfl⟩
        · exact ⟨_, rfl⟩
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
    obtain ⟨cvA', cvm', mval', hccv', -, -, -, -, hkind'⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0', -, -, -, -, -, tyA', stype', u', -, -, -, -, -,
      hcvA'⟩ := checkConstantVal_inv hccv'
    have hnameA' : cvA'.name = ci.name := by
      rw [hcvA']
      rfl
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA'.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind' with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩ |
        ⟨cv, nP, nm, ni, rules, rules', -, -, -, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
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

end Setlec
