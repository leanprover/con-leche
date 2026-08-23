import Setlec.Model.Extend.Modeled
import Setlec.Model.ModeledCaps

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
the fold invariant.  The eta head obligation is *forwarded* to the
caller (`hheadEta`, phrased over the result environment `env₁` and an
abstract extended valuation): only the caller knows whether the member
completes a family — the generic multi-constructor fold refutes it
(its capability record is empty), the single-constructor assembly
either refutes it from the run's freshness facts or discharges it
through `modeled_caps_eta`.  The unit law of a freshly installed
unit-like former is discharged here, through `modeled_caps_unit`. -/
theorem checkIndMember_sound {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁)
    (hpins : ∀ cv caps₂, ci = .indInfo cv caps₂ →
      EtaPins env' cv.name cv.levelParams caps)
    (hbn : blockNames.contains ci.name = true)
    (m : EnvModel V env') (hI : BlockInstalled blockNames env' m.val)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      env₁.find? T = some (.indInfo cvT capsT) → capsT.eta = true →
      reservedBasisNames.contains T = false →
      EtaFamilyStored env₁ T capsT →
      (T = ci.name ∨ capsT.etaCtor = ci.name ∨
        ∃ j, j < capsT.etaFields ∧ projFnName T j = ci.name) →
      ∀ val₁ : ConstVal V,
        (∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name →
          val₁ n ψ = m.val n ψ) →
        (∀ ψ : Name → Nat,
          val₁ ci.name ψ = m.val (ci.name.str "_model") ψ) →
        BlockInstalled blockNames env₁ val₁ →
        EtaLaw V env₁ val₁ T cvT capsT) :
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
  have hrenfb := hrenf
  rw [← hfb] at hrenfb
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
        obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -, -⟩ := hI n hc ci₂ hf₂
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
          obtain ⟨cvm₂, mval₂, hm₂, -, -, -, hv₂⟩ := hI n hc ci₂ hf₂
          exact (hv₂ ψ).symm
        · rw [if_neg hc]
  have hrenS : Expr.eqUpToNames (cvA.type.renameConsts fS) cvm.type =
      true := by
    rw [htypeA, ← Expr.renameConsts_congr_resolve
      (fun n hn => (hfSfound n hn).symm) tyA hres]
    rw [← htypeA]
    exact hrenfb
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
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
      · intro cv2 v2 heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.indInfo cvA caps) fS (cvA.name.str "_model") hfind' hnres hwf htres
      (Or.inl ⟨_, _, rfl⟩) hfm hlps hrenS hannT hroS
      (fun val₁ hv₁ he₁ => by
        have hI₁ : BlockInstalled blockNames
            ⟨.indInfo cvA caps :: env'.consts⟩ val₁ :=
          BlockInstalled.step (ci₁ := .indInfo cvA caps) hI hms hfm hlps
            hrenf hv₁ he₁
        refine ⟨?_, ?_⟩
        · intro T cvT capsT hfT hcape hresT hfam hpart
          have hv₁' : ∀ ψ : Name → Nat,
              val₁ (ConstantInfo.indInfo cv caps').name ψ =
                m.val ((ConstantInfo.indInfo cv caps').name.str
                  "_model") ψ := by
            intro ψ
            rw [← hnameA]
            exact hv₁ ψ
          have he₁' : ∀ (n : Name) (ψ : Name → Nat),
              n ≠ (ConstantInfo.indInfo cv caps').name →
              val₁ n ψ = m.val n ψ := by
            intro n ψ hne
            exact he₁ n ψ (fun hh => hne (by rw [← hnameA]; exact hh))
          refine hheadEta T cvT capsT hfT hcape hresT hfam ?_ val₁ he₁'
            hv₁' hI₁
          rw [← hnameA]
          exact hpart
        · intro cv₂ caps₂ heq hcapu hres₂
          injection heq with hcv hcaps
          subst hcv
          subst hcaps
          have hpinsA : EtaPins env' cvA.name cvA.levelParams caps := by
            rw [hnameA, hlpsA]
            exact hpins cv caps' rfl
          have hpins₁ : EtaPins ⟨.indInfo cvA caps :: env'.consts⟩
              cvA.name cvA.levelParams caps :=
            EtaPins.step hpinsA hfind'
          have hren₁ : ∀ cvmT mvalT hm,
              (⟨.indInfo cvA caps :: env'.consts⟩ : Env).find?
                (cvA.name.str "_model") =
                some (.defnInfo cvmT mvalT hm) →
              Expr.eqUpToNames (cvA.type.renameConsts (fun n =>
                if blockNames.contains n then n.str "_model" else n))
                cvmT.type = true := by
            intro cvmT mvalT hm hf₁
            rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo cvA
              caps).name = cvA.name.str "_model" from
              fun hh => Name.str_ne cvA.name "_model" hh.symm)] at hf₁
            rw [hfm] at hf₁
            obtain h1 := Option.some.inj hf₁
            injection h1 with e1 e2 e3
            subst e1
            exact hrenf
          have hvT₁ : ∀ ψ : Name → Nat,
              val₁ (ConstantInfo.indInfo cvA caps).name ψ =
                val₁ ((ConstantInfo.indInfo cvA caps).name.str
                  "_model") ψ := by
            intro ψ
            rw [hv₁ ψ]
            exact (he₁ _ ψ (Name.str_ne cvA.name "_model")).symm
          exact modeled_caps_unit (ci := .indInfo cvA caps) m hfind'
            he₁ hI₁ (ConstValParams.extend_head m he₁ hI₁ hbnA) hnres
            (fun cv2 v2 hcon => nomatch hcon)
            hcapu hpins₁ hren₁ htyf (Expr.constsResolve_mono htres) hvT₁)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hrenf hval₁ hpres₁⟩
  · -- constructor
    have hwf : ConstWF ⟨.ctorInfo cvA nP nF :: env'.consts⟩
        (.ctorInfo cvA nP nF) := by
      refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
      · intro cv2 v2 heq; exact nomatch heq
    obtain ⟨m₁, hval₁, hpres₁⟩ := extend_modeled_one m
      (.ctorInfo cvA nP nF) fS (cvA.name.str "_model")
      hfind' hnres hwf htres
      (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) hfm hlps hrenS hannT hroS
      (fun val₁ hv₁ he₁ => by
        have hI₁ : BlockInstalled blockNames
            ⟨.ctorInfo cvA nP nF :: env'.consts⟩ val₁ :=
          BlockInstalled.step (ci₁ := .ctorInfo cvA nP nF) hI hms hfm
            hlps hrenf hv₁ he₁
        refine ⟨?_, fun cv₂ caps₂ hcon => nomatch hcon⟩
        intro T cvT capsT hfT hcape hresT hfam hpart
        have hv₁' : ∀ ψ : Name → Nat,
            val₁ (ConstantInfo.ctorInfo cv nP nF).name ψ =
              m.val ((ConstantInfo.ctorInfo cv nP nF).name.str
                "_model") ψ := by
          intro ψ
          rw [← hnameA]
          exact hv₁ ψ
        have he₁' : ∀ (n : Name) (ψ : Name → Nat),
            n ≠ (ConstantInfo.ctorInfo cv nP nF).name →
            val₁ n ψ = m.val n ψ := by
          intro n ψ hne
          exact he₁ n ψ (fun hh => hne (by rw [← hnameA]; exact hh))
        refine hheadEta T cvT capsT hfT hcape hresT hfam ?_ val₁ he₁'
          hv₁' hI₁
        rw [← hnameA]
        exact hpart)
    exact ⟨m₁, BlockInstalled.step hI hms hfm hlps hrenf hval₁ hpres₁⟩

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

/-- Members installed by the fold never carry a model-shaped name
(`checkMemberVal` rejects them). -/
theorem checkIndFold_modelfree {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, ci.name.isModelSuffix = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      obtain ⟨-, -, -, -, -, -, tyA, stype, u, -, -, -, -, -, hcvA⟩ :=
        checkConstantVal_inv hccv
      rw [hcvA] at hms
      rcases hkind with ⟨⟨cv, caps', rfl⟩, -⟩ | ⟨cv, nP, nF, rfl, -⟩ <;>
        exact hms
    · exact checkIndFold_modelfree rest env₁ env₂ h ci hci


/-- Members installed by the fold never carry a
projection-function-shaped name. -/
theorem checkIndFold_projshape {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, ci.name.isProjFnShape = false
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      obtain ⟨-, -, hpshape0, -, -, -, tyA, stype, u, -, -, -, -, -,
        hcvA⟩ := checkConstantVal_inv hccv
      exact hpshape0
    · exact checkIndFold_projshape rest env₁ env₂ h ci hci

/-- The member fold adds only block-named inductive-former or
constructor constants. -/
theorem checkIndFold_find_new {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
    env'.find? n = some ci ∨
      (blockNames.contains n = true ∧
        ((∃ cv, ci = .indInfo cv caps) ∨
          ∃ cv nP nF, ci = .ctorInfo cv nP nF))
  | [], _, _, _, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl hf
  | ci₀ :: rest, env', env₂, hns, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -,
      hcvA⟩ := checkConstantVal_inv hccv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hbn₀ : blockNames.contains cvA.name = true := by
      rw [hnameA]
      exact hns ci₀ List.mem_cons_self
    rcases checkIndFold_find_new rest env₁ env₂
      (fun ci' hci' => hns ci' (List.mem_cons_of_mem _ hci')) h n ci hf
      with hf' | hnew
    · rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next hh =>
          obtain rfl := Option.some.inj hf'
          refine Or.inr ⟨?_, Or.inl ⟨cvA, rfl⟩⟩
          rw [← hh]
          exact hbn₀
        · exact Or.inl hf'
      · rw [Env.find?_cons] at hf'
        split at hf'
        · next hh =>
          obtain rfl := Option.some.inj hf'
          refine Or.inr ⟨?_, Or.inr ⟨cvA, nP, nF, rfl⟩⟩
          rw [← hh]
          exact hbn₀
        · exact Or.inl hf'
    · exact Or.inr hnew


/-- Every successfully folded member is an inductive former or a
constructor. -/
theorem checkIndFold_kinds {blockNames : List Name} {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ ci ∈ rest, (∃ cv caps', ci = .indInfo cv caps') ∨
      ∃ cv nP nF, ci = .ctorInfo cv nP nF
  | [], _, _, _, ci, hci => nomatch hci
  | ci₀ :: rest, env', env₂, h, ci, hci => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ =>
    rw [hstep] at h
    rw [List.mem_cons] at hci
    rcases hci with rfl | hci
    · obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
        checkIndMember_inv hstep
      rcases hkind with ⟨⟨cv, caps', rfl⟩, -⟩ | ⟨cv, nP, nF, rfl, -⟩
      · exact Or.inl ⟨cv, caps', rfl⟩
      · exact Or.inr ⟨cv, nP, nF, rfl⟩
    · exact checkIndFold_kinds rest env₁ env₂ h ci hci


/-- The member fold preserves stored lookups exactly (every install is
fresh). -/
theorem checkIndFold_find_preserved {blockNames : List Name}
    {caps : IndCaps} :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ (n : Name) (ci : ConstantInfo), env'.find? n = some ci →
    env₂.find? n = some ci
  | [], _, _, h, n, ci, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hf
  | ci₀ :: rest, env', env₂, h, n, ci, hf => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci₀ with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0, -, -, -, -, -, tyA, stype, u, -, -, -, -, -,
      hcvA⟩ := checkConstantVal_inv hccv
    have hfindA : env'.find? cvA.name = none := by
      rw [show cvA.name = ci₀.name from by rw [hcvA]; rfl]
      exact hfind0
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ := by
      rcases hkind with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    obtain ⟨ci₁, hname₁, rfl⟩ := henv₁
    refine checkIndFold_find_preserved rest _ env₂ h n ci ?_
    rw [Env.find?_cons_of_isSome (by rw [hname₁]; exact hfindA)
      (by rw [hf]; rfl)]
    exact hf

/-- The eta families of stored formers *outside* the block are closed:
their capability constructor is stored at the record's arities.  The
block-fold form of the threaded `EtaFamiliesClosed` (which cannot hold
for a former whose constructor is still pending). -/
def EtaFamiliesClosedO (blockNames : List Name) (env : Env) : Prop :=
  ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    blockNames.contains T = false →
    ∃ cvC, env.find? caps.etaCtor =
      some (.ctorInfo cvC caps.etaParams caps.etaFields)

/-- Stored block formers carry exactly the fold's capability record. -/
def BlockCapsPinned (blockNames : List Name) (caps : IndCaps)
    (env : Env) : Prop :=
  ∀ (n : Name) (cvS : ConstantVal) (capsS : IndCaps),
    blockNames.contains n = true →
    env.find? n = some (.indInfo cvS capsS) → capsS = caps

/-- The fold of `checkIndDecl` preserves having a model together with
the block-install invariant.  Restricted to a capability record with
`eta = false` (the generic multi-constructor branch; the
single-constructor branch is assembled member by member in
`checkIndDecl_sound`): every eta head obligation is refuted — a block
former never claims the capability, an outside former's family is
closed (`EtaFamiliesClosedO`), so a fresh member never completes
one. -/
theorem checkIndFold_sound {blockNames : List Name} {caps : IndCaps}
    (hoff : caps.eta = false) :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    (∀ cv caps₂,
      (ConstantInfo.indInfo cv caps₂) ∈ rest →
      EtaPins env' cv.name cv.levelParams caps) →
    rest.foldlM (checkIndMember (fueledOps F) blockNames caps) env' = .ok env₂ →
    ∀ m : EnvModel V env', BlockInstalled blockNames env' m.val →
    EtaFamiliesClosedO blockNames env' →
    BlockCapsPinned blockNames caps env' →
    ∃ m₂ : EnvModel V env₂, BlockInstalled blockNames env₂ m₂.val ∧
      EtaFamiliesClosedO blockNames env₂ ∧
      BlockCapsPinned blockNames caps env₂
  | [], env', env₂, hns, _hp, h, m, hI, hE1O, hBcaps => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hI, hE1O, hBcaps⟩
  | ci :: rest, env', env₂, hns, hp, h, m, hI, hE1O, hBcaps => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps F) blockNames caps env' ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA', cvm', mval', hm', hccv', -, -, -, -, hkind'⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0', -, hpshape0', -, -, -, tyA', stype', u', -, -, -,
      -, -, hcvA'⟩ := checkConstantVal_inv hccv'
    have hnameA' : cvA'.name = ci.name := by
      rw [hcvA']
      rfl
    have hfreshc : env'.find? ci.name = none := hfind0'
    have hpshapec : ci.name.isProjFnShape = false := hpshape0'
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA'.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ ∧
        ((∃ capsS, ci₁ = .indInfo cvA' capsS ∧ capsS = caps) ∨
          ∃ nP nF, ci₁ = .ctorInfo cvA' nP nF) := by
      rcases hkind' with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl, Or.inl ⟨caps, rfl, rfl⟩⟩
      · exact ⟨_, rfl, rfl, Or.inr ⟨nP, nF, rfl⟩⟩
    obtain ⟨ci₁, hname₁, rfl, hshape₁⟩ := henv₁
    have hfresh₁ : env'.find? ci₁.name = none := by
      rw [hname₁, hnameA']
      exact hfind0'
    have hcin : ci₁.name = ci.name := by rw [hname₁, hnameA']
    have hheadEta : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
        (⟨ci₁ :: env'.consts⟩ : Env).find? T =
          some (.indInfo cvT capsT) → capsT.eta = true →
        reservedBasisNames.contains T = false →
        EtaFamilyStored ⟨ci₁ :: env'.consts⟩ T capsT →
        (T = ci.name ∨ capsT.etaCtor = ci.name ∨
          ∃ j, j < capsT.etaFields ∧ projFnName T j = ci.name) →
        ∀ val₁ : ConstVal V,
          (∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name →
            val₁ n ψ = m.val n ψ) →
          (∀ ψ : Name → Nat,
            val₁ ci.name ψ = m.val (ci.name.str "_model") ψ) →
          BlockInstalled blockNames ⟨ci₁ :: env'.consts⟩ val₁ →
          EtaLaw V ⟨ci₁ :: env'.consts⟩ val₁ T cvT capsT := by
      intro T cvT capsT hfT hcape hresT hfam hpart val₁ _ _ _
      exfalso
      rcases hpart with rfl | hC | ⟨j, hj, hP⟩
      · -- the head would be the (eta-capable) former: the fold's
        -- record claims no capability
        rw [Env.find?_cons, if_pos hcin] at hfT
        rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hfT
          obtain hh := Option.some.inj hfT
          injection hh with h1 h2
          rw [← h2, hoff] at hcape
          exact nomatch hcape
        · rw [heq₁] at hfT
          exact nomatch (Option.some.inj hfT)
      · -- the head would be the family's constructor
        obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [hC, Env.find?_cons, if_pos hcin] at hfC
        rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hfC
          exact nomatch (Option.some.inj hfC)
        · -- the family's owner is stored below the head
          have hTne : T ≠ ci.name := by
            intro he
            rw [he, Env.find?_cons, if_pos hcin, heq₁] at hfT
            exact nomatch (Option.some.inj hfT)
          rw [Env.find?_cons,
            if_neg (fun hh => hTne (hh.symm.trans hcin))] at hfT
          by_cases hTb : blockNames.contains T = true
          · have hcaps := hBcaps T cvT capsT hTb hfT
            rw [hcaps, hoff] at hcape
            exact nomatch hcape
          · have hTbf : blockNames.contains T = false := by
              revert hTb
              cases blockNames.contains T <;> simp
            obtain ⟨cvC', hfC'⟩ := hE1O T cvT capsT hfT hcape hresT hTbf
            have hsC : (env'.find? capsT.etaCtor).isSome = true := by
              rw [hfC']
              rfl
            rw [hC, hfreshc] at hsC
            exact nomatch hsC
      · rw [← hP] at hpshapec
        simp [projFnName, Name.isProjFnShape] at hpshapec
    obtain ⟨m₁, hI₁⟩ := checkIndMember_sound hstep
      (fun cv caps₂ heq => hp cv caps₂
        (by rw [← heq]; exact List.mem_cons_self))
      (hns ci (by simp)) m hI hheadEta
    have hE1O₁ : EtaFamiliesClosedO blockNames ⟨ci₁ :: env'.consts⟩ := by
      intro T cvT capsT hfT hcape hres hTb
      have hTne : T ≠ ci₁.name := by
        intro he
        rw [he, hcin, hns ci (by simp)] at hTb
        exact nomatch hTb
      rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hfT
      obtain ⟨cvC, hfC⟩ := hE1O T cvT capsT hfT hcape hres hTb
      refine ⟨cvC, ?_⟩
      rw [Env.find?_cons_of_isSome hfresh₁ (by rw [hfC]; rfl)]
      exact hfC
    have hBcaps₁ : BlockCapsPinned blockNames caps
        ⟨ci₁ :: env'.consts⟩ := by
      intro n cvS capsS hnb hf
      rw [Env.find?_cons] at hf
      split at hf
      · rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hf
          obtain h2 := Option.some.inj hf
          injection h2 with e1 e2
          exact e2.symm
        · rw [heq₁] at hf
          exact nomatch (Option.some.inj hf)
      · exact hBcaps n cvS capsS hnb hf
    exact checkIndFold_sound hoff rest _ env₂
      (fun ci' hci' => hns ci' (by simp [hci']))
      (fun cv caps₂ hmem => EtaPins.step
        (hp cv caps₂ (List.mem_cons_of_mem _ hmem)) hfresh₁)
      h m₁ hI₁ hE1O₁ hBcaps₁


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
