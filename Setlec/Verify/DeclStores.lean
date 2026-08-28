import Setlec.Verify.BridgeWFDecl

/-!
# What a checked value declaration stores (V-free)

`checkDecl_stores`: a successful `defnDecl`/`thmDecl` run leaves a
constant carrying the *annotated* declared type.  Both soundness
routes' input-level corollaries ("no accepted stream declares a proof
of `Empty`") turn on it, so it lives in the shared tier
(task #148 T6).
-/

namespace Setlec

variable {mode : CheckMode} {F : Nat}

/-- A checked `def` or `theorem` stores a constant carrying the
annotated declared type. -/
theorem checkDecl_stores {env env₁ : Env} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint} {d : Declaration}
    (h : checkDecl mode (fueledOps mode F) env d = .ok env₁)
    (hd : d = .defnDecl cv value hint ∨ d = .thmDecl cv value) :
    ∃ type, annotateCore mode env F 0 cv.type = .ok type ∧
      ∃ c ∈ env₁.consts, c.toConstantVal = ⟨cv.name, cv.levelParams, type⟩ := by
  rcases hd with rfl | rfl
  · simp only [checkDecl, checkDefnVal, fueledOps_annotate,
        fueledOps_inferType, fueledOps_isDefEq, Bind.bind,
        Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore mode env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore mode env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore mode env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have henv1 : env₁ =
        ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
          env.consts⟩ := by
      by_cases hnop : natOpNames.contains cv.name = true
      · rw [if_pos hnop] at h
        by_cases hgd : (natOpGuard (⟨ConstantInfo.defnInfo
              { cv with type := type } value' hint :: env.consts⟩ : Env)
              cv.name &&
            (natOpDeps cv.name).all (natOpStoredOk
              (⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
                env.consts⟩ : Env))) = true
        case neg =>
          rw [if_neg hgd] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        rw [if_pos hgd] at h
        have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ : Env).find? cv.name =
            some (.defnInfo { cv with type := type } value' hint) := by
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.defnInfo { cv with type := type }
              value' hint).name = cv.name from rfl)]
        rw [hfind2] at h
        dsimp only at h
        revert h
        cases hcert0 : certifyNatEqs (fueledOps mode F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error err => intro h; exact nomatch h
        | ok okb =>
          cases okb with
          | false =>
            intro h
            simp [throw, throwThe, MonadExceptOf.throw] at h
          | true =>
            intro h
            simp only [↓reduceIte] at h
            by_cases hdm : natDivModNames.contains cv.name = true
            · rw [if_pos hdm] at h
              revert h
              cases hpin : checkDivModPin (fueledOps mode F) env
                  (⟨ConstantInfo.defnInfo { cv with type := type } value'
                    hint :: env.consts⟩ : Env) cv.name with
              | error err => intro h; exact nomatch h
              | ok u =>
                intro h
                simp only [Except.ok.injEq] at h
                exact h.symm
            · rw [if_neg hdm] at h
              simp only [Except.ok.injEq] at h
              exact h.symm
      · rw [if_neg hnop] at h
        by_cases hdm : natDivModNames.contains cv.name = true
        · rw [if_pos hdm] at h
          revert h
          cases hpin : checkDivModPin (fueledOps mode F) env
              (⟨ConstantInfo.defnInfo { cv with type := type } value'
                hint :: env.consts⟩ : Env) cv.name with
          | error err => intro h; exact nomatch h
          | ok u =>
            intro h
            simp only [Except.ok.injEq] at h
            exact h.symm
        · rw [if_neg hdm] at h
          simp only [Except.ok.injEq] at h
          exact h.symm
    subst henv1
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩
  · simp only [checkDecl, checkThmVal, fueledOps_annotate,
        fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal (fueledOps mode F) env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hpshape', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    cases hst2 : inferTypeCore mode env F 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSortCore mode env F 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotateCore mode env F 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferTypeCore mode env F 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEqCore mode env F 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩

end Setlec
