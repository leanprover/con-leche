import Setlec.Verify.DiscI2

/-!
# Interned body walks, part 3: the stuck-major rescue and iota

Simulation walks for `majorToCtorI` and `iotaRecI`, mirroring
`majorToCtor_disc`/`iotaRec_disc` (`Setlec/Verify/Disc.lean`).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Setlec

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

private theorem majorToCtor_unfold (env : Env) (d : Nat) (recName : Name)
    (rules : List RecRule) (major : Expr) :
    majorToCtor (fueledFns env) env d recName rules major =
    (if isCtorApp env major then pure major else
    match rules with
    | [rl] =>
      match env.find? rl.ctor with
      | some (.ctorInfo cvj cnP cnF) =>
        match (cvj.type.piResult).getAppFn with
        | .const T _ =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if caps.ruleK = true ∧ cnF = 0 then
              (fueledFns env).infer d major >>= fun tm =>
              (fueledFns env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ cvj.levelParams.length = ust.length then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs.take cnP)
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    proofIrrel (fueledFns env) env d fab major >>= fun r =>
                    if r then pure fab
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                Name.isProjFnShape recName = false ∧
                piResultIsProp cvT.type = false then
              (fueledFns env).infer d major >>= fun tm =>
              (fueledFns env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                    ust.length = cvT.levelParams.length then
                  let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (tmaj.getAppArgs ++
                      (List.range caps.etaFields).map fun j =>
                        Expr.mkAppN (.const (projFnName T j) ust)
                          (tmaj.getAppArgs ++ [major]))
                  if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    structEtaCertWith (fueledFns env) env d fab major
                        tmaj >>= fun r =>
                    if r then pure fab
                    else if caps.etaFields = 0 ∧
                        cvj.levelParams.length = ust.length ∧
                        piResultNeverZero cvT.levelParams ust cvT.type
                          = true then
                      proofIrrel (fueledFns env) env d fab major >>=
                        fun r' =>
                      if r' then pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else pure major
          | _ => pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major) := rfl

theorem majorToCtorI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : EIdx}
    {major : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some major) (hmaj : WScoped d major) :
    SimAt env s₀ (RelE d)
      (majorToCtorI (coreKnotI (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (majorToCtor (fueledFns env) env d recName rules major) := by
  show SimAt env s₀ (RelE d)
    (Setlec.withStore (fun st => isCtorAppI (mkFEnv env) st i) >>=
      fun ctor =>
      if ctor then pure i else
      match rules with
      | [rl] =>
        match (mkFEnv env).find? rl.ctor with
        | some (.ctorInfo cvj cnP cnF) =>
          match (cvj.type.piResult).getAppFn with
          | .const T _ =>
            match (mkFEnv env).find? T with
            | some (.indInfo cvT caps) =>
              if caps.ruleK = true ∧ cnF = 0 then
                (coreKnotI (mkFEnv env) f).infer d i >>= fun tm =>
                (coreKnotI (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                Setlec.withStore
                    (fun st => st.nodes[st.getAppFnI tmaj]?) >>= fun n =>
                match n with
                | some (.const T' ust) =>
                  if T' = T ∧ cvj.levelParams.length = ust.length then
                    Setlec.withStore (·.getAppArgsI tmaj) >>= fun margs =>
                    internI (.const rl.ctor ust) >>= fun h =>
                    mkAppNM h (margs.take cnP) >>= fun fab =>
                    Setlec.withStore (fun st => st.wscopedBI d fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      (st.fvarLeavesI fab).all
                        (fun l => (st.fvarLeavesI i).contains l)) >>=
                      fun g =>
                    if g then
                      proofIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env)
                          d fab i >>= fun r =>
                      if r then pure fab
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                  Name.isProjFnShape recName = false ∧
                  piResultIsProp cvT.type = false then
                (coreKnotI (mkFEnv env) f).infer d i >>= fun tm =>
                (coreKnotI (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                Setlec.withStore
                    (fun st => st.nodes[st.getAppFnI tmaj]?) >>= fun n =>
                match n with
                | some (.const T' ust) =>
                  Setlec.withStore (·.getAppArgsI tmaj) >>= fun margs =>
                  readbackLevelsM ust >>= fun ustL =>
                  if T' = T ∧ margs.length = caps.etaParams ∧
                      ust.length = cvT.levelParams.length then
                    projAppsI T ust margs i
                        (List.range caps.etaFields) >>= fun projs =>
                    internI (.const caps.etaCtor ust) >>= fun h =>
                    mkAppNM h (margs ++ projs) >>= fun fab =>
                    Setlec.withStore (fun st => st.wscopedBI d fab &&
                      st.looseBVarsBoundedI 0 fab &&
                      (st.fvarLeavesI fab).all
                        (fun l => (st.fvarLeavesI i).contains l)) >>=
                      fun g =>
                    if g then
                      structEtaCertWithI (coreKnotI (mkFEnv env) f)
                          (mkFEnv env) d fab i tmaj >>= fun r =>
                      if r then pure fab
                      else if caps.etaFields = 0 ∧
                          cvj.levelParams.length = ust.length ∧
                          piResultNeverZero cvT.levelParams ustL cvT.type
                            = true then
                        proofIrrelI (coreKnotI (mkFEnv env) f)
                            (mkFEnv env) d fab i >>= fun r' =>
                        if r' then pure fab
                        else pure i
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else pure i
            | _ => pure i
          | _ => pure i
        | _ => pure i
      | _ => pure i)
    (majorToCtor (fueledFns env) env d recName rules major)
  rw [majorToCtor_unfold]
  refine SimAt.withStore ?_
  rw [isCtorAppI_spec hs.wf hden]
  by_cases hctor : isCtorApp env major
  · rw [if_pos hctor, if_pos hctor]
    exact SimAt.pure hs ⟨hden, hmaj⟩
  · rw [if_neg hctor, if_neg hctor]
    match rules with
    | [] => exact SimAt.pure hs ⟨hden, hmaj⟩
    | _ :: _ :: _ => exact SimAt.pure hs ⟨hden, hmaj⟩
    | [rl] =>
      dsimp only
      rw [show (mkFEnv env).find? rl.ctor = env.find? rl.ctor from
        mkFEnv_find? env rl.ctor]
      cases hfj : env.find? rl.ctor with
      | none => exact SimAt.pure hs ⟨hden, hmaj⟩
      | some ci =>
        cases ci with
        | ctorInfo cvj cnP cnF =>
          dsimp only
          cases hpr : (cvj.type.piResult).getAppFn with
          | const T lus =>
            dsimp only
            rw [show (mkFEnv env).find? T = env.find? T from
              mkFEnv_find? env T]
            cases hfT : env.find? T with
            | none => exact SimAt.pure hs ⟨hden, hmaj⟩
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                by_cases hK : caps.ruleK = true ∧ cnF = 0
                · rw [if_pos hK, if_pos hK]
                  refine SimAt.bind (ih.infer hs hden hmaj)
                    (fun s₁ tm tmx hs₁ hext₁ hP => ?_)
                  obtain ⟨htmd, hwtm⟩ := hP
                  refine SimAt.bind (ih.whnf hs₁ htmd hwtm)
                    (fun s₂ tmaj tmajx hs₂ hext₂ hP₂ => ?_)
                  obtain ⟨htmajd, hwtmaj⟩ := hP₂
                  refine SimAt.withStore ?_
                  obtain ⟨n, hn, hc, hd⟩ :=
                    denote_some_inv (getAppFnI_spec hs₂.wf htmajd)
                  rw [hn]
                  have hext₀₂ := hext₁.trans hext₂
                  cases n with
                  | const T' ust =>
                    rw [denoteNode, Option.map_eq_some_iff] at hd
                    obtain ⟨lust, hlustDen, hd⟩ := hd
                    rw [← hd]
                    have hlen := denoteLList_length hlustDen
                    dsimp only
                    rw [← hlen]
                    split
                    · refine SimAt.withStore ?_
                      have hmargs := getAppArgsI_spec hs₂.wf htmajd
                      have hcn : denoteNode s₂.store.denote
                          s₂.store.denoteL (.const rl.ctor ust)
                          = some (.const rl.ctor lust) := by
                        rw [denoteNode, hlustDen]
                        rfl
                      refine SimAt.bind_left (internI_eff hs₂ hcn)
                        (fun s₃ h hs₃ hext₃ hQh => ?_)
                      refine SimAt.bind_left (mkAppNM_eff hs₃ hQh
                        ((hmargs.mono hext₃).take cnP))
                        (fun s₄ fab hs₄ hext₄ hQfab => ?_)
                      refine SimAt.withStore ?_
                      rw [wscopedBI_spec hs₄.wf hQfab,
                        looseBVarsBoundedI_spec hs₄.wf hQfab,
                        leafGuardI_spec hs₄.wf hQfab
                          (denote_mono
                            ((hext₀₂.trans hext₃).trans hext₄) hden)]
                      split
                      · rename_i hguard
                        have hwfab := WScoped.of_wscopedB
                          (by simp only [Bool.and_eq_true] at hguard
                              exact hguard.1.1)
                        refine SimAt.bind (proofIrrelI_sim ih hs₄ hQfab
                          (denote_mono
                            ((hext₀₂.trans hext₃).trans hext₄) hden)
                          hwfab hmaj)
                          (fun s₅ r r' hs₅ hext₅ hPr => ?_)
                        obtain rfl : r = r' := hPr
                        cases r with
                        | true =>
                          simp only [↓reduceIte]
                          exact SimAt.pure hs₅
                            ⟨denote_mono hext₅ hQfab, hwfab⟩
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimAt.pure hs₅
                            ⟨denote_mono
                              (((hext₀₂.trans hext₃).trans hext₄).trans
                                hext₅) hden, hmaj⟩
                      · exact SimAt.pure hs₄
                          ⟨denote_mono
                            ((hext₀₂.trans hext₃).trans hext₄) hden,
                            hmaj⟩
                    · exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | bvar k =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | sort u =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | lit l =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | fvar idx nm t =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | app f' a' =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | lam nm t b' m =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | forallE nm t b' m =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | letE nm t v b' =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                  | proj s' j' e' =>
                    invert_head hd
                    exact SimAt.pure hs₂ ⟨denote_mono hext₀₂ hden, hmaj⟩
                · rw [if_neg hK, if_neg hK]
                  by_cases hEta : caps.eta = true ∧
                      rl.ctor = caps.etaCtor ∧
                      Name.isProjFnShape recName = false ∧
                      piResultIsProp cvT.type = false
                  · rw [if_pos hEta, if_pos hEta]
                    refine SimAt.bind (ih.infer hs hden hmaj)
                      (fun s₁ tm tmx hs₁ hext₁ hP => ?_)
                    obtain ⟨htmd, hwtm⟩ := hP
                    refine SimAt.bind (ih.whnf hs₁ htmd hwtm)
                      (fun s₂ tmaj tmajx hs₂ hext₂ hP₂ => ?_)
                    obtain ⟨htmajd, hwtmaj⟩ := hP₂
                    refine SimAt.withStore ?_
                    obtain ⟨n, hn, hc, hd⟩ :=
                      denote_some_inv (getAppFnI_spec hs₂.wf htmajd)
                    rw [hn]
                    have hext₀₂ := hext₁.trans hext₂
                    cases n with
                    | const T' ust =>
                      rw [denoteNode, Option.map_eq_some_iff] at hd
                      obtain ⟨lust, hlustDen, hd⟩ := hd
                      rw [← hd]
                      have hlen := denoteLList_length hlustDen
                      dsimp only
                      refine SimAt.withStore ?_
                      have hmargs := getAppArgsI_spec hs₂.wf htmajd
                      refine SimAt.bind_left
                        (readbackLevelsM_eff hs₂ hlustDen)
                        (fun s₂r ustL hs₂r hext₂r hustL => ?_)
                      rw [hustL, hmargs.length_eq, ← hlen]
                      split
                      · refine SimAt.bind_left (projAppsI_eff T ust
                          lust (List.range caps.etaFields) hs₂r
                          (denoteLList_mono hext₂r hlustDen)
                          (hmargs.mono hext₂r)
                          (denote_mono (hext₀₂.trans hext₂r) hden))
                          (fun s₃ projs hs₃ hext₃ hQp => ?_)
                        have hcn : denoteNode s₃.store.denote
                            s₃.store.denoteL (.const caps.etaCtor ust)
                            = some (.const caps.etaCtor lust) := by
                          rw [denoteNode, denoteLList_mono
                            (hext₂r.trans hext₃) hlustDen]
                          rfl
                        refine SimAt.bind_left (internI_eff hs₃ hcn)
                          (fun s₄ h hs₄ hext₄ hQh => ?_)
                        refine SimAt.bind_left (mkAppNM_eff hs₄ hQh
                          ((((hmargs.mono hext₂r).mono hext₃).mono
                            hext₄).append (hQp.mono hext₄)))
                          (fun s₅ fab hs₅ hext₅ hQfab => ?_)
                        refine SimAt.withStore ?_
                        have hext₀₅ :=
                          (((hext₀₂.trans hext₂r).trans hext₃).trans
                            hext₄).trans hext₅
                        rw [wscopedBI_spec hs₅.wf hQfab,
                          looseBVarsBoundedI_spec hs₅.wf hQfab,
                          leafGuardI_spec hs₅.wf hQfab
                            (denote_mono hext₀₅ hden)]
                        split
                        · rename_i hguard
                          have hwfab := WScoped.of_wscopedB
                            (by simp only [Bool.and_eq_true] at hguard
                                exact hguard.1.1)
                          refine SimAt.bind (structEtaCertWithI_sim ih
                            henv hs₅ hQfab
                            (denote_mono hext₀₅ hden)
                            (denote_mono
                              ((((hext₂r.trans hext₃).trans hext₄).trans
                                hext₅)) htmajd)
                            hwfab hmaj hwtmaj)
                            (fun s₆ r r' hs₆ hext₆ hPr => ?_)
                          obtain rfl : r = r' := hPr
                          cases r with
                          | true =>
                            simp only [↓reduceIte]
                            exact SimAt.pure hs₆
                              ⟨denote_mono hext₆ hQfab, hwfab⟩
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            split
                            · refine SimAt.bind (proofIrrelI_sim ih hs₆
                                (denote_mono hext₆ hQfab)
                                (denote_mono (hext₀₅.trans hext₆) hden)
                                hwfab hmaj)
                                (fun s₇ r₂ r₂' hs₇ hext₇ hPr₂ => ?_)
                              obtain rfl : r₂ = r₂' := hPr₂
                              cases r₂ with
                              | true =>
                                simp only [↓reduceIte]
                                exact SimAt.pure hs₇
                                  ⟨denote_mono hext₇
                                    (denote_mono hext₆ hQfab), hwfab⟩
                              | false =>
                                simp only [Bool.false_eq_true,
                                  ↓reduceIte]
                                exact SimAt.pure hs₇
                                  ⟨denote_mono
                                    ((hext₀₅.trans hext₆).trans hext₇)
                                    hden, hmaj⟩
                            · exact SimAt.pure hs₆
                                ⟨denote_mono (hext₀₅.trans hext₆) hden,
                                  hmaj⟩
                        · exact SimAt.pure hs₅
                            ⟨denote_mono hext₀₅ hden, hmaj⟩
                      · exact SimAt.pure hs₂r
                          ⟨denote_mono (hext₀₂.trans hext₂r) hden, hmaj⟩
                    | bvar k =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | sort u =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | lit l =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | fvar idx nm t =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | app f' a' =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | lam nm t b' m =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | forallE nm t b' m =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | letE nm t v b' =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                    | proj s' j' e' =>
                      invert_head hd
                      exact SimAt.pure hs₂
                        ⟨denote_mono hext₀₂ hden, hmaj⟩
                  · rw [if_neg hEta, if_neg hEta]
                    exact SimAt.pure hs ⟨hden, hmaj⟩
              | axiomInfo cv => exact SimAt.pure hs ⟨hden, hmaj⟩
              | defnInfo cv v h => exact SimAt.pure hs ⟨hden, hmaj⟩
              | thmInfo cv v => exact SimAt.pure hs ⟨hden, hmaj⟩
              | ctorInfo cv nP' nF' => exact SimAt.pure hs ⟨hden, hmaj⟩
              | recInfo cv mI rP rules' =>
                exact SimAt.pure hs ⟨hden, hmaj⟩
              | projInfo entry => exact SimAt.pure hs ⟨hden, hmaj⟩
          | bvar k => exact SimAt.pure hs ⟨hden, hmaj⟩
          | fvar idx nm t => exact SimAt.pure hs ⟨hden, hmaj⟩
          | sort u => exact SimAt.pure hs ⟨hden, hmaj⟩
          | app f' a' => exact SimAt.pure hs ⟨hden, hmaj⟩
          | lam nm t b' m => exact SimAt.pure hs ⟨hden, hmaj⟩
          | forallE nm t b' m => exact SimAt.pure hs ⟨hden, hmaj⟩
          | letE nm t v b' => exact SimAt.pure hs ⟨hden, hmaj⟩
          | lit l => exact SimAt.pure hs ⟨hden, hmaj⟩
          | proj s' j' e' => exact SimAt.pure hs ⟨hden, hmaj⟩
        | axiomInfo cv => exact SimAt.pure hs ⟨hden, hmaj⟩
        | defnInfo cv v h => exact SimAt.pure hs ⟨hden, hmaj⟩
        | thmInfo cv v => exact SimAt.pure hs ⟨hden, hmaj⟩
        | indInfo cv caps => exact SimAt.pure hs ⟨hden, hmaj⟩
        | recInfo cv mI rP rules' => exact SimAt.pure hs ⟨hden, hmaj⟩
        | projInfo entry => exact SimAt.pure hs ⟨hden, hmaj⟩

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The interned pin instantiations denote the nested comparand's
mapped list. -/
theorem pinArgsI_eff (lps : List Name) (us : List LIdx)
    (lus : List Level) :
    ∀ (ps : List Expr) {s₀ : IState}, ISOK env s₀ →
      denoteLList s₀.store.denoteL us = some lus →
      ∀ {args : List EIdx} {xs : List Expr} (t : Nat),
      DenL s₀.store args xs →
      IEff env s₀ (fun s rs => DenL s.store rs
          (ps.map fun p => Expr.instSpine xs t
            (p.instantiateLevelParams lps lus)))
        (pinArgsI lps us args t ps)
  | [], s₀, hs, hus, args, xs, t, hargs => by
    exact IEff.pure hs trivial
  | p :: ps, s₀, hs, hus, args, xs, t, hargs => by
    show IEff env s₀ _
      (internExprM p >>= fun praw =>
        instLevelParamsM lps us praw >>= fun pi =>
        instSpineM args t pi >>= fun r =>
        pinArgsI lps us args t ps >>= fun rs =>
        pure (r :: rs))
    refine IEff.bind (internExprM_eff hs _) (fun s₁ praw hs₁ hext₁ hQpr => ?_)
    refine IEff.bind (instLevelParamsM_eff hs₁
      (denoteLList_mono hext₁ hus) hQpr)
      (fun s₁' pi hs₁' hext₁' hQp => ?_)
    refine IEff.bind (instSpineM_eff hs₁' hQp
      (hargs.mono (hext₁.trans hext₁')))
      (fun s₂ r hs₂ hext₂ hQr => ?_)
    refine IEff.bind (pinArgsI_eff lps us lus ps hs₂
      (denoteLList_mono (((hext₁.trans hext₁').trans hext₂)) hus) t
      (hargs.mono ((hext₁.trans hext₁').trans hext₂)))
      (fun s₃ rs hs₃ hext₃ hQrs => ?_)
    exact IEff.pure hs₃ ⟨denote_mono hext₃ hQr, hQrs⟩

/-- The shared certificate tail of the iota step (after the firing-mode
comparands): recursor/constructor telescope certificates, the
canonical-index check, and the reduct. -/
private theorem iotaRec_certs_tail (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i major : EIdx} {ex majorx : Expr} {c cj : Name}
    {us usj : List LIdx} {lus lusj : List Level}
    {cv cvj : ConstantVal} {mI rP cnP cnF : Nat}
    {rules : List RecRule} {rl : RecRule}
    {args margs : List EIdx} {s₀ : IState} (hs : ISOK env s₀)
    (hus : denoteLList s₀.store.denoteL us = some lus)
    (husj : denoteLList s₀.store.denoteL usj = some lusj)
    (_hden : s₀.store.denote i = some ex) (hw : WScoped d ex)
    (hfc : env.find? c = some (.recInfo cv mI rP rules))
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmd : s₀.store.denote major = some majorx) (hmaj : WScoped d majorx)
    (hargs : DenL s₀.store args ex.getAppArgs)
    (hmargs : DenL s₀.store margs majorx.getAppArgs) :
    SimAt env s₀ (RelO d)
      (constTyAtM (mkFEnv env) c us >>= fun tyRec =>
        iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d tyRec
            (args.take mI ++ [major]) >>= fun r₂ =>
        if r₂ then
          constTyAtM (mkFEnv env) cj usj >>= fun tyCtor =>
          iotaCertsI (coreKnotI (mkFEnv env) f) (mkFEnv env) d tyCtor
              margs >>= fun r₃ =>
          if r₃ then
            Setlec.withStore (fun st =>
                st.stripPisBodyI (rl.ctorParams + rl.nfields)
                  tyCtor) >>= fun ocb =>
            piResidualM tyCtor margs >>= fun ores =>
            match ocb, ores with
            | some cbody, some residual =>
              Setlec.withStore (fun st =>
                  st.nodes[st.getAppFnI cbody]?) >>= fun n'' =>
              match n'' with
              | some (.const _ _) =>
                Setlec.withStore (·.getAppArgsI residual) >>= fun resArgs =>
                defEqListI (coreKnotI (mkFEnv env) f) (mkFEnv env) d
                    (resArgs.drop rl.ctorParams)
                    ((args.take mI).drop rP) >>= fun r₄ =>
                if r₄ then
                  ruleRhsAtM (mkFEnv env) c cj us >>= fun rhs =>
                  mkAppNM rhs (args.take rP ++
                      margs.drop rl.ctorParams) >>= fun red =>
                  pure (some red)
                else pure none
              | _ => pure none
            | _, _ => pure none
          else pure none
        else pure none)
      (iotaCerts (fueledFns env) env d
          (cv.type.instantiateLevelParams cv.levelParams lus)
          (ex.getAppArgs.take mI ++ [majorx]) >>= fun r₂ =>
        if r₂ then
          iotaCerts (fueledFns env) env d
              (cvj.type.instantiateLevelParams cvj.levelParams lusj)
              majorx.getAppArgs >>= fun r₃ =>
          if r₃ then
            match (cvj.type.instantiateLevelParams cvj.levelParams
                  lusj).stripPis (rl.ctorParams + rl.nfields),
                piResidual (cvj.type.instantiateLevelParams
                  cvj.levelParams lusj) majorx.getAppArgs with
            | some (_, cbody), some residual =>
              match cbody.getAppFn with
              | .const _ _ =>
                defEqList (fueledFns env) env d
                    (residual.getAppArgs.drop rl.ctorParams)
                    ((ex.getAppArgs.take mI).drop rP) >>= fun r₄ =>
                if r₄ then
                  pure (some (Expr.mkAppN
                    (rl.rhs.instantiateLevelParams cv.levelParams lus)
                    (ex.getAppArgs.take rP ++
                      majorx.getAppArgs.drop rl.ctorParams)))
                else pure none
              | _ => pure none
            | _, _ => pure none
          else pure none
        else pure none) := by
  have hwrecty : WScoped d
      (cv.type.instantiateLevelParams cv.levelParams lus) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  have hwctorty : WScoped d
      (cvj.type.instantiateLevelParams cvj.levelParams lusj) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine SimAt.bind_left (constTyAtM_eff hs hus hfc)
    (fun s₁ tyRec hs₁ hext₁ hQrec => ?_)
  simp only [ConstantInfo.toConstantVal] at hQrec
  refine SimAt.bind (iotaCertsI_sim ih hs₁ hQrec hwrecty
    (((hargs.mono hext₁).take mI).append
      (DenL.cons (denote_mono hext₁ hmd) DenL.nil)) ?_)
    (fun s₂ r₂ r₂' hs₂ hext₂ hPr₂ => ?_)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw.getAppArgs x (List.mem_of_mem_take hx)
    · rcases List.mem_singleton.mp hx with rfl
      exact hmaj
  obtain rfl : r₂ = r₂' := hPr₂
  cases r₂ with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.pure hs₂ trivial
  | true =>
    simp only [↓reduceIte]
    refine SimAt.bind_left (constTyAtM_eff hs₂
      (denoteLList_mono (hext₁.trans hext₂) husj) hfj)
      (fun s₃ tyCtor hs₃ hext₃ hQctor => ?_)
    simp only [ConstantInfo.toConstantVal] at hQctor
    have hext₀₃ := (hext₁.trans hext₂).trans hext₃
    refine SimAt.bind (iotaCertsI_sim ih hs₃ hQctor hwctorty
      (hmargs.mono hext₀₃) hmaj.getAppArgs)
      (fun s₄ r₃ r₃' hs₄ hext₄ hPr₃ => ?_)
    obtain rfl : r₃ = r₃' := hPr₃
    cases r₃ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.pure hs₄ trivial
    | true =>
      simp only [↓reduceIte]
      refine SimAt.withStore ?_
      have hsp := stripPisBodyI_spec hs₄.wf
        (k := rl.ctorParams + rl.nfields)
        (denote_mono hext₄ hQctor)
      refine SimAt.bind_left (piResidualM_eff hs₄
        (denote_mono hext₄ hQctor)
        (hmargs.mono (hext₀₃.trans hext₄)))
        (fun s₅ ores hs₅ hext₅ hQres => ?_)
      cases hspx : (cvj.type.instantiateLevelParams cvj.levelParams
          lusj).stripPis (rl.ctorParams + rl.nfields) with
      | none =>
        rw [hspx] at hsp
        cases hocb : s₄.store.stripPisBodyI
            (rl.ctorParams + rl.nfields) tyCtor with
        | some cb => rw [hocb] at hsp; exact nomatch hsp
        | none =>
          cases hresx : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams lusj) majorx.getAppArgs with
          | none =>
            cases ores with
            | none => exact SimAt.pure hs₅ trivial
            | some res => rw [hresx] at hQres; exact nomatch hQres
          | some residual =>
            cases ores with
            | none => exact SimAt.pure hs₅ trivial
            | some res => exact SimAt.pure hs₅ trivial
      | some p =>
        obtain ⟨bs, cbody⟩ := p
        rw [hspx] at hsp
        cases hocb : s₄.store.stripPisBodyI
            (rl.ctorParams + rl.nfields) tyCtor with
        | none => rw [hocb] at hsp; exact nomatch hsp
        | some cb =>
          rw [hocb] at hsp
          have hcbd : s₄.store.denote cb = some cbody := hsp
          cases hresx : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams lusj) majorx.getAppArgs with
          | none =>
            rw [hresx] at hQres
            cases ores with
            | none => exact SimAt.pure hs₅ trivial
            | some res => exact nomatch hQres
          | some residual =>
            rw [hresx] at hQres
            cases ores with
            | none => exact nomatch hQres
            | some res =>
              have hresd : s₅.store.denote res = some residual := hQres
              dsimp only
              refine SimAt.withStore ?_
              obtain ⟨n'', hn'', hc'', hd''⟩ :=
                denote_some_inv (getAppFnI_spec hs₅.wf
                  (denote_mono hext₅ hcbd))
              rw [hn'']
              cases n'' with
              | const cn cus =>
                rw [denoteNode, Option.map_eq_some_iff] at hd''
                obtain ⟨lcus, hlcusDen, hd''⟩ := hd''
                rw [← hd'']
                dsimp only
                refine SimAt.withStore ?_
                have hres := getAppArgsI_spec hs₅.wf hresd
                have hresW : WScoped d residual :=
                  piResidual_WScoped hresx hwctorty hmaj.getAppArgs
                refine SimAt.bind (defEqListI_sim ih hs₅
                  (hres.drop rl.ctorParams)
                  (((hargs.mono ((hext₀₃.trans hext₄).trans
                    hext₅)).take mI).drop rP)
                  (fun x hx => hresW.getAppArgs x
                    (List.mem_of_mem_drop hx))
                  (fun x hx => hw.getAppArgs x
                    (List.mem_of_mem_take (List.mem_of_mem_drop hx))))
                  (fun s₆ r₄ r₄' hs₆ hext₆ hPr₄ => ?_)
                obtain rfl : r₄ = r₄' := hPr₄
                cases r₄ with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact SimAt.pure hs₆ trivial
                | true =>
                  simp only [↓reduceIte]
                  refine SimAt.bind_left (ruleRhsAtM_eff hs₆
                    (denoteLList_mono
                      ((((hext₁.trans hext₂).trans hext₃).trans
                        hext₄).trans (hext₅.trans hext₆)) hus)
                    hfc hrule)
                    (fun s₇ rhs hs₇ hext₇ hQrhs => ?_)
                  have hext₀₇ :=
                    (((hext₀₃.trans hext₄).trans hext₅).trans
                      hext₆).trans hext₇
                  refine SimAt.bind_left (mkAppNM_eff hs₇ hQrhs
                    (((hargs.mono hext₀₇).take rP).append
                      ((hmargs.mono hext₀₇).drop rl.ctorParams)))
                    (fun s₈ red hs₈ hext₈ hQred => ?_)
                  refine SimAt.pure hs₈ ⟨hQred, ?_⟩
                  refine Expr.WScoped.mkAppN ?_ ?_
                  · obtain ⟨-, -, -, -, -, hrules, -⟩ :=
                      henv _ (find?_mem hfc)
                    obtain ⟨hrf, -, -, -, -⟩ := hrules cv mI rP rules
                      rfl rl (List.mem_of_find?_eq_some hrule)
                    exact wscoped_instLevels_of_not_hasFvar hrf _ _
                  · intro x hx
                    rcases List.mem_append.mp hx with hx | hx
                    · exact hw.getAppArgs x (List.mem_of_mem_take hx)
                    · exact hmaj.getAppArgs x (List.mem_of_mem_drop hx)
              | bvar k => invert_head hd''; exact SimAt.pure hs₅ trivial
              | sort u => invert_head hd''; exact SimAt.pure hs₅ trivial
              | lit l => invert_head hd''; exact SimAt.pure hs₅ trivial
              | fvar idx nm t =>
                invert_head hd''; exact SimAt.pure hs₅ trivial
              | app f' a' => invert_head hd''; exact SimAt.pure hs₅ trivial
              | lam nm t b' m =>
                invert_head hd''; exact SimAt.pure hs₅ trivial
              | forallE nm t b' m =>
                invert_head hd''; exact SimAt.pure hs₅ trivial
              | letE nm t v b' =>
                invert_head hd''; exact SimAt.pure hs₅ trivial
              | proj s' j' e' =>
                invert_head hd''; exact SimAt.pure hs₅ trivial

private theorem iotaRec_unfold (env : Env) (d : Nat) (e : Expr) :
    iotaRec (fueledFns env) env d e =
    (match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv mI rP rules) =>
        if e.getAppArgs.length = mI + 1 then
          (fueledFns env).whnf d (e.getAppArgs.getD mI (.bvar 0)) >>=
            fun major₀ =>
          litMajorToCtor (fueledFns env) env d major₀ >>= fun major₁ =>
          majorToCtor (fueledFns env) env d c rules major₁ >>= fun major =>
          match major.getAppFn with
          | .const cj usj =>
            match env.find? cj with
            | some (.ctorInfo cvj _ _) =>
              match rules.find? (fun r' => r'.ctor == cj) with
              | some rl =>
                if major.getAppArgs.length = rl.ctorParams + rl.nfields
                    then
                  if rl.fire = .inert then
                    throw (.notImplemented
                      "iota reduction over a nested auxiliary recursor rule")
                  else
                  if (cv.type.stripPis (mI + 1)).isSome ∧
                      (cvj.type.stripPis
                        (rl.ctorParams + rl.nfields)).isSome then
                    liftFueled "level comparison" (Level.isEquivList usj
                        (recFireComparands rl cv.levelParams us
                          cvj.levelParams e.getAppArgs mI).1) >>=
                      fun okl =>
                    if okl then
                      defEqList (fueledFns env) env d
                          (major.getAppArgs.take rl.ctorParams)
                          (recFireComparands rl cv.levelParams us
                            cvj.levelParams e.getAppArgs mI).2 >>=
                        fun r₁ =>
                      if r₁ then
                        iotaCerts (fueledFns env) env d
                            (cv.type.instantiateLevelParams
                              cv.levelParams us)
                            (e.getAppArgs.take mI ++ [major]) >>=
                          fun r₂ =>
                        if r₂ then
                          iotaCerts (fueledFns env) env d
                              (cvj.type.instantiateLevelParams
                                cvj.levelParams usj)
                              major.getAppArgs >>= fun r₃ =>
                          if r₃ then
                            match (cvj.type.instantiateLevelParams
                                  cvj.levelParams usj).stripPis
                                  (rl.ctorParams + rl.nfields),
                                piResidual (cvj.type.instantiateLevelParams
                                  cvj.levelParams usj)
                                  major.getAppArgs with
                            | some (_, cbody), some residual =>
                              match cbody.getAppFn with
                              | .const _ _ =>
                                defEqList (fueledFns env) env d
                                    (residual.getAppArgs.drop
                                      rl.ctorParams)
                                    ((e.getAppArgs.take mI).drop rP) >>=
                                  fun r₄ =>
                                if r₄ then
                                  pure (some (Expr.mkAppN
                                    (rl.rhs.instantiateLevelParams
                                      cv.levelParams us)
                                    (e.getAppArgs.take rP ++
                                      major.getAppArgs.drop
                                        rl.ctorParams)))
                                else pure none
                              | _ => pure none
                            | _, _ => pure none
                          else pure none
                        else pure none
                      else pure none
                    else pure none
                  else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

set_option maxHeartbeats 8000000 in
theorem iotaRecI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i : EIdx} {ex : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hden : s₀.store.denote i = some ex) (hw : WScoped d ex) :
    SimAt env s₀ (RelO d)
      (iotaRecI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i)
      (iotaRec (fueledFns env) env d ex) := by
  unfold iotaRecI
  rw [iotaRec_unfold]
  refine SimAt.withStore ?_
  obtain ⟨n, hn, hc, hd⟩ := denote_some_inv (getAppFnI_spec hs.wf hden)
  rw [hn]
  cases n with
  | const c us =>
    rw [denoteNode, Option.map_eq_some_iff] at hd
    obtain ⟨lus, hlusDen, hd⟩ := hd
    rw [← hd]
    dsimp only
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimAt.pure hs trivial
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only
        refine SimAt.withStore ?_
        have hargs := getAppArgsI_spec hs.wf hden
        rw [hargs.length_eq]
        by_cases hlen : ex.getAppArgs.length = mI + 1
        rotate_right
        · rw [if_neg hlen, if_neg hlen]
          exact SimAt.pure hs trivial
        rw [if_pos hlen, if_pos hlen]
        · have hbv : denoteNode s₀.store.denote s₀.store.denoteL (.bvar 0)
              = some (.bvar 0) := rfl
          refine SimAt.bind_left (internI_eff hs hbv)
            (fun s₁ bvar0 hs₁ hext₁ hQ0 => ?_)
          refine SimAt.bind (ih.whnf hs₁
            (DenL.getD hQ0 mI (hargs.mono hext₁))
            (wscoped_getD hw.getAppArgs _))
            (fun s₂ major₀ major₀x hs₂ hext₂ hP₀ => ?_)
          obtain ⟨hm₀d, hwm₀⟩ := hP₀
          refine SimAt.bind (litMajorToCtorI_sim ih hs₂ hm₀d hwm₀)
            (fun s₃ major₁ major₁x hs₃ hext₃ hP₁ => ?_)
          obtain ⟨hm₁d, hwm₁⟩ := hP₁
          refine SimAt.bind (majorToCtorI_sim ih henv hs₃ hm₁d hwm₁)
            (fun s₄ major majorx hs₄ hext₄ hP₂ => ?_)
          obtain ⟨hmd, hmaj⟩ := hP₂
          refine SimAt.withStore ?_
          obtain ⟨n', hn', hc', hd'⟩ :=
            denote_some_inv (getAppFnI_spec hs₄.wf hmd)
          rw [hn']
          have hext₀₄ :=
            ((hext₁.trans hext₂).trans hext₃).trans hext₄
          cases n' with
          | const cj usj =>
            rw [denoteNode, Option.map_eq_some_iff] at hd'
            obtain ⟨lusj, hlusjDen, hd'⟩ := hd'
            rw [← hd']
            dsimp only
            rw [mkFEnv_find?]
            cases hfj : env.find? cj with
            | none => exact SimAt.pure hs₄ trivial
            | some cij =>
              cases cij with
              | ctorInfo cvj cnP cnF =>
                dsimp only
                cases hrule : rules.find? (fun r' => r'.ctor == cj) with
                | none => exact SimAt.pure hs₄ trivial
                | some rl =>
                  dsimp only
                  refine SimAt.withStore ?_
                  have hmargs := getAppArgsI_spec hs₄.wf hmd
                  rw [hmargs.length_eq]
                  by_cases hmlen : majorx.getAppArgs.length =
                      rl.ctorParams + rl.nfields
                  rotate_right
                  · rw [if_neg hmlen, if_neg hmlen]
                    exact SimAt.pure hs₄ trivial
                  rw [if_pos hmlen, if_pos hmlen]
                  · by_cases hin : rl.fire = RecRuleFire.inert
                    rotate_right
                    · rw [if_neg hin, if_neg hin]
                      by_cases hpins : (cv.type.stripPis (mI + 1)).isSome
                          = true ∧
                          (cvj.type.stripPis
                            (rl.ctorParams + rl.nfields)).isSome = true
                      rotate_right
                      · rw [if_neg hpins, if_neg hpins]
                        exact SimAt.pure hs₄ trivial
                      rw [if_pos hpins, if_pos hpins]
                      · -- both isSome pins hold; walk the certificates
                        have hargsW : ∀ a ∈ ex.getAppArgs, WScoped d a :=
                          hw.getAppArgs
                        have hpinsW : ∀ lvls pins,
                            rl.fire = .nested lvls pins →
                            ∀ pin ∈ pins, pin.hasFvar = false := by
                          intro lvls pins hf' pin hpin
                          obtain ⟨-, -, -, -, -, hrules, -⟩ :=
                            henv _ (find?_mem hfc)
                          obtain ⟨-, -, -, -, g5⟩ := hrules cv mI rP rules
                            rfl rl (List.mem_of_find?_eq_some hrule)
                          exact ((g5 lvls pins hf').2.2.1 pin hpin).1
                        have hcmpW := recFireComparands_snd_WScoped rl
                          cv.levelParams lus cvj.levelParams
                          ex.getAppArgs mI hargsW hpinsW
                        cases hfire : rl.fire with
                        | inert => simp [hfire] at *
                        | plain =>
                          simp only [recFireComparands, hfire] at hcmpW ⊢
                          refine SimAt.bind_left (substLevelTreesM_eff hs₄
                            (ks := cv.levelParams)
                            (cvj.levelParams.map Level.param)
                            (denoteLList_mono hext₀₄ hlusDen))
                            (fun s₄l cmpLvls hs₄l hext₄l hQl => ?_)
                          rw [List.map_map] at hQl
                          refine SimAt.bind_pure_left ?_
                          refine SimAt.bind_left (isEquivListLM_eff hs₄l
                            (denoteLList_mono hext₄l hlusjDen) hQl)
                            (fun s₄o oL hs₄o hext₄o hoL => ?_)
                          subst hoL
                          refine SimAt.bind (SimAt.liftFueled _ _ hs₄o)
                            (fun s₆ okl okl' hs₆ hext₆ hPok => ?_)
                          obtain rfl : okl = okl' := hPok
                          cases okl with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimAt.pure hs₆ trivial
                          | true =>
                            simp only [↓reduceIte]
                            have hext₄₆ :=
                              (hext₄l.trans hext₄o).trans hext₆
                            have hext₀₆ := hext₀₄.trans hext₄₆
                            refine SimAt.bind (defEqListI_sim ih hs₆
                              ((hmargs.mono hext₄₆).take rl.ctorParams)
                              ((hargs.mono hext₀₆).take rl.ctorParams)
                              (fun x hx => hmaj.getAppArgs x
                                (List.mem_of_mem_take hx))
                              (fun x hx => hargsW x
                                (List.mem_of_mem_take hx)))
                              (fun s₇ r₁ r₁' hs₇ hext₇ hPr₁ => ?_)
                            obtain rfl : r₁ = r₁' := hPr₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimAt.pure hs₇ trivial
                            | true =>
                              simp only [↓reduceIte]
                              exact iotaRec_certs_tail ih henv hs₇
                                (denoteLList_mono
                                  (hext₀₆.trans hext₇) hlusDen)
                                (denoteLList_mono
                                  (hext₄₆.trans hext₇) hlusjDen)
                                (denote_mono (hext₀₆.trans hext₇) hden)
                                hw hfc hfj hrule
                                (denote_mono
                                  ((hext₄₆.trans hext₇))
                                  hmd)
                                hmaj
                                (hargs.mono (hext₀₆.trans hext₇))
                                (hmargs.mono
                                  (hext₄₆.trans hext₇))
                        | nested lvls pins =>
                          simp only [recFireComparands, hfire] at hcmpW ⊢
                          refine SimAt.bind_left (substLevelTreesM_eff hs₄
                            (ks := cv.levelParams) lvls
                            (denoteLList_mono hext₀₄ hlusDen))
                            (fun s₄l cmpLvls hs₄l hext₄l hQl => ?_)
                          refine SimAt.bind_left (pinArgsI_eff
                            cv.levelParams us
                            lus pins hs₄l
                            (denoteLList_mono (hext₀₄.trans hext₄l)
                              hlusDen) (mI - 1)
                            ((hargs.mono (hext₀₄.trans hext₄l)).take mI))
                            (fun s₅ cmpArgs hs₅ hext₅ hQc => ?_)
                          refine SimAt.bind_left (isEquivListLM_eff hs₅
                            (denoteLList_mono (hext₄l.trans hext₅)
                              hlusjDen)
                            (denoteLList_mono hext₅ hQl))
                            (fun s₄o oL hs₄o hext₄o hoL => ?_)
                          subst hoL
                          refine SimAt.bind (SimAt.liftFueled _ _ hs₄o)
                            (fun s₆ okl okl' hs₆ hext₆ hPok => ?_)
                          obtain rfl : okl = okl' := hPok
                          cases okl with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimAt.pure hs₆ trivial
                          | true =>
                            simp only [↓reduceIte]
                            have hext₄₆ :=
                              ((hext₄l.trans hext₅).trans hext₄o).trans
                                hext₆
                            have hext₀₆ := hext₀₄.trans hext₄₆
                            refine SimAt.bind (defEqListI_sim ih hs₆
                              ((hmargs.mono hext₄₆).take rl.ctorParams)
                              (hQc.mono (hext₄o.trans hext₆))
                              (fun x hx => hmaj.getAppArgs x
                                (List.mem_of_mem_take hx))
                              hcmpW)
                              (fun s₇ r₁ r₁' hs₇ hext₇ hPr₁ => ?_)
                            obtain rfl : r₁ = r₁' := hPr₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimAt.pure hs₇ trivial
                            | true =>
                              simp only [↓reduceIte]
                              exact iotaRec_certs_tail ih henv hs₇
                                (denoteLList_mono
                                  (hext₀₆.trans hext₇) hlusDen)
                                (denoteLList_mono
                                  (hext₄₆.trans hext₇) hlusjDen)
                                (denote_mono (hext₀₆.trans hext₇) hden)
                                hw hfc hfj hrule
                                (denote_mono
                                  (hext₄₆.trans hext₇)
                                  hmd)
                                hmaj
                                (hargs.mono (hext₀₆.trans hext₇))
                                (hmargs.mono
                                  (hext₄₆.trans hext₇))
                    · rw [if_pos hin, if_pos hin]
                      exact SimAt.throw
              | axiomInfo cv' => exact SimAt.pure hs₄ trivial
              | defnInfo cv' v h => exact SimAt.pure hs₄ trivial
              | thmInfo cv' v => exact SimAt.pure hs₄ trivial
              | indInfo cv' caps => exact SimAt.pure hs₄ trivial
              | recInfo cv' mI' rP' rules' => exact SimAt.pure hs₄ trivial
              | projInfo entry => exact SimAt.pure hs₄ trivial
          | bvar k => invert_head hd'; exact SimAt.pure hs₄ trivial
          | sort u => invert_head hd'; exact SimAt.pure hs₄ trivial
          | lit l => invert_head hd'; exact SimAt.pure hs₄ trivial
          | fvar idx nm t => invert_head hd'; exact SimAt.pure hs₄ trivial
          | app f' a' => invert_head hd'; exact SimAt.pure hs₄ trivial
          | lam nm t b' m => invert_head hd'; exact SimAt.pure hs₄ trivial
          | forallE nm t b' m =>
            invert_head hd'; exact SimAt.pure hs₄ trivial
          | letE nm t v b' => invert_head hd'; exact SimAt.pure hs₄ trivial
          | proj s' j' e' => invert_head hd'; exact SimAt.pure hs₄ trivial
      | axiomInfo cv => exact SimAt.pure hs trivial
      | defnInfo cv v h => exact SimAt.pure hs trivial
      | thmInfo cv v => exact SimAt.pure hs trivial
      | indInfo cv caps => exact SimAt.pure hs trivial
      | ctorInfo cv nP nF => exact SimAt.pure hs trivial
      | projInfo entry => exact SimAt.pure hs trivial
  | bvar k => invert_head hd; exact SimAt.pure hs trivial
  | sort u => invert_head hd; exact SimAt.pure hs trivial
  | lit l => invert_head hd; exact SimAt.pure hs trivial
  | fvar idx nm t => invert_head hd; exact SimAt.pure hs trivial
  | app f' a' => invert_head hd; exact SimAt.pure hs trivial
  | lam nm t b' m => invert_head hd; exact SimAt.pure hs trivial
  | forallE nm t b' m => invert_head hd; exact SimAt.pure hs trivial
  | letE nm t v b' => invert_head hd; exact SimAt.pure hs trivial
  | proj s' j' e' => invert_head hd; exact SimAt.pure hs trivial

end Walks2

end Setlec
