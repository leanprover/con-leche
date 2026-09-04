import Setlec.Verify.Cached.DiscC2

/-!
# Cached body walks, part 3: the stuck-major rescue and iota

Simulation walks for the cached `majorToCtorI`/`pinArgsI`/`iotaRecI`
(`Setlec/Cached/CoreC.lean`) against `majorToCtor`/`iotaRec`
(`Setlec/Verify/Disc.lean`) — the port of `Setlec/Verify/DiscI3.lean`
under the task #163 recipe.  The pure comparand side of every statement
is byte-identical to the interned original's.
-/

namespace Setlec.Cached

open Setlec.Cached.ExprC

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

private theorem majorToCtor_unfold (env : Env) (d : Nat) (recName : Name)
    (rules : List RecRule) (major : Expr) :
    majorToCtor mode (fueledFns mode env) env d recName rules major =
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
              (fueledFns mode env).infer d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ cvj.levelParams.length = ust.length then
                  if cnP ≤ tmaj.getAppArgs.length ∧
                      (cvj.type.stripPis cnP).isSome = true then
                    let fab := Expr.mkAppN (.const rl.ctor ust)
                      (tmaj.getAppArgs.take cnP)
                    if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                        fab.fvarLeaves.all
                          (fun l => major.fvarLeaves.contains l) then
                      iotaCerts (fueledFns mode env) env d
                          (cvj.type.instantiateLevelParams
                            cvj.levelParams ust)
                          (tmaj.getAppArgs.take cnP) >>= fun rc =>
                      if rc then
                        (fueledFns mode env).infer d fab >>= fun tfab =>
                        (fueledFns mode env).defeq d tmaj tfab >>= fun rd =>
                        if rd then
                          proofIrrel (fueledFns mode env) env d fab major >>=
                            fun r =>
                          if r then pure fab
                          else pure major
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                Name.isProjFnShape recName = false then
              (fueledFns mode env).infer d major >>= fun tm =>
              (fueledFns mode env).whnf d tm >>= fun tmaj =>
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                    ust.length = cvT.levelParams.length ∧
                    piResultNeverZero cvT.levelParams ust cvT.type = true then
                  if cvj.levelParams.length = ust.length ∧
                      (cvj.type.stripPis
                        (caps.etaParams + caps.etaFields)).isSome
                        = true then
                    let fab := Expr.mkAppN (.const caps.etaCtor ust)
                      (tmaj.getAppArgs ++
                        (List.range caps.etaFields).map fun j =>
                          Expr.mkAppN (.const (projFnName T j) ust)
                            (tmaj.getAppArgs ++ [major]))
                    if fab.wscopedB d && fab.looseBVarsBounded 0 &&
                        fab.fvarLeaves.all
                          (fun l => major.fvarLeaves.contains l) then
                      iotaCerts (fueledFns mode env) env d
                          (cvj.type.instantiateLevelParams
                            cvj.levelParams ust)
                          (tmaj.getAppArgs ++
                            (List.range caps.etaFields).map fun j =>
                              Expr.mkAppN (.const (projFnName T j) ust)
                                (tmaj.getAppArgs ++ [major])) >>=
                        fun rc =>
                      if rc then
                        structEtaCertWith mode (fueledFns mode env) env d fab major
                            tmaj >>= fun r =>
                        if r then pure fab
                        else if caps.etaFields = 0 ∧
                            cvj.levelParams.length = ust.length then
                          proofIrrel (fueledFns mode env) env d fab major >>=
                            fun r' =>
                          if r' then pure fab
                          else pure major
                        else pure major
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

/-- Port of `majorToCtorI_sim`. -/
theorem majorToCtorC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : ExprC}
    {major : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i major) (hmaj : Expr.WScoped d major) :
    SimC mode env s₀ (RelEC d)
      (majorToCtorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName
        rules i)
      (majorToCtor mode (fueledFns mode env) env d recName rules major) := by
  show SimC mode env s₀ (RelEC d)
    (Setlec.Cached.withStore (fun st => isCtorAppI (mkFEnv env) st i) >>=
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
                (coreKnotI mode (mkFEnv env) f).infer d i >>= fun tm =>
                (coreKnotI mode (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                Setlec.Cached.withStore
                    (fun st => st.getNode (st.getAppFnI tmaj)) >>= fun n =>
                match n with
                | some (.const T' ust) =>
                  beqNameM T' T >>= fun bq =>
                  if bq ∧ cvj.levelParams.length = ust.length then
                    Setlec.Cached.withStore (·.getAppArgsI tmaj) >>= fun margs =>
                    if cnP ≤ margs.length ∧
                        (cvj.type.stripPis cnP).isSome = true then
                      internNameM rl.ctor >>= fun ctorI =>
                      internI (.const ctorI ust) >>= fun h =>
                      mkAppNM h (margs.take cnP) >>= fun fab =>
                      Setlec.Cached.withStore (fun st => st.wscopedBI d fab &&
                        st.looseBVarsBoundedI 0 fab &&
                        st.leafGuardI fab i) >>=
                        fun g =>
                      if g then
                        constTyAtM (mkFEnv env) ctorI rl.ctor ust >>=
                          fun tyCtor =>
                        iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
                            d tyCtor (margs.take cnP) >>= fun rc =>
                        if rc then
                          (coreKnotI mode (mkFEnv env) f).infer d fab >>=
                            fun tfab =>
                          (coreKnotI mode (mkFEnv env) f).defeq d tmaj
                              tfab >>= fun rd =>
                          if rd then
                            proofIrrelI (coreKnotI mode (mkFEnv env) f)
                                (mkFEnv env) d fab i >>= fun r =>
                            if r then pure fab
                            else pure i
                          else pure i
                        else pure i
                      else pure i
                    else pure i
                  else pure i
                | _ => pure i
              else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
                  Name.isProjFnShape recName = false then
                (coreKnotI mode (mkFEnv env) f).infer d i >>= fun tm =>
                (coreKnotI mode (mkFEnv env) f).whnf d tm >>= fun tmaj =>
                Setlec.Cached.withStore
                    (fun st => st.getNode (st.getAppFnI tmaj)) >>= fun n =>
                match n with
                | some (.const T' ust) =>
                  Setlec.Cached.withStore (·.getAppArgsI tmaj) >>= fun margs =>
                  readbackLevelsM ust >>= fun ustL =>
                  beqNameM T' T >>= fun bq =>
                  if bq ∧ margs.length = caps.etaParams ∧
                      ust.length = cvT.levelParams.length ∧
                      piResultNeverZero cvT.levelParams ustL cvT.type
                        = true then
                    if cvj.levelParams.length = ust.length ∧
                        (cvj.type.stripPis
                          (caps.etaParams + caps.etaFields)).isSome
                          = true then
                      internNameM T >>= fun TI =>
                      projAppsI TI ust margs i
                          (List.range caps.etaFields) >>= fun projs =>
                      internNameM caps.etaCtor >>= fun ctorI =>
                      internI (.const ctorI ust) >>= fun h =>
                      mkAppNM h (margs ++ projs) >>= fun fab =>
                      Setlec.Cached.withStore (fun st => st.wscopedBI d fab &&
                        st.looseBVarsBoundedI 0 fab &&
                        st.leafGuardI fab i) >>=
                        fun g =>
                      if g then
                        constTyAtM (mkFEnv env) ctorI rl.ctor ust >>=
                          fun tyCtor =>
                        iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env)
                            d tyCtor (margs ++ projs) >>= fun rc =>
                        if rc then
                          structEtaCertWithI mode (coreKnotI mode (mkFEnv env) f)
                              (mkFEnv env) d fab i tmaj >>= fun r =>
                          if r then pure fab
                          else if caps.etaFields = 0 ∧
                              cvj.levelParams.length = ust.length then
                            proofIrrelI (coreKnotI mode (mkFEnv env) f)
                                (mkFEnv env) d fab i >>= fun r' =>
                            if r' then pure fab
                            else pure i
                          else pure i
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
    (majorToCtor mode (fueledFns mode env) env d recName rules major)
  rw [majorToCtor_unfold]
  refine SimC.withStore ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hden : RelC i i := ⟨hwc, rfl⟩
  rw [isCtorAppI_spec hwc rfl]
  by_cases hctor : isCtorApp env i
  · rw [if_pos hctor, if_pos hctor]
    exact SimC.pure hs ⟨hden, hmaj⟩
  · rw [if_neg hctor, if_neg hctor]
    match rules with
    | [] => exact SimC.pure hs ⟨hden, hmaj⟩
    | _ :: _ :: _ => exact SimC.pure hs ⟨hden, hmaj⟩
    | [rl] =>
      dsimp only
      rw [show (mkFEnv env).find? rl.ctor = env.find? rl.ctor from
        mkFEnv_find? env rl.ctor]
      cases hfj : env.find? rl.ctor with
      | none => exact SimC.pure hs ⟨hden, hmaj⟩
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
            | none => exact SimC.pure hs ⟨hden, hmaj⟩
            | some ciT =>
              cases ciT with
              | indInfo cvT caps =>
                dsimp only
                by_cases hK : caps.ruleK = true ∧ cnF = 0
                · rw [if_pos hK, if_pos hK]
                  refine SimC.bind (ih.infer hs hden hmaj)
                    (fun s₁ tm tmx hs₁ hP => ?_)
                  obtain ⟨htmd, hwtm⟩ := hP
                  refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                    (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                  obtain ⟨⟨hwtmajc, rfl⟩, hwtmaj⟩ := hP₂
                  have hmargs : RelCL (ExprC.getAppArgs tmaj)
                      (Expr.getAppArgs tmaj) :=
                    ExprC.getAppArgs_spec hwtmajc
                  refine SimC.withStore ?_
                  obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwtmajc
                  dsimp only [CStore.getNode, CStore.getAppFnI]
                  generalize hg : ExprC.getAppFn tmaj = g at hwfn hfn ⊢
                  cases g with
                  | const T' ust =>
                    rw [show (Expr.getAppFn tmaj) = Expr.const T' ust
                      from hfn.symm]
                    dsimp only
                    refine SimC.bind_left (beqNameM_eff hs₂ T' T)
                      (fun s₂b bq hs₂ hbq => ?_)
                    subst bq
                    simp only [beq_iff_eq]
                    split
                    · refine SimC.withStore ?_
                      simp only [CStore.getAppArgsI, hmargs.length]
                      split
                      rotate_left
                      · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                      refine SimC.bind_left (internNameM_eff hs₂ rl.ctor)
                        (fun s₂n ctorI hs₂ hQctorI => ?_)
                      subst hQctorI
                      refine SimC.bind_left (internI_eff hs₂
                        (n := ExprView.const rl.ctor ust) trivial)
                        (fun s₃ hd hs₃ hQh => ?_)
                      refine SimC.bind_left (mkAppNM_eff hs₃ hQh
                        (hmargs.take cnP))
                        (fun s₄ fab hs₄ hQfab => ?_)
                      have hQfab' : RelC fab
                          (Expr.mkAppN (.const rl.ctor ust)
                            ((Expr.getAppArgs tmaj).take cnP)) := hQfab
                      refine SimC.withStore ?_
                      rw [wscopedBI_spec hQfab'.1 hQfab'.2,
                        looseBVarsBoundedI_spec hQfab'.1 hQfab'.2,
                        leafGuardI_spec hQfab'.1 hwc hQfab'.2 rfl]
                      split
                      · rename_i hguard
                        have hwfab := Expr.WScoped.of_wscopedB
                          (by simp only [Bool.and_eq_true] at hguard
                              exact hguard.1.1)
                        -- the relocated synthetic-spine certificate
                        refine SimC.bind_left (constTyAtM_eff hs₄ hfj)
                          (fun s₄c tyCtor hs₄c hQty => ?_)
                        simp only [ConstantInfo.toConstantVal] at hQty
                        have hwty : Expr.WScoped d
                            (cvj.type.instantiateLevelParams
                              cvj.levelParams ust) := by
                          obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
                          exact wscoped_instLevels_of_not_hasFvar
                            htf _ _
                        refine SimC.bind (iotaCertsC_sim ih hs₄c hQty
                          hwty (hmargs.take cnP)
                          (fun x hx => hwtmaj.getAppArgs x
                            (List.mem_of_mem_take hx)))
                          (fun s₄d rc rc' hs₄d hPrc => ?_)
                        obtain rfl : rc = rc' := hPrc
                        cases rc with
                        | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          exact SimC.pure hs₄d ⟨hden, hmaj⟩
                        | true =>
                          simp only [↓reduceIte]
                          -- the official `to_cnstr_when_K` type check
                          refine SimC.bind (ih.infer hs₄d hQfab' hwfab)
                            (fun s₄e tfab tfabx hs₄e hPtf => ?_)
                          obtain ⟨htfd, hwtf⟩ := hPtf
                          refine SimC.bind (ih.defeq hs₄e ⟨hwtmajc, rfl⟩
                            htfd hwtmaj hwtf)
                            (fun s₄f rd rd' hs₄f hPrd => ?_)
                          obtain rfl : rd = rd' := hPrd
                          cases rd with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₄f ⟨hden, hmaj⟩
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (proofIrrelC_sim ih hs₄f
                              hQfab' hden hwfab hmaj)
                              (fun s₅ r r' hs₅ hPr => ?_)
                            obtain rfl : r = r' := hPr
                            cases r with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimC.pure hs₅ ⟨hQfab', hwfab⟩
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₅ ⟨hden, hmaj⟩
                      · exact SimC.pure hs₄ ⟨hden, hmaj⟩
                    · exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | bvar k =>
                    rw [show (Expr.getAppFn tmaj) = Expr.bvar k
                      from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | sort u =>
                    rw [show (Expr.getAppFn tmaj) = Expr.sort u
                      from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | lit l =>
                    rw [show (Expr.getAppFn tmaj) = Expr.lit l
                      from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | fvar ix nm t =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.fvar ix nm t from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | app f' a' =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.app f' a' from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | lam nm t b' m =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.lam nm t b' m from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | forallE nm t b' m =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.forallE nm t b' m
                      from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | letE nm t v b' =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.letE nm t v b'
                      from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  | proj sn jx e' =>
                    rw [show (Expr.getAppFn tmaj)
                      = Expr.proj sn jx e' from hfn.symm]
                    exact SimC.pure hs₂ ⟨hden, hmaj⟩
                · rw [if_neg hK, if_neg hK]
                  by_cases hEta : caps.eta = true ∧
                      rl.ctor = caps.etaCtor ∧
                      Name.isProjFnShape recName = false
                  · rw [if_pos hEta, if_pos hEta]
                    refine SimC.bind (ih.infer hs hden hmaj)
                      (fun s₁ tm tmx hs₁ hP => ?_)
                    obtain ⟨htmd, hwtm⟩ := hP
                    refine SimC.bind (ih.whnf hs₁ htmd hwtm)
                      (fun s₂ tmaj tmajx hs₂ hP₂ => ?_)
                    obtain ⟨⟨hwtmajc, rfl⟩, hwtmaj⟩ := hP₂
                    have hmargs : RelCL (ExprC.getAppArgs tmaj)
                        (Expr.getAppArgs tmaj) :=
                      ExprC.getAppArgs_spec hwtmajc
                    refine SimC.withStore ?_
                    obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwtmajc
                    dsimp only [CStore.getNode, CStore.getAppFnI]
                    generalize hg : ExprC.getAppFn tmaj = g at hwfn hfn ⊢
                    cases g with
                    | const T' ust =>
                      rw [show (Expr.getAppFn tmaj) = Expr.const T' ust
                        from hfn.symm]
                      dsimp only
                      refine SimC.withStore ?_
                      refine SimC.bind_left (readbackLevelsM_eff hs₂ ust)
                        (fun s₂r ustL hs₂r hustL => ?_)
                      subst ustL
                      refine SimC.bind_left (beqNameM_eff hs₂r T' T)
                        (fun s₂rb bq hs₂r hbq => ?_)
                      subst bq
                      simp only [CStore.getAppArgsI, hmargs.length,
                        beq_iff_eq]
                      split
                      · split
                        rotate_left
                        · exact SimC.pure hs₂r ⟨hden, hmaj⟩
                        refine SimC.bind_left (internNameM_eff hs₂r T)
                          (fun s₂t TI hs₂r hQTI => ?_)
                        subst TI
                        refine SimC.bind_left (projAppsC_eff T ust
                          (List.range caps.etaFields) hs₂r hmargs hden)
                          (fun s₃ projs hs₃ hQp => ?_)
                        refine SimC.bind_left (internNameM_eff hs₃
                          caps.etaCtor)
                          (fun s₃n ctorI hs₃ hQctorI => ?_)
                        subst hQctorI
                        refine SimC.bind_left (internI_eff hs₃
                          (n := ExprView.const caps.etaCtor ust) trivial)
                          (fun s₄ hd hs₄ hQh => ?_)
                        refine SimC.bind_left (mkAppNM_eff hs₄ hQh
                          (hmargs.append hQp))
                          (fun s₅ fab hs₅ hQfab => ?_)
                        have hQfab' : RelC fab
                            (Expr.mkAppN (.const caps.etaCtor ust)
                              ((Expr.getAppArgs tmaj) ++
                                (List.range caps.etaFields).map fun j =>
                                  Expr.mkAppN (.const (projFnName T j) ust)
                                    ((Expr.getAppArgs tmaj) ++
                                      [i]))) := hQfab
                        refine SimC.withStore ?_
                        rw [wscopedBI_spec hQfab'.1 hQfab'.2,
                          looseBVarsBoundedI_spec hQfab'.1 hQfab'.2,
                          leafGuardI_spec hQfab'.1 hwc hQfab'.2 rfl]
                        split
                        · rename_i hguard
                          have hwfab := Expr.WScoped.of_wscopedB
                            (by simp only [Bool.and_eq_true] at hguard
                                exact hguard.1.1)
                          -- the relocated synthetic-spine certificate
                          refine SimC.bind_left (constTyAtM_eff hs₅ hfj)
                            (fun s₅c tyCtor hs₅c hQty => ?_)
                          simp only [ConstantInfo.toConstantVal] at hQty
                          have hwty : Expr.WScoped d
                              (cvj.type.instantiateLevelParams
                                cvj.levelParams ust) := by
                            obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
                            exact wscoped_instLevels_of_not_hasFvar
                              htf _ _
                          refine SimC.bind (iotaCertsC_sim ih hs₅c hQty
                            hwty (hmargs.append hQp) (fun x hx => ?_))
                            (fun s₅d rc rc' hs₅d hPrc => ?_)
                          · rcases List.mem_append.mp hx with hx | hx
                            · exact hwtmaj.getAppArgs x hx
                            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
                              refine Expr.WScoped.mkAppN
                                (by simp [Expr.WScoped]) ?_
                              intro y hy
                              rcases List.mem_append.mp hy with hy | hy
                              · exact hwtmaj.getAppArgs y hy
                              · rw [List.mem_singleton.mp hy]
                                exact hmaj
                          obtain rfl : rc = rc' := hPrc
                          cases rc with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₅d ⟨hden, hmaj⟩
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (structEtaCertWithC_sim ih
                              henv hs₅d hQfab' hden ⟨hwtmajc, rfl⟩
                              hwfab hmaj hwtmaj)
                              (fun s₆ r r' hs₆ hPr => ?_)
                            obtain rfl : r = r' := hPr
                            cases r with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimC.pure hs₆ ⟨hQfab', hwfab⟩
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              split
                              · refine SimC.bind (proofIrrelC_sim ih hs₆
                                  hQfab' hden hwfab hmaj)
                                  (fun s₇ r₂ r₂' hs₇ hPr₂ => ?_)
                                obtain rfl : r₂ = r₂' := hPr₂
                                cases r₂ with
                                | true =>
                                  simp only [↓reduceIte]
                                  exact SimC.pure hs₇ ⟨hQfab', hwfab⟩
                                | false =>
                                  simp only [Bool.false_eq_true,
                                    ↓reduceIte]
                                  exact SimC.pure hs₇ ⟨hden, hmaj⟩
                              · exact SimC.pure hs₆ ⟨hden, hmaj⟩
                        · exact SimC.pure hs₅ ⟨hden, hmaj⟩
                      · exact SimC.pure hs₂r ⟨hden, hmaj⟩
                    | bvar k =>
                      rw [show (Expr.getAppFn tmaj) = Expr.bvar k
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | sort u =>
                      rw [show (Expr.getAppFn tmaj) = Expr.sort u
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lit l =>
                      rw [show (Expr.getAppFn tmaj) = Expr.lit l
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | fvar ix nm t =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.fvar ix nm t from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | app f' a' =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.app f' a' from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | lam nm t b' m =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.lam nm t b' m
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | forallE nm t b' m =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.forallE nm t b' m
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | letE nm t v b' =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.letE nm t v b'
                        from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                    | proj sn jx e' =>
                      rw [show (Expr.getAppFn tmaj)
                        = Expr.proj sn jx e' from hfn.symm]
                      exact SimC.pure hs₂ ⟨hden, hmaj⟩
                  · rw [if_neg hEta, if_neg hEta]
                    exact SimC.pure hs ⟨hden, hmaj⟩
              | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
              | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
              | thmInfo cv v => exact SimC.pure hs ⟨hden, hmaj⟩
              | ctorInfo cv nP' nF' => exact SimC.pure hs ⟨hden, hmaj⟩
              | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
              | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩
          | bvar k => exact SimC.pure hs ⟨hden, hmaj⟩
          | fvar ix nmᵢ t => exact SimC.pure hs ⟨hden, hmaj⟩
          | sort u => exact SimC.pure hs ⟨hden, hmaj⟩
          | app f' a' => exact SimC.pure hs ⟨hden, hmaj⟩
          | lam nmᵢ t b' m => exact SimC.pure hs ⟨hden, hmaj⟩
          | forallE nmᵢ t b' m => exact SimC.pure hs ⟨hden, hmaj⟩
          | letE nmᵢ t v b' => exact SimC.pure hs ⟨hden, hmaj⟩
          | lit l => exact SimC.pure hs ⟨hden, hmaj⟩
          | proj s'ᵢ j' e' => exact SimC.pure hs ⟨hden, hmaj⟩
        | axiomInfo cv => exact SimC.pure hs ⟨hden, hmaj⟩
        | defnInfo cv v h => exact SimC.pure hs ⟨hden, hmaj⟩
        | thmInfo cv v => exact SimC.pure hs ⟨hden, hmaj⟩
        | indInfo cv caps => exact SimC.pure hs ⟨hden, hmaj⟩
        | recInfo cv mI rP rules' => exact SimC.pure hs ⟨hden, hmaj⟩
        | projInfo entry => exact SimC.pure hs ⟨hden, hmaj⟩

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- Port of `pinArgsI_eff`: the cached pin instantiations denote the
nested comparand's mapped list.  (The interned original's separate
`us : List LIdx` / `lus : List Level` pair collapses to the single
level list, so its `denoteLList` premise vanishes.) -/
theorem pinArgsC_eff (lps : List Name) (us : List Level) :
    ∀ (ps : List Expr) {s₀ : CState}, CSOK mode env s₀ →
      ∀ {args : List ExprC} {xs : List Expr} (t : Nat),
      RelCL args xs →
      CEff mode env s₀ (fun rs => RelCL rs
          (ps.map fun p => Expr.instSpine xs t
            (p.instantiateLevelParams lps us)))
        (pinArgsI lps us args t ps)
  | [], s₀, hs, args, xs, t, hargs => by
    exact CEff.pure hs RelCL.nil
  | p :: ps, s₀, hs, args, xs, t, hargs => by
    show CEff mode env s₀ _
      (internExprM p >>= fun praw =>
        instLevelParamsM lps us praw >>= fun pi =>
        instSpineM args t pi >>= fun r =>
        pinArgsI lps us args t ps >>= fun rs =>
        pure (r :: rs))
    refine CEff.bind (internExprM_eff hs p) (fun s₁ praw hs₁ hQpr => ?_)
    refine CEff.bind (instLevelParamsM_eff hs₁ hQpr)
      (fun s₁' pi hs₁' hQp => ?_)
    refine CEff.bind (instSpineM_eff hs₁' hQp hargs)
      (fun s₂ r hs₂ hQr => ?_)
    refine CEff.bind (pinArgsC_eff lps us ps hs₂ t hargs)
      (fun s₃ rs hs₃ hQrs => ?_)
    exact CEff.pure hs₃ (RelCL.cons hQr hQrs)

/-- Port of `iotaRec_certs_tail`: the shared certificate tail of the
iota step (after the firing-mode comparands).  The interned original's
`cI jI : NIdx` name indices stay as (unconstrained) `Name` parameters;
their `denoteN` premises vanish with the name collapse. -/
private theorem iotaRec_certs_tail (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i major : ExprC} {ex majorx : Expr} {cI jI : Name}
    {c cj : Name}
    {us usj : List Level}
    {cv cvj : ConstantVal} {mI rP cnP cnF : Nat}
    {rules : List RecRule} {rl : RecRule}
    {args margs : List ExprC} {s₀ : CState} (hs : CSOK mode env s₀)
    (_hden : RelC i ex) (hw : Expr.WScoped d ex)
    (hfc : env.find? c = some (.recInfo cv mI rP rules))
    (hfj : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmd : RelC major majorx) (hmaj : Expr.WScoped d majorx)
    (hargs : RelCL args ex.getAppArgs)
    (hmargs : RelCL margs majorx.getAppArgs) :
    SimC mode env s₀ (RelOC d)
      (constTyAtM (mkFEnv env) cI c us >>= fun tyRec =>
        iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d tyRec
            (args.take mI ++ [major]) >>= fun r₂ =>
        if r₂ then
          constTyAtM (mkFEnv env) jI cj usj >>= fun tyCtor =>
          iotaCertsI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d tyCtor
              margs >>= fun r₃ =>
          if r₃ then
            Setlec.Cached.withStore (fun st =>
                st.stripPisBodyI (rl.ctorParams + rl.nfields)
                  tyCtor) >>= fun ocb =>
            piResidualM tyCtor margs >>= fun ores =>
            match ocb, ores with
            | some cbody, some residual =>
              Setlec.Cached.withStore (fun st =>
                  st.getNode (st.getAppFnI cbody)) >>= fun n'' =>
              match n'' with
              | some (.const _ _) =>
                Setlec.Cached.withStore (·.getAppArgsI residual) >>=
                  fun resArgs =>
                defEqListI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d
                    (resArgs.drop rl.ctorParams)
                    ((args.take mI).drop rP) >>= fun r₄ =>
                if r₄ then
                  ruleRhsAtM (mkFEnv env) cI jI c cj us >>= fun rhs =>
                  mkAppNM rhs (args.take rP ++
                      margs.drop rl.ctorParams) >>= fun red =>
                  pure (some red)
                else pure none
              | _ => pure none
            | _, _ => pure none
          else pure none
        else pure none)
      (iotaCerts (fueledFns mode env) env d
          (cv.type.instantiateLevelParams cv.levelParams us)
          (ex.getAppArgs.take mI ++ [majorx]) >>= fun r₂ =>
        if r₂ then
          iotaCerts (fueledFns mode env) env d
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              majorx.getAppArgs >>= fun r₃ =>
          if r₃ then
            match (cvj.type.instantiateLevelParams cvj.levelParams
                  usj).stripPis (rl.ctorParams + rl.nfields),
                piResidual (cvj.type.instantiateLevelParams
                  cvj.levelParams usj) majorx.getAppArgs with
            | some (_, cbody), some residual =>
              match cbody.getAppFn with
              | .const _ _ =>
                defEqList (fueledFns mode env) env d
                    (residual.getAppArgs.drop rl.ctorParams)
                    ((ex.getAppArgs.take mI).drop rP) >>= fun r₄ =>
                if r₄ then
                  pure (some (Expr.mkAppN
                    (rl.rhs.instantiateLevelParams cv.levelParams us)
                    (ex.getAppArgs.take rP ++
                      majorx.getAppArgs.drop rl.ctorParams)))
                else pure none
              | _ => pure none
            | _, _ => pure none
          else pure none
        else pure none) := by
  have hwrecty : Expr.WScoped d
      (cv.type.instantiateLevelParams cv.levelParams us) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfc)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  have hwctorty : Expr.WScoped d
      (cvj.type.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨htf, -⟩ := henv _ (find?_mem hfj)
    exact wscoped_instLevels_of_not_hasFvar htf _ _
  refine SimC.bind_left (constTyAtM_eff hs hfc)
    (fun s₁ tyRec hs₁ hQrec => ?_)
  simp only [ConstantInfo.toConstantVal] at hQrec
  refine SimC.bind (iotaCertsC_sim ih hs₁ hQrec hwrecty
    ((hargs.take mI).append (RelCL.cons hmd RelCL.nil)) ?_)
    (fun s₂ r₂ r₂' hs₂ hPr₂ => ?_)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hw.getAppArgs x (List.mem_of_mem_take hx)
    · rcases List.mem_singleton.mp hx with rfl
      exact hmaj
  obtain rfl : r₂ = r₂' := hPr₂
  cases r₂ with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs₂ trivial
  | true =>
    simp only [↓reduceIte]
    refine SimC.bind_left (constTyAtM_eff hs₂ hfj)
      (fun s₃ tyCtor hs₃ hQctor => ?_)
    simp only [ConstantInfo.toConstantVal] at hQctor
    refine SimC.bind (iotaCertsC_sim ih hs₃ hQctor hwctorty hmargs
      hmaj.getAppArgs)
      (fun s₄ r₃ r₃' hs₄ hPr₃ => ?_)
    obtain rfl : r₃ = r₃' := hPr₃
    cases r₃ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₄ trivial
    | true =>
      simp only [↓reduceIte]
      refine SimC.withStore ?_
      have hsp : OptEr (ExprC.stripPisBody (rl.ctorParams + rl.nfields) tyCtor)
          (((cvj.type.instantiateLevelParams cvj.levelParams usj).stripPis
            (rl.ctorParams + rl.nfields)).map (·.2)) := by
        have h := ExprC.stripPisBody_spec
          (k := rl.ctorParams + rl.nfields) hQctor.1
        rw [← hQctor.2]
        exact h
      simp only [CStore.stripPisBodyI]
      refine SimC.bind_left (piResidualM_eff hs₄ hQctor hmargs)
        (fun s₅ ores hs₅ hQres => ?_)
      cases hspx : (cvj.type.instantiateLevelParams cvj.levelParams
          usj).stripPis (rl.ctorParams + rl.nfields) with
      | none =>
        rw [hspx] at hsp
        cases hocb : ExprC.stripPisBody (rl.ctorParams + rl.nfields)
            tyCtor with
        | some cb => rw [hocb] at hsp; exact nomatch hsp
        | none =>
          cases hresx : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams usj) majorx.getAppArgs with
          | none =>
            cases ores with
            | none => exact SimC.pure hs₅ trivial
            | some res => rw [hresx] at hQres; exact nomatch hQres
          | some residual =>
            cases ores with
            | none => exact SimC.pure hs₅ trivial
            | some res => exact SimC.pure hs₅ trivial
      | some p =>
        obtain ⟨bs, cbody⟩ := p
        rw [hspx] at hsp
        cases hocb : ExprC.stripPisBody (rl.ctorParams + rl.nfields)
            tyCtor with
        | none => rw [hocb] at hsp; exact nomatch hsp
        | some cb =>
          rw [hocb] at hsp
          have hcbd : RelC cb cbody := hsp
          obtain ⟨hwcb, rfl⟩ := hcbd
          cases hresx : piResidual (cvj.type.instantiateLevelParams
              cvj.levelParams usj) majorx.getAppArgs with
          | none =>
            rw [hresx] at hQres
            cases ores with
            | none => exact SimC.pure hs₅ trivial
            | some res => exact nomatch hQres
          | some residual =>
            rw [hresx] at hQres
            cases ores with
            | none => exact nomatch hQres
            | some res =>
              have hresd : RelC res residual := hQres
              have hresW : Expr.WScoped d residual :=
                piResidual_WScoped hresx hwctorty hmaj.getAppArgs
              obtain ⟨hwres, rfl⟩ := hresd
              dsimp only
              refine SimC.withStore ?_
              obtain ⟨hwfn'', hfn''⟩ := ExprC.getAppFn_spec hwcb
              dsimp only [CStore.getNode, CStore.getAppFnI]
              generalize hg'' : ExprC.getAppFn cb = g'' at hwfn'' hfn'' ⊢
              cases g'' with
              | const cnᵢ cus =>
                rw [show (Expr.getAppFn cb) = Expr.const cnᵢ cus
                  from hfn''.symm]
                dsimp only
                refine SimC.withStore ?_
                have hres : RelCL (ExprC.getAppArgs res)
                    (Expr.getAppArgs res) := ExprC.getAppArgs_spec hwres
                simp only [CStore.getAppArgsI]
                refine SimC.bind (defEqListC_sim ih hs₅
                  (hres.drop rl.ctorParams)
                  ((hargs.take mI).drop rP)
                  (fun x hx => hresW.getAppArgs x
                    (List.mem_of_mem_drop hx))
                  (fun x hx => hw.getAppArgs x
                    (List.mem_of_mem_take (List.mem_of_mem_drop hx))))
                  (fun s₆ r₄ r₄' hs₆ hPr₄ => ?_)
                obtain rfl : r₄ = r₄' := hPr₄
                cases r₄ with
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  exact SimC.pure hs₆ trivial
                | true =>
                  simp only [↓reduceIte]
                  refine SimC.bind_left (ruleRhsAtM_eff hs₆ hfc hrule)
                    (fun s₇ rhs hs₇ hQrhs => ?_)
                  refine SimC.bind_left (mkAppNM_eff hs₇ hQrhs
                    ((hargs.take rP).append (hmargs.drop rl.ctorParams)))
                    (fun s₈ red hs₈ hQred => ?_)
                  refine SimC.pure hs₈ ⟨hQred, ?_⟩
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
              | bvar k =>
                rw [show (Expr.getAppFn cb) = Expr.bvar k from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | sort u =>
                rw [show (Expr.getAppFn cb) = Expr.sort u from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | lit l =>
                rw [show (Expr.getAppFn cb) = Expr.lit l from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | fvar ix nmᵢ t =>
                rw [show (Expr.getAppFn cb)
                  = Expr.fvar ix nmᵢ t from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | app f' a' =>
                rw [show (Expr.getAppFn cb)
                  = Expr.app f' a' from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | lam nmᵢ t b' m =>
                rw [show (Expr.getAppFn cb)
                  = Expr.lam nmᵢ t b' m from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | forallE nmᵢ t b' m =>
                rw [show (Expr.getAppFn cb)
                  = Expr.forallE nmᵢ t b' m
                  from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | letE nmᵢ t v b' =>
                rw [show (Expr.getAppFn cb)
                  = Expr.letE nmᵢ t v b'
                  from hfn''.symm]
                exact SimC.pure hs₅ trivial
              | proj s'ᵢ j' e' =>
                rw [show (Expr.getAppFn cb)
                  = Expr.proj s'ᵢ j' e' from hfn''.symm]
                exact SimC.pure hs₅ trivial

private theorem iotaRec_unfold (env : Env) (d : Nat) (e : Expr) :
    iotaRec mode (fueledFns mode env) env d e =
    (match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv mI rP rules) =>
        if e.getAppArgs.length = mI + 1 ∧
            us.length = cv.levelParams.length then
          (fueledFns mode env).whnf d (e.getAppArgs.getD mI (.bvar 0)) >>=
            fun major₀ =>
          litMajorToCtor (fueledFns mode env) env d major₀ >>= fun major₁ =>
          majorToCtor mode (fueledFns mode env) env d c rules major₁ >>=
            fun major =>
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
                          cvj.levelParams e.getAppArgs rP).1) >>=
                      fun okl =>
                    if okl then
                      defEqList (fueledFns mode env) env d
                          (major.getAppArgs.take rl.ctorParams)
                          (recFireComparands rl cv.levelParams us
                            cvj.levelParams e.getAppArgs rP).2 >>=
                        fun r₁ =>
                      if r₁ then
                        iotaCerts (fueledFns mode env) env d
                            (cv.type.instantiateLevelParams
                              cv.levelParams us)
                            (e.getAppArgs.take mI ++ [major]) >>=
                          fun r₂ =>
                        if r₂ then
                          iotaCerts (fueledFns mode env) env d
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
                                defEqList (fueledFns mode env) env d
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

/-- Port of `iotaRecI_sim`. -/
theorem iotaRecC_sim (ih : SSimC mode env f) (henv : EnvWF env)
    {d : Nat} {i : ExprC} {ex : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hden : RelC i ex) (hw : Expr.WScoped d ex) :
    SimC mode env s₀ (RelOC d)
      (iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i)
      (iotaRec mode (fueledFns mode env) env d ex) := by
  unfold iotaRecI
  rw [iotaRec_unfold]
  refine SimC.withStore ?_
  obtain ⟨hwc, rfl⟩ := hden
  have hden : RelC i i := ⟨hwc, rfl⟩
  have hargs : RelCL (ExprC.getAppArgs i) (Expr.getAppArgs i) :=
    ExprC.getAppArgs_spec hwc
  obtain ⟨hwfn, hfn⟩ := ExprC.getAppFn_spec hwc
  dsimp only [CStore.getNode, CStore.getAppFnI]
  generalize hg : ExprC.getAppFn i = g at hwfn hfn ⊢
  cases g with
  | const c us =>
    rw [show (Expr.getAppFn i) = Expr.const c us from hfn.symm]
    dsimp only
    refine SimC.bind_left (readbackNM_eff hs c) (fun s₀c cw hs hcw => ?_)
    subst cw
    rw [mkFEnv_find?]
    cases hfc : env.find? c with
    | none => exact SimC.pure hs trivial
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only
        refine SimC.withStore ?_
        simp only [CStore.getAppArgsI, hargs.length]
        by_cases hlen : (Expr.getAppArgs i).length = mI + 1 ∧
            us.length = cv.levelParams.length
        · rw [if_pos hlen, if_pos hlen]
          refine SimC.bind_left
            (internI_eff hs (n := ExprView.bvar 0) trivial)
            (fun s₁ bvar0 hs₁ hQ0 => ?_)
          have hQ0' : RelC bvar0 (Expr.bvar 0) := hQ0
          refine SimC.bind (ih.whnf hs₁ (RelCL.getD hQ0' mI hargs)
            (wscoped_getD hw.getAppArgs _))
            (fun s₂ major₀ major₀x hs₂ hP₀ => ?_)
          obtain ⟨hm₀d, hwm₀⟩ := hP₀
          refine SimC.bind (litMajorToCtorC_sim ih hs₂ hm₀d hwm₀)
            (fun s₃ major₁ major₁x hs₃ hP₁ => ?_)
          obtain ⟨hm₁d, hwm₁⟩ := hP₁
          refine SimC.bind (majorToCtorC_sim ih henv hs₃ hm₁d hwm₁)
            (fun s₄ major majorx hs₄ hP₂ => ?_)
          obtain ⟨⟨hwmajc, rfl⟩, hmaj⟩ := hP₂
          have hmargs : RelCL (ExprC.getAppArgs major)
              (Expr.getAppArgs major) := ExprC.getAppArgs_spec hwmajc
          refine SimC.withStore ?_
          obtain ⟨hwfn', hfn'⟩ := ExprC.getAppFn_spec hwmajc
          generalize hg' : ExprC.getAppFn major = g' at hwfn' hfn' ⊢
          cases g' with
          | const cj usj =>
            rw [show (Expr.getAppFn major) = Expr.const cj usj
              from hfn'.symm]
            dsimp only
            refine SimC.bind_left (readbackNM_eff hs₄ cj)
              (fun s₄c cjw hs₄ hcjw => ?_)
            subst cjw
            rw [mkFEnv_find?]
            cases hfj : env.find? cj with
            | none => exact SimC.pure hs₄ trivial
            | some cij =>
              cases cij with
              | ctorInfo cvj cnP cnF =>
                dsimp only
                cases hrule : rules.find? (fun r' => r'.ctor == cj) with
                | none => exact SimC.pure hs₄ trivial
                | some rl =>
                  dsimp only
                  refine SimC.withStore ?_
                  simp only [hmargs.length]
                  by_cases hmlen : (Expr.getAppArgs major).length =
                      rl.ctorParams + rl.nfields
                  · rw [if_pos hmlen, if_pos hmlen]
                    by_cases hin : rl.fire = RecRuleFire.inert
                    · rw [if_pos hin, if_pos hin]
                      exact SimC.throw
                    · rw [if_neg hin, if_neg hin]
                      by_cases hpins : (cv.type.stripPis (mI + 1)).isSome
                          = true ∧
                          (cvj.type.stripPis
                            (rl.ctorParams + rl.nfields)).isSome = true
                      · rw [if_pos hpins, if_pos hpins]
                        -- both isSome pins hold; walk the certificates
                        have hargsW : ∀ a ∈ (Expr.getAppArgs i),
                            Expr.WScoped d a := hw.getAppArgs
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
                          cv.levelParams us cvj.levelParams
                          (Expr.getAppArgs i) rP hargsW hpinsW
                        cases hfire : rl.fire with
                        | inert => simp [hfire] at *
                        | plain =>
                          simp only [recFireComparands, hfire] at hcmpW ⊢
                          refine SimC.bind_left (substLevelTreesM_eff hs₄
                            cv.levelParams us
                            (cvj.levelParams.map Level.param))
                            (fun s₄l cmpLvls hs₄l hQl => ?_)
                          rw [List.map_map] at hQl
                          subst cmpLvls
                          refine SimC.bind_pure_left ?_
                          refine SimC.bind_left (isEquivListLM_eff hs₄l)
                            (fun s₄o oL hs₄o hoL => ?_)
                          subst oL
                          refine SimC.bind (SimC.liftFueled _ _ hs₄o)
                            (fun s₆ okl okl' hs₆ hPok => ?_)
                          obtain rfl : okl = okl' := hPok
                          cases okl with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₆ trivial
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (defEqListC_sim ih hs₆
                              (hmargs.take rl.ctorParams)
                              (hargs.take rl.ctorParams)
                              (fun x hx => hmaj.getAppArgs x
                                (List.mem_of_mem_take hx))
                              (fun x hx => hargsW x
                                (List.mem_of_mem_take hx)))
                              (fun s₇ r₁ r₁' hs₇ hPr₁ => ?_)
                            obtain rfl : r₁ = r₁' := hPr₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₇ trivial
                            | true =>
                              simp only [↓reduceIte]
                              exact iotaRec_certs_tail ih henv hs₇ hden hw
                                hfc hfj hrule ⟨hwmajc, rfl⟩ hmaj hargs
                                hmargs
                        | nested lvls pins =>
                          simp only [recFireComparands, hfire] at hcmpW ⊢
                          refine SimC.bind_left (substLevelTreesM_eff hs₄
                            cv.levelParams us lvls)
                            (fun s₄l cmpLvls hs₄l hQl => ?_)
                          subst cmpLvls
                          refine SimC.bind_left (pinArgsC_eff
                            cv.levelParams us pins hs₄l (rP - 1)
                            (hargs.take rP))
                            (fun s₅ cmpArgs hs₅ hQc => ?_)
                          refine SimC.bind_left (isEquivListLM_eff hs₅)
                            (fun s₄o oL hs₄o hoL => ?_)
                          subst oL
                          refine SimC.bind (SimC.liftFueled _ _ hs₄o)
                            (fun s₆ okl okl' hs₆ hPok => ?_)
                          obtain rfl : okl = okl' := hPok
                          cases okl with
                          | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            exact SimC.pure hs₆ trivial
                          | true =>
                            simp only [↓reduceIte]
                            refine SimC.bind (defEqListC_sim ih hs₆
                              (hmargs.take rl.ctorParams) hQc
                              (fun x hx => hmaj.getAppArgs x
                                (List.mem_of_mem_take hx))
                              hcmpW)
                              (fun s₇ r₁ r₁' hs₇ hPr₁ => ?_)
                            obtain rfl : r₁ = r₁' := hPr₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact SimC.pure hs₇ trivial
                            | true =>
                              simp only [↓reduceIte]
                              exact iotaRec_certs_tail ih henv hs₇ hden hw
                                hfc hfj hrule ⟨hwmajc, rfl⟩ hmaj hargs
                                hmargs
                      · rw [if_neg hpins, if_neg hpins]
                        exact SimC.pure hs₄ trivial
                  · rw [if_neg hmlen, if_neg hmlen]
                    exact SimC.pure hs₄ trivial
              | axiomInfo cv' => exact SimC.pure hs₄ trivial
              | defnInfo cv' v h => exact SimC.pure hs₄ trivial
              | thmInfo cv' v => exact SimC.pure hs₄ trivial
              | indInfo cv' caps => exact SimC.pure hs₄ trivial
              | recInfo cv' mI' rP' rules' => exact SimC.pure hs₄ trivial
              | projInfo entry => exact SimC.pure hs₄ trivial
          | bvar k =>
            rw [show (Expr.getAppFn major) = Expr.bvar k from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | sort u =>
            rw [show (Expr.getAppFn major) = Expr.sort u from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | lit l =>
            rw [show (Expr.getAppFn major) = Expr.lit l from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | fvar ix nm t =>
            rw [show (Expr.getAppFn major)
              = Expr.fvar ix nm t from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | app f' a' =>
            rw [show (Expr.getAppFn major)
              = Expr.app f' a' from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | lam nm t b' m =>
            rw [show (Expr.getAppFn major)
              = Expr.lam nm t b' m from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | forallE nm t b' m =>
            rw [show (Expr.getAppFn major)
              = Expr.forallE nm t b' m from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | letE nm t v b' =>
            rw [show (Expr.getAppFn major)
              = Expr.letE nm t v b'
              from hfn'.symm]
            exact SimC.pure hs₄ trivial
          | proj sn jx e' =>
            rw [show (Expr.getAppFn major)
              = Expr.proj sn jx e' from hfn'.symm]
            exact SimC.pure hs₄ trivial
        · rw [if_neg hlen, if_neg hlen]
          exact SimC.pure hs trivial
      | axiomInfo cv => exact SimC.pure hs trivial
      | defnInfo cv v h => exact SimC.pure hs trivial
      | thmInfo cv v => exact SimC.pure hs trivial
      | indInfo cv caps => exact SimC.pure hs trivial
      | ctorInfo cv nP nF => exact SimC.pure hs trivial
      | projInfo entry => exact SimC.pure hs trivial
  | bvar k =>
    rw [show (Expr.getAppFn i) = Expr.bvar k from hfn.symm]
    exact SimC.pure hs trivial
  | sort u =>
    rw [show (Expr.getAppFn i) = Expr.sort u from hfn.symm]
    exact SimC.pure hs trivial
  | lit l =>
    rw [show (Expr.getAppFn i) = Expr.lit l from hfn.symm]
    exact SimC.pure hs trivial
  | fvar ix nmᵢ t =>
    rw [show (Expr.getAppFn i) = Expr.fvar ix nmᵢ t
      from hfn.symm]
    exact SimC.pure hs trivial
  | app f' a' =>
    rw [show (Expr.getAppFn i) = Expr.app f' a'
      from hfn.symm]
    exact SimC.pure hs trivial
  | lam nmᵢ t b' m =>
    rw [show (Expr.getAppFn i) = Expr.lam nmᵢ t b' m
      from hfn.symm]
    exact SimC.pure hs trivial
  | forallE nmᵢ t b' m =>
    rw [show (Expr.getAppFn i)
      = Expr.forallE nmᵢ t b' m from hfn.symm]
    exact SimC.pure hs trivial
  | letE nmᵢ t v b' =>
    rw [show (Expr.getAppFn i)
      = Expr.letE nmᵢ t v b' from hfn.symm]
    exact SimC.pure hs trivial
  | proj s'ᵢ j' e' =>
    rw [show (Expr.getAppFn i) = Expr.proj s'ᵢ j' e'
      from hfn.symm]
    exact SimC.pure hs trivial

end Walks2

end Setlec.Cached
