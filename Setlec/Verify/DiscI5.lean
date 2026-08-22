import Setlec.Verify.DiscI4

/-!
# Interned body walks, part 5: definitional equality

Simulation walk for `defeqBodyI`, mirroring `defeqBody_disc`
(`Setlec/Verify/Disc.lean`).  The syntactic fast paths compare arena
indices; canonicity of the store (`denote_inj`) identifies the verdict
with the spec's structural comparison.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Setlec

open EStore Expr

section Walks

variable {env : Env} {f : Nat}

/-- Index equality decides expression equality on canonical stores. -/
private theorem beq_transfer {st : EStore} (hwf : st.WF) {i j : EIdx}
    {a b : Expr} (ha : st.denote i = some a) (hb : st.denote j = some b) :
    (i == j) = (a == b) := by
  by_cases hij : i = j
  · subst hij
    rw [ha] at hb
    obtain rfl : a = b := Option.some.inj hb
    rw [beq_self_eq_true, beq_self_eq_true]
  · have hab : ¬ a = b := by
      rintro rfl
      exact hij (denote_inj hwf ha hb)
    rw [beq_eq_false_iff_ne.mpr hij, beq_eq_false_iff_ne.mpr hab]

/-- The one-sided-λ (right) stuck arm. -/
private theorem defeqI_etaR_arm (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₂ b₂ : EIdx} {a'x ty₂x body₂x : Expr} {nm₂ : Name}
    {m₂ : BinderMeta} {s₀ : IState} (hs : ISOK env s₀)
    (haS : s₀.store.denote a' = some a'x)
    (hty₂ : s₀.store.denote t₂ = some ty₂x)
    (hbody₂ : s₀.store.denote b₂ = some body₂x)
    (hbS : s₀.store.denote b' = some (.lam nm₂ ty₂x body₂x m₂))
    (hwa' : WScoped d a'x)
    (hwb' : WScoped d (Expr.lam nm₂ ty₂x body₂x m₂)) :
    SimAt env s₀ RelV
      (etaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d nm₂ t₂ b₂ m₂
          a' >>= fun r =>
        if r then pure true
        else stuckIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert (fueledFns env) env d nm₂ ty₂x body₂x m₂ a'x >>= fun r =>
        if r then pure true
        else stuckIrrel (fueledFns env) env d a'x
          (.lam nm₂ ty₂x body₂x m₂)) := by
  have h2 : WScoped d ty₂x ∧ WScoped d body₂x := by
    simpa only [WScoped] using hwb'
  refine SimAt.bind (etaCertI_sim ih hty₂ hbody₂ haS h2.1 h2.2 hwa'
    (s₀ := s₀) (hs := hs)) (fun s₁ r r' hs₁ hext₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelI_sim ih henv hs₁ (denote_mono hext₁ haS)
      (denote_mono hext₁ hbS) hwa' hwb'

/-- The one-sided-λ (left) stuck arm. -/
private theorem defeqI_etaL_arm (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {a' b' t₁ b₁ : EIdx} {b'x ty₁x body₁x : Expr} {nm₁ : Name}
    {m₁ : BinderMeta} {s₀ : IState} (hs : ISOK env s₀)
    (haS : s₀.store.denote a' = some (.lam nm₁ ty₁x body₁x m₁))
    (hty₁ : s₀.store.denote t₁ = some ty₁x)
    (hbody₁ : s₀.store.denote b₁ = some body₁x)
    (hbS : s₀.store.denote b' = some b'x)
    (hwa' : WScoped d (Expr.lam nm₁ ty₁x body₁x m₁))
    (hwb' : WScoped d b'x) :
    SimAt env s₀ RelV
      (etaCertI (coreKnotI (mkFEnv env) f) (mkFEnv env) d nm₁ t₁ b₁ m₁
          b' >>= fun r =>
        if r then pure true
        else stuckIrrelI (coreKnotI (mkFEnv env) f) (mkFEnv env) d a' b')
      (etaCert (fueledFns env) env d nm₁ ty₁x body₁x m₁ b'x >>= fun r =>
        if r then pure true
        else stuckIrrel (fueledFns env) env d
          (.lam nm₁ ty₁x body₁x m₁) b'x) := by
  have h1 : WScoped d ty₁x ∧ WScoped d body₁x := by
    simpa only [WScoped] using hwa'
  refine SimAt.bind (etaCertI_sim ih hty₁ hbody₁ hbS h1.1 h1.2 hwb'
    (s₀ := s₀) (hs := hs)) (fun s₁ r r' hs₁ hext₁ hP => ?_)
  obtain rfl : r = r' := hP
  cases r with
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs₁ rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact stuckIrrelI_sim ih henv hs₁ (denote_mono hext₁ haS)
      (denote_mono hext₁ hbS) hwa' hwb'

set_option maxHeartbeats 12000000 in
theorem defeqBodyI_sim (ih : SSimI env f) (henv : EnvWF env)
    {d : Nat} {i j : EIdx} {a b : Expr} {s₀ : IState} (hs : ISOK env s₀)
    (hdena : s₀.store.denote i = some a)
    (hdenb : s₀.store.denote j = some b)
    (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV
      (defeqBodyI (coreKnotI (mkFEnv env) f) (mkFEnv env) d i j)
      (defeqBody (fueledFns env) env d a b) := by
  unfold defeqBodyI
  unfold defeqBody
  rw [beq_transfer hs.wf hdena hdenb]
  by_cases hab : (a == b) = true
  · rw [if_pos hab, if_pos hab]
    exact SimAt.pure hs rfl
  · rw [if_neg hab, if_neg hab]
    refine SimAt.bind (ih.whnfCore hs hdena hwa)
      (fun s₁ a' a'x hs₁ hext₁ hPa => ?_)
    obtain ⟨ha'd, hwa'⟩ := hPa
    refine SimAt.bind (ih.whnfCore hs₁ (denote_mono hext₁ hdenb) hwb)
      (fun s₂ b' b'x hs₂ hext₂ hPb => ?_)
    obtain ⟨hb'd, hwb'⟩ := hPb
    have ha'd₂ := denote_mono hext₂ ha'd
    rw [beq_transfer hs₂.wf ha'd₂ hb'd]
    by_cases hab' : (a'x == b'x) = true
    · rw [if_pos hab', if_pos hab']
      exact SimAt.pure hs₂ rfl
    · rw [if_neg hab', if_neg hab']
      refine SimAt.bind (reduceNatI_sim ih hs₂ ha'd₂ hwa')
        (fun s₃ o₁ o₁x hs₃ hext₃ hPo₁ => ?_)
      cases o₁ with
      | some a₂ =>
        cases o₁x with
        | none => exact absurd hPo₁ (by simp [RelO])
        | some a₂x =>
          obtain ⟨ha₂d, hwa₂⟩ := hPo₁
          exact ih.defeq hs₃ ha₂d (denote_mono hext₃ hb'd) hwa₂ hwb'
      | none =>
        cases o₁x with
        | some a₂x => exact absurd hPo₁ (by simp [RelO])
        | none =>
          refine SimAt.bind (reduceNatI_sim ih hs₃
            (denote_mono hext₃ hb'd) hwb')
            (fun s₄ o₂ o₂x hs₄ hext₄ hPo₂ => ?_)
          cases o₂ with
          | some b₂ =>
            cases o₂x with
            | none => exact absurd hPo₂ (by simp [RelO])
            | some b₂x =>
              obtain ⟨hb₂d, hwb₂⟩ := hPo₂
              exact ih.defeq hs₄
                (denote_mono ((hext₃.trans hext₄)) ha'd₂) hb₂d hwa' hwb₂
          | none =>
            cases o₂x with
            | some b₂x => exact absurd hPo₂ (by simp [RelO])
            | none =>
              have ha'd₄ := denote_mono (hext₃.trans hext₄) ha'd₂
              have hb'd₄ := denote_mono hext₄ (denote_mono hext₃ hb'd)
              refine SimAt.bind_left (unfoldDefinitionI_eff hs₄ ha'd₄)
                (fun s₅ ua hs₅ hext₅ hQa => ?_)
              refine SimAt.bind_left (unfoldDefinitionI_eff hs₅
                (denote_mono hext₅ hb'd₄))
                (fun s₆ ub hs₆ hext₆ hQb => ?_)
              have haS := denote_mono (hext₅.trans hext₆) ha'd₄
              have hbS := denote_mono (hext₅.trans hext₆) hb'd₄
              have hQa' := hQa.mono hext₆
              cases hua : unfoldDefinition env a'x with
              | some a₂x =>
                rw [hua] at hQa'
                cases ua with
                | none => exact absurd hQa' (by simp [OptDen])
                | some a₂ =>
                  cases hub : unfoldDefinition env b'x with
                  | none =>
                    rw [hub] at hQb
                    cases ub with
                    | some b₂ => exact absurd hQb (by simp [OptDen])
                    | none =>
                      exact ih.defeq hs₆ hQa' hbS
                        (unfoldDefinition_WScoped henv hua hwa') hwb'
                  | some b₂x =>
                    rw [hub] at hQb
                    cases ub with
                    | none => exact absurd hQb (by simp [OptDen])
                    | some b₂ =>
                      have hwa₂ := unfoldDefinition_WScoped henv hua hwa'
                      have hwb₂ := unfoldDefinition_WScoped henv hub hwb'
                      dsimp only
                      refine SimAt.withStore ?_
                      refine SimAt.withStore ?_
                      rw [headHintI_spec hs₆.wf haS,
                        headHintI_spec hs₆.wf hbS]
                      by_cases hlt₁ : ReducibilityHint.lt
                          (headHint env b'x) (headHint env a'x) = true
                      · rw [if_pos hlt₁, if_pos hlt₁]
                        exact ih.defeq hs₆ hQa' hbS hwa₂ hwb'
                      · rw [if_neg hlt₁, if_neg hlt₁]
                        by_cases hlt₂ : ReducibilityHint.lt
                            (headHint env a'x) (headHint env b'x) = true
                        · rw [if_pos hlt₂, if_pos hlt₂]
                          exact ih.defeq hs₆ haS hQb hwa' hwb₂
                        · rw [if_neg hlt₂, if_neg hlt₂]
                          refine SimAt.withStore ?_
                          rw [sameConstHeadsI_spec hs₆.wf haS hbS]
                          by_cases hsr : (ReducibilityHint.sameRegular
                              (headHint env a'x) (headHint env b'x) &&
                              sameConstHeads a'x b'x) = true
                          · rw [if_pos hsr, if_pos hsr]
                            refine SimAt.bind (defeqSpineI_sim ih hs₆
                              haS hbS hwa' hwb')
                              (fun s₇ sp sp' hs₇ hext₇ hPsp => ?_)
                            obtain rfl : sp = sp' := hPsp
                            cases sp with
                            | true =>
                              simp only [↓reduceIte]
                              exact SimAt.pure hs₇ rfl
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              exact ih.defeq hs₇
                                (denote_mono hext₇ hQa')
                                (denote_mono hext₇ hQb) hwa₂ hwb₂
                          · rw [if_neg hsr, if_neg hsr]
                            exact ih.defeq hs₆ hQa' hQb hwa₂ hwb₂
              | none =>
                rw [hua] at hQa'
                cases ua with
                | some a₂ => exact absurd hQa' (by simp [OptDen])
                | none =>
                  cases hub : unfoldDefinition env b'x with
                  | some b₂x =>
                    rw [hub] at hQb
                    cases ub with
                    | none => exact absurd hQb (by simp [OptDen])
                    | some b₂ =>
                      exact ih.defeq hs₆ haS hQb hwa'
                        (unfoldDefinition_WScoped henv hub hwb')
                  | none =>
                    rw [hub] at hQb
                    cases ub with
                      | some b₂ => exact absurd hQb (by simp [OptDen])
                      | none =>
                        obtain ⟨na, hna, hca, hda⟩ := denote_some_inv haS
                        obtain ⟨nb, hnb, hcb, hdb⟩ := denote_some_inv hbS
                        try dsimp only
                        refine SimAt.view ?_
                        rw [hna]
                        try dsimp only
                        refine SimAt.view ?_
                        rw [hnb]
                        cases na with
                        | sort u₁ =>
                          cases hda
                          cases nb with
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact SimAt.liftFueled _ _ hs₆
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | lit l₁ =>
                          cases hda
                          cases l₁ with
                          | natVal n₁ =>
                            cases nb with
                            | lit l₂ =>
                              cases hdb
                              try dsimp only
                              exact SimAt.pure hs₆ rfl
                            | const c₂ us₂ =>
                              cases hdb
                              try dsimp only
                              by_cases hz : c₂ = natZeroName ∧ us₂ = []
                              try dsimp only
                              · rw [if_pos hz, if_pos hz]
                                try dsimp only
                                exact SimAt.pure hs₆ rfl
                              try dsimp only
                              · rw [if_neg hz, if_neg hz]
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | app f₂ a₂ =>
                              rw [denoteNode, Option.bind_eq_some_iff] at hdb
                              obtain ⟨xf₂, hf₂, hdb⟩ := hdb
                              rw [Option.map_eq_some_iff] at hdb
                              obtain ⟨xa₂, ha₂, hdb⟩ := hdb
                              subst hdb
                              cases n₁ with
                              | zero =>
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | succ k =>
                                try dsimp only
                                refine SimAt.view ?_
                                obtain ⟨nf, hnf, hcf, hdf⟩ := denote_some_inv hf₂
                                rw [hnf]
                                cases nf with
                                | const cf usf =>
                                  cases hdf
                                  cases usf with
                                  | cons u us' => exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                  | nil =>
                                    dsimp only
                                    try dsimp only
                                    by_cases hsc : cf = natSuccName
                                    try dsimp only
                                    · rw [if_pos hsc, if_pos hsc]
                                      have hxw : WScoped d xa₂ := by
                                        simp only [WScoped] at hwb'
                                        try dsimp only
                                        exact hwb'.2
                                      try dsimp only
                                      refine SimAt.bind_left (internI_eff hs₆
                                        (x := .lit (.natVal k)) rfl)
                                        (fun s₇ kl hs₇ hext₇ hQk => ?_)
                                      try dsimp only
                                      exact ih.defeq hs₇ hQk (denote_mono hext₇ ha₂)
                                        (by simp [WScoped]) hxw
                                    try dsimp only
                                    · rw [if_neg hsc, if_neg hsc]
                                      try dsimp only
                                      exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | bvar kf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | sort uf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | lit lf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | fvar if₁ nmf tf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | app ff af =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | lam nmf tf bf mf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | forallE nmf tf bf mf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | letE nmf tf vf bf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | proj sf jf ef =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | bvar k₂ =>
                              cases hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | sort u₂ =>
                              cases hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | fvar i₂ nm₂ t₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | lam nm₂ t₂ b₂ m₂ =>
                              rw [denoteNode, Option.bind_eq_some_iff] at hdb
                              obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                              rw [Option.bind_eq_some_iff] at hdb
                              obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                              rw [Option.map_eq_some_iff] at hdb
                              obtain ⟨bm, hbmDen, hdb⟩ := hdb
                              subst hdb
                              try dsimp only
                              exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                            | forallE nm₂ t₂ b₂ m₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | letE nm₂ t₂ v₂ b₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | proj s₂' j₂ e₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | strVal str =>
                            cases nb with
                            | lit l₂ =>
                              cases hdb
                              try dsimp only
                              exact SimAt.pure hs₆ rfl
                            | app f₂ a₂ =>
                              rw [denoteNode, Option.bind_eq_some_iff] at hdb
                              obtain ⟨xf₂, hf₂, hdb⟩ := hdb
                              rw [Option.map_eq_some_iff] at hdb
                              obtain ⟨xa₂, ha₂, hdb⟩ := hdb
                              subst hdb
                              try dsimp only
                              refine SimAt.view ?_
                              obtain ⟨nf, hnf, hcf, hdf⟩ := denote_some_inv hf₂
                              rw [hnf]
                              cases nf with
                              | const cf usf =>
                                cases hdf
                                rw [strLitSupportedF_eq]
                                try dsimp only
                                by_cases hsc : cf = stringOfListName ∧ usf = [] ∧
                                    strLitSupported env = true
                                try dsimp only
                                · rw [if_pos hsc, if_pos hsc]
                                  try dsimp only
                                  refine SimAt.bind_left (internExprM_eff hs₆
                                    (strLitToConstructor str))
                                    (fun s₇ sc hs₇ hext₇ hQs => ?_)
                                  try dsimp only
                                  exact ih.defeq hs₇ hQs (denote_mono hext₇ hbS)
                                    (strLitToConstructor_WScoped str d) hwb'
                                try dsimp only
                                · rw [if_neg hsc, if_neg hsc]
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | bvar kf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | sort uf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | lit lf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | fvar if₁ nmf tf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | app ff af =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | lam nmf tf bf mf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | forallE nmf tf bf mf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | letE nmf tf vf bf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | proj sf jf ef =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | bvar k₂ =>
                              cases hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | sort u₂ =>
                              cases hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | const c₂ us₂ =>
                              cases hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | fvar i₂ nm₂ t₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | lam nm₂ t₂ b₂ m₂ =>
                              rw [denoteNode, Option.bind_eq_some_iff] at hdb
                              obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                              rw [Option.bind_eq_some_iff] at hdb
                              obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                              rw [Option.map_eq_some_iff] at hdb
                              obtain ⟨bm, hbmDen, hdb⟩ := hdb
                              subst hdb
                              try dsimp only
                              exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                            | forallE nm₂ t₂ b₂ m₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | letE nm₂ t₂ v₂ b₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | proj s₂' j₂ e₂ =>
                              invert_node hdb
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | fvar i₁ nm₁ t₁ =>
                          rw [denoteNode, Option.map_eq_some_iff] at hda
                          obtain ⟨ty₁x, hty₁, hda⟩ := hda
                          subst hda
                          cases nb with
                          | fvar i₂ nm₂ t₂ =>
                            rw [denoteNode, Option.map_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            by_cases hij : (i₁ == i₂) = true
                            try dsimp only
                            · rw [if_pos hij, if_pos hij]
                              try dsimp only
                              exact SimAt.pure hs₆ rfl
                            try dsimp only
                            · rw [if_neg hij, if_neg hij]
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | const c₁ us₁ =>
                          cases hda
                          cases nb with
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            by_cases hcc : c₁ = c₂
                            try dsimp only
                            · rw [if_pos hcc, if_pos hcc]
                              try dsimp only
                              refine SimAt.bind (SimAt.liftFueled _ _ hs₆)
                                (fun s₇ ok ok' hs₇ hext₇ hPok => ?_)
                              obtain rfl : ok = ok' := hPok
                              cases ok with
                              | true =>
                                simp only [↓reduceIte]
                                try dsimp only
                                exact SimAt.pure hs₇ rfl
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₇ (denote_mono hext₇ haS)
                                  (denote_mono hext₇ hbS) hwa' hwb'
                            try dsimp only
                            · rw [if_neg hcc, if_neg hcc]
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            cases l₂ with
                            | natVal n₂ =>
                              try dsimp only
                              by_cases hz : c₁ = natZeroName ∧ us₁ = []
                              try dsimp only
                              · rw [if_pos hz, if_pos hz]
                                try dsimp only
                                exact SimAt.pure hs₆ rfl
                              try dsimp only
                              · rw [if_neg hz, if_neg hz]
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | strVal str =>
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | forallE nm₁ t₁ b₁ m₁ =>
                          rw [denoteNode, Option.bind_eq_some_iff] at hda
                          obtain ⟨ty₁x, hty₁, hda⟩ := hda
                          rw [Option.bind_eq_some_iff] at hda
                          obtain ⟨body₁x, hbody₁, hda⟩ := hda
                          rw [Option.map_eq_some_iff] at hda
                          obtain ⟨bm, hbmDen, hda⟩ := hda
                          subst hda
                          have h1 : WScoped d ty₁x ∧ WScoped d body₁x := by
                            simpa only [WScoped] using hwa'
                          cases nb with
                          | forallE nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            have h2 : WScoped d ty₂x ∧ WScoped d body₂x := by
                              simpa only [WScoped] using hwb'
                            try dsimp only
                            refine SimAt.bind (ih.defeq hs₆ hty₁ hty₂ h1.1 h2.1)
                              (fun s₇ r₁ r₁' hs₇ hext₇ hP₁ => ?_)
                            obtain rfl : r₁ = r₁' := hP₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              try dsimp only
                              exact SimAt.pure hs₇ rfl
                            | true =>
                              simp only [↓reduceIte]
                              have hfv₁ : denoteNode s₇.store.denote (.fvar d nm₁ t₁)
                                  = some (.fvar d nm₁ ty₁x) := by
                                rw [denoteNode, denote_mono hext₇ hty₁]; rfl
                              try dsimp only
                              refine SimAt.bind_left (internI_eff hs₇ hfv₁)
                                (fun s₈ fv₁ hs₈ hext₈ hQf₁ => ?_)
                              try dsimp only
                              refine SimAt.bind_left (inst1M_eff hs₈
                                (denote_mono (hext₇.trans hext₈) hbody₁) hQf₁)
                                (fun s₉ ob₁ hs₉ hext₉ hQo₁ => ?_)
                              have hfv₂ : denoteNode s₉.store.denote (.fvar d nm₂ t₂)
                                  = some (.fvar d nm₂ ty₂x) := by
                                rw [denoteNode, denote_mono
                                  ((hext₇.trans hext₈).trans hext₉) hty₂]
                                rfl
                              try dsimp only
                              refine SimAt.bind_left (internI_eff hs₉ hfv₂)
                                (fun s₁₀ fv₂ hs₁₀ hext₁₀ hQf₂ => ?_)
                              try dsimp only
                              refine SimAt.bind_left (inst1M_eff hs₁₀
                                (denote_mono (((hext₇.trans hext₈).trans
                                  hext₉).trans hext₁₀) hbody₂) hQf₂)
                                (fun s₁₁ ob₂ hs₁₁ hext₁₁ hQo₂ => ?_)
                              try dsimp only
                              refine SimAt.bind (ih.defeq hs₁₁
                                (denote_mono (hext₁₀.trans hext₁₁) hQo₁) hQo₂
                                (WScoped.instantiate1 h1.1 0 h1.2)
                                (WScoped.instantiate1 h2.1 0 h2.2))
                                (fun s₁₂ r₂ r₂' hs₁₂ hext₁₂ hP₂ => ?_)
                              obtain rfl : r₂ = r₂' := hP₂
                              cases r₂ with
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                try dsimp only
                                exact SimAt.pure hs₁₂ rfl
                              | true =>
                                simp only [↓reduceIte]
                                obtain ⟨bi₁, cod₁⟩ := m₁
                                obtain ⟨bi₂, cod₂⟩ := m₂
                                dsimp only
                                cases cod₁ with
                                | none => cases cod₂ <;> exact SimAt.throw
                                | some v₁ =>
                                  cases cod₂ with
                                  | none => exact SimAt.throw
                                  | some v₂ =>
                                    dsimp only
                                    try dsimp only
                                    exact SimAt.liftFueled _ _ hs₁₂
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | lam nm₁ t₁ b₁ m₁ =>
                          rw [denoteNode, Option.bind_eq_some_iff] at hda
                          obtain ⟨ty₁x, hty₁, hda⟩ := hda
                          rw [Option.bind_eq_some_iff] at hda
                          obtain ⟨body₁x, hbody₁, hda⟩ := hda
                          rw [Option.map_eq_some_iff] at hda
                          obtain ⟨bm, hbmDen, hda⟩ := hda
                          subst hda
                          have h1 : WScoped d ty₁x ∧ WScoped d body₁x := by
                            simpa only [WScoped] using hwa'
                          cases nb with
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            have h2 : WScoped d ty₂x ∧ WScoped d body₂x := by
                              simpa only [WScoped] using hwb'
                            try dsimp only
                            refine SimAt.bind (ih.defeq hs₆ hty₁ hty₂ h1.1 h2.1)
                              (fun s₇ r₁ r₁' hs₇ hext₇ hP₁ => ?_)
                            obtain rfl : r₁ = r₁' := hP₁
                            cases r₁ with
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              try dsimp only
                              exact SimAt.pure hs₇ rfl
                            | true =>
                              simp only [↓reduceIte]
                              have hfv₁ : denoteNode s₇.store.denote (.fvar d nm₁ t₁)
                                  = some (.fvar d nm₁ ty₁x) := by
                                rw [denoteNode, denote_mono hext₇ hty₁]; rfl
                              try dsimp only
                              refine SimAt.bind_left (internI_eff hs₇ hfv₁)
                                (fun s₈ fv₁ hs₈ hext₈ hQf₁ => ?_)
                              try dsimp only
                              refine SimAt.bind_left (inst1M_eff hs₈
                                (denote_mono (hext₇.trans hext₈) hbody₁) hQf₁)
                                (fun s₉ ob₁ hs₉ hext₉ hQo₁ => ?_)
                              have hfv₂ : denoteNode s₉.store.denote (.fvar d nm₂ t₂)
                                  = some (.fvar d nm₂ ty₂x) := by
                                rw [denoteNode, denote_mono
                                  ((hext₇.trans hext₈).trans hext₉) hty₂]
                                rfl
                              try dsimp only
                              refine SimAt.bind_left (internI_eff hs₉ hfv₂)
                                (fun s₁₀ fv₂ hs₁₀ hext₁₀ hQf₂ => ?_)
                              try dsimp only
                              refine SimAt.bind_left (inst1M_eff hs₁₀
                                (denote_mono (((hext₇.trans hext₈).trans
                                  hext₉).trans hext₁₀) hbody₂) hQf₂)
                                (fun s₁₁ ob₂ hs₁₁ hext₁₁ hQo₂ => ?_)
                              try dsimp only
                              refine SimAt.bind (ih.defeq hs₁₁
                                (denote_mono (hext₁₀.trans hext₁₁) hQo₁) hQo₂
                                (WScoped.instantiate1 h1.1 0 h1.2)
                                (WScoped.instantiate1 h2.1 0 h2.2))
                                (fun s₁₂ r₂ r₂' hs₁₂ hext₁₂ hP₂ => ?_)
                              obtain rfl : r₂ = r₂' := hP₂
                              cases r₂ with
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                try dsimp only
                                exact SimAt.pure hs₁₂ rfl
                              | true =>
                                simp only [↓reduceIte]
                                obtain ⟨bi₁, cod₁⟩ := m₁
                                obtain ⟨bi₂, cod₂⟩ := m₂
                                dsimp only
                                cases cod₁ with
                                | none => cases cod₂ <;> exact SimAt.throw
                                | some v₁ =>
                                  cases cod₂ with
                                  | none => exact SimAt.throw
                                  | some v₂ =>
                                    dsimp only
                                    try dsimp only
                                    exact SimAt.liftFueled _ _ hs₁₂
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact defeqI_etaL_arm ih henv hs₆ haS hty₁ hbody₁ hbS hwa' hwb'
                        | app f₁ a₁ =>
                          rw [denoteNode, Option.bind_eq_some_iff] at hda
                          obtain ⟨xf₁, hf₁, hda⟩ := hda
                          rw [Option.map_eq_some_iff] at hda
                          obtain ⟨xa₁, ha₁, hda⟩ := hda
                          subst hda
                          have h1 : WScoped d xf₁ ∧ WScoped d xa₁ := by
                            simpa only [WScoped] using hwa'
                          cases nb with
                          | app f₂ a₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨xf₂, hf₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨xa₂, ha₂, hdb⟩ := hdb
                            subst hdb
                            have h2 : WScoped d xf₂ ∧ WScoped d xa₂ := by
                              simpa only [WScoped] using hwb'
                            try dsimp only
                            refine SimAt.bind (ih.defeq hs₆ hf₁ hf₂ h1.1 h2.1)
                              (fun s₇ r₁ r₁' hs₇ hext₇ hP₁ => ?_)
                            obtain rfl : r₁ = r₁' := hP₁
                            cases r₁ with
                            | true =>
                              simp only [↓reduceIte]
                              try dsimp only
                              refine SimAt.bind (ih.defeq hs₇ (denote_mono hext₇ ha₁)
                                (denote_mono hext₇ ha₂) h1.2 h2.2)
                                (fun s₈ r₂ r₂' hs₈ hext₈ hP₂ => ?_)
                              obtain rfl : r₂ = r₂' := hP₂
                              cases r₂ with
                              | true =>
                                simp only [↓reduceIte]
                                try dsimp only
                                exact SimAt.pure hs₈ rfl
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₈
                                  (denote_mono (hext₇.trans hext₈) haS)
                                  (denote_mono (hext₇.trans hext₈) hbS) hwa' hwb'
                            | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₇ (denote_mono hext₇ haS)
                                (denote_mono hext₇ hbS) hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            cases l₂ with
                            | natVal nn =>
                              cases nn with
                              | zero => exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | succ k =>
                                try dsimp only
                                refine SimAt.view ?_
                                obtain ⟨nf, hnf, hcf, hdf⟩ := denote_some_inv hf₁
                                rw [hnf]
                                cases nf with
                                | const cf usf =>
                                  cases hdf
                                  cases usf with
                                  | cons u us' => exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                  | nil =>
                                    dsimp only
                                    try dsimp only
                                    by_cases hsc : cf = natSuccName
                                    try dsimp only
                                    · rw [if_pos hsc, if_pos hsc]
                                      try dsimp only
                                      refine SimAt.bind_left (internI_eff hs₆
                                        (x := .lit (.natVal k)) rfl)
                                        (fun s₇ kl hs₇ hext₇ hQk => ?_)
                                      try dsimp only
                                      exact ih.defeq hs₇ (denote_mono hext₇ ha₁) hQk h1.2
                                        (by simp [WScoped])
                                    try dsimp only
                                    · rw [if_neg hsc, if_neg hsc]
                                      try dsimp only
                                      exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | bvar kf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | sort uf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | lit lf =>
                                  cases hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | fvar if₁ nmf tf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | app ff af =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | lam nmf tf bf mf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | forallE nmf tf bf mf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | letE nmf tf vf bf =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                                | proj sf jf ef =>
                                  invert_node hdf
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                            | strVal str =>
                              try dsimp only
                              refine SimAt.view ?_
                              obtain ⟨nf, hnf, hcf, hdf⟩ := denote_some_inv hf₁
                              rw [hnf]
                              cases nf with
                              | const cf usf =>
                                cases hdf
                                rw [strLitSupportedF_eq]
                                try dsimp only
                                by_cases hsc : cf = stringOfListName ∧ usf = [] ∧
                                    strLitSupported env = true
                                try dsimp only
                                · rw [if_pos hsc, if_pos hsc]
                                  try dsimp only
                                  refine SimAt.bind_left (internExprM_eff hs₆
                                    (strLitToConstructor str))
                                    (fun s₇ sc hs₇ hext₇ hQs => ?_)
                                  try dsimp only
                                  exact ih.defeq hs₇ (denote_mono hext₇ haS) hQs hwa'
                                    (strLitToConstructor_WScoped str d)
                                try dsimp only
                                · rw [if_neg hsc, if_neg hsc]
                                  try dsimp only
                                  exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | bvar kf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | sort uf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | lit lf =>
                                cases hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | fvar if₁ nmf tf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | app ff af =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | lam nmf tf bf mf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | forallE nmf tf bf mf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | letE nmf tf vf bf =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                              | proj sf jf ef =>
                                invert_node hdf
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | bvar k₁ =>
                          cases hda
                          cases nb with
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | letE nm₁ t₁ v₁ b₁ =>
                          invert_node hda
                          cases nb with
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | proj s₂' j₂ e₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                        | proj s₁' j₁ e₁ =>
                          rw [denoteNode, Option.map_eq_some_iff] at hda
                          obtain ⟨xe₁, he₁, hda⟩ := hda
                          subst hda
                          have h1 : WScoped d xe₁ := by simpa only [WScoped] using hwa'
                          cases nb with
                          | proj s₂' j₂ e₂ =>
                            rw [denoteNode, Option.map_eq_some_iff] at hdb
                            obtain ⟨xe₂, he₂, hdb⟩ := hdb
                            subst hdb
                            have h2 : WScoped d xe₂ := by simpa only [WScoped] using hwb'
                            try dsimp only
                            by_cases hjj : (j₁ == j₂) = true
                            try dsimp only
                            · rw [if_pos hjj, if_pos hjj]
                              try dsimp only
                              refine SimAt.bind (ih.defeq hs₆ he₁ he₂ h1 h2)
                                (fun s₇ r₁ r₁' hs₇ hext₇ hP₁ => ?_)
                              obtain rfl : r₁ = r₁' := hP₁
                              cases r₁ with
                              | true =>
                                simp only [↓reduceIte]
                                try dsimp only
                                exact SimAt.pure hs₇ rfl
                              | false =>
                                simp only [Bool.false_eq_true, ↓reduceIte]
                                try dsimp only
                                exact stuckIrrelI_sim ih henv hs₇ (denote_mono hext₇ haS)
                                  (denote_mono hext₇ hbS) hwa' hwb'
                            try dsimp only
                            · rw [if_neg hjj, if_neg hjj]
                              try dsimp only
                              exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | bvar k₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | sort u₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | const c₂ us₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lit l₂ =>
                            cases hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | fvar i₂ nm₂ t₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | app f₂ a₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | lam nm₂ t₂ b₂ m₂ =>
                            rw [denoteNode, Option.bind_eq_some_iff] at hdb
                            obtain ⟨ty₂x, hty₂, hdb⟩ := hdb
                            rw [Option.bind_eq_some_iff] at hdb
                            obtain ⟨body₂x, hbody₂, hdb⟩ := hdb
                            rw [Option.map_eq_some_iff] at hdb
                            obtain ⟨bm, hbmDen, hdb⟩ := hdb
                            subst hdb
                            try dsimp only
                            exact defeqI_etaR_arm ih henv hs₆ haS hty₂ hbody₂ hbS hwa' hwb'
                          | forallE nm₂ t₂ b₂ m₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'
                          | letE nm₂ t₂ v₂ b₂ =>
                            invert_node hdb
                            try dsimp only
                            exact stuckIrrelI_sim ih henv hs₆ haS hbS hwa' hwb'

end Walks

end Setlec
