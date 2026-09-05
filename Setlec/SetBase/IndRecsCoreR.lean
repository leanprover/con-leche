import Setlec.SetBase.EnvRCons
import Setlec.Verify.Denote.EnvExt
import Setlec.Verify.Denote.Levels

/-!
# The recursor group's **model-free core** (task #161 S7, Wall A)

S6 measured the last wall under `Bridge/DeclInd.lean`'s finding 8 and
found it one level below the residue: the projection walk starts at
`env₃`, the recursor group's output, and `env₃` is not a *cons* of
anything the bridge built — it is a **swap** of the provisional
environment (`EnvS.swap`, `SwapShList`).  An `EnvR env₃` therefore
needs, for every fired rule of every swapped recursor, the two facts
`rec_params_le` (`rP ≤ mI`) and `rec_rhs_denotes` (the right-hand
side's denotation at every level instantiation), and until S6 both
lived only inside `RecRuleLawV`, a model-carrying wrapper.

S6 built the storage half (`RuleFactsR` / `iotaRulesFactsR` /
`indRecsFoldFacts`, `SetBase/IndBlockR.lean`).  This module is the
other half — the group's `EnvR` core, in three pieces:

* `provisionRecsRcore` — `provisionRecsS`'s `EnvR` twin, off the
  *relation*; its step is `memberInstallR` (S6);
* `EnvR.swap` — `EnvS.swap`'s `EnvR` shadow.  It is **strictly
  smaller** than the `EnvS` swap: no `RecCtorsStored`, no
  `SwapNResS`, no `RecRulesV` — an `EnvR` has no `rec_ctors`, no
  `basis_pinned` and no law field, so the transport is
  `denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq` plus the two rule
  facts, taken as hypotheses exactly as `EnvS.swap` takes its law;
* `indRecsCoreR` — `indRecsS`'s tail (`hwf₃`, the block invariant's
  survival, the three preservation facts), whose every ingredient is
  now `RuleFactsR`.

**The one join that is not a copy.**  `RuleFactsR`'s fired-rule
conjunct denotes the right-hand side *uninstantiated* (that is the
shape `IotaRuleR`'s H1 run exposure stores), while `rec_rhs_denotes`
asks for the *level-instantiated* one.  `denote_instLevels`
(`Verify/Denote/Levels.lean`) is the bridge, at the substituted
assignment `Level.substFn ψ cv.levelParams us`, and its `ValParams`
premise is `EnvR.val_params` verbatim.  Nothing semantic is involved.

Model-free by construction: no `V`, no `SetTheory`, no `EnvS`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

/-! ## The provisioning fold, at the `EnvR` level -/

/-- **The recursor provisioning fold, off the relation, model-free** —
`provisionRecsS`'s `EnvR` twin.  The step is `memberInstallR`, so the
proof is the install's with `hkey` and the model dropped. -/
theorem provisionRecsRcore {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} (m : EnvR envAcc)
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsR μ F blockNames envAcc m.cval recs envSelf cvalSelf
        checked →
      BlockInstalledTT blockNames envAcc m.cval →
      EtaFamiliesClosedO blockNames envAcc →
      BlockEtaPinned μ blockNames envAcc →
      ∃ mS : EnvR envSelf,
        mS.cval = cvalSelf ∧
        BlockInstalledTT blockNames envSelf cvalSelf ∧
        EtaFamiliesClosedO blockNames envSelf ∧
        BlockEtaPinned μ blockNames envSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc m envSelf cvalSelf checked _ h hI hEC hBP
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨m, rfl, hI, hEC, hBP⟩
  | cons ci rest ih =>
    intro envAcc m envSelf cvalSelf checked hbn h hI hEC hBP
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hrec, -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
      memberInstallR m hmv
      hI (by rw [hnameA]; exact hbn ci List.mem_cons_self)
      (fun caps₃ heq => ConstantInfo.noConfusion heq)
      hEC hBP
      rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
    exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
      (by rw [hm₁cval]; exact hrec)
      (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁

/-! ## The group rule-list swap, at the `EnvR` level -/

set_option maxHeartbeats 800000 in
/-- **The group rule-list swap, model-free**: an `EnvR` of the
provisional (rule-less) environment transports to the environment
carrying the checked rule lists, with the *same* valuation —
definitionally.

The two rule fields are hypotheses, exactly as `EnvS.swap` takes
`RecRulesV` as one: they are what the group install proves (there from
the iota bottoms, here from `RuleFactsR`). -/
def EnvR.swap {env₀ env₃ : Env} (m₀ : EnvR env₀)
    (hsw : SwapShList env₀.consts env₃.consts)
    (hwf : EnvWF env₃)
    (hle : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI)
    (hrhs : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert →
        ∀ (us : List Level) (ψ : Name → Nat),
          us.length = cv.levelParams.length →
          ∃ R, denoteClosed m₀.cval env₃ ψ
            (r.rhs.instantiateLevelParams cv.levelParams us) = some R) :
    EnvR env₃ := by
  have hcorr : ∀ n : Name,
      env₃.find? n = env₀.find? n ∨
      ∃ cv mI rP rules,
        env₀.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := swapSh_find?_corr hsw
  have hcg : SwapCongr env₀ env₃ := SwapShList.congr hsw
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote m₀.cval env₀ φ d e = denote m₀.cval env₃ φ d e :=
    fun _ => denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq
  have hdeC : ∀ (φ : Name → Nat) (e : Expr),
      denoteClosed m₀.cval env₀ φ e = denoteClosed m₀.cval env₃ φ e :=
    fun φ e => hde φ 0 e
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  refine
    { cval := m₀.cval
      cval_closed := m₀.cval_closed
      wf := hwf
      val_params := ?_
      ty_denotes := ?_
      defn_eq := ?_
      rec_rhs_denotes := hrhs
      rec_params_le := hle
      proj_ok := ?_
      thm_ok := ?_
      nat_op_guard := ?_ }
  · -- val_params: the swap keeps every stored `ConstantVal`
    intro n ci hf φ₁ φ₂ hp
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · exact m₀.val_params n ci (by rw [← heq]; exact hf) φ₁ φ₂ hp
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n _ h₀ φ₁ φ₂ hp
  · -- ty_denotes: the member correspondence plus the denote congruence
    intro c₃ hc₃ ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw c₃ hc₃
    obtain ⟨t, ht⟩ := m₀.ty_denotes c₀ hc₀ ψ
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
    · exact ⟨t, by rw [← hdeC]; exact ht⟩
    · exact ⟨t, by rw [← hdeC]; exact ht⟩
  · -- defn_eq: a definition is never a swap's right side
    intro cv value hint hmem ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw _ hmem
    rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
    · rw [← hdeC]
      exact m₀.defn_eq cv value hint hc₀ ψ
    · exact nomatch heq
  · -- proj_ok: projection entries and their blocks are untouched
    obtain ⟨hp1, hp2, hp3⟩ := m₀.proj_ok
    refine ⟨?_, ?_, ?_⟩
    · intro n entry hf hnat
      obtain ⟨he, hps, hpm⟩ :=
        hp1 n entry ((hsame n _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hnat
      refine ⟨he, ?_, ?_⟩
      · exact (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hps
      · exact (hsame _ _
          (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hpm
    · intro i entry hf
      exact hp2 i entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    · intro n entry hf
      exact hp3 n entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
  · -- thm_ok: likewise a theorem is never a swap's right side
    intro cv value hmem ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hsw _ hmem
    rcases hpair with rfl | ⟨cv2, mI, rP, rules, rfl, heq⟩
    · rw [← hdeC]
      exact m₀.thm_ok cv value hc₀ ψ
    · exact nomatch heq
  · -- nat_op_guard: keyed on definitions, with the guard congruent
    intro c hmem hst
    obtain ⟨cv, v, hh, hf⟩ := natOpStored_inv hst
    have hf₀ : env₀.find? c = some (.defnInfo cv v hh) :=
      hcg.findDown c _ hf (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon)
    rw [← hcg.guardEq]
    exact m₀.nat_op_guard c hmem (by simp [natOpStored, hf₀])

/-- The swap keeps the valuation — definitionally. -/
theorem EnvR.swap_cval {env₀ env₃ : Env} (m₀ : EnvR env₀)
    (hsw : SwapShList env₀.consts env₃.consts) (hwf : EnvWF env₃)
    (hle : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI)
    (hrhs : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert →
        ∀ (us : List Level) (ψ : Name → Nat),
          us.length = cv.levelParams.length →
          ∃ R, denoteClosed m₀.cval env₃ ψ
            (r.rhs.instantiateLevelParams cv.levelParams us) = some R) :
    (m₀.swap hsw hwf hle hrhs).cval = m₀.cval := rfl

/-! ## The swapped environment's four syntactic facts

`EnvR.swap` takes `EnvWF env₃` as a hypothesis and needs no
`RecCtorsStored`/`BasisPinnedTT`/`ProjOkT` of its own — but the *P*
lane's carrier (`EnvS2Core`) carries all four, and the [set] install
proves them inside `indRecsS`.  They are extracted here so that the
ind tier's two swaps (`indRecsCoreR` below and `EnvS2PM.swapP`) share
one proof, off `RuleFactsR` alone.
-/

set_option maxHeartbeats 1600000 in
/-- **The four syntactic environment facts survive the group swap.** -/
theorem swapEnvFacts {envSelf env₃ : Env} {cvalSelf : TConstVal}
    (hwfS : EnvWF envSelf) (hctorsS : RecCtorsStored envSelf)
    (hbpS : BasisPinnedTT envSelf cvalSelf) (hprojS : ProjOkT envSelf)
    (hswR : SwapShList envSelf.consts env₃.consts)
    (hnresR : SwapNResS envSelf env₃)
    (hentR : ∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
      ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        c = .recInfo cv mI rP rules ∧
        ∀ rl ∈ rules, RuleFactsR envSelf cvalSelf cv mI rP rl)
    (hentF : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      envSelf.find? n = some (.recInfo cv mI rP rules) ∨
      ∀ rl ∈ rules, RuleFactsR envSelf cvalSelf cv mI rP rl) :
    EnvWF env₃ ∧ RecCtorsStored env₃ ∧
      BasisPinnedTT env₃ cvalSelf ∧ ProjOkT env₃ := by
  have hcg : SwapCongr envSelf env₃ := SwapShList.congr hswR
  have hcorr : ∀ n : Name,
      env₃.find? n = envSelf.find? n ∨
      ∃ cv mI rP rules,
        envSelf.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := swapSh_find?_corr hswR
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ envSelf.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hres₃ : ∀ e : Expr, e.constsResolve envSelf = true →
      e.constsResolve env₃ = true := by
    intro e he
    rw [← Expr.constsResolve_congr hcg.isSomeEq]
    exact he
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `EnvWF`
    intro c hc
    rcases hentR c hc with hcS | ⟨cv, mI, rP, rules, rfl, hfacts⟩
    · obtain ⟨hSw, hSlp, hSres, hSb, hSdef, hSrec, hSthm⟩ := hwfS c hcS
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb, ?_, ?_, ?_⟩
      · intro cv v hint heq
        obtain ⟨d1, d2, d3, d4⟩ := hSdef cv v hint heq
        exact ⟨d1, d2, hres₃ _ d3, d4⟩
      · intro cv mI rP rules heq r hr
        obtain ⟨r1, r2, r3, r4, r5⟩ := hSrec cv mI rP rules heq r hr
        refine ⟨r1, r2, hres₃ _ r3, r4, ?_⟩
        intro lvls pins hfr
        obtain ⟨n1, n2, n3, n4⟩ := r5 lvls pins hfr
        refine ⟨n1, n2, ?_, n4⟩
        intro pin hpin
        obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        exact ⟨p1, p2, hres₃ _ p3, p4⟩
      · intro cv v heq
        obtain ⟨t1, t2, t3, t4⟩ := hSthm cv v heq
        exact ⟨t1, t2, hres₃ _ t3, t4⟩
    · obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hswR _ hc
      obtain ⟨hSw, hSlp, hSres, hSb, -, -, -⟩ := hwfS c₀ hc₀
      have hcvt : c₀.toConstantVal = cv := by
        rcases hpair with rfl | ⟨cv', mI', rP', rules', rfl, heq⟩
        · rfl
        · obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj heq
          rfl
      rw [hcvt] at hSw hSlp hSres hSb
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb,
        fun _ _ _ hcon => ConstantInfo.noConfusion hcon, ?_,
        fun _ _ hcon => ConstantInfo.noConfusion hcon⟩
      intro cv' mI' rP' rules' heq r hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      obtain ⟨w1, w2, w3, w4, w5, -, -⟩ := hfacts r hr
      refine ⟨w1, w2, hres₃ _ w3, w4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := w5 lvls pins hfr
      refine ⟨n1, n2, ?_, n4⟩
      intro pin hpin
      obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      exact ⟨p1, p2, hres₃ _ p3, p4⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · obtain ⟨cvj, cnP, cnF, hfc⟩ := hctorsS n cv mI rP rules hfS r hr
      exact ⟨cvj, cnP, cnF, hcg.findUp _ _ hfc
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon)⟩
    · obtain ⟨-, -, -, -, -, ⟨cvj, cnP, cnF, hfc⟩, -⟩ := hfacts r hr
      exact ⟨cvj, cnP, cnF, hcg.findUp _ _ hfc
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon)⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : envSelf.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnresR n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact hbpS n ci hf₀ hres
  · -- `ProjOkT`: projection entries are untouched
    obtain ⟨hp1, hp2, hp3⟩ := hprojS
    refine ⟨?_, ?_, ?_⟩
    · intro n entry hf hnat
      obtain ⟨he, hps, hpm⟩ :=
        hp1 n entry ((hsame n _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) hnat
      exact ⟨he,
        (hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hps,
        (hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mpr hpm⟩
    · intro i entry hf
      exact hp2 i entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)
    · intro n entry hf
      exact hp3 n entry ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf)

/-! ## The group phase, at the `EnvR` level -/

set_option maxHeartbeats 3200000 in
/-- **The recursor-group phase, model-free** — `indRecsS`'s `EnvR`
twin: provision (`provisionRecsRcore`), collect the rules' facts
(`indRecsFoldFacts` at `RuleFactsR`), swap (`EnvR.swap`).

`hall`/`blockRenameOkT` are **not** premises here, and that is a
measurement, not an omission: the renaming soundness was needed only
to fire the per-rule *law*, and `RuleFactsR` has no law. -/
theorem indRecsCoreR {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo} {cval₃ : TConstVal}
    (m : EnvR env₂) (hI : BlockInstalledTT blockNames env₂ m.cval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hEC : EtaFamiliesClosedO blockNames env₂)
    (hBP : BlockEtaPinned μ blockNames env₂)
    (h : IndRecsR μ F blockNames env₂ m.cval recs env₃ cval₃) :
    ∃ m₃ : EnvR env₃,
      m₃.cval = cval₃ ∧ BlockInstalledTT blockNames env₃ cval₃ ∧
      (∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
        (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
        env₃.find? n = some ci) ∧
      (∀ n : Name,
        (env₂.find? n).isSome = true → (env₃.find? n).isSome = true) ∧
      (∀ ci ∈ recs, (env₃.find? ci.name).isSome = true) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, heqf, envSelf, cvalSelf, checked,
    hprov, hfold⟩
  · exact ⟨m, rfl, hI, fun n ci hf _ => hf, fun n hn => hn,
      fun ci hci => nomatch hci⟩
  obtain ⟨mS, hmScval, hIS, -, -⟩ :=
    provisionRecsRcore recs m hbn hprov hI hEC hBP
  rw [← hmScval] at hprov hfold hIS
  -- run the two folds in step, at the model-free rule facts
  obtain ⟨hswR, -, rfl, hentR, hentF⟩ :=
    indRecsFoldFacts (RuleFactsR envSelf mS.cval)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsR
          (fun n ci hf => Or.inl (provisionRecsS_mono recs hprov n ci hf))
          0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf => Or.inl (provisionRecsS_mono recs hprov n ci hf))
      (provisionRecsS_mono recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsS_mem recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsS_mono recs hprov n _ hf))
      hbn hprov hfold
  have hcg : SwapCongr envSelf env₃ := SwapShList.congr hswR
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote mS.cval envSelf φ d e = denote mS.cval env₃ φ d e :=
    fun _ => denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq
  -- the swapped environment's syntactic facts
  have hres₃ : ∀ e : Expr, e.constsResolve envSelf = true →
      e.constsResolve env₃ = true := by
    intro e he
    rw [← Expr.constsResolve_congr hcg.isSomeEq]
    exact he
  have hwf₃ : EnvWF env₃ := by
    intro c hc
    rcases hentR c hc with hcS | ⟨cv, mI, rP, rules, rfl, hfacts⟩
    · -- an unswapped entry: its own facts, resolution transported
      obtain ⟨hSw, hSlp, hSres, hSb, hSdef, hSrec, hSthm⟩ := mS.wf c hcS
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb, ?_, ?_, ?_⟩
      · intro cv v hint heq
        obtain ⟨d1, d2, d3, d4⟩ := hSdef cv v hint heq
        exact ⟨d1, d2, hres₃ _ d3, d4⟩
      · intro cv mI rP rules heq r hr
        obtain ⟨r1, r2, r3, r4, r5⟩ := hSrec cv mI rP rules heq r hr
        refine ⟨r1, r2, hres₃ _ r3, r4, ?_⟩
        intro lvls pins hfr
        obtain ⟨n1, n2, n3, n4⟩ := r5 lvls pins hfr
        refine ⟨n1, n2, ?_, n4⟩
        intro pin hpin
        obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        exact ⟨p1, p2, hres₃ _ p3, p4⟩
      · intro cv v heq
        obtain ⟨t1, t2, t3, t4⟩ := hSthm cv v heq
        exact ⟨t1, t2, hres₃ _ t3, t4⟩
    · -- a swapped recursor: the *type* facts come from the provisional
      -- entry, the *rule* facts from the fired kits
      obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hswR _ hc
      obtain ⟨hSw, hSlp, hSres, hSb, -, -, -⟩ := mS.wf c₀ hc₀
      have hcvt : c₀.toConstantVal = cv := by
        rcases hpair with rfl | ⟨cv', mI', rP', rules', rfl, heq⟩
        · rfl
        · obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj heq
          rfl
      rw [hcvt] at hSw hSlp hSres hSb
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb,
        fun _ _ _ hcon => ConstantInfo.noConfusion hcon, ?_,
        fun _ _ hcon => ConstantInfo.noConfusion hcon⟩
      intro cv' mI' rP' rules' heq r hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      obtain ⟨w1, w2, w3, w4, w5, -, -⟩ := hfacts r hr
      refine ⟨w1, w2, hres₃ _ w3, w4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := w5 lvls pins hfr
      refine ⟨n1, n2, ?_, n4⟩
      intro pin hpin
      obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      exact ⟨p1, p2, hres₃ _ p3, p4⟩
  -- the two rule fields at the swapped environment
  have hle₃ : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert → rP ≤ mI := by
    intro n cv mI rP rules hf r hr hfire
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · exact mS.rec_params_le n cv mI rP rules hfS r hr hfire
    · exact ((hfacts r hr).2.2.2.2.2.2 hfire).1
  have hrhs₃ : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      ∀ r ∈ rules, RecRule.fire r ≠ .inert →
        ∀ (us : List Level) (ψ : Name → Nat),
          us.length = cv.levelParams.length →
          ∃ R, denoteClosed mS.cval env₃ ψ
            (r.rhs.instantiateLevelParams cv.levelParams us)
            = some R := by
    intro n cv mI rP rules hf r hr hfire us ψ hlen
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · obtain ⟨R, hR⟩ :=
        mS.rec_rhs_denotes n cv mI rP rules hfS r hr hfire us ψ hlen
      refine ⟨R, ?_⟩
      show denote mS.cval env₃ ψ 0 _ = some R
      rw [← hde]
      exact hR
    · -- the fired kit denotes the *uninstantiated* right-hand side;
      -- `denote_instLevels` moves the instantiation into the level
      -- assignment (`EnvR.val_params` is its `ValParams` premise)
      obtain ⟨-, hden⟩ := (hfacts r hr).2.2.2.2.2.2 hfire
      obtain ⟨Rv, hRv⟩ := hden (Level.substFn ψ cv.levelParams us)
      refine ⟨Rv, ?_⟩
      show denote mS.cval env₃ ψ 0 _ = some Rv
      rw [← hde, denote_instLevels mS.val_params ψ 0 (RecRule.rhs r)]
      exact hRv
  refine ⟨mS.swap hswR hwf₃ hle₃ hrhs₃, rfl, ?_,
    (fun n ci hf hnr => hcg.findUp n ci
      (provisionRecsS_mono recs hprov n ci hf) hnr),
    (fun n hn => by
      rw [← hcg.isSomeEq n]
      rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hn; exact nomatch hn
      · rw [provisionRecsS_mono recs hprov n ci hf]; rfl),
    (fun ci hci => by
      rw [← hcg.isSomeEq ci.name]
      exact provisionRecsS_stored recs hprov ci hci)⟩
  -- the block invariant survives the swap
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq |
    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ :=
      hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon),
      hlps, hren, hv⟩

end Setlec.SetR
