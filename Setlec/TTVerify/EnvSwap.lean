import Setlec.TTVerify.Extend

/-!
# The group rule-list swap (`DeclIndTT`'s transport)

Transpose of `Setlec/Model/Extend/GroupSwap.lean`.  A block's recursors
are provisioned rule-less together and installed together; the final
environment differs from the provisional one only in that rule-less
recursors gained their checked rule lists.  `EnvTT.swap` transports the
derivation model across that swap.

The design is §24's: `denote` reads the environment only through
`find?`-`toConstantVal` (the `.const` clause's arity check and level
parameters) and the two literal guards, so one congruence —
`denote_env_ext`, mirroring `denote_cval_congr` — transports every
denotation on the nose (an *equation*, so hypotheses and conclusions
move for free), and the field transports are lookup bookkeeping plus
the per-recursor obligations (`RecMemberTT`, discharged by the bottoms).
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

open Setlec.TT

/-! ## The environment congruence -/

/-- The stored level parameters only read the constant's
level-parameter slot. -/
theorem levelParamsAt_ext {env₁ env₂ : Env} {n : Name}
    (h : (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams)) :
    levelParamsAt env₁ n = levelParamsAt env₂ n := by
  unfold levelParamsAt
  cases h1 : env₁.find? n <;> cases h2 : env₂.find? n <;>
    rw [h1, h2] at h <;> simp at h ⊢ <;> exact h

/-- **Denotation reads the environment only through the stored level
parameters and the two literal guards.**  Transpose of
`interp_env_ext`; the swap's workhorse.  An equation, so a law's
denote *hypotheses* and *conclusions* both move across it for free —
which is what makes the fired-form fields transportable at all. -/
theorem denote_env_ext {cval : TConstVal} {env₁ env₂ : Env}
    {φ : Name → Nat}
    (henvLev : ∀ n,
      (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported env₁ = natLitSupported env₂)
    (hstr : strLitSupported env₁ = strLitSupported env₂) :
    ∀ (d : Nat) (e : Expr),
      denote cval env₁ φ d e = denote cval env₂ φ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env₁) (φ := φ) with
  | case1 d u => simp only [denote_sort]
  | case2 d idx nm ty => simp only [denote_fvar]
  | case3 d n us ci h1 h2 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => rw [h2'] at h; exact nomatch h
    | some ci₂ =>
      rw [h2'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [denote_const, h1, h2', ← h, if_pos h2]
  | case4 d n us ci h1 h2 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => rw [h2'] at h; exact nomatch h
    | some ci₂ =>
      rw [h2'] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp only [denote_const, h1, h2', ← h, if_neg h2]
  | case5 d n us h1 =>
    have h := henvLev n
    rw [h1] at h
    cases h2' : env₂.find? n with
    | none => simp only [denote_const, h1, h2']
    | some ci₂ => rw [h2'] at h; exact nomatch h
  | case6 d n ty body mb h1 ihty =>
    simp only [denote_forallE, ← ihty, h1]
  | case7 d n ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_forallE, ← ihty, ← ihbody, h1, h2]
  | case8 d n ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_forallE, ← ihty, ← ihbody, h1, h2]
  | case9 d n ty body mb h1 ihty => simp only [denote_lam, ← ihty, h1]
  | case10 d n ty body mb B h1 h2 ihty ihbody =>
    simp only [denote_lam, ← ihty, ← ihbody, h1, h2]
  | case11 d n ty body mb B h1 B' h2 ihty ihbody =>
    simp only [denote_lam, ← ihty, ← ihbody, h1, h2]
  | case12 d f a vf va h1 h2 ihf iha =>
    simp only [denote_app, ← ihf, ← iha]
  | case13 d f a hbad ihf iha => simp only [denote_app, ← ihf, ← iha]
  | case14 d n ty val body vf va h1 h2 h3 ihty ihval ihbody =>
    simp only [denote_letE, ← ihty, ← ihval, ← ihbody]
  | case15 d n ty val body vf va h1 h2 B h3 ihty ihval ihbody =>
    simp only [denote_letE, ← ihty, ← ihval, ← ihbody]
  | case16 d n ty val body hbad ihty ihval =>
    simp only [denote_letE, ← ihty, ← ihval]
  | case17 d sn i e h1 ihe => simp only [denote_proj, ← ihe]
  | case18 d sn i e B h1 h2 ihe => simp only [denote_proj, ← ihe]
  | case19 d sn i e B h1 h2 ihe => simp only [denote_proj, ← ihe]
  | case20 d n _ | case21 d n _ =>
    simp only [denote_natLit, hnat]
  | case22 d s _ | case23 d s _ =>
    simp only [denote_strLit, hstr]
    by_cases hg2 : strLitSupported env₂ = true
    · rw [if_pos hg2, if_pos hg2, strLitT, strLitT,
        levelParamsAt_ext (henvLev listNilName),
        levelParamsAt_ext (henvLev listConsName)]
    · simp [hg2]
  | case24 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    match x with
    | .bvar i => simp only [denote_bvar]
    | .sort u => exact (k1 u rfl).elim
    | .fvar a b c => exact (k2 a b c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE a b c dd => exact (k4 a b c dd rfl).elim
    | .lam a b c dd => exact (k5 a b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE a b c dd => exact (k7 a b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-! ## The swap relation -/

/-- The fold facts a freshly rule-equipped recursor supplies: the
`RecRulesTT` clause for each of its rules, at the final environment.
The transpose of `RecMemberOk`, in the fired form — its supplier is
the bottoms (`IndBottomPlainTT` / `IndBottomNestedTT` /
`IndBottomProjTT`) via `denote_env_ext` from the provisional
environment. -/
def RecMemberTT (env' : Env) (cval : TConstVal) (ci : ConstantInfo) :
    Prop :=
  ∀ cv mI rP rules, ci = .recInfo cv mI rP rules →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
    rP ≤ mI ∧
    ∀ (φ : Name → Nat) (d : Nat) (us : List Level),
      us.length = cv.levelParams.length →
      ∃ R, denote cval env' φ d
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
          = some R ∧
        ∀ (cvj : ConstantVal) (cnP cnF : Nat),
          env'.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
        ∀ (Δ : List VExpr) (usj : List Level) (xs ys : List VExpr)
          (TV TVj restR restC : VExpr),
          xs.length = mI →
          ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (recFireComparands rl cv.levelParams us cvj.levelParams
                  [] rP).1 →
          (RecRule.fire rl = .plain →
            ∀ i, i < RecRule.ctorParams rl → i < mI →
              Deq Δ (ys.getD i default) (xs.getD i default)) →
          (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
            ∀ i, i < RecRule.ctorParams rl →
            ∀ vp : VExpr,
              denote cval env' φ rP
                (openRev 0 rP ((pins.getD i
                  default).instantiateLevelParams cv.levelParams us))
                = some vp →
              Deq Δ (ys.getD i default)
                (VExpr.instRevChain (xs.take rP) vp)) →
          IotaIndexPin Δ restC (RecRule.ctorParams rl) mI rP xs →
          denote cval env' φ d
            (cv.type.instantiateLevelParams cv.levelParams us) = some TV →
          denote cval env' φ d
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVj →
          VTeleTyped Δ TV
            (xs ++ [VExpr.mkAppN
              (cval (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys])
            restR →
          VTeleTyped Δ TVj ys restC →
          Deq Δ
            (VExpr.mkAppN (cval ci.name (Level.substFn φ cv.levelParams us))
              (xs ++ [VExpr.mkAppN
                (cval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
            (VExpr.mkAppN R
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))

/-- Pointwise swap relation: equal constants, or a rule-less recursor
paired with the same recursor carrying its checked rules, together
with the rule-carrying side's obligations.  Transpose of `SwapPair`. -/
def SwapPairT (env₃ : Env) (cval : TConstVal) (c₀ c₃ : ConstantInfo) :
    Prop :=
  c₀ = c₃ ∨
  ∃ cv mI rP rules,
    c₀ = .recInfo cv mI rP [] ∧
    c₃ = .recInfo cv mI rP rules ∧
    reservedBasisNames.contains cv.name = false ∧
    cv.name.isProjFnShape = false ∧
    ConstWF env₃ (.recInfo cv mI rP rules) ∧
    (∀ r ∈ rules, ∃ cvj cnP cnF,
      env₃.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
    RecMemberTT env₃ cval (.recInfo cv mI rP rules)

theorem SwapPairT.name_eq {env₃ : Env} {cval : TConstVal}
    {c₀ c₃ : ConstantInfo} (h : SwapPairT env₃ cval c₀ c₃) :
    c₀.name = c₃.name := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -⟩ <;> rfl

theorem SwapPairT.cv_eq {env₃ : Env} {cval : TConstVal}
    {c₀ c₃ : ConstantInfo} (h : SwapPairT env₃ cval c₀ c₃) :
    c₀.toConstantVal = c₃.toConstantVal := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -⟩ <;> rfl

/-- Pointwise swap of two constant lists.  Transpose of `SwapList`. -/
inductive SwapListT (env₃ : Env) (cval : TConstVal) :
    List ConstantInfo → List ConstantInfo → Prop
  | nil : SwapListT env₃ cval [] []
  | cons {c₀ c₃ : ConstantInfo} {rest₀ rest₃ : List ConstantInfo} :
      SwapPairT env₃ cval c₀ c₃ → SwapListT env₃ cval rest₀ rest₃ →
      SwapListT env₃ cval (c₀ :: rest₀) (c₃ :: rest₃)

theorem SwapListT.of_eq {env₃ : Env} {cval : TConstVal} :
    ∀ (l : List ConstantInfo), SwapListT env₃ cval l l
  | [] => .nil
  | _c :: l => .cons (Or.inl rfl) (SwapListT.of_eq l)

/-- The lookup correspondence of a pointwise swap.  Transpose of
`swap_find?_corr`. -/
theorem swapT_find?_corr {env₃ : Env} {cval : TConstVal} :
    ∀ {consts₀ consts₃ : List ConstantInfo},
    SwapListT env₃ cval consts₀ consts₃ →
    ∀ n : Name,
    (Env.mk consts₃).find? n = (Env.mk consts₀).find? n ∨
    ∃ cv mI rP rules,
      (Env.mk consts₀).find? n = some (.recInfo cv mI rP []) ∧
      (Env.mk consts₃).find? n = some (.recInfo cv mI rP rules) ∧
      cv.name = n ∧
      reservedBasisNames.contains cv.name = false ∧
      cv.name.isProjFnShape = false ∧
      ConstWF env₃ (.recInfo cv mI rP rules) ∧
      (∀ r ∈ rules, ∃ cvj cnP cnF,
        env₃.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
      RecMemberTT env₃ cval (.recInfo cv mI rP rules) := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro n; exact Or.inl rfl
  | @cons c₀ c₃ rest₀ rest₃ hpair hrest ih =>
    intro n
    show (Env.mk (c₃ :: rest₃)).find? n
        = (Env.mk (c₀ :: rest₀)).find? n ∨ _
    by_cases hn : c₃.name = n
    · have hn₀ : c₀.name = n := by rw [SwapPairT.name_eq hpair, hn]
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n = some c₃ := by
        show (c₃ :: rest₃).find? (·.name == n) = some c₃
        rw [List.find?_cons_of_pos (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n = some c₀ := by
        show (c₀ :: rest₀).find? (·.name == n) = some c₀
        rw [List.find?_cons_of_pos (by simp [hn₀])]
      rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl, hres,
        hshape, hwf, hctors, hrecm⟩
      · exact Or.inl (h₃.trans h₀.symm)
      · exact Or.inr ⟨cv, mI, rP, rules, h₀, h₃,
          (show cv.name = n from hn), hres, hshape, hwf, hctors, hrecm⟩
    · have hn₀ : ¬c₀.name = n := by
        rw [SwapPairT.name_eq hpair]
        exact hn
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n =
          (Env.mk rest₃).find? n := by
        show (c₃ :: rest₃).find? (·.name == n) = rest₃.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n =
          (Env.mk rest₀).find? n := by
        show (c₀ :: rest₀).find? (·.name == n) = rest₀.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn₀])]
      rw [h₃, h₀]
      exact ih n

/-- Member correspondence (right to left). -/
theorem swapT_mem_corr {env₃ : Env} {cval : TConstVal}
    {consts₀ consts₃ : List ConstantInfo}
    (hsw : SwapListT env₃ cval consts₀ consts₃) :
    ∀ c₃ ∈ consts₃, ∃ c₀ ∈ consts₀, SwapPairT env₃ cval c₀ c₃ := by
  induction hsw with
  | nil => intro c₃ hc; exact nomatch hc
  | @cons a b rest₀ rest₃ hpair hrest ih =>
    intro c₃ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨a, List.mem_cons_self, hpair⟩
    · obtain ⟨c₀, hc₀, hp⟩ := ih c₃ hc
      exact ⟨c₀, List.mem_cons_of_mem _ hc₀, hp⟩

set_option maxHeartbeats 3200000 in
/-- **The group rule-list swap**: a derivation model of the provisional
(rule-less) environment transports to the environment with the checked
rule lists attached, with the *same* valuation.  Transpose of
`extend_rules_eq`; the valuation identity is definitional here
(`(m₀.swap hsw).cval = m₀.cval` by `rfl`), which is what makes the
downstream rewrites disappear. -/
def EnvTT.swap {env₀ env₃ : Env} (m₀ : EnvTT env₀)
    (hsw : SwapListT env₃ m₀.cval env₀.consts env₃.consts) :
    EnvTT env₃ := by
  have hcorr' : ∀ n : Name,
      env₃.find? n = env₀.find? n ∨
      ∃ cv mI rP rules,
        env₀.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n ∧
        reservedBasisNames.contains cv.name = false ∧
        cv.name.isProjFnShape = false ∧
        ConstWF env₃ (.recInfo cv mI rP rules) ∧
        (∀ r ∈ rules, ∃ cvj cnP cnF,
          env₃.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        RecMemberTT env₃ m₀.cval (.recInfo cv mI rP rules) :=
    swapT_find?_corr hsw
  have henvLev : ∀ n, (env₀.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  have hisoSome : ∀ n, (env₀.find? n).isSome = (env₃.find? n).isSome := by
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  -- a component check that ignores a recursor's rule list is congruent
  -- across the swap
  have hchk : ∀ (chk : Option ConstantInfo → Bool),
      (∀ cv mI rP rules rules',
        chk (some (.recInfo cv mI rP rules)) =
        chk (some (.recInfo cv mI rP rules'))) →
      ∀ n, chk (env₀.find? n) = chk (env₃.find? n) := by
    intro chk hins n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      exact hins cv mI rP [] rules
  have hnat : natLitSupported env₀ = natLitSupported env₃ := by
    unfold natLitSupported
    rw [hchk natIndOk (fun _ _ _ _ _ => rfl) natName,
      hchk natZeroOk (fun _ _ _ _ _ => rfl) natZeroName,
      hchk natSuccOk (fun _ _ _ _ _ => rfl) natSuccName]
  have hstr : strLitSupported env₀ = strLitSupported env₃ := by
    unfold strLitSupported
    rw [hnat,
      hchk stringTyOk (fun _ _ _ _ _ => rfl) stringName,
      hchk stringOfListTyOk (fun _ _ _ _ _ => rfl) stringOfListName,
      hchk listTyOk (fun _ _ _ _ _ => rfl) listName,
      hchk listNilTyOk (fun _ _ _ _ _ => rfl) listNilName,
      hchk listConsTyOk (fun _ _ _ _ _ => rfl) listConsName,
      hchk charTyOk (fun _ _ _ _ _ => rfl) charName,
      hchk charOfNatTyOk (fun _ _ _ _ _ => rfl) charOfNatName]
  have hguardAll : ∀ c, natOpGuard env₀ c = natOpGuard env₃ c := by
    intro c
    unfold natOpGuard
    rw [hnat]
    congr 1
    · congr 1
      refine congrArg (List.all (natOpDeps c)) (funext fun n => ?_)
      rcases hcorr' n with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
    · split
      · congr 1
        · rcases hcorr' boolTrueName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
        · rcases hcorr' boolFalseName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
      · rfl
  have hde : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote m₀.cval env₀ φ d e = denote m₀.cval env₃ φ d e :=
    fun φ => denote_env_ext henvLev hnat hstr
  have hlpAll : ∀ n, levelParamsAt env₀ n = levelParamsAt env₃ n :=
    fun n => levelParamsAt_ext (henvLev n)
  have hfindDown : ∀ (n : Name) (ci : ConstantInfo),
      env₃.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₀.find? n = some ci := by
    intro n ci hf hnr
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [← heq]; exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP rules)
  have hfindUp : ∀ (n : Name) (ci : ConstantInfo),
      env₀.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₃.find? n = some ci := by
    intro n ci hf hnr
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]; exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP [])
  refine
    { cval := m₀.cval
      cval_closed := m₀.cval_closed
      wf := ?_
      val_params := ?_
      has_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := m₀.empty_pinned
      rec_rules := ?_
      caps_ok := ?_
      ctor_residual := ?_
      proj_ok := ?_
      rec_ctors := ?_
      eq_law := ?_
      basis_pinned := ?_
      nat_ops := ?_
      div_mod := ?_
      reduce_ops := ?_ }
  · -- wf
    intro c₃ hc₃
    obtain ⟨c₀, hc₀, hpair⟩ := swapT_mem_corr hsw c₃ hc₃
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -, -, hwf, -, -⟩
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := m₀.wf _ hc₀
      refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_⟩
      · rw [← Expr.constsResolve_congr hisoSome]
        exact h3
      · intro cv2 v2 h2' heq
        obtain ⟨g1, g2, g3, g4⟩ := h5 cv2 v2 h2' heq
        refine ⟨g1, g2, ?_, g4⟩
        rw [← Expr.constsResolve_congr hisoSome]
        exact g3
      · intro cv2 mI2 rP2 rules2 heq r hr
        obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv2 mI2 rP2 rules2 heq r hr
        refine ⟨g1, g2, ?_, g4, ?_⟩
        · rw [← Expr.constsResolve_congr hisoSome]
          exact g3
        · intro lvls pins hfr
          obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
          refine ⟨n1, n2, fun pin hpin => ?_, n4⟩
          obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
          refine ⟨p1, p2, ?_, p4⟩
          rw [← Expr.constsResolve_congr hisoSome]
          exact p3
      · intro cv2 v2 heq
        obtain ⟨g1, g2, g3, g4⟩ := h7 cv2 v2 heq
        refine ⟨g1, g2, ?_, g4⟩
        rw [← Expr.constsResolve_congr hisoSome]
        exact g3
    · exact hwf
  · -- val_params
    intro n ci₃ hf₃ ψ₁ ψ₂ hψ
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq] at hf₃
      exact m₀.val_params n ci₃ hf₃ ψ₁ ψ₂ hψ
    · rw [h₃] at hf₃
      obtain rfl := Option.some.inj hf₃
      exact m₀.val_params n _ h₀ ψ₁ ψ₂ hψ
  · -- has_type
    intro c₃ hc₃ φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapT_mem_corr hsw c₃ hc₃
    obtain ⟨t, ht, hd⟩ := m₀.has_type c₀ hc₀ φ
    refine ⟨t, ?_, ?_⟩
    · rw [← SwapPairT.cv_eq hpair]
      show denote m₀.cval env₃ φ 0 c₀.toConstantVal.type = some t
      rw [← hde]
      exact ht
    · rw [← SwapPairT.name_eq hpair]
      exact hd
  · -- defn_eq
    intro cv2 v2 h2 hmem2 φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapT_mem_corr hsw _ hmem2
    have hc₀eq : c₀ = .defnInfo cv2 v2 h2 := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, -, hcon, -⟩
      · rfl
      · exact nomatch hcon
    subst hc₀eq
    show denote m₀.cval env₃ φ 0 v2 = some (m₀.cval cv2.name φ)
    rw [← hde]
    exact m₀.defn_eq cv2 v2 h2 hc₀ φ
  · -- thm_ok
    intro cv2 v2 hmem2 φ
    obtain ⟨c₀, hc₀, hpair⟩ := swapT_mem_corr hsw _ hmem2
    have hc₀eq : c₀ = .thmInfo cv2 v2 := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, -, hcon, -⟩
      · rfl
      · exact nomatch hcon
    subst hc₀eq
    show denote m₀.cval env₃ φ 0 v2 = some (m₀.cval cv2.name φ)
    rw [← hde]
    exact m₀.thm_ok cv2 v2 hc₀ φ
  · -- rec_rules
    intro n cv mI rP rules hf rl hrl hfire
    rcases hcorr' n with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, hnm, -, -,
      -, -, hrecm⟩
    · rw [heq] at hf
      obtain ⟨hple, hbody⟩ := m₀.rec_rules n cv mI rP rules hf rl hrl hfire
      refine ⟨hple, ?_⟩
      intro φ d us hlenU
      obtain ⟨R, hR, hlaw⟩ := hbody φ d us hlenU
      refine ⟨R, by rw [← hde]; exact hR, ?_⟩
      intro cvj cnP cnF hctor
      have hctor₀ : env₀.find? (RecRule.ctor rl)
          = some (.ctorInfo cvj cnP cnF) :=
        hfindDown _ _ hctor (fun _ _ _ _ h => nomatch h)
      intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar
        hparN hidx hTV hTVj hfitR hfitC
      refine hlaw cvj cnP cnF hctor₀ Δ usj xs ys TV TVj restR restC
        hlenX hlenY hlenJ hlev hpar
        (fun lvls pins hn' i hi vp hvp =>
          hparN lvls pins hn' i hi vp (by rw [← hde]; exact hvp))
        hidx (by rw [hde]; exact hTV) (by rw [hde]; exact hTVj)
        hfitR hfitC
    · rw [h₃] at hf
      obtain heq2 := Option.some.inj hf
      injection heq2 with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      rw [← hnm]
      exact hrecm _ _ _ _ rfl rl hrl hfire
  · -- caps_ok
    obtain ⟨mo1, mo2⟩ := m₀.caps_ok
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcape hres hfam
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      have hf₀ := hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
      have hfC₀ := hfindDown _ _ hfC (fun _ _ _ _ h => nomatch h)
      have hfP₀ : ∀ j, j < caps.etaFields → ∃ cv2 mI2 rP2 rules2,
          env₀.find? (projFnName T j) =
            some (.recInfo cv2 mI2 rP2 rules2) := by
        intro j hj
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
        rcases hcorr' (projFnName T j) with heq |
          ⟨cv3, mI3, rP3, rules3, h₀, h₃, -⟩
        · rw [heq] at hf2
          exact ⟨cv2, mI2, rP2, rules2, hf2⟩
        · exact ⟨cv3, mI3, rP3, [], h₀⟩
      have hlaw := mo1 T cvT caps hf₀ hcape hres ⟨hCres, ⟨cvC, hfC₀⟩, hfP₀⟩
      intro φ d Δ us xs TV rest B hlen hTV hfit hB hrhsT
      have hTV₀ : denote m₀.cval env₀ φ d
          (cvT.type.instantiateLevelParams cvT.levelParams us)
          = some TV := by
        rw [hde]; exact hTV
      have h1 := hlaw φ d Δ us xs TV rest B hlen hTV₀ hfit hB
        (by simp only [hlpAll]; exact hrhsT)
      simp only [hlpAll] at h1
      exact h1
    · intro T cvT caps hf hcapu hres
      have hf₀ := hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
      have hlaw := mo2 T cvT caps hf₀ hcapu hres
      intro φ d Δ us xs TV rest B B' hlen hTV hfit hB hB'
      exact hlaw φ d Δ us xs TV rest B B' hlen (by rw [hde]; exact hTV)
        hfit hB hB'
  · -- ctor_residual
    intro T cvT caps cvC hfT hcape hTres hCres hfC
    exact m₀.ctor_residual T cvT caps cvC
      (hfindDown _ _ hfT (fun _ _ _ _ h => nomatch h)) hcape hTres hCres
      (hfindDown _ _ hfC (fun _ _ _ _ h => nomatch h))
  · -- proj_ok
    obtain ⟨p1, p2⟩ := m₀.proj_ok
    refine ⟨?_, ?_⟩
    · intro n entry hf hnat'
      obtain ⟨he, h1, h2⟩ := p1 n entry
        (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)) hnat'
      exact ⟨he, hfindUp _ _ h1 (fun _ _ _ _ h => by simp [psigmaA] at h),
        hfindUp _ _ h2 (fun _ _ _ _ h => by simp [psigmaMkA] at h)⟩
    · intro i entry hf
      exact p2 i entry (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h))
  · -- rec_ctors
    intro n cv mI rP rules hf r hr
    rcases hcorr' n with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, -, -, -, -,
      hctors, -⟩
    · rw [heq] at hf
      obtain ⟨cvj, cnP, cnF, hc⟩ := m₀.rec_ctors n cv mI rP rules hf r hr
      exact ⟨cvj, cnP, cnF, hfindUp _ _ hc (fun _ _ _ _ h => nomatch h)⟩
    · rw [h₃] at hf
      obtain heq2 := Option.some.inj hf
      injection heq2 with e1 e2 e3 e4
      subst e4
      exact hctors r hr
  · -- eq_law
    intro hf
    have hf₀ : env₀.find? eqName = some eqA :=
      hfindDown _ _ hf (fun _ _ _ _ h => by simp [eqA] at h)
    exact m₀.eq_law hf₀
  · -- basis_pinned
    intro n ci hf hres
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, hnm, hnres, -⟩
    · rw [heq] at hf
      exact m₀.basis_pinned n ci hf hres
    · rw [hnm] at hnres
      rw [hnres] at hres
      exact nomatch hres
  · -- nat_ops
    intro c hc cv v hint hf
    have hf₀ : env₀.find? c = some (.defnInfo cv v hint) :=
      hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
    obtain ⟨hg, heqs⟩ := m₀.nat_ops c hc cv v hint hf₀
    refine ⟨by rw [← hguardAll c]; exact hg, ?_⟩
    intro eq heq φ
    obtain ⟨L, R, hL, hR, hD⟩ := heqs eq heq φ
    exact ⟨L, R, by rw [← hde]; exact hL, by rw [← hde]; exact hR, hD⟩
  · -- div_mod
    intro c hc cv v hint hf
    have hf₀ : env₀.find? c = some (.defnInfo cv v hint) :=
      hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
    obtain ⟨hg, heqs⟩ := m₀.div_mod c hc cv v hint hf₀
    exact ⟨by rw [← hguardAll c]; exact hg, heqs⟩
  · -- reduce_ops
    intro c hc cv hf hpin
    have hf₀ : env₀.find? c = some (.axiomInfo cv) :=
      hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
    obtain ⟨hsome, hid⟩ := m₀.reduce_ops c hc cv hf₀ hpin
    refine ⟨?_, hid⟩
    rw [← hisoSome]
    exact hsome

/-- The valuation is untouched by the swap — definitionally. -/
theorem EnvTT.swap_cval {env₀ env₃ : Env} (m₀ : EnvTT env₀)
    (hsw : SwapListT env₃ m₀.cval env₀.consts env₃.consts) :
    (m₀.swap hsw).cval = m₀.cval := rfl

/-! ## Revaluing a fresh name

The denotation reads the valuation only at *stored* constants, so a
model's valuation may be changed at an unstored name freely.  The
projection install needs this (§24's `Proj.lean` row): the
`proj_i.iota` kit's checker runs happened at the *base* environment,
before the projection function was stored, while the bottom's `hro`
identifies `cval (projFnName T i)` with the model's — so the bottom
must run at the base environment under the *aliased* valuation.  No
set-model counterpart is missing: `interpExpr` has the same blindness,
but the model's per-rule lemma (`proj_rule_eq`) bridges the base and
extended environments internally instead. -/

/-- Overwrite a valuation at one name. -/
def cvalSetC (cval : TConstVal) (n₀ : Name) (v : VExpr) : TConstVal :=
  fun c ψ => if c = n₀ then v else cval c ψ

theorem cvalSetC_ne {cval : TConstVal} {n₀ : Name} {v : VExpr} {c : Name}
    (h : c ≠ n₀) : cvalSetC cval n₀ v c = cval c := by
  funext ψ; simp [cvalSetC, h]

theorem cvalSetC_self {cval : TConstVal} {n₀ : Name} {v : VExpr}
    {ψ : Name → Nat} : cvalSetC cval n₀ v n₀ ψ = v := by
  simp [cvalSetC]

set_option maxHeartbeats 3200000 in
/-- Revalue one fresh, unreserved name by an arbitrary closed value:
the invariant is untouched, because nothing stored reads it. -/
def EnvTT.revalue {env : Env} (m : EnvTT env) (n₀ : Name) (v : VExpr)
    (hfresh : env.find? n₀ = none)
    (hnres : reservedBasisNames.contains n₀ = false)
    (hvc : VExpr.Closed v) :
    EnvTT env := by
  have hag : ∀ c, c ≠ n₀ → cvalSetC m.cval n₀ v c = m.cval c :=
    fun c hc => cvalSetC_ne hc
  have hagE : ∀ nn (ci : ConstantInfo), env.find? nn = some ci →
      m.cval nn = cvalSetC m.cval n₀ v nn := by
    intro nn ci hf
    refine (hag nn ?_).symm
    intro he
    rw [he, hfresh] at hf
    exact nomatch hf
  have hagS : ∀ nn, (env.find? nn).isSome = true →
      m.cval nn = cvalSetC m.cval n₀ v nn := by
    intro nn hnn
    cases hf : env.find? nn with
    | none => rw [hf] at hnn; exact nomatch hnn
    | some ci => exact hagE nn ci hf
  have hlit : LitAgree env m.cval (cvalSetC m.cval n₀ v) :=
    LitAgree.of_fresh (c₀ := .axiomInfo ⟨n₀, [], .sort .zero⟩) hfresh
      (fun n hn => (hag n hn).symm)
  have hdc : ∀ (φ : Name → Nat) (d : Nat) (e : Expr),
      denote (cvalSetC m.cval n₀ v) env φ d e = denote m.cval env φ d e :=
    fun φ d e => (denote_cval_congr hagE hlit.nat hlit.succ hlit.sol
      hlit.nil hlit.cons hlit.char hlit.ofn d e).symm
  have hne : ∀ c ∈ env.consts, c.name ≠ n₀ := by
    have h0 := hfresh
    rw [Env.find?, List.find?_eq_none] at h0
    intro c hc h
    exact h0 c hc (by simp [h])
  refine
    { cval := cvalSetC m.cval n₀ v
      cval_closed := ?_
      wf := m.wf
      val_params := ?_
      has_type := ?_
      defn_eq := ?_
      thm_ok := ?_
      empty_pinned := ?_
      rec_rules := ?_
      caps_ok := ?_
      ctor_residual := m.ctor_residual
      proj_ok := m.proj_ok
      rec_ctors := m.rec_ctors
      eq_law := ?_
      basis_pinned := ?_
      nat_ops := ?_
      div_mod := ?_
      reduce_ops := ?_ }
  · -- cval_closed
    intro n ψ
    by_cases hn : n = n₀
    · subst hn
      rw [cvalSetC_self]
      exact hvc
    · rw [show cvalSetC m.cval n₀ v n = m.cval n from hag n hn]
      exact m.cval_closed n ψ
  · -- val_params
    intro n ci hf φ₁ φ₂ hψ
    rw [← hagE n ci hf]
    exact m.val_params n ci hf φ₁ φ₂ hψ
  · -- has_type
    intro c hc φ
    obtain ⟨t, ht, hd⟩ := m.has_type c hc φ
    refine ⟨t, ?_, ?_⟩
    · show denote (cvalSetC m.cval n₀ v) env φ 0 c.toConstantVal.type
        = some t
      rw [hdc]
      exact ht
    · rw [show cvalSetC m.cval n₀ v c.name = m.cval c.name from
        hag c.name (hne c hc)]
      exact hd
  · -- defn_eq
    intro cv value hint hmem φ
    show denote (cvalSetC m.cval n₀ v) env φ 0 value = some _
    rw [hdc,
      show cvalSetC m.cval n₀ v cv.name = m.cval cv.name from
        hag cv.name (hne _ hmem)]
    exact m.defn_eq cv value hint hmem φ
  · -- thm_ok
    intro cv value hmem φ
    show denote (cvalSetC m.cval n₀ v) env φ 0 value = some _
    rw [hdc,
      show cvalSetC m.cval n₀ v cv.name = m.cval cv.name from
        hag cv.name (hne _ hmem)]
    exact m.thm_ok cv value hmem φ
  · -- empty_pinned
    intro ψ
    rw [show cvalSetC m.cval n₀ v emptyName = m.cval emptyName from
      hag emptyName (fun he => by
        rw [← he] at hnres
        exact absurd hnres (by decide))]
    exact m.empty_pinned ψ
  · -- rec_rules
    intro n cv mI rP rules hf rl hrl hfire
    obtain ⟨hple, hbody⟩ := m.rec_rules n cv mI rP rules hf rl hrl hfire
    refine ⟨hple, ?_⟩
    intro φ d us hlenU
    obtain ⟨R, hR, hlaw⟩ := hbody φ d us hlenU
    refine ⟨R, by rw [hdc]; exact hR, ?_⟩
    intro cvj cnP cnF hctor
    intro Δ usj xs ys TV TVj restR restC hlenX hlenY hlenJ hlev hpar
      hparN hidx hTV hTVj hfitR hfitC
    rw [← hagE n _ hf, ← hagE _ _ hctor] at *
    exact hlaw cvj cnP cnF hctor Δ usj xs ys TV TVj restR restC hlenX
      hlenY hlenJ hlev hpar
      (fun lvls pins hn' i hi vp hvp =>
        hparN lvls pins hn' i hi vp (by rw [hdc]; exact hvp))
      hidx (by rw [← hdc]; exact hTV) (by rw [← hdc]; exact hTVj)
      hfitR hfitC
  · -- caps_ok
    obtain ⟨mo1, mo2⟩ := m.caps_ok
    refine ⟨?_, ?_⟩
    · intro T cvT caps hf hcape hres hfam
      have hlaw := mo1 T cvT caps hf hcape hres hfam
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      intro φ d Δ us xs TV rest B hlen hTV hfit hBt hfabT
      have hproj : ∀ j ∈ List.range caps.etaFields,
          VExpr.mkAppN (cvalSetC m.cval n₀ v (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
            (xs ++ [B])
          = VExpr.mkAppN (m.cval (projFnName T j)
            (Level.substFn φ (levelParamsAt env (projFnName T j)) us))
            (xs ++ [B]) := by
        intro j hj
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ :=
          hfP j (List.mem_range.mp hj)
        rw [← hagE _ _ hf2]
      rw [← hagE T _ hf] at hBt hfabT
      rw [← hagE _ _ hfC] at hfabT ⊢
      rw [List.map_congr_left hproj] at hfabT ⊢
      exact hlaw φ d Δ us xs TV rest B hlen (by rw [← hdc]; exact hTV)
        hfit hBt hfabT
    · intro T cvT caps hf hcapu hres
      have hlaw := mo2 T cvT caps hf hcapu hres
      intro φ d Δ us xs TV rest B B' hlen hTV hfit hBt hBt'
      rw [← hagE T _ hf] at hBt hBt'
      exact hlaw φ d Δ us xs TV rest B B' hlen (by rw [← hdc]; exact hTV)
        hfit hBt hBt'
  · -- eq_law
    intro hf
    have hlaw := m.eq_law hf
    intro ψ Δ A a b hA ha hb
    rw [← hagE eqName _ hf]
    exact hlaw ψ Δ A a b hA ha hb
  · -- basis_pinned
    intro n ci hf hres
    refine ⟨(m.basis_pinned n ci hf hres).1, ?_⟩
    intro t ψ hpin
    rw [← hagE n ci hf]
    exact (m.basis_pinned n ci hf hres).2 t ψ hpin
  · -- nat_ops
    intro c hc cv vl hint hf
    obtain ⟨hg, heqs⟩ := m.nat_ops c hc cv vl hint hf
    have hnat : m.cval natName = cvalSetC m.cval n₀ v natName := by
      refine hagS natName ?_
      simp only [natOpGuard, Bool.and_eq_true] at hg
      have h0 := hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      have h1 := h0.1.1
      revert h1
      cases env.find? natName <;> simp [natIndOk]
    refine ⟨hg, ?_⟩
    intro eq heq φ
    obtain ⟨L, R, hL, hR, hD⟩ := heqs eq heq φ
    refine ⟨L, R, by rw [hdc]; exact hL, by rw [hdc]; exact hR, ?_⟩
    rw [← hnat]
    exact hD
  · -- div_mod
    intro c hc cv vl hint hf
    obtain ⟨hg, heqs⟩ := m.div_mod c hc cv vl hint hf
    have hagS' : ∀ nn, (env.find? nn).isSome = true →
        m.cval nn = cvalSetC m.cval n₀ v nn := hagS
    obtain ⟨hdep, hz, hs, hbool⟩ := divModNames_agree hagS' hg
    obtain ⟨hT, hF⟩ := hbool (by simpa using hc)
    have hnat : m.cval natName = cvalSetC m.cval n₀ v natName := by
      simp only [natOpGuard, Bool.and_eq_true] at hg
      have h0 := hg.1.1
      simp only [natLitSupported, Bool.and_eq_true] at h0
      refine hagS natName ?_
      have h1 := h0.1.1
      revert h1
      cases env.find? natName <;> simp [natIndOk]
    refine ⟨hg, ?_⟩
    intro φ Δ x y hx hy
    rw [← hnat] at hx hy
    have hcl := heqs φ Δ x y hx hy
    simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natSubName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide)] at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natSubName (by decide), hdep natBleName (by decide),
        hdep natModName (by decide)] at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natBleName (by decide), hdep natModName (by decide),
        hdep natGcdName (by decide)] at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natAddName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide), hdep natLandName (by decide)]
        at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natAddName (by decide), hdep natSubName (by decide),
        hdep natMulName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natModName (by decide),
        hdep natLorName (by decide)] at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natAddName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natModName (by decide), hdep natXorName (by decide)]
        at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natSubName (by decide), hdep natMulName (by decide),
        hdep natBleName (by decide), hdep natShiftLeftName (by decide)]
        at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natSubName (by decide), hdep natBleName (by decide),
        hdep natDivName (by decide), hdep natShiftRightName (by decide)]
        at hcl ⊢
      exact hcl
    · simp only [DivModClausesTT, hz, hs, hT, hF,
        hdep natBleName (by decide), hdep natDivName (by decide),
        hdep natLog2Name (by decide)] at hcl ⊢
      exact hcl
  · -- reduce_ops
    intro c hc cv hf hpin
    obtain ⟨hsome, hid⟩ := m.reduce_ops c hc cv hf hpin
    refine ⟨hsome, ?_⟩
    intro φ Δ X hX
    rw [← hagS _ hsome] at hX
    rw [← hagE c _ hf]
    exact hid φ Δ X hX

/-- The revalued model's valuation, by construction. -/
theorem EnvTT.revalue_cval {env : Env} (m : EnvTT env) (n₀ : Name)
    (v : VExpr) (hfresh : env.find? n₀ = none)
    (hnres : reservedBasisNames.contains n₀ = false)
    (hvc : VExpr.Closed v) :
    (m.revalue n₀ v hfresh hnres hvc).cval = cvalSetC m.cval n₀ v := rfl

end Setlec.TTVerify
