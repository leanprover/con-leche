import Setlec.Model.Extend.Sibs

/-!
# GroupSwap — the rule-list swap for a recursor *group*

A block's recursors are provisioned rule-less together and installed
together (mutual and nested blocks: rule right-hand sides mention each
other).  `extend_rules_eq` transports an `EnvModel` from the
provisional environment to the one with all the checked rule lists
attached: the environments' constant lists are pointwise equal except
that rule-less recursors gain their rules (`SwapPair`), and each
rule-carrying side supplies its own obligations (`ConstWF`, stored
rule constructors, `RecMemberOk`).  Generalizes the single-head
`extend_rec_swap`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Pointwise swap relation: equal constants, or a rule-less recursor
paired with the same recursor carrying its checked rules, together
with the rule-carrying side's obligations. -/
def SwapPair (env₃ : Env) (val : ConstVal V) (c₀ c₃ : ConstantInfo) :
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
    RecMemberOk (V := V) env₃ val (.recInfo cv mI rP rules)

theorem SwapPair.name_eq {env₃ : Env} {val : ConstVal V}
    {c₀ c₃ : ConstantInfo} (h : SwapPair env₃ val c₀ c₃) :
    c₀.name = c₃.name := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -⟩
  · rfl
  · rfl

theorem SwapPair.cv_eq {env₃ : Env} {val : ConstVal V}
    {c₀ c₃ : ConstantInfo} (h : SwapPair env₃ val c₀ c₃) :
    c₀.toConstantVal = c₃.toConstantVal := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -⟩
  · rfl
  · rfl

/-- Pointwise swap of two constant lists. -/
inductive SwapList (env₃ : Env) (val : ConstVal V) :
    List ConstantInfo → List ConstantInfo → Prop
  | nil : SwapList env₃ val [] []
  | cons {c₀ c₃ : ConstantInfo} {rest₀ rest₃ : List ConstantInfo} :
      SwapPair env₃ val c₀ c₃ → SwapList env₃ val rest₀ rest₃ →
      SwapList env₃ val (c₀ :: rest₀) (c₃ :: rest₃)

/-- The lookup correspondence of a pointwise swap. -/
theorem swap_find?_corr {env₃ : Env} {val : ConstVal V} :
    ∀ {consts₀ consts₃ : List ConstantInfo},
    SwapList env₃ val consts₀ consts₃ →
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
      RecMemberOk (V := V) env₃ val (.recInfo cv mI rP rules) := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro n; exact Or.inl rfl
  | @cons c₀ c₃ rest₀ rest₃ hpair hrest ih =>
    intro n
    show (Env.mk (c₃ :: rest₃)).find? n = (Env.mk (c₀ :: rest₀)).find? n ∨ _
    by_cases hn : c₃.name = n
    · have hn₀ : c₀.name = n := by rw [SwapPair.name_eq hpair, hn]
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
        rw [SwapPair.name_eq hpair]
        exact hn
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n =
          (Env.mk rest₃).find? n := by
        show (c₃ :: rest₃).find? (·.name == n) =
          rest₃.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n =
          (Env.mk rest₀).find? n := by
        show (c₀ :: rest₀).find? (·.name == n) =
          rest₀.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn₀])]
      rw [h₃, h₀]
      exact ih n

/-- Member correspondence (right to left). -/
theorem swap_mem_corr {env₃ : Env} {val : ConstVal V}
    {consts₀ consts₃ : List ConstantInfo}
    (hsw : SwapList env₃ val consts₀ consts₃) :
    ∀ c₃ ∈ consts₃, ∃ c₀ ∈ consts₀, SwapPair env₃ val c₀ c₃ := by
  induction hsw with
  | nil => intro c₃ hc; exact nomatch hc
  | @cons a b rest₀ rest₃ hpair hrest ih =>
    intro c₃ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨a, List.mem_cons_self, hpair⟩
    · obtain ⟨c₀, hc₀, hp⟩ := ih c₃ hc
      exact ⟨c₀, List.mem_cons_of_mem _ hc₀, hp⟩

/-- Member correspondence (left to right). -/
theorem swap_mem_corr' {env₃ : Env} {val : ConstVal V}
    {consts₀ consts₃ : List ConstantInfo}
    (hsw : SwapList env₃ val consts₀ consts₃) :
    ∀ c₀ ∈ consts₀, ∃ c₃ ∈ consts₃, SwapPair env₃ val c₀ c₃ := by
  induction hsw with
  | nil => intro c₀ hc; exact nomatch hc
  | @cons a b rest₀ rest₃ hpair hrest ih =>
    intro c₀ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨b, List.mem_cons_self, hpair⟩
    · obtain ⟨c₃, hc₃, hp⟩ := ih c₀ hc
      exact ⟨c₃, List.mem_cons_of_mem _ hc₃, hp⟩

set_option maxHeartbeats 1600000 in
/-- The group rule-list swap: an `EnvModel` of the provisional
(rule-less) environment transports to the environment with the checked
rule lists attached, given the pointwise swap with its obligations. -/
theorem extend_rules_eq {env₀ env₃ : Env} (m₀ : EnvModel V env₀)
    (hsw : SwapList env₃ m₀.val env₀.consts env₃.consts) :
    ∃ m₃ : EnvModel V env₃, ∀ (n : Name) (ψ : Name → Nat),
      m₃.val n ψ = m₀.val n ψ := by
  have hcorr := swap_find?_corr hsw
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
        RecMemberOk (V := V) env₃ m₀.val
          (.recInfo cv mI rP rules) := hcorr
  have henvLev : ∀ n, (env₀.find? n).map
      (fun ci => ci.toConstantVal.levelParams) =
      (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      rfl
  have hisoSome : ∀ n, (env₀.find? n).isSome = (env₃.find? n).isSome := by
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      rfl
  have hnat : natLitSupported env₀ = natLitSupported env₃ := by
    unfold natLitSupported
    have hone : ∀ (chk : Option ConstantInfo → Bool) (n : Name),
        (∀ cv mI rP rules,
          chk (some (.recInfo cv mI rP rules)) = false) →
        chk (env₀.find? n) = chk (env₃.find? n) := by
      intro chk n hrec
      rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃, hrec, hrec]
    rw [hone natIndOk natName (fun _ _ _ _ => rfl),
      hone natZeroOk natZeroName (fun _ _ _ _ => rfl),
      hone natSuccOk natSuccName (fun _ _ _ _ => rfl)]
  have htoCV : ∀ n, (env₀.find? n).map ConstantInfo.toConstantVal =
      (env₃.find? n).map ConstantInfo.toConstantVal := by
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  have hstr : strLitSupported env₀ = strLitSupported env₃ :=
    strLitSupported_env_ext htoCV hnat
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val env₃ ψ e = interpClosed V m₀.val env₀ ψ e :=
    fun e ψ => (interp_env_ext henvLev hnat hstr e 0 (rho0 V)).symm
  have hAtrans : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val env₀ ψ d ρ e → AnnotOk V m₀.val env₃ ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henvLev hnat hstr e d ρ h
  -- shape-based lookup transports
  have hfindDown : ∀ (n : Name) (ci : ConstantInfo),
      env₃.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₀.find? n = some ci := by
    intro n ci hf hnr
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [← heq]
      exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP rules)
  have hfindUp : ∀ (n : Name) (ci : ConstantInfo),
      env₀.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₃.find? n = some ci := by
    intro n ci hf hnr
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
      exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP [])
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun n ψ => rfl⟩
  · -- wf
    intro c₃ hc₃
    obtain ⟨c₀, hc₀, hpair⟩ := swap_mem_corr hsw c₃ hc₃
    rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl, -, -,
      hwf, -, -⟩
    · -- unchanged member: transport the well-formedness
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := m₀.wf _ hc₀
      refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_⟩
      · rw [← Expr.constsResolve_congr hisoSome]
        exact h3
      · intro cv2 v2 h2 heq
        obtain ⟨g1, g2, g3, g4⟩ := h5 cv2 v2 h2 heq
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
  · -- mem_type
    intro c₃ hc₃ ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swap_mem_corr hsw c₃ hc₃
    obtain ⟨t, ht, hmem⟩ := m₀.mem_type c₀ hc₀ ψ
    refine ⟨t, ?_, ?_⟩
    · rw [hitrans, ← SwapPair.cv_eq hpair]
      exact ht
    · rw [← SwapPair.name_eq hpair]
      exact hmem
  · -- defn_eq
    intro cv2 v2 h2 hmem2 ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swap_mem_corr hsw _ hmem2
    have hc₀eq : c₀ = .defnInfo cv2 v2 h2 := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, -, hcon, -⟩
      · rfl
      · exact nomatch hcon
    subst hc₀eq
    rw [hitrans]
    exact m₀.defn_eq cv2 v2 h2 hc₀ ψ
  · -- thm_ok
    intro cv2 v2 hmem2 ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swap_mem_corr hsw _ hmem2
    have hc₀eq : c₀ = .thmInfo cv2 v2 := by
      rcases hpair with rfl | ⟨cv, mI, rP, rules, -, hcon, -⟩
      · rfl
      · exact nomatch hcon
    subst hc₀eq
    obtain ⟨hde, hAv⟩ := m₀.thm_ok cv2 v2 hc₀ ψ
    exact ⟨by rw [hitrans]; exact hde, hAtrans _ ψ 0 (rho0 V) hAv⟩
  · -- annot_ok
    intro c₃ hc₃ ψ
    obtain ⟨c₀, hc₀, hpair⟩ := swap_mem_corr hsw c₃ hc₃
    obtain ⟨hA1, hA2⟩ := m₀.annot_ok c₀ hc₀ ψ
    constructor
    · rw [← SwapPair.cv_eq hpair]
      exact hAtrans _ ψ 0 (rho0 V) hA1
    · intro cv2 v2 h2 heq
      have hc₀eq : c₀ = .defnInfo cv2 v2 h2 := by
        rcases hpair with rfl | ⟨cv, mI, rP, rules, -, hcon, -⟩
        · rw [heq]
        · rw [heq] at hcon
          exact nomatch hcon
      exact hAtrans _ ψ 0 (rho0 V) (hA2 cv2 v2 h2 hc₀eq)
  · -- ind_ok
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := m₀.ind_ok
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, i7⟩
    · intro cv caps hfp
      exact i1 cv caps (hfindDown _ _ hfp (fun _ _ _ _ h => nomatch h))
    · intro cv nP' nF' hfp
      exact i2 cv nP' nF'
        (hfindDown _ _ hfp (fun _ _ _ _ h => nomatch h))
    · intro cv caps hfp
      exact i3 cv caps (hfindDown _ _ hfp (fun _ _ _ _ h => nomatch h))
    · intro n ci hfp hbasis hres2
      rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, hnm,
        hres, -⟩
      · rw [heq] at hfp
        exact i4 n ci hfp hbasis hres2
      · rw [hnm] at hres
        rw [hres] at hres2
        exact nomatch hres2
    · obtain ⟨b1, b2, b3, b4⟩ := i5
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cv mI' rP' rules hfp
        rcases hcorr' (eqName.str "rec") with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
        · rw [heq] at hfp
          obtain ⟨f1, f2⟩ := b1 cv mI' rP' rules hfp
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [eqA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [eqReflA] at h)⟩
        · obtain ⟨f1, f2⟩ := b1 cv2 mI2 rP2 [] h₀
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [eqA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [eqReflA] at h)⟩
      · intro cv mI' rP' rules hfp
        rcases hcorr' (natName.str "rec") with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
        · rw [heq] at hfp
          obtain ⟨f1, f2, f3⟩ := b2 cv mI' rP' rules hfp
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [natA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [natZeroA] at h),
            hfindUp _ _ f3 (fun _ _ _ _ h => by
              simp [natSuccA] at h)⟩
        · obtain ⟨f1, f2, f3⟩ := b2 cv2 mI2 rP2 [] h₀
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [natA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [natZeroA] at h),
            hfindUp _ _ f3 (fun _ _ _ _ h => by
              simp [natSuccA] at h)⟩
      · intro cv mI' rP' rules hfp
        rcases hcorr' (psigmaName.str "rec") with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
        · rw [heq] at hfp
          obtain ⟨f1, f2⟩ := b3 cv mI' rP' rules hfp
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [psigmaA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [psigmaMkA] at h)⟩
        · obtain ⟨f1, f2⟩ := b3 cv2 mI2 rP2 [] h₀
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [psigmaA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [psigmaMkA] at h)⟩
      · intro cv mI' rP' rules hfp
        rcases hcorr' (punitName.str "rec") with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, -⟩
        · rw [heq] at hfp
          obtain ⟨f1, f2⟩ := b4 cv mI' rP' rules hfp
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [punitA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [punitUnitA] at h)⟩
        · obtain ⟨f1, f2⟩ := b4 cv2 mI2 rP2 [] h₀
          exact ⟨hfindUp _ _ f1 (fun _ _ _ _ h => by
              simp [punitA] at h),
            hfindUp _ _ f2 (fun _ _ _ _ h => by
              simp [punitUnitA] at h)⟩
    · intro n cv mI' rP' rules hfp r hr
      rcases hcorr' n with heq | ⟨cv2, mI2, rP2, rules2, h₀,
        h₃, -, -, -, -, hctors, -⟩
      · rw [heq] at hfp
        obtain ⟨cvj, cnP, cnF, hc⟩ := i6 n cv mI' rP' rules hfp
          r hr
        exact ⟨cvj, cnP, cnF, hfindUp _ _ hc
          (fun _ _ _ _ h => nomatch h)⟩
      · rw [h₃] at hfp
        obtain heq2 := Option.some.inj hfp
        injection heq2 with e1 e2 e3 e4
        subst e4
        exact hctors r hr
  · -- rec_rules
    intro n cvR mI' rP' rules hfp r hr
    rcases hcorr' n with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃,
      hnm, -, -, -, -, hrecm⟩
    · rw [heq] at hfp
      obtain ⟨hA, hle, hple, hpinsLen, hfold⟩ :=
        m₀.rec_rules n cvR mI' rP' rules hfp r hr
      refine ⟨fun ψ => hAtrans _ ψ 0 (rho0 V) (hA ψ), hle, hple,
        hpinsLen, ?_⟩
      intro cvj cnP cnF hfj hfire
      have hfj₀ : env₀.find? (RecRule.ctor r) =
          some (.ctorInfo cvj cnP cnF) :=
        hfindDown _ _ hfj (fun _ _ _ _ h => nomatch h)
      obtain ⟨fvms, bL, hparts, hwfF, hlenF, hres, hψ⟩ :=
        hfold cvj cnP cnF hfj₀ hfire
      have hsome : ∀ nn : Name, (env₀.find? nn).isSome =
          (env₃.find? nn).isSome := by
        intro nn
        have h0 := henvLev nn
        cases h1 : env₀.find? nn <;> cases h2 : env₃.find? nn <;>
          rw [h1, h2] at h0 <;> simp_all
      refine ⟨fvms, bL, hparts, hwfF, hlenF, ?_, ?_⟩
      · rw [← Expr.constsResolve_congr hsome]
        exact hres
      · intro ψ
        obtain ⟨hAL, Rv, hLi, hRi⟩ := hψ ψ
        exact ⟨hAtrans _ ψ 0 (rho0 V) hAL, Rv,
          by rw [hitrans]; exact hLi,
          by rw [hitrans]; exact hRi⟩
    · rw [h₃] at hfp
      obtain heq2 := Option.some.inj hfp
      have hrecm' := hrecm cvR mI' rP' rules heq2 r hr
      rw [show (ConstantInfo.recInfo cv2 mI2 rP2 rules2).name =
        cv2.name from rfl, hnm] at hrecm'
      exact hrecm'
  · -- proj_ok: the swap moves only recursor rule lists
    refine ProjOk.env_swap (env₁ := env₀) ?_ m₀.proj_ok
    intro n
    rcases hcorr' n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · exact Or.inl heq
    · exact Or.inr ⟨cv, mI, rP, [], rules, h₀, h₃⟩
  · -- modeled_ok
    obtain ⟨mo1, mo2, mo3, mo4, mo5⟩ := m₀.modeled_ok
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n cv caps hf hres
      obtain ⟨hms, hveq⟩ := mo1 n cv caps
        (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)) hres
      refine ⟨?_, hveq⟩
      rw [← hisoSome]
      exact hms
    · intro n cv cnP' cnF' hf hres
      obtain ⟨hms, hveq⟩ := mo2 n cv cnP' cnF'
        (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)) hres
      refine ⟨?_, hveq⟩
      rw [← hisoSome]
      exact hms
    · intro T j cv3 mI3 rP3 rules3 hf
      rcases hcorr' (projFnName T j) with heq | ⟨cv2, mI2, rP2, rules2, h₀, h₃, hnm, -, hshape, -⟩
      · rw [heq] at hf
        obtain ⟨hms, hveq⟩ := mo3 T j cv3 mI3 rP3 rules3 hf
        refine ⟨?_, hveq⟩
        rw [← hisoSome]
        exact hms
      · rw [hnm] at hshape
        exact absurd hshape (by simp [projFnName, Name.isProjFnShape])
    · intro T cvT caps hf hcape hres
      obtain ⟨hmsC, hmsP, hlaw⟩ := mo4 T cvT caps
        (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)) hcape hres
      refine ⟨?_, ?_, ?_⟩
      · rw [← hisoSome]
        exact hmsC
      · intro j hj
        rw [← hisoSome]
        exact hmsP j hj
      · intro φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hfit
        exact hlaw φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx
          (TeleFit.env_levelext (fun n' => (henvLev n').symm) hnat.symm
            hstr.symm hfit)
    · intro T cvT caps hf hcapu hres
      have hlaw := mo5 T cvT caps
        (hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)) hcapu hres
      intro φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy hfit
      exact hlaw φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy
        (TeleFit.env_levelext (fun n' => (henvLev n').symm) hnat.symm
          hstr.symm hfit)
  · -- nat_ops
    intro c hc cv v hint hf
    have hf₀ : env₀.find? c = some (.defnInfo cv v hint) :=
      hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
    obtain ⟨hg, heqs⟩ := m₀.nat_ops c hc cv v hint hf₀
    obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
    have hie : ∀ (e : Expr) (ψ : Name → Nat) (dd : Nat) (ρ : Nat → V),
        interpExpr V m₀.val env₃ ψ dd ρ e =
        interpExpr V m₀.val env₀ ψ dd ρ e :=
      fun e ψ dd ρ => (interp_env_ext henvLev hnat hstr e dd ρ).symm
    refine ⟨natOpGuard_intro (by rw [← hnat]; exact hs) ?_ ?_, ?_⟩
    · intro n' hn'
      obtain ⟨cvn, vn, hintn, hfn, hlpn⟩ := hdeps n' hn'
      exact ⟨cvn, vn, hintn,
        hfindUp _ _ hfn (fun _ _ _ _ h => nomatch h), hlpn⟩
    · intro hcb
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb
      have conv : ∀ (nb : Name) (ci : ConstantInfo),
          env₀.find? nb = some ci →
          ci.toConstantVal.levelParams = [] →
          ∃ ci₂, env₃.find? nb = some ci₂ ∧
            ci₂.toConstantVal.levelParams = [] := by
        intro nb ci hfb hlpb
        have h2 := henvLev nb
        rw [hfb] at h2
        cases hf2 : env₃.find? nb with
        | none => rw [hf2] at h2; exact nomatch h2
        | some ci₂ =>
          rw [hf2] at h2
          simp only [Option.map_some, Option.some.injEq] at h2
          exact ⟨ci₂, rfl, by rw [← h2, hlpb]⟩
      exact ⟨conv _ _ hT hlpT, conv _ _ hF hlpF⟩
    · intro eq heq ψ x y hxy
      rw [hie eq.1 ψ 2 _, hie eq.2 ψ 2 _]
      refine heqs eq heq ψ x y ?_
      intro T hT
      refine hxy T ?_
      rw [hie]
      exact hT
  · -- div_mod (value-level equations; guard and lookups transported)
    intro c hc cv v hint hf
    have hf₀ : env₀.find? c = some (.defnInfo cv v hint) :=
      hfindDown _ _ hf (fun _ _ _ _ h => nomatch h)
    obtain ⟨hg, heqs⟩ := m₀.div_mod c hc cv v hint hf₀
    obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
    refine ⟨natOpGuard_intro (by rw [← hnat]; exact hs) ?_ ?_, heqs⟩
    · intro n' hn'
      obtain ⟨cvn, vn, hintn, hfn, hlpn⟩ := hdeps n' hn'
      exact ⟨cvn, vn, hintn,
        hfindUp _ _ hfn (fun _ _ _ _ h => nomatch h), hlpn⟩
    · intro hcb
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb
      have conv : ∀ (nb : Name) (ci : ConstantInfo),
          env₀.find? nb = some ci →
          ci.toConstantVal.levelParams = [] →
          ∃ ci₂, env₃.find? nb = some ci₂ ∧
            ci₂.toConstantVal.levelParams = [] := by
        intro nb ci hfb hlpb
        have h2 := henvLev nb
        rw [hfb] at h2
        cases hf2 : env₃.find? nb with
        | none => rw [hf2] at h2; exact nomatch h2
        | some ci₂ =>
          rw [hf2] at h2
          simp only [Option.map_some, Option.some.injEq] at h2
          exact ⟨ci₂, rfl, by rw [← h2, hlpb]⟩
      exact ⟨conv _ _ hT hlpT, conv _ _ hF hlpF⟩


end Setlec
