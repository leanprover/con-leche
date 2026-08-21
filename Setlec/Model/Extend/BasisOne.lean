import Setlec.Model.Extend.Sibs

/-!
# BasisOne — split out of `Setlec.Model.Extend`

`extend_basis_one`: extend a model by one pinned basis constant
with a hand-supplied value.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one pinned basis constant with a hand-supplied
value.  The membership and annotation facts are stated over the *old*
valuation (basis types only mention previously installed constants);
the conclusion exposes the new valuation's equations so block
installation can chain. -/
theorem extend_basis_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (v₀ : (Name → Nat) → V)
    (hfind' : env.find? ci.name = none)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hnotdefn : ∀ cv2 value2, ci ≠ .defnInfo cv2 value2)
    (hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧ v₀ ψ ∈ˢ T)
    (hparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → v₀ ψ₁ = v₀ ψ₂)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) ci.toConstantVal.type)
    (hnewty : ∀ cv caps, ci = .indInfo cv caps → ci.name = psigmaName →
      cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairTyFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewmk : ∀ cv nP nF, ci = .ctorInfo cv nP nF → ci.name = psigmaMkName →
      nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairMkFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewunit : ∀ cv caps, ci = .indInfo cv caps → ci.name = punitName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → x = pt)
    (hnewempty : ci.name = emptyName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → False)
    (hpin : ci.isBasis = true →
      reservedBasisNames.contains ci.name = true →
      ci = pinnedInfo ci.name ∧
      ∀ ψ : Name → Nat, v₀ ψ = pinnedVal V ci.name ψ)
    (hsib : SibFinds env ci)
    (hrecm : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
      (∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name → val' n ψ = m.val n ψ) →
      RecMemberOk (V := V) ⟨ci :: env.consts⟩ val' ci)
    (hctors : ∀ cvR nP nM nm ni rules,
      ci = .recInfo cvR nP nM nm ni rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hmodv : reservedBasisNames.contains ci.name = false →
      ((∃ cv caps, ci = .indInfo cv caps) ∨
       (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (ci.name.str "_model") ψ)
    (hproj : ∀ (T : Name) (j : Nat), ci.name = projFnName T j →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (projModelName T j) ψ)
    (hetaL : ∀ cv caps, ci = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains ci.name = false →
      (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        (env.find? (projModelName ci.name j)).isSome = true) ∧
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.etaParams →
        x ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = SpineFold V (m.val (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us))
          (ps ++ (List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])))
    (hunitL : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.unitParams →
        x ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        y ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = y) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = v₀ ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hfresh := find?_none_ne hfind'
  obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n ψ =>
      if n = ci.name then v₀ ψ else m.val n ψ := ⟨_, rfl⟩
  have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ := by
    intro n hn ψ
    have : n ≠ ci.name := by
      intro hcontra
      rw [hcontra, hfind'] at hn
      exact nomatch hn
    simp [hval', this]
  have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨ci :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := val') hfind' hres]
    exact interp_cval_ext hagree e 0 (rho0 V)
  have hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨ci :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha
  have hwf' : EnvWF ⟨ci :: env.consts⟩ := EnvWF.cons m.wf hwf
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- val_params
    intro n ci2 hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      have hn' : n = ci.name := hn.symm ▸ rfl
      subst hn'
      simp only [hval', if_pos rfl]
      exact hparams ψ₁ ψ₂ hψ
    · next hn =>
      have hne : n ≠ ci.name := fun hc => hn (hc ▸ rfl)
      simp only [hval', if_neg hne]
      exact m.val_params n ci2 hf ψ₁ ψ₂ hψ
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨T, hT, hv⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [htrans _ htyres0 ψ]
        exact hT
      · have : val' c.name ψ = v₀ ψ := by simp [hval']
        rw [this]
        exact hv
    · obtain ⟨T, hT, hv⟩ := m.mem_type c hc ψ
      obtain ⟨-, -, hres, -, -, -⟩ := m.wf c hc
      refine ⟨T, ?_, ?_⟩
      · rw [htrans _ hres ψ]
        exact hT
      · have hne : c.name ≠ ci.name := hfresh c hc ∘ fun h => h
        simp only [hval', if_neg hne]
        exact hv
  · -- defn_eq
    intro cv2 value2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact absurd heq.symm (hnotdefn cv2 value2)
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 rfl
      have := m.defn_eq cv2 value2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ ci.name := by
        have := hfresh (.defnInfo cv2 value2) hmem2
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨hAtrans _ htyres0 ψ (hAty ψ), ?_⟩
      intro cv2 value2 heq
      exact absurd heq (hnotdefn cv2 value2)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 heq)
  · -- ind_ok
    refine ⟨?_, ?_, ?_, ?_, BasisBlocks.cons m.ind_ok.right.right.right.right.left
      hfind' hsib,
      RecCtorsStored.cons m.ind_ok.right.right.right.right.right.left hfind'
        hctors, ?_⟩
    · intro cv caps hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hlp, hfacts⟩ := hnewty cv caps rfl hn
        refine ⟨hlp, fun ψ => ?_⟩
        have hval'eq : val' psigmaName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq]
        exact hfacts ψ
      · next hn =>
        have hne : psigmaName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv caps).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv caps hfp
        refine ⟨hlp, fun ψ => ?_⟩
        have hval'eq : val' psigmaName ψ = m.val psigmaName ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact hfacts ψ
    · intro cv nP nF hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨h1, h2, h3, h4⟩ := hnewmk cv nP nF rfl hn
        refine ⟨h1, h2, h3, fun ψ => ?_⟩
        have hval'eq : val' psigmaMkName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq]
        exact h4 ψ
      · next hn =>
        have hne : psigmaMkName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.ctorInfo cv nP nF).name = psigmaMkName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨h1, h2, h3, h4⟩ := m.ind_ok.right.left cv nP nF hfp
        refine ⟨h1, h2, h3, fun ψ => ?_⟩
        have hval'eq : val' psigmaMkName ψ = m.val psigmaMkName ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact h4 ψ
    · intro cv caps hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        have hval'eq : val' punitName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq] at hx
        exact hnewunit cv caps rfl hn ψ x hx
      · next hn =>
        have hne : punitName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv caps).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hval'eq : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hval'eq] at hx
        exact m.ind_ok.right.right.left cv caps hfp ψ x hx
    · intro n ci' hfp hbasis hres2
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hpi, hpv⟩ := hpin hbasis (by rw [hn]; exact hres2)
        refine ⟨by rw [← hn]; exact hpi, fun ψ => ?_⟩
        have hval'eq : val' n ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq, hpv ψ, hn]
      · next hn =>
        have hne : n ≠ ci.name := by
          intro hcontra
          rw [hcontra, hfind'] at hfp
          exact nomatch hfp
        obtain ⟨hpi, hpv⟩ := m.ind_ok.right.right.right.left n ci' hfp
          hbasis hres2
        refine ⟨hpi, fun ψ => ?_⟩
        have hval'eq : val' n ψ = m.val n ψ := by
          simp [hval', hne]
        rw [hval'eq]
        exact hpv ψ
    · -- the Empty type stays uninhabited
      intro ψ x hx
      by_cases hn : emptyName = ci.name
      · have hval'eq : val' emptyName ψ = v₀ ψ := by
          simp [hval', hn]
        rw [hval'eq] at hx
        exact hnewempty hn.symm ψ x hx
      · have hval'eq : val' emptyName ψ = m.val emptyName ψ := by
          simp [hval', hn]
        rw [hval'eq] at hx
        exact m.ind_ok.right.right.right.right.right.right ψ x hx
  · -- rec_rules
    exact RecRulesOk.cons m hfind'
      (fun n hn ψ => hagree n hn ψ)
      (fun e hres ψ => htrans e hres ψ)
      (fun e hres ψ hAe => hAtrans e hres ψ hAe)
      (hrecm val' (fun ψ => by simp [hval'])
        (fun n ψ hne => by simp [hval', hne]))
  · -- modeled_ok
    refine ModeledOk.cons m.modeled_ok m.wf hfind' ?_ ?_ ?_ ?_ ?_ ?_
    · intro n ψ hn
      simp [hval', hn]
    · intro cv caps heq hres
      obtain ⟨hms, hveq⟩ := hmodv hres (Or.inl ⟨cv, caps, heq⟩)
      have hmne : ¬ci.name = ci.name.str "_model" :=
        fun hh => Name.str_ne ci.name "_model" hh.symm
      refine ⟨?_, ?_⟩
      · rw [Env.find?_cons, if_neg hmne]
        exact hms
      · intro ψ
        have h1 : val' ci.name ψ = v₀ ψ := by simp [hval']
        have hmne2 : ¬ci.name.str "_model" = ci.name :=
          fun hh => hmne hh.symm
        have h2 : val' (ci.name.str "_model") ψ =
            m.val (ci.name.str "_model") ψ := by
          simp [hval', hmne2]
        rw [h1, h2, hveq ψ]
    · intro cv cnP cnF heq hres
      obtain ⟨hms, hveq⟩ := hmodv hres (Or.inr ⟨cv, cnP, cnF, heq⟩)
      have hmne : ¬ci.name = ci.name.str "_model" :=
        fun hh => Name.str_ne ci.name "_model" hh.symm
      refine ⟨?_, ?_⟩
      · rw [Env.find?_cons, if_neg hmne]
        exact hms
      · intro ψ
        have h1 : val' ci.name ψ = v₀ ψ := by simp [hval']
        have hmne2 : ¬ci.name.str "_model" = ci.name :=
          fun hh => hmne hh.symm
        have h2 : val' (ci.name.str "_model") ψ =
            m.val (ci.name.str "_model") ψ := by
          simp [hval', hmne2]
        rw [h1, h2, hveq ψ]
    · intro T j hh
      obtain ⟨hms, hveq⟩ := hproj T j hh
      have hpmne : projModelName T j ≠ ci.name := by
        intro he
        rw [he, hfind'] at hms
        exact nomatch hms
      refine ⟨?_, ?_⟩
      · rw [Env.find?_cons, if_neg (fun hh2 => hpmne hh2.symm)]
        exact hms
      · intro ψ
        have h1 : val' (projFnName T j) ψ = v₀ ψ := by
          rw [← hh]
          simp [hval']
        have h2 : val' (projModelName T j) ψ =
            m.val (projModelName T j) ψ := by
          simp [hval', hpmne]
        rw [h1, h2, hveq ψ]
    · -- the eta law of a freshly installed eta-capable structure
      intro cv caps heq hcape hres
      obtain ⟨hms1, hms2, hlaw⟩ := hetaL cv caps heq hcape hres
      have hCne : caps.etaCtor.str "_model" ≠ ci.name := by
        intro he
        rw [he, hfind'] at hms1
        exact nomatch hms1
      have hPne : ∀ j, j < caps.etaFields →
          projModelName ci.name j ≠ ci.name := by
        intro j hj he
        have h1 := hms2 j hj
        rw [he, hfind'] at h1
        exact nomatch h1
      refine ⟨?_, ?_, ?_⟩
      · rw [Env.find?_cons, if_neg (fun hh => hCne hh.symm)]
        exact hms1
      · intro j hj
        rw [Env.find?_cons, if_neg (fun hh => hPne j hj hh.symm)]
        exact hms2 j hj
      · intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
        have hcvty : cv.type = ci.toConstantVal.type := by
          rw [heq]
          rfl
        have hcvlps : cv.levelParams = ci.toConstantVal.levelParams := by
          rw [heq]
          rfl
        have hfit' := TeleFit.env_shrink hfind' hagree hfit
          (by rw [Expr.constsResolve_instantiateLevelParams, hcvty]
              exact htyres0)
        have hx' : x ∈ˢ SpineFold V
            (v₀ (Level.substFn φ'' cv.levelParams us)) ps := by
          have hv : val' ci.name (Level.substFn φ'' cv.levelParams us) =
              v₀ (Level.substFn φ'' cv.levelParams us) := by
            simp [hval']
          rw [hv] at hx
          exact hx
        have h1 := hlaw φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx' hfit'
        have hvC : val' (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us) =
            m.val (caps.etaCtor.str "_model")
              (Level.substFn φ'' cv.levelParams us) := by
          simp [hval', hCne]
        have hvP : ((List.range caps.etaFields).map fun j =>
            SpineFold V (val' (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])) =
            ((List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])) := by
          refine List.map_congr_left ?_
          intro j hj
          have : val' (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us) =
              m.val (projModelName ci.name j)
                (Level.substFn φ'' cv.levelParams us) := by
            simp [hval', hPne j (List.mem_range.mp hj)]
          rw [this]
        rw [hvC, hvP]
        exact h1
    · -- the unit-like law of a freshly installed family
      intro cv caps heq hcapu hres
      intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
      have hcvty : cv.type = ci.toConstantVal.type := by
        rw [heq]
        rfl
      have hfit' := TeleFit.env_shrink hfind' hagree hfit
        (by rw [Expr.constsResolve_instantiateLevelParams, hcvty]
            exact htyres0)
      have hveq : val' ci.name (Level.substFn φ'' cv.levelParams us) =
          v₀ (Level.substFn φ'' cv.levelParams us) := by
        simp [hval']
      rw [hveq] at hx hy
      exact hunitL cv caps heq hcapu hres φ'' us ps x y d₁ ρ₁ d₂ ρ₂
        rest hlen hx hy hfit'
  · -- nat_ops: the new constant is never a fast-path definition
    refine NatOpsOk.cons m.nat_ops hfind' ?_ ?_
    · intro n hne ψ'
      simp [hval', hne]
    · intro cv₀ v₀' heq _
      exact absurd heq (hnotdefn cv₀ v₀')
  · -- the new constant's value
    intro ψ
    simp [hval']
  · -- untouched values
    intro n ψ hne
    simp [hval', hne]

end Setlec
