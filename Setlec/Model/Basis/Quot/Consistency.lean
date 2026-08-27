import Setlec.Model.Extend
import Setlec.Model.Basis.Quot.Iota

/-!
# Quotient-basis consistency

Installing the pinned quotient basis block (`Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`, `Quot.sound`) preserves having a model.
Split out of the `checkDecl_sound` case analysis in
`Setlec.Model.Consistency`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The `.basisDecl .quotK` case of `checkDecl_sound`: installing the
quotient basis block preserves having a model. -/
theorem installQuotBasis_sound {F : Nat} {env env' : Env}
    (h : checkDecl mode (fueledOps mode F) env (.basisDecl .quotK) = .ok env')
    (m : EnvModel V env) (hE1 : EtaFamiliesClosed env) :
    Nonempty (EnvModel V env') ∧ EtaFamiliesClosed env' := by
      simp only [checkDecl, checkDefnVal, checkThmVal, installBasisDecl,
        fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
        fueledOps_ensureSort, fueledOps_whnf, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind, reduceCtorEq, reduceIte, pure, Except.pure] at h
      -- the Eq-pin guard
      by_cases hEq : env.find? eqName = some eqA
      case neg => simp [hEq, pure, Except.pure] at h
      simp only [hEq, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 1: Quot
      by_cases h1 : (env.find? quotA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Quot.mk
      by_cases h2 : ((⟨quotA :: env.consts⟩ : Env).find? quotMkA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Quot.lift
      by_cases h3 : ((⟨quotMkA :: quotA :: env.consts⟩ : Env).find?
        quotLiftA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 4: Quot.ind
      by_cases h4 : ((⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
        Env).find? quotIndA.name).isNone
      case neg => simp [h4, pure, Except.pure] at h
      simp only [h4, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 5: Quot.sound
      by_cases h5 : ((⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotSoundA.name).isNone
      case neg => simp [h5, pure, Except.pure] at h
      simp only [h5, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- the base environment's Eq carries the pinned value
      have hvalEq0 : ∀ ψ' : Name → Nat, m.val eqName ψ' = eqVal V ψ' := by
        intro ψ'
        obtain ⟨-, hval⟩ := m.ind_ok.right.right.right.left eqName eqA hEq
          rfl (by decide)
        rw [hval ψ']
        show pinnedVal V eqName ψ' = eqVal V ψ'
        delta pinnedVal
        rw [if_pos rfl]
      -- step 1: Quot
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m quotA
        (fun ψ => quotVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [quotA]),
          fun _ _ _ _ hx => absurd hx (by simp [quotA]),
          fun _ _ hx => absurd hx (by simp [quotA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => quot_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [quotVal]
          rw [hψ uN (by simp [quotA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_quot_type)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR mI rP rules hx =>
          absurd hx (by simp [quotA]))
        (fun _ _ _ _ hx => absurd hx (by simp [quotA]))
        (fun _ hx _ => nomatch hx)
      have hvalQ1 : ∀ ψ' : Name → Nat, m1.val quotName ψ' = quotVal V ψ' :=
        fun ψ' => hval1 ψ'
      -- step 2: Quot.mk
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 quotMkA
        (fun ψ => quotMkVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [quotMkA]),
          fun _ _ _ _ hx => absurd hx (by simp [quotMkA]),
          fun _ _ hx => absurd hx (by simp [quotMkA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => quotMk_key rfl hvalQ1)
        (fun ψ₁ ψ₂ hψ => by
          simp only [quotMkVal]
          rw [hψ uN (by simp [quotMkA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_quotMk_type rfl hvalQ1)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR mI rP rules hx =>
          absurd hx (by simp [quotMkA]))
        (fun _ _ _ _ hx => absurd hx (by simp [quotMkA]))
        (fun _ hx _ => nomatch hx)
      have hvalQ2 : ∀ ψ' : Name → Nat, m2.val quotName ψ' = quotVal V ψ' :=
        fun ψ' => by
          rw [hpres2 quotName ψ' (by decide)]
          exact hvalQ1 ψ'
      have hvalM2 : ∀ ψ' : Name → Nat,
          m2.val quotMkName ψ' = quotMkVal V ψ' := fun ψ' => hval2 ψ'
      have hfE2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? eqName =
          some eqA := by
        rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
          if_neg (by decide)]
        exact hEq
      have hvalE2 : ∀ ψ' : Name → Nat, m2.val eqName ψ' = eqVal V ψ' :=
        fun ψ' => by
          rw [hpres2 eqName ψ' (by decide), hpres1 eqName ψ' (by decide)]
          exact hvalEq0 ψ'
      -- step 3: Quot.lift
      have hresL : Expr.constsResolve
          (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
          quotLiftA.toConstantVal.type = true := by
        have hfE3 : ((⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
            Env).find? eqName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_neg (by decide), hEq]
          rfl
        have hfQ3 : ((⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
            Env).find? quotName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_pos (by decide)]
          rfl
        simp only [eqName] at hfE3
        simp only [quotName] at hfQ3
        generalize (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
          Env) = E at hfE3 hfQ3 ⊢
        simp +decide [quotLiftA, ConstantInfo.toConstantVal,
          Expr.constsResolve, hfE3, hfQ3]
      have hresL0 : Expr.constsResolve
          (⟨quotMkA :: quotA :: env.consts⟩ : Env)
          quotLiftA.toConstantVal.type = true := by
        have hfE3 : ((⟨quotMkA :: quotA :: env.consts⟩ :
            Env).find? eqName).isSome = true := by
          rw [hfE2]
          rfl
        have hfQ3 : ((⟨quotMkA :: quotA :: env.consts⟩ :
            Env).find? quotName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_pos (by decide)]
          rfl
        simp only [eqName] at hfE3
        simp only [quotName] at hfQ3
        generalize (⟨quotMkA :: quotA :: env.consts⟩ : Env) = E
          at hfE3 hfQ3 ⊢
        simp +decide [quotLiftA, ConstantInfo.toConstantVal,
          Expr.constsResolve, hfE3, hfQ3]
      have hresLr : Expr.constsResolve
          (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
          (RecRule.rhs ((ConstantInfo.recRules quotLiftA).getD 0 default))
          = true := by
        have hfE3 : ((⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
            Env).find? eqName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_neg (by decide), hEq]
          rfl
        simp only [eqName] at hfE3
        generalize (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
          Env) = E at hfE3 ⊢
        simp +decide [quotLiftA, ConstantInfo.recRules, RecRule.rhs,
          Expr.constsResolve, hfE3]
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 quotLiftA
        (fun ψ => quotLiftVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, hresL, rfl,
          fun _ _ _ hx => absurd hx (by simp [quotLiftA]),
          (fun cv mI rP rules heq r hr => by
            simp only [quotLiftA] at heq
            injection heq with e1 e2 e3 e4
            subst e1 e2 e3 e4
            rcases List.mem_cons.mp hr with rfl | hr
            · exact ⟨rfl, rfl, hresLr, rfl, fun lvls pins hf => RecRuleFire.noConfusion hf⟩
            · cases hr),
          fun _ _ hx => absurd hx (by simp [quotLiftA])⟩
        hresL0
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => quotLift_key hfE2 hvalE2 rfl hvalQ2)
        (fun ψ₁ ψ₂ hψ => by
          simp only [quotLiftVal]
          rw [hψ uN (by simp [quotLiftA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [quotLiftA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_quotLift_type hfE2 hvalE2 rfl hvalQ2)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv mI rP rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR mI rP rules heq => by
          simp only [quotLiftA] at heq
          injection heq with e1 e2 e3 e4
          subst e1 e2 e3 e4
          intro r hr
          have hfE' : Env.find?
              (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
              eqName = some eqA := by
            rw [Env.find?_cons, if_neg (by decide)]
            exact hfE2
          have hvalE' : ∀ ψ' : Name → Nat, val' eqName ψ' = eqVal V ψ' := by
            intro ψ'
            rw [hv2 eqName ψ' (by decide)]
            exact hvalE2 ψ'
          have hvalM' : ∀ ψ' : Name → Nat,
              val' quotMkName ψ' = quotMkVal V ψ' := by
            intro ψ'
            rw [hv2 quotMkName ψ' (by decide)]
            exact hvalM2 ψ'
          have hvalQ' : ∀ ψ' : Name → Nat,
              val' quotName ψ' = quotVal V ψ' := by
            intro ψ'
            rw [hv2 quotName ψ' (by decide)]
            exact hvalQ2 ψ'
          have hvalL' : ∀ ψ' : Name → Nat,
              val' quotLiftName ψ' = quotLiftVal V ψ' :=
            fun ψ' => hv1 ψ'
          have hfQ' : Env.find?
              (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
              quotName = some quotA := rfl
          have hfMk' : Env.find?
              (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
              quotMkName = some quotMkA := rfl
          have hfL' : Env.find?
              (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
              quotLiftName = some quotLiftA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_quotLift_rhs (cval := val') (ψ := ψ)
              hfE' hvalE', fun _ => Nat.le_refl _,
              fun _ => by decide, fun lvls pins hf => RecRuleFire.noConfusion hf, ?_⟩
            intro cvj cnP cnF hfj _hfire
            have hje := Option.some.inj hfj
            simp only [quotMkA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            exact quotLift_ruleOk hfE' hvalE' hfQ' hvalQ' hfMk' hvalM'
              hfL' hvalL'
          · cases hr)
        (fun cvR mI rP rules heq => by
          simp only [quotLiftA] at heq
          injection heq with e1 e2 e3 e4
          subst e4
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨quotMkA :: quotA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Quot").str "mk") = some quotMkA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
        (fun _ hx _ => nomatch hx)
      have hvalQ3 : ∀ ψ' : Name → Nat, m3.val quotName ψ' = quotVal V ψ' :=
        fun ψ' => by
          rw [hpres3 quotName ψ' (by decide)]
          exact hvalQ2 ψ'
      have hvalM3 : ∀ ψ' : Name → Nat,
          m3.val quotMkName ψ' = quotMkVal V ψ' := fun ψ' => by
        rw [hpres3 quotMkName ψ' (by decide)]
        exact hvalM2 ψ'
      have hfE3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :
          Env).find? eqName = some eqA := by
        rw [Env.find?_cons, if_neg (by decide)]
        exact hfE2
      have hvalE3 : ∀ ψ' : Name → Nat, m3.val eqName ψ' = eqVal V ψ' :=
        fun ψ' => by
          rw [hpres3 eqName ψ' (by decide)]
          exact hvalE2 ψ'
      -- step 4: Quot.ind
      obtain ⟨m4, hval4, hpres4⟩ := extend_basis_one m3 quotIndA
        (fun ψ => quotIndVal V ψ)
        (Option.isNone_iff_eq_none.mp h4)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ _ hx => absurd hx (by simp [quotIndA]),
          (fun cv mI rP rules heq r hr => by
            simp only [quotIndA] at heq
            injection heq with e1 e2 e3 e4
            subst e1 e2 e3 e4
            rcases List.mem_cons.mp hr with rfl | hr
            · exact ⟨rfl, rfl, rfl, rfl, fun lvls pins hf => RecRuleFire.noConfusion hf⟩
            · cases hr),
          fun _ _ hx => absurd hx (by simp [quotIndA])⟩
        rfl
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => quotInd_key rfl hvalQ3 rfl hvalM3)
        (fun ψ₁ ψ₂ hψ => by
          simp only [quotIndVal]
          rw [hψ uN (by simp [quotIndA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_quotInd_type rfl hvalQ3 rfl hvalM3)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv mI rP rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR mI rP rules heq => by
          simp only [quotIndA] at heq
          injection heq with e1 e2 e3 e4
          subst e1 e2 e3 e4
          intro r hr
          have hfQ' : Env.find?
              (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
                env.consts⟩ : Env) quotName = some quotA := by
            rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
              if_neg (by decide), Env.find?_cons, if_neg (by decide),
              Env.find?_cons, if_pos (by decide)]
          have hfM' : Env.find?
              (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
                env.consts⟩ : Env) quotMkName = some quotMkA := by
            rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
              if_neg (by decide), Env.find?_cons, if_pos (by decide)]
          have hvalQ' : ∀ ψ' : Name → Nat, val' quotName ψ' = quotVal V ψ' := by
            intro ψ'
            rw [hv2 quotName ψ' (by decide)]
            exact hvalQ3 ψ'
          have hvalM' : ∀ ψ' : Name → Nat,
              val' quotMkName ψ' = quotMkVal V ψ' := by
            intro ψ'
            rw [hv2 quotMkName ψ' (by decide)]
            exact hvalM3 ψ'
          have hvalI' : ∀ ψ' : Name → Nat,
              val' quotIndName ψ' = quotIndVal V ψ' :=
            fun ψ' => hv1 ψ'
          have hfI' : Env.find?
              (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
                env.consts⟩ : Env)
              quotIndName = some quotIndA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_quotInd_rhs (cval := val') (ψ := ψ)
              hfQ' hvalQ' hfM' hvalM', fun _ => Nat.le_refl _,
              fun _ => by decide, fun lvls pins hf => RecRuleFire.noConfusion hf, ?_⟩
            intro cvj cnP cnF hfj _hfire
            have hje := Option.some.inj hfj
            simp only [quotMkA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            exact quotInd_ruleOk hfQ' hvalQ' hfM' hvalM' hfI' hvalI'
          · cases hr)
        (fun cvR mI rP rules heq => by
          simp only [quotIndA] at heq
          injection heq with e1 e2 e3 e4
          subst e4
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Quot").str "mk") = some quotMkA := by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
        (fun _ hx _ => nomatch hx)
      have hvalQ4 : ∀ ψ' : Name → Nat, m4.val quotName ψ' = quotVal V ψ' :=
        fun ψ' => by
          rw [hpres4 quotName ψ' (by decide)]
          exact hvalQ3 ψ'
      have hvalM4 : ∀ ψ' : Name → Nat,
          m4.val quotMkName ψ' = quotMkVal V ψ' := fun ψ' => by
        rw [hpres4 quotMkName ψ' (by decide)]
        exact hvalM3 ψ'
      have hfE4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons, if_neg (by decide)]
        exact hfE3
      have hvalE4 : ∀ ψ' : Name → Nat, m4.val eqName ψ' = eqVal V ψ' :=
        fun ψ' => by
          rw [hpres4 eqName ψ' (by decide)]
          exact hvalE3 ψ'
      -- step 5: Quot.sound
      have hresS : Expr.constsResolve
          (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
            env.consts⟩ : Env)
          quotSoundA.toConstantVal.type = true := by
        have hfE5 : ((⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
            quotA :: env.consts⟩ : Env).find? eqName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), hfE4]
          rfl
        have hfQ5 : ((⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
            quotA :: env.consts⟩ : Env).find? quotName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_neg (by decide),
            Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_pos (by decide)]
          rfl
        have hfM5 : ((⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
            quotA :: env.consts⟩ : Env).find? quotMkName).isSome =
            true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_neg (by decide),
            Env.find?_cons, if_pos (by decide)]
          rfl
        simp only [eqName] at hfE5
        simp only [quotName] at hfQ5
        simp only [quotMkName, quotName] at hfM5
        generalize (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
          quotA :: env.consts⟩ : Env) = E at hfE5 hfQ5 hfM5 ⊢
        simp +decide [quotSoundA, ConstantInfo.toConstantVal,
          Expr.constsResolve, hfE5, hfQ5, hfM5]
      have hresS0 : Expr.constsResolve
          (⟨quotIndA :: quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env)
          quotSoundA.toConstantVal.type = true := by
        have hfE5 : ((⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
            env.consts⟩ : Env).find? eqName).isSome = true := by
          rw [hfE4]
          rfl
        have hfQ5 : ((⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
            env.consts⟩ : Env).find? quotName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_neg (by decide),
            Env.find?_cons, if_pos (by decide)]
          rfl
        have hfM5 : ((⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
            env.consts⟩ : Env).find? quotMkName).isSome = true := by
          rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
            if_neg (by decide), Env.find?_cons, if_pos (by decide)]
          rfl
        simp only [eqName] at hfE5
        simp only [quotName] at hfQ5
        simp only [quotMkName, quotName] at hfM5
        generalize (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
          env.consts⟩ : Env) = E at hfE5 hfQ5 hfM5 ⊢
        simp +decide [quotSoundA, ConstantInfo.toConstantVal,
          Expr.constsResolve, hfE5, hfQ5, hfM5]
      obtain ⟨m5, hval5, hpres5⟩ := extend_basis_one m4 quotSoundA
        (fun ψ => quotSoundVal V ψ)
        (Option.isNone_iff_eq_none.mp h5)
        ⟨rfl, rfl, hresS, rfl,
          fun _ _ _ hx => absurd hx (by simp [quotSoundA]),
          fun _ _ _ _ hx => absurd hx (by simp [quotSoundA]),
          fun _ _ hx => absurd hx (by simp [quotSoundA])⟩
        hresS0
        (fun _ _ _ hx => nomatch hx)
        (fun ψ => quotSound_key hfE4 hvalE4 rfl hvalQ4 rfl hvalM4)
        (fun ψ₁ ψ₂ hψ => by
          simp only [quotSoundVal]
          rw [hψ uN (by simp [quotSoundA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_quotSound_type hfE4 hvalE4 rfl hvalQ4 rfl hvalM4)
        (fun cv _ hx hn => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv _ hx hn => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun hb _ => by simp [quotSoundA, ConstantInfo.isBasis] at hb)
        (fun _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR mI rP rules hx =>
          absurd hx (by simp [quotSoundA]))
        (fun _ _ _ _ hx => absurd hx (by simp [quotSoundA]))
        (fun _ hx _ => nomatch hx)
      refine ⟨⟨m5⟩, ?_⟩
      exact EtaFamiliesClosed.cons_nonind (EtaFamiliesClosed.cons_nonind
        (EtaFamiliesClosed.cons_nonind (EtaFamiliesClosed.cons_nonind
          (EtaFamiliesClosed.cons_nonind hE1
            (Option.isNone_iff_eq_none.mp h1) (fun _ _ _ _ => by decide))
          (Option.isNone_iff_eq_none.mp h2) (fun _ _ _ _ => by decide))
        (Option.isNone_iff_eq_none.mp h3) (fun _ _ _ _ => by decide))
        (Option.isNone_iff_eq_none.mp h4) (fun _ _ _ _ => by decide))
        (Option.isNone_iff_eq_none.mp h5) (fun _ _ _ _ => by decide)

end Setlec
