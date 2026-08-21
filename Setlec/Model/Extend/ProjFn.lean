import Setlec.Model.Extend.Modeled

/-!
# ProjFn — split out of `Setlec.Model.Extend`

`extend_proj_fn`: extend a model by an installed projection
function, a degenerate recursor whose single rule's fold obligation
is discharged by the checked `proj_i.iota` theorem.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by an installed projection function: a degenerate
recursor (no motive, no minors) whose value is its `_model.proj_i`
counterpart's and whose single rule's fold obligation is discharged by
the checked `proj_i.iota` theorem (`proj_rule_fold`). -/
theorem extend_proj_fn {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nF i : Nat) (rule : RecRule)
    (f : Name → Name) (mnameP : Name)
    {cvm : ConstantVal} {mval : Expr} {cvj : ConstantVal}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩
      (.recInfo cvA nP 0 0 0 [rule]))
    (htyres0 : cvA.type.constsResolve env = true)
    (hmodel : env.find? mnameP = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = cvA.levelParams)
    (hprojm : ∀ (T : Name) (j : Nat), cvA.name = projFnName T j →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mnameP ψ = m.val (projModelName T j) ψ)
    (hren : cvA.type.renameConsts f = cvm.type)
    (f₀ : Name → Name) (hro : RenameOk m.val env f₀)
    (hff₀ : ∀ n, n ≠ cvA.name → f n = f₀ n)
    (hfself : f cvA.name = mnameP)
    (hfnot : ∀ n, f n ≠ cvA.name)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'')
    (hi : i < nF)
    (hctor : env.find? (RecRule.ctor rule) = some (.ctorInfo cvj nP nF))
    (_hnf : rule.nfields = nF)
    {raw : Expr}
    (hann : annotateCore env F 0 raw = .ok (RecRule.rhs rule))
    (hrawf : raw.hasFvar = false)
    (hrawb : raw.looseBVarsBounded 0 = true)
    (hrhsf : (RecRule.rhs rule).hasFvar = false)
    (hrhsb : (RecRule.rhs rule).looseBVarsBounded 0 = true)
    (hrhsres : (RecRule.rhs rule).constsResolve env = true)
    {rbinders cbinders sbinders : List (Name × Expr × BinderMeta)}
    {rbody cbody sbody tySlot : Expr} {ℓA : Level}
    {thmName : Name} {cvt : ConstantVal} {tval : Expr}
    (hstripR : (RecRule.rhs rule).stripLams (nP + nF) =
      some (rbinders, rbody))
    (hrbody : rbody = .bvar (nF - 1 - i))
    (hC_strip : cvj.type.stripPis (nP + nF) = some (cbinders, cbody))
    (hS_strip : cvt.type.stripPis (nP + nF) = some (sbinders, sbody))
    (hdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = b'.2.1)
    (hsdoms : ∀ (k : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[k]? = some b → cbinders[k]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f)
    (hsbody : sbody = Expr.mkAppN (.const eqName [ℓA])
      [tySlot,
       Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
        (((List.range nP).map fun k =>
            Expr.bvar (nP + nF - 1 - k)) ++
         [Expr.mkAppN (.const (f (RecRule.ctor rule))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + nF - 1 - k)) ++
            ((List.range nF).map fun k => Expr.bvar (nF - 1 - k)))]),
       .bvar (nF - 1 - i)])
    (hthm : env.find? thmName = some (.thmInfo cvt tval))
    (_hlpt : cvt.levelParams = cvA.levelParams) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val mnameP ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hisoRes : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).isSome := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h)]
  have hwf₀ : ConstWF (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env)
      (.recInfo cvA nP 0 0 0 []) := by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := hwf
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [← Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      exact nomatch heq
    · intro cv nP' nM' nm' ni' rules heq
      injection heq with e1 e2 e3 e4 e5 e6
      subst e6
      intro r hr
      cases hr
  have hren₀ : cvA.type.renameConsts f₀ = cvm.type := by
    rw [← Expr.renameConsts_congr_resolve
      (fun n hn => hff₀ n (fun he => by
        rw [he, hfind'] at hn; exact nomatch hn))
      cvA.type htyres0]
    exact hren
  obtain ⟨m₀, hval₀, hpres₀⟩ := extend_modeled_one m
    (.recInfo cvA nP 0 0 0 []) f₀ (mnameP)
    hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, 0, 0, 0, rfl⟩)) hmodel hlps hren₀ hro
    (fun hk => by
      rcases hk with ⟨_, _, hcon⟩ | ⟨_, _, _, hcon⟩ <;> exact nomatch hcon)
    hprojm
    (fun cv caps hcon => nomatch hcon)
    (fun cv caps hcon => nomatch hcon)
  have henv01 : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          []).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
          [rule]).name = n from h)]
  -- shared transports between the provisional and final environments
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n := by
    intro n hn
    rw [Env.find?_cons, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n
        from fun h => hn h.symm),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
        from fun h => hn h.symm)]
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env) ψ e := by
    intro e ψ
    exact (interp_env_ext henv01 natLitSupported_cons_recRules e 0 (rho0 V)).symm
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henv01 natLitSupported_cons_recRules e d ρ h
  have hCWtrans : ∀ c,
      ConstWF (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env) c →
      ConstWF (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) c := by
    intro c hc
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
    refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
    · rw [Expr.constsResolve_congr hisoRes]
      exact h3
    · intro cv2 v2 heq
      obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 heq
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
    · intro cv nP' nM' nm' ni' rules heq r hr
      obtain ⟨a, b, cres, dd⟩ := h6 cv nP' nM' nm' ni' rules heq r hr
      exact ⟨a, b, by rw [Expr.constsResolve_congr hisoRes]; exact cres,
        dd⟩
  -- hoisted: parameter-dependence over the final environment, and
  -- transports from the base model
  have hvp₁ : ConstValParams m₀.val
      (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) := by
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 0 0 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
          from hn)]
      exact hf
  have hagreeM : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      m₀.val n ψ = m.val n ψ := by
    intro n hn ψ
    refine hpres₀ n ψ ?_
    intro h
    have h2 : n = cvA.name := h
    rw [h2, hfind'] at hn
    exact nomatch hn
  have htransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := m₀.val) hfind' hres]
    exact interp_cval_ext hagreeM e 0 (rho0 V)
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ 0
        (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagreeM n hn ψ').symm)
      e 0 (rho0 V) ha
  have henv10 : ∀ n,
      ((⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) :=
    fun n => (henv01 n).symm
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun ψ => hval₀ ψ, fun n ψ hne => hpres₀ n ψ hne⟩
  · -- wf
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hwf
    · exact hCWtrans c (m₀.wf c (List.mem_cons_of_mem _ hc))
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 0 0 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n
          from hn)]
      exact hf
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP 0 0 0 [])
        List.mem_cons_self ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
  · -- defn_eq
    intro cv2 v2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact nomatch heq
    · have h := m₀.defn_eq cv2 v2 (List.mem_cons_of_mem _ hmem2) ψ
      rw [hitrans]
      exact h
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP 0 0 0 [])
        List.mem_cons_self ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => nomatch heq⟩
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 heq => hAtrans01 _ ψ 0 (rho0 V) (hA2 cv2 v2 heq)⟩
  · -- ind_ok
    have hneName : ∀ x : Name, reservedBasisNames.contains x = true →
        x ≠ cvA.name := by
      intro x hx h
      rw [h] at hx
      rw [hx] at hnres
      exact nomatch hnres
    obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := m₀.ind_ok
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, i7⟩
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i1 cv caps hfp
    · intro cv nP' nF' hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i2 cv nP' nF' hfp
    · intro cv caps hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i3 cv caps hfp
    · -- decl_ok
      intro n ci hfp hbasis hres2
      by_cases hn : cvA.name = n
      · exfalso
        subst hn
        rw [hnres] at hres2
        exact nomatch hres2
      · have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
            env.consts⟩ : Env).find? n = some ci := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        exact i4 n ci hfp₀ hbasis hres2
    · -- BasisBlocks
      obtain ⟨b1, b2, b3, b4⟩ := i5
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b1 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2, f3⟩ := b2 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f3⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b3 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv nP' nM' nm' ni' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b4 cv nP' nM' nm' ni' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
    · -- RecCtorsStored
      intro n cv nP' nM' nm' ni' rules hfp r hr
      by_cases hn : cvA.name = n
      · subst hn
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain rfl : rule = r := by
          rcases List.mem_cons.mp hr with h | h
          · exact h.symm
          · cases h
        refine ⟨cvj, nP, nF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = RecRule.ctor rule from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj nP nF).name =
              RecRule.ctor rule := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
            env.consts⟩ : Env).find? n =
            some (.recInfo cv nP' nM' nm' ni' rules) := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        obtain ⟨cvj, cnP', cnF', hc⟩ := i6 n cv nP' nM' nm' ni' rules
          hfp₀ r hr
        refine ⟨cvj, cnP', cnF', ?_⟩
        have hnc : RecRule.ctor r ≠ cvA.name := by
          intro h
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
              []).name = RecRule.ctor r from h.symm)] at hc
          exact nomatch (Option.some.inj hc)
        rw [hfindEq _ hnc]
        exact hc
  · -- rec_rules
    intro n cvR nP' nM' nm' ni' rules hfp r hr
    rw [Env.find?_cons] at hfp
    split at hfp
    · next hn =>
      obtain rfl : cvA.name = n := hn
      obtain hceq := Option.some.inj hfp
      injection hceq with e1 e2 e3 e4 e5 e6
      subst e1 e2 e3 e4 e5 e6
      obtain rfl : rule = r := by
        rcases List.mem_cons.mp hr with h | h
        · exact h.symm
        · cases h
      have hncc : RecRule.ctor rule ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hctor)
        have h3 : (ConstantInfo.ctorInfo cvj nP nF).name =
            RecRule.ctor rule := by
          have h4 := List.find?_some hctor
          simpa using h4
        exact h2 (by rw [h3, h])
      have hArhs₁ : ∀ ψ : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs rule) := by
        intro ψ
        exact hAtransM _ hrhsres ψ
          (annotate_sound m raw hann (WScoped.of_not_hasFvar hrawf)
            hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
            (FvarsOk.of_not_hasFvar hrawf))
      refine ⟨hArhs₁, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hctor₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? (RecRule.ctor rule) =
          some (.ctorInfo cvj nP nF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = RecRule.ctor rule from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      subst hψeq hψjeq
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) f := by
        refine ⟨?_, ?_, ?_⟩
        · intro n₂ ci₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain rfl := Option.some.inj hf₂
            refine ⟨.defnInfo cvm mval, ?_, ?_⟩
            · rw [show f n₂ = mnameP from by
                rw [← (show cvA.name = n₂ from hh)]
                exact hfself]
              rw [Env.find?_cons,
                if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                  [rule]).name = mnameP from
                  fun h => hfnot cvA.name (hfself.trans h.symm))]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP 0 0 0
                  [rule]).toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
                [rule]).name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = mnameP from hfself]
            rw [hpres₀ _ ψ₂
              (fun h => hfnot cvA.name (hfself.trans h))]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hff₀ n₂ hh,
                hro.2.2 n₂]
      have hfRm₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? (f cvA.name) =
          some (.defnInfo cvm mval) := by
        rw [hfself, Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = mnameP from
            fun h => hfnot cvA.name (hfself.trans h.symm))]
        exact hmodel
      have heqne : eqName ≠ cvA.name := by
        intro h
        rw [← h] at hnres
        exact absurd hnres (by decide)
      have heqfind₁ : (⟨.recInfo cvA nP 0 0 0 [rule] ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = eqName from fun h => heqne h.symm)]
        exact heqfind
      have heqval₁ : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'' :=
        fun ψ'' => by
          rw [hagreeM eqName (by rw [heqfind]; rfl) ψ'', heqval ψ'']
      obtain ⟨hthw, -, hthres, -, -, -⟩ := m.wf _ (find?_mem hthm)
      have hthmne : thmName ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hthm)
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          have h4 := List.find?_some hthm
          simpa using h4
        exact h2 (by rw [h3, h])
      have hthm_mem₁ : ∀ ψ'' : Name → Nat, ∃ P,
          interpClosed V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ''
            cvt.type = some P ∧
          m₀.val thmName ψ'' ∈ˢ P := by
        intro ψ''
        obtain ⟨P, hP, hmem⟩ := m.mem_type _ (find?_mem hthm) ψ''
        have h3 : (ConstantInfo.thmInfo cvt tval).name = thmName := by
          simpa using List.find?_some hthm
        refine ⟨P, ?_, ?_⟩
        · rw [htransM cvt.type hthres ψ'']
          exact hP
        · rw [← h3, hagreeM _ (by rw [h3, hthm]; rfl) ψ'']
          exact hmem
      have hthm_annot₁ : ∀ ψ'' : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env) ψ'' 0
            (rho0 V) cvt.type := by
        intro ψ''
        obtain ⟨hA1, -⟩ := m.annot_ok _ (find?_mem hthm) ψ''
        exact hAtransM cvt.type hthres ψ'' hA1
      obtain ⟨hCtf, hCtp, -, -, -, -⟩ := m.wf _ (find?_mem hctor)
      have htyw₁ : cvA.type.hasFvar = false := hwf.1
      have hClps₁ : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
          m₀.val (RecRule.ctor rule) ψ₁ = m₀.val (RecRule.ctor rule) ψ₂ :=
        fun ψ₁ ψ₂ hψ => hvp₁ _ _ hctor₁ ψ₁ ψ₂ (by exact hψ)
      have hl' : args.length = nP := by simpa using hl
      have hml' : margs.length = nP + nF := by simpa using hml
      have hout := proj_rule_fold (P := cvA.name) (i := i)
        hro₁ hvp₁ hi hctor₁ hfRm₁
        (show (ConstantInfo.defnInfo cvm
          mval).toConstantVal.levelParams = cvA.levelParams from hlps)
        hClps₁ heqfind₁ heqval₁ hthm_mem₁ hthm_annot₁ hthw hstripR
        hrbody hC_strip hS_strip hsdoms hdoms hsbody hrhsf
        hrhsb hArhs₁ hCtf
        (show cvj.type.allLevelParamsDefined cvj.levelParams = true from
          hCtp)
        hl' hml' htv hpeq hlev hfit2
      obtain ⟨Rv, hRi, hfoldEq, hslots⟩ := hout
      exact ⟨Rv, hRi, by simpa using hfoldEq, by simpa using hslots⟩
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0
            []).name = n from hn)]
        exact hfp
      obtain ⟨hA, hfold⟩ := m₀.rec_rules n cvR nP' nM' nm' ni' rules
        hfp₀ r hr
      refine ⟨fun ψ => hAtrans01 _ ψ 0 (rho0 V) (hA ψ), ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        rw [h, Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0
            [rule]).name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP 0 0 0 [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq, TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit1,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit2, by
            rw [← mapM_interp_congr (fun e => interp_env_ext henv10
              natLitSupported_cons_recRules e dd₂ ρρ₂)]
            exact hidx⟩
      refine ⟨R', ?_, hfoldEq, hRch⟩
      rw [hitrans]
      exact hRi
  · -- modeled_ok: lookups only differ in the head's rule list
    obtain ⟨mo1, mo2, mo3, mo4, mo5⟩ := m₀.modeled_ok
    have hisoF : ∀ n,
        (⟨.recInfo cvA nP 0 0 0 [rule] :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA nP 0 0 0 [rule])
        else (⟨.recInfo cvA nP 0 0 0 [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 [rule]).name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 0 0 0 []).name = n from h)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro n cv caps hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo1 n cv caps hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro n cv cnP' cnF' hf hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hms, hveq⟩ := mo2 n cv cnP' cnF' hf hres
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T j ci hf
      rw [hisoF] at hf
      split at hf
      · next hh =>
        obtain ⟨hms, hveq⟩ := mo3 T j (.recInfo cvA nP 0 0 0 [])
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 0 0 0 []).name = projFnName T j from hh)])
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
      · obtain ⟨hms, hveq⟩ := mo3 T j ci hf
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
    · intro T cvT caps hf hcape hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨hmsC, hmsP, hlaw⟩ := mo4 T cvT caps hf hcape hres
        refine ⟨?_, ?_, ?_⟩
        · rw [hisoF]
          split
          · rfl
          · exact hmsC
        · intro j hj
          rw [hisoF]
          split
          · rfl
          · exact hmsP j hj
        · intro φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hfit
          exact hlaw φ'' us ps x dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx
            (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
    · intro T cvT caps hf hcapu hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · have hlaw := mo5 T cvT caps hf hcapu hres
        intro φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy hfit
        exact hlaw φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy
          (TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit)
  · -- nat_ops: lookups only differ in the head's rule list
    exact NatOpsOk.cons_recRules m₀.nat_ops

end Setlec
