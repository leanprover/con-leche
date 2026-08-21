import Setlec.Model.Extend.Sibs

/-!
# Transport — split out of `Setlec.Model.Extend`

Reusable transport lemmas for the extension proofs:

* fresh-extension transports (`interpClosed_extend_fresh`,
  `AnnotOk.extend_fresh`): interpretation and annotation facts stated
  over the old environment survive prepending one fresh constant when
  the valuations agree on stored names;
* rule-list swaps (`Env.find?_recRules_swap` …,
  `ConstWF.recRules_swap`): everything the model reads through the
  environment ignores a stored recursor's rule list;
* `extend_rec_swap`: the clause-by-clause `EnvModel` transport from
  the provisional rules-free recursor to the recursor with its checked
  rules attached, given the head's stored-constructor facts and fold
  obligations (`RecMemberOk`).  `extend_modeled_rec` and
  `extend_proj_fn` both go through it.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Interpreting an expression that resolves in the old environment is
unchanged by prepending one fresh constant, given valuation agreement
on stored names. -/
theorem interpClosed_extend_fresh {env : Env} {c₀ : ConstantInfo}
    {val' val : ConstVal V}
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = val n ψ)
    {e : Expr} (hres : e.constsResolve env = true) (ψ : Name → Nat) :
    interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
      interpClosed V val env ψ e := by
  rw [interpClosed_mono (cval := val') hfresh hres]
  exact interp_cval_ext hagree e 0 (rho0 V)

/-- `AnnotOk` over the old environment survives prepending one fresh
constant, given valuation agreement on stored names. -/
theorem AnnotOk.extend_fresh {env : Env} {c₀ : ConstantInfo}
    {val' val : ConstVal V}
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ' : Name → Nat,
      val' n ψ' = val n ψ')
    {e : Expr} (hres : e.constsResolve env = true) (ψ : Name → Nat)
    (ha : AnnotOk V val env ψ 0 (rho0 V) e) :
    AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
  refine AnnotOk.mono hfresh e 0 (rho0 V) hres ?_
  exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha

section RecRulesSwap

variable {env : Env} {cvA : ConstantVal} {nP nM nm ni : Nat}

/-- Lookups of other names ignore the head recursor's rule list. -/
theorem Env.find?_recRules_swap (rules₁ rules₂ : List RecRule) {n : Name}
    (hn : n ≠ cvA.name) :
    (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n =
    (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n := by
  rw [Env.find?_cons, Env.find?_cons,
    if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
      from fun h => hn h.symm),
    if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni rules₂).name = n
      from fun h => hn h.symm)]

/-- Stored level parameters ignore the head recursor's rule list. -/
theorem Env.recRules_levelext (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
        rules₂).name = n from h)]

/-- Lookup success ignores the head recursor's rule list. -/
theorem Env.recRules_isSome (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n).isSome := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
        rules₂).name = n from h)]

/-- The interpretation ignores the head recursor's rule list. -/
theorem interpClosed_recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule) (e : Expr) (ψ : Name → Nat) :
    interpClosed V val
      (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env) ψ e =
    interpClosed V val
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) ψ e :=
  interp_env_ext (Env.recRules_levelext rules₁ rules₂)
    natLitSupported_cons_recRules e 0 (rho0 V)

/-- `AnnotOk` ignores the head recursor's rule list. -/
theorem AnnotOk.recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule) (e : Expr) (ψ : Name → Nat) (d : Nat)
    (ρ : Nat → V)
    (h : AnnotOk V val
      (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env) ψ d ρ e) :
    AnnotOk V val
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) ψ d ρ e :=
  AnnotOk.env_ext (Env.recRules_levelext rules₁ rules₂)
    natLitSupported_cons_recRules e d ρ h

/-- `ConstWF` of a stored constant ignores the head recursor's rule
list. -/
theorem ConstWF.recRules_swap (rules₁ rules₂ : List RecRule)
    {c : ConstantInfo}
    (hc : ConstWF (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env) c) :
    ConstWF (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
    exact h3
  · intro cv2 v2 heq
    obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 heq
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩
  · intro cv nP' nM' nm' ni' rules heq r hr
    obtain ⟨a, b, cres, dd⟩ := h6 cv nP' nM' nm' ni' rules heq r hr
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩

/-- The head recursor's own `ConstWF`, with the rule list dropped (the
rules-free provisional install). -/
theorem ConstWF.recRules_head_empty {rules' : List RecRule}
    (hwf : ConstWF (⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ : Env)
      (.recInfo cvA nP nM nm ni rules')) :
    ConstWF (⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩ : Env)
      (.recInfo cvA nP nM nm ni []) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hwf
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules' [])]
    exact h3
  · intro cv2 v2 heq
    exact nomatch heq
  · intro cv nP' nM' nm' ni' rules heq
    injection heq with e1 e2 e3 e4 e5 e6
    subst e6
    intro r hr
    cases hr

omit [SetTheory V] in
/-- `ConstValParams` ignores the head recursor's rule list. -/
theorem ConstValParams.recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule)
    (h : ConstValParams val
      (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env)) :
    ConstValParams val
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) := by
  intro n ci hf ψ₁ ψ₂ hψ
  rw [Env.find?_cons] at hf
  split at hf
  · next hn =>
    obtain rfl := Option.some.inj hf
    exact h n (.recInfo cvA nP nM nm ni rules₁)
      (by rw [Env.find?_cons,
        if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
          from hn)]) ψ₁ ψ₂ (by exact hψ)
  · next hn =>
    refine h n ci ?_ ψ₁ ψ₂ hψ
    rw [Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
        from hn)]
    exact hf

/-- The clause-by-clause `EnvModel` transport from the provisional
rules-free recursor to the same recursor with its checked rules
attached: only the head's own fold obligations (`RecMemberOk`) and
stored-constructor facts are new, everything else ignores the rule
list. -/
theorem extend_rec_swap {rules' : List RecRule}
    (m₀ : EnvModel V ⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩)
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩
      (.recInfo cvA nP nM nm ni rules'))
    (hctors : ∀ r ∈ rules', ∃ cvj cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hrecm : RecMemberOk (V := V)
      ⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ m₀.val
      (.recInfo cvA nP nM nm ni rules')) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩,
      ∀ (n : Name) (ψ : Name → Nat), m'.val n ψ = m₀.val n ψ := by
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩ : Env).find? n :=
    fun n hn => Env.find?_recRules_swap rules' [] hn
  have henv10 := Env.recRules_levelext (env := env) (cvA := cvA)
    (nP := nP) (nM := nM) (nm := nm) (ni := ni) rules' []
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩ : Env) ψ e :=
    fun e ψ => interpClosed_recRules_swap rules' [] e ψ
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.recRules_swap [] rules' e ψ d ρ h
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun n ψ => rfl⟩
  · -- wf
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hwf
    · exact ConstWF.recRules_swap [] rules'
        (m₀.wf c (List.mem_cons_of_mem _ hc))
  · -- val_params
    exact ConstValParams.recRules_swap [] rules' m₀.val_params
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP nM nm ni [])
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
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP nM nm ni [])
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
      · have hfp₀ : (⟨.recInfo cvA nP nM nm ni [] ::
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
          if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
            rules').name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨cvj, cnP, cnF, hctor⟩ := hctors r hr
        refine ⟨cvj, cnP, cnF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
            rules').name = RecRule.ctor r from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj cnP cnF).name =
              RecRule.ctor r := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP nM nm ni [] ::
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
            if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
              []).name = RecRule.ctor r from h.symm)] at hc
          exact nomatch (Option.some.inj hc)
        rw [hfindEq _ hnc]
        exact hc
  · -- rec_rules: the head's fold obligations are supplied, the rest
    -- ignores the rule list
    intro n cvR nP' nM' nm' ni' rules hfp r hr
    rw [Env.find?_cons] at hfp
    split at hfp
    · next hn =>
      obtain rfl : cvA.name = n := hn
      obtain hceq := Option.some.inj hfp
      exact hrecm cvR nP' nM' nm' ni' rules hceq r hr
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP nM nm ni [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni
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
          if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni
            rules').name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP nM nm ni [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules hfit1,
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
        (⟨.recInfo cvA nP nM nm ni rules' :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA nP nM nm ni rules')
        else (⟨.recInfo cvA nP nM nm ni [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni rules').name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni rules').name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP nM nm ni []).name = n from h)]
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
        obtain ⟨hms, hveq⟩ := mo3 T j (.recInfo cvA nP nM nm ni [])
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni []).name = projFnName T j from hh)])
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

end RecRulesSwap

end Setlec
