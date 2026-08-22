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

variable {env : Env} {cvA : ConstantVal} {mI rP : Nat}

/-- Lookups of other names ignore the head recursor's rule list. -/
theorem Env.find?_recRules_swap (rules₁ rules₂ : List RecRule) {n : Name}
    (hn : n ≠ cvA.name) :
    (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
    (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n := by
  rw [Env.find?_cons, Env.find?_cons,
    if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules₁).name = n
      from fun h => hn h.symm),
    if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules₂).name = n
      from fun h => hn h.symm)]

/-- Stored level parameters ignore the head recursor's rule list. -/
theorem Env.recRules_levelext (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]

/-- Lookup success ignores the head recursor's rule list. -/
theorem Env.recRules_isSome (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).isSome := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]

/-- The interpretation ignores the head recursor's rule list. -/
theorem interpClosed_recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule) (e : Expr) (ψ : Name → Nat) :
    interpClosed V val
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) ψ e =
    interpClosed V val
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) ψ e :=
  interp_env_ext (Env.recRules_levelext rules₁ rules₂)
    natLitSupported_cons_recRules strLitSupported_cons_recRules e 0 (rho0 V)

/-- `AnnotOk` ignores the head recursor's rule list. -/
theorem AnnotOk.recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule) (e : Expr) (ψ : Name → Nat) (d : Nat)
    (ρ : Nat → V)
    (h : AnnotOk V val
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) ψ d ρ e) :
    AnnotOk V val
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) ψ d ρ e :=
  AnnotOk.env_ext (Env.recRules_levelext rules₁ rules₂)
    natLitSupported_cons_recRules strLitSupported_cons_recRules e d ρ h

/-- `ConstWF` of a stored constant ignores the head recursor's rule
list. -/
theorem ConstWF.recRules_swap (rules₁ rules₂ : List RecRule)
    {c : ConstantInfo}
    (hc : ConstWF (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) c) :
    ConstWF (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
    exact h3
  · intro cv2 v2 h2 heq
    obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 h2 heq
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩
  · intro cv mI' rP' rules heq r hr
    obtain ⟨a, b, cres, dd⟩ := h6 cv mI' rP' rules heq r hr
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩

/-- The head recursor's own `ConstWF`, with the rule list dropped (the
rules-free provisional install). -/
theorem ConstWF.recRules_head_empty {rules' : List RecRule}
    (hwf : ConstWF (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env)
      (.recInfo cvA mI rP rules')) :
    ConstWF (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env)
      (.recInfo cvA mI rP []) := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := hwf
  refine ⟨h1, h2, ?_, h4, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules' [])]
    exact h3
  · intro cv2 v2 h2 heq
    exact nomatch heq
  · intro cv mI' rP' rules heq
    injection heq with e1 e2 e3 e4
    subst e4
    intro r hr
    cases hr

omit [SetTheory V] in
/-- `ConstValParams` ignores the head recursor's rule list. -/
theorem ConstValParams.recRules_swap {val : ConstVal V}
    (rules₁ rules₂ : List RecRule)
    (h : ConstValParams val
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env)) :
    ConstValParams val
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) := by
  intro n ci hf ψ₁ ψ₂ hψ
  rw [Env.find?_cons] at hf
  split at hf
  · next hn =>
    obtain rfl := Option.some.inj hf
    exact h n (.recInfo cvA mI rP rules₁)
      (by rw [Env.find?_cons,
        if_pos (show (ConstantInfo.recInfo cvA mI rP rules₁).name = n
          from hn)]) ψ₁ ψ₂ (by exact hψ)
  · next hn =>
    refine h n ci ?_ ψ₁ ψ₂ hψ
    rw [Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules₁).name = n
        from hn)]
    exact hf

/-- The clause-by-clause `EnvModel` transport from the provisional
rules-free recursor to the same recursor with its checked rules
attached: only the head's own fold obligations (`RecMemberOk`) and
stored-constructor facts are new, everything else ignores the rule
list. -/
theorem extend_rec_swap {rules' : List RecRule}
    (m₀ : EnvModel V ⟨.recInfo cvA mI rP [] :: env.consts⟩)
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA mI rP rules' :: env.consts⟩
      (.recInfo cvA mI rP rules'))
    (hctors : ∀ r ∈ rules', ∃ cvj cnP cnF,
      env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hrecm : RecMemberOk (V := V)
      ⟨.recInfo cvA mI rP rules' :: env.consts⟩ m₀.val
      (.recInfo cvA mI rP rules')) :
    ∃ m' : EnvModel V ⟨.recInfo cvA mI rP rules' :: env.consts⟩,
      ∀ (n : Name) (ψ : Name → Nat), m'.val n ψ = m₀.val n ψ := by
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env).find? n :=
    fun n hn => Env.find?_recRules_swap rules' [] hn
  have henv10 := Env.recRules_levelext (env := env) (cvA := cvA)
    (mI := mI) (rP := rP) rules' []
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env) ψ e :=
    fun e ψ => interpClosed_recRules_swap rules' [] e ψ
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.recRules_swap [] rules' e ψ d ρ h
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
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
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA mI rP [])
        List.mem_cons_self ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨t, by rw [hitrans]; exact ht, hmem⟩
  · -- defn_eq
    intro cv2 v2 h2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · exact nomatch heq
    · have h := m₀.defn_eq cv2 v2 h2 (List.mem_cons_of_mem _ hmem2) ψ
      rw [hitrans]
      exact h
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA mI rP [])
        List.mem_cons_self ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 h2 heq => nomatch heq⟩
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok c (List.mem_cons_of_mem _ hc) ψ
      exact ⟨hAtrans01 _ ψ 0 (rho0 V) hA1,
        fun cv2 v2 h2 heq => hAtrans01 _ ψ 0 (rho0 V) (hA2 cv2 v2 h2 heq)⟩
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
      · have hfp₀ : (⟨.recInfo cvA mI rP [] ::
            env.consts⟩ : Env).find? n = some ci := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        exact i4 n ci hfp₀ hbasis hres2
    · -- BasisBlocks
      obtain ⟨b1, b2, b3, b4⟩ := i5
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro cv mI' rP' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b1 cv mI' rP' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv mI' rP' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2, f3⟩ := b2 cv mI' rP' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f3⟩
      · intro cv mI' rP' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b3 cv mI' rP' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
      · intro cv mI' rP' rules hfp
        rw [hfindEq _ (hneName _ (by decide))] at hfp
        obtain ⟨f1, f2⟩ := b4 cv mI' rP' rules hfp
        exact ⟨by rw [hfindEq _ (hneName _ (by decide))]; exact f1,
          by rw [hfindEq _ (hneName _ (by decide))]; exact f2⟩
    · -- RecCtorsStored
      intro n cv mI' rP' rules hfp r hr
      by_cases hn : cvA.name = n
      · subst hn
        rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA mI rP
            rules').name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4
        subst e4
        obtain ⟨cvj, cnP, cnF, hctor⟩ := hctors r hr
        refine ⟨cvj, cnP, cnF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
            rules').name = RecRule.ctor r from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj cnP cnF).name =
              RecRule.ctor r := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA mI rP [] ::
            env.consts⟩ : Env).find? n =
            some (.recInfo cv mI' rP' rules) := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        obtain ⟨cvj, cnP', cnF', hc⟩ := i6 n cv mI' rP' rules
          hfp₀ r hr
        refine ⟨cvj, cnP', cnF', ?_⟩
        have hnc : RecRule.ctor r ≠ cvA.name := by
          intro h
          rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA mI rP
              []).name = RecRule.ctor r from h.symm)] at hc
          exact nomatch (Option.some.inj hc)
        rw [hfindEq _ hnc]
        exact hc
  · -- rec_rules: the head's fold obligations are supplied, the rest
    -- ignores the rule list
    intro n cvR mI' rP' rules hfp r hr
    rw [Env.find?_cons] at hfp
    split at hfp
    · next hn =>
      obtain rfl : cvA.name = n := hn
      obtain hceq := Option.some.inj hfp
      exact hrecm cvR mI' rP' rules hceq r hr
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA mI rP [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR mI' rP' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
            []).name = n from hn)]
        exact hfp
      obtain ⟨hA, hle, hfold⟩ := m₀.rec_rules n cvR mI' rP' rules
        hfp₀ r hr
      refine ⟨fun ψ => hAtrans01 _ ψ 0 (rho0 V) (hA ψ), hle, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hplain hlev hfit
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        rw [h, Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA mI rP
            rules').name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA mI rP [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hplain hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules strLitSupported_cons_recRules hfit1,
          TeleFit.env_levelext henv10 natLitSupported_cons_recRules strLitSupported_cons_recRules hfit2, by
            rw [← mapM_interp_congr (fun e => interp_env_ext henv10
              natLitSupported_cons_recRules strLitSupported_cons_recRules
              e dd₂ ρρ₂)]
            exact hidx⟩
      refine ⟨R', ?_, hfoldEq, hRch⟩
      rw [hitrans]
      exact hRi
  · -- proj_ok: lookups only differ in the head's rule list
    refine ProjOk.env_swap
      (env₁ := ⟨.recInfo cvA mI rP [] :: env.consts⟩) ?_ m₀.proj_ok
    intro n
    by_cases h : cvA.name = n
    · subst h
      exact Or.inr ⟨cvA, mI, rP, [], rules',
        by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA mI rP []).name =
            cvA.name from rfl)],
        by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA mI rP rules').name =
            cvA.name from rfl)]⟩
    · exact Or.inl (Env.find?_recRules_swap rules' []
        (fun he => h he.symm))
  · -- modeled_ok: lookups only differ in the head's rule list
    obtain ⟨mo1, mo2, mo3, mo4, mo5⟩ := m₀.modeled_ok
    have hisoF : ∀ n,
        (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA mI rP rules')
        else (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA mI rP rules').name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules').name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA mI rP []).name = n from h)]
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
    · intro T j cv3 mI3 rP3 rules3 hf
      rw [hisoF] at hf
      split at hf
      · next hh =>
        obtain hceq := Option.some.inj hf
        injection hceq with e1 e2 e3 e4
        subst e1 e2 e3
        obtain ⟨hms, hveq⟩ := mo3 T j cvA mI rP []
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA mI rP []).name = projFnName T j from hh)])
        refine ⟨?_, hveq⟩
        rw [hisoF]
        split
        · rfl
        · exact hms
      · obtain ⟨hms, hveq⟩ := mo3 T j cv3 mI3 rP3 rules3 hf
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
            (TeleFit.env_levelext henv10 natLitSupported_cons_recRules strLitSupported_cons_recRules hfit)
    · intro T cvT caps hf hcapu hres
      rw [hisoF] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · have hlaw := mo5 T cvT caps hf hcapu hres
        intro φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy hfit
        exact hlaw φ'' us ps x y dd₁ ρρ₁ dd₂ ρρ₂ rrest hlen hx hy
          (TeleFit.env_levelext henv10 natLitSupported_cons_recRules strLitSupported_cons_recRules hfit)
  · -- nat_ops: lookups only differ in the head's rule list
    exact NatOpsOk.cons_recRules m₀.nat_ops
  · -- div_mod: value-level equations, only the lookups move
    exact DivModOk.cons_recRules m₀.div_mod

end RecRulesSwap

/-- The generic one-constant model extension: prepend a fresh constant
`ci` valued by a hand-supplied `v₀`.  Every `EnvModel` clause is
transported from the old model via valuation agreement on stored
names; the head's own obligations enter as hypotheses, phrased over
the *old* valuation.  `extend_model` and `extend_basis_one` are
wrappers around this lemma. -/
theorem extend_fresh {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (v₀ : (Name → Nat) → V)
    (hfind' : env.find? ci.name = none)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hdefn : ∀ cv2 value2 h2, ci = .defnInfo cv2 value2 h2 →
      value2.constsResolve env = true ∧
      (∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value2) ∧
      ∀ ψ : Name → Nat,
        interpClosed V m.val env ψ value2 = some (v₀ ψ))
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
    (hctors : ∀ cvR mI rP rules,
      ci = .recInfo cvR mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hmodv : reservedBasisNames.contains ci.name = false →
      ((∃ cv caps, ci = .indInfo cv caps) ∨
       (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (ci.name.str "_model") ψ)
    (hproj : ∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule), ci.name = projFnName T j →
      ci = .recInfo cv mI rP rules →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (projModelName T j) ψ)
    (hprojOk : ∀ entry, ci = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
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
        x = y)
    (hnatop : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
      (∀ n, n ≠ ci.name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      ∀ cv₀ v₀' h₀', ci = .defnInfo cv₀ v₀' h₀' → ci.name ∈ natOpNames →
      natOpGuard (⟨ci :: env.consts⟩ : Env) ci.name = true ∧
      ∀ eq ∈ natOpEquations 0 ci.name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V val' (⟨ci :: env.consts⟩ : Env) ψ 2 (rho0 V)
          (.const natName []) = some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V val' (⟨ci :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.1 =
        interpExpr V val' (⟨ci :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.2)
    (hdivmod : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
      (∀ n, n ≠ ci.name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      ∀ cv₀ v₀' h₀', ci = .defnInfo cv₀ v₀' h₀' →
      ci.name ∈ natDivModNames →
      natOpGuard (⟨ci :: env.consts⟩ : Env) ci.name = true ∧
      DivModEqs V val' ci.name) :
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
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
    intro cv2 value2 h2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · obtain ⟨hres2, -, hveq⟩ := hdefn cv2 value2 h2 heq.symm
      rw [htrans _ hres2 ψ, hveq ψ]
      have h1 : val' cv2.name ψ = v₀ ψ := by
        have hn2 : cv2.name = ci.name := by rw [← heq]; rfl
        simp [hval', hn2]
      rw [h1]
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 h2 rfl
      have := m.defn_eq cv2 value2 h2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ ci.name := by
        have := hfresh (.defnInfo cv2 value2 h2) hmem2
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨hAtrans _ htyres0 ψ (hAty ψ), ?_⟩
      intro cv2 value2 h2 heq
      obtain ⟨hres2, hAv, -⟩ := hdefn cv2 value2 h2 heq
      exact hAtrans _ hres2 ψ (hAv ψ)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 h2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 h2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 h2 heq)
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
  · -- proj_ok
    exact ProjOk.cons m.proj_ok hfind' hprojOk
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
    · intro T j cv3 mI3 rP3 rules3 hh hceq
      obtain ⟨hms, hveq⟩ := hproj T j cv3 mI3 rP3 rules3 hh hceq
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
  · -- nat_ops: preservation plus the forwarded head obligations
    refine NatOpsOk.cons m.nat_ops hfind' ?_ ?_
    · intro n hne ψ'
      simp [hval', hne]
    · exact hnatop val' (fun ψ => by simp [hval'])
        (fun n hne ψ' => by simp [hval', hne])
  · -- div_mod: preservation plus the forwarded head obligations
    refine DivModOk.cons m.div_mod hfind' ?_ ?_
    · intro n hne ψ'
      simp [hval', hne]
    · exact hdivmod val' (fun ψ => by simp [hval'])
        (fun n hne ψ' => by simp [hval', hne])
  · -- the new constant's value
    intro ψ
    simp [hval']
  · -- untouched values
    intro n ψ hne
    simp [hval', hne]

end Setlec
