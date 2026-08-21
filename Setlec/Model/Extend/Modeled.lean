import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Iota

/-!
# Modeled — split out of `Setlec.Model.Extend`

Extension by opaque modeled inductive-kind members:
`extend_modeled_one` for type formers and constructors,
`extend_modeled_rec` for recursors with checked iota rules, and the
`checkIndMember` inversion feeding them.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one opaque modeled inductive-kind member (an
inductive type former or constructor; the recursor carries rule
obligations and is handled separately): its value is its `_model`
counterpart's, and its type interprets identically through the block
renaming. -/
theorem extend_modeled_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (f : Name → Name) (mname : Name)
    {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv nP nM nm ni, ci = .recInfo cv nP nM nm ni []))
    (hmodel : env.find? mname = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : ci.toConstantVal.type.renameConsts f = cvm.type)
    (hro : RenameOk m.val env f)
    (hmodm : ((∃ cv caps, ci = .indInfo cv caps) ∨
        (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (ci.name.str "_model") ψ)
    (hprojm : ∀ (T : Name) (j : Nat), ci.name = projFnName T j →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, m.val mname ψ = m.val (projModelName T j) ψ)
    (hetaLm : ∀ cv caps, ci = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains ci.name = false →
      (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        (env.find? (projModelName ci.name j)).isSome = true) ∧
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.etaParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = SpineFold V (m.val (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us))
          (ps ++ (List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])))
    (hunitLm : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.unitParams →
        x ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        y ∈ˢ SpineFold V
          (m.val mname (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = y) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = m.val mname ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hmm : ConstantInfo.defnInfo cvm mval ∈ env.consts :=
    List.mem_of_find?_eq_some hmodel
  have hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧
        m.val (mname) ψ ∈ˢ T := by
    intro ψ
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ hmm ψ
    have hname : cvm.name = mname := by
      have := List.find?_some hmodel
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T, ?_, by rw [← hname]; exact hmem⟩
    have hri : interpClosed V m.val env ψ (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ ci.toConstantVal.type :=
      interp_renameConsts hro _ 0 (rho0 V)
    rw [← hri, hren]
    exact hT
  exact extend_basis_one m ci (fun ψ => m.val (mname) ψ)
    hfind' hwf htyres0
    (fun cv2 value2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩ <;> simp)
    hkey
    (fun ψ₁ ψ₂ hψ => by
      refine m.val_params _ _ hmodel ψ₁ ψ₂ ?_
      intro p hp
      refine hψ p ?_
      rwa [show (ConstantInfo.defnInfo cvm mval).toConstantVal = cvm from rfl,
        hlps] at hp)
    (fun ψ => by
      obtain ⟨hA, -⟩ := m.annot_ok _ hmm ψ
      have hA' : AnnotOk V m.val env ψ 0 (rho0 V)
          (ci.toConstantVal.type.renameConsts f) := by
        rw [hren]; exact hA
      exact AnnotOk_renameConsts hro _ 0 (rho0 V) hA')
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv nP nF heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun hn => absurd (hn ▸ hnres) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnres) (by simp))
    (fun cv nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · exact ⟨fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide)⟩)
    (fun val' _ _ cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)
    (fun cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nM', nm', ni', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)
    (fun _ => hmodm) hprojm hetaLm hunitLm

/-- Invert a successful `checkIndMember` run. -/
theorem checkIndMember_inv {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps F) blockNames caps env' ci = .ok env₁) :
    ∃ cvA cvm mval,
      checkConstantVal (fueledOps F) env' ci.toConstantVal = .ok cvA ∧
      cvA.name.isModelSuffix = false ∧
      env'.find? (cvA.name.str "_model") = some (.defnInfo cvm mval) ∧
      cvm.levelParams = cvA.levelParams ∧
      cvA.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n) = cvm.type ∧
      ((∃ cv caps', ci = .indInfo cv caps') ∧
         env₁ = ⟨.indInfo cvA caps :: env'.consts⟩ ∨
       (∃ cv nP nF, ci = .ctorInfo cv nP nF ∧
         env₁ = ⟨.ctorInfo cvA nP nF :: env'.consts⟩) ∨
       (∃ cv nP nm ni rules rules', ci = .recInfo cv nP 1 nm ni rules ∧
         blockNames.all (fun n =>
           n == cvA.name || (env'.find? n).isSome) = true ∧
         env'.find? eqName = some eqA ∧
         checkIotaRules (fueledOps F) env'
           ⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩
           (fun n => if blockNames.contains n then n.str "_model" else n)
           cvA.name cvA.levelParams cvA.type nP 1 nm ni 0 rules =
           .ok rules' ∧
         env₁ = ⟨.recInfo cvA nP 1 nm ni rules' :: env'.consts⟩)) := by
  simp only [checkIndMember, fueledOps_annotate, fueledOps_inferType, fueledOps_isDefEq,
    fueledOps_ensureSort, fueledOps_whnf, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps F) env' ci.toConstantVal with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  by_cases hms : cvA.name.isModelSuffix = true
  case pos => rw [if_pos hms] at h; exact nomatch h
  rw [if_neg hms] at h
  have hmsF : cvA.name.isModelSuffix = false := by
    revert hms; cases cvA.name.isModelSuffix <;> simp
  try dsimp only at h
  revert h
  match hfm : env'.find? (cvA.name.str "_model") with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cvm mval) => ?_
  intro h
  dsimp only at h
  by_cases hlps : cvm.levelParams = cvA.levelParams
  case neg => rw [if_neg hlps] at h; exact nomatch h
  rw [if_pos hlps] at h
  try dsimp only at h
  by_cases hren : (cvA.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n) ==
      cvm.type) = true
  case neg => rw [if_neg hren] at h; exact nomatch h
  rw [if_pos hren] at h
  try dsimp only at h
  refine ⟨cvA, cvm, mval, rfl, hmsF, hfm, hlps, eq_of_beq hren, ?_⟩
  cases ci with
  | axiomInfo cv => exact nomatch h
  | defnInfo cv value => exact nomatch h
  | thmInfo cv value => exact nomatch h
  | indInfo cv caps' =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨⟨cv, caps', rfl⟩, h.symm⟩
  | ctorInfo cv nP nF =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inr (Or.inl ⟨cv, nP, nF, rfl, h.symm⟩)
  | recInfo cv nP nM nm ni rules =>
    refine Or.inr (Or.inr ?_)
    simp only [Bind.bind, Except.bind] at h
    by_cases hnM : nM = 1
    case neg => rw [if_neg hnM] at h; exact nomatch h
    rw [if_pos hnM] at h
    subst hnM
    try dsimp only at h
    by_cases hall : (blockNames.all fun n =>
        n == cvA.name || (env'.find? n).isSome) = true
    case neg => rw [if_neg hall] at h; exact nomatch h
    rw [if_pos hall] at h
    try dsimp only at h
    by_cases heqf : env'.find? eqName = some eqA
    case neg => rw [if_neg heqf] at h; exact nomatch h
    rw [if_pos heqf] at h
    try dsimp only at h
    try dsimp only at h
    cases hcir : checkIotaRules (fueledOps F) env'
        ⟨.recInfo cvA nP 1 nm ni [] :: env'.consts⟩
        (fun n => if blockNames.contains n then n.str "_model" else n)
        cvA.name cvA.levelParams cvA.type nP 1 nm ni 0 rules with
    | error e => rw [hcir] at h; exact nomatch h
    | ok rules' =>
    rw [hcir] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨cv, nP, nm, ni, rules, rules', rfl, hall, heqf, hcir, h.symm⟩

/-- Extend a model by an opaque modeled *recursor*: its value is its
`_model`'s, and every rule's fold obligation is discharged by the
checked `iota` theorem (`modeled_rule_fold`).  Two-phase: the rule
right-hand sides were annotated against the provisional rules-free
recursor, whose model exists trivially; the final environment differs
only in the attached rule list, which the interpretation never
reads. -/
theorem extend_modeled_rec {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nm ni : Nat) (rules' : List RecRule)
    (f : Name → Name) {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hpshape : cvA.name.isProjFnShape = false)
    (hwf : ConstWF ⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩
      (.recInfo cvA nP 1 nm ni rules'))
    (htyres0 : cvA.type.constsResolve env = true)
    (hmodel : env.find? (cvA.name.str "_model") = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = cvA.levelParams)
    (hren : cvA.type.renameConsts f = cvm.type)
    (f₀ : Name → Name) (hro : RenameOk m.val env f₀)
    (hff₀ : ∀ n, n ≠ cvA.name → f n = f₀ n)
    (hfself : f cvA.name = cvA.name.str "_model")
    (hfnot : ∀ n, f n ≠ cvA.name)
    (heqfind : env.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m.val eqName ψ'' = eqVal V ψ'')
    (hrules : ∀ r ∈ rules', RuleChecked F env
      ⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ f cvA nP nm ni r) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val (cvA.name.str "_model") ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hisoRes : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).isSome := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h)]
  have hwf₀ : ConstWF (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env)
      (.recInfo cvA nP 1 nm ni []) := by
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
    (.recInfo cvA nP 1 nm ni []) f₀ (cvA.name.str "_model")
    hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, 1, nm, ni, rfl⟩)) hmodel hlps hren₀ hro
    (fun hk => by
      rcases hk with ⟨_, _, hcon⟩ | ⟨_, _, _, hcon⟩ <;> exact nomatch hcon)
    (fun T j hh => by
      have hh' : cvA.name = projFnName T j := hh
      rw [hh'] at hpshape
      exact nomatch hpshape)
    (fun cv caps hcon => nomatch hcon)
    (fun cv caps hcon => nomatch hcon)
  have henv01 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          []).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
          rules').name = n from h)]
  -- shared transports between the provisional and final environments
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n := by
    intro n hn
    rw [Env.find?_cons, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n
        from fun h => hn h.symm),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
        from fun h => hn h.symm)]
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env) ψ e := by
    intro e ψ
    exact (interp_env_ext henv01 natLitSupported_cons_recRules e 0 (rho0 V)).symm
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henv01 natLitSupported_cons_recRules e d ρ h
  have hCWtrans : ∀ c,
      ConstWF (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env) c →
      ConstWF (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) c := by
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
      (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) := by
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 1 nm ni [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
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
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := m₀.val) hfind' hres]
    exact interp_cval_ext hagreeM e 0 (rho0 V)
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ 0
        (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagreeM n hn ψ').symm)
      e 0 (rho0 V) ha
  have henv10 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n).map
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
      exact m₀.val_params n (.recInfo cvA nP 1 nm ni [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n
          from hn)]
      exact hf
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP 1 nm ni [])
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
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP 1 nm ni [])
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
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
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
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨cvj, cnF, _, _, _, _, _, _, _, _, _, _, _, _, _, hctor,
          hnf, -⟩ := hrules r hr
        refine ⟨cvj, nP, cnF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = RecRule.ctor r from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj nP cnF).name =
              RecRule.ctor r := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
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
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
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
      obtain ⟨cvj, cnF, raw, rbinders, tbinders, cbinders, sbinders,
        rbody, tybody, cbody, sbody, thmName, cvt, tval, ℓA,
        hctor, hnf, hann, hrawf, hrawb, hrhsf, hrhsb, hstripR,
        hR_strip, hC_strip, hclen, hS_strip, hdomsPre, hdomsF, hsdoms,
        hsbody, hthm, hlpt, -, -⟩ := hrules r hr
      have hncc : RecRule.ctor r ≠ cvA.name := by
        intro h
        have h2 := find?_none_ne hfind' _ (find?_mem hctor)
        have h3 : (ConstantInfo.ctorInfo cvj nP cnF).name =
            RecRule.ctor r := by
          have h4 := List.find?_some hctor
          simpa using h4
        exact h2 (by rw [h3, h])
      have hArhs₁ : ∀ ψ : Name → Nat,
          AnnotOk V m₀.val
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs r) := by
        intro ψ
        refine hAtrans01 _ ψ 0 (rho0 V) ?_
        exact annotate_sound m₀ raw hann (WScoped.of_not_hasFvar hrawf)
          hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
          (FvarsOk.of_not_hasFvar hrawf)
      refine ⟨hArhs₁, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hctor₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj nP cnF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = RecRule.ctor r from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2, hidx⟩ := hfit
      subst hψeq hψjeq
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) f := by
        refine ⟨?_, ?_, ?_⟩
        · intro n₂ ci₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · next hh =>
            obtain rfl := Option.some.inj hf₂
            refine ⟨.defnInfo cvm mval, ?_, ?_⟩
            · rw [show f n₂ = cvA.name.str "_model" from by
                rw [← (show cvA.name = n₂ from hh)]
                exact hfself]
              rw [Env.find?_cons,
                if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                  rules').name = cvA.name.str "_model" from
                  fun h => Name.str_ne cvA.name "_model" h.symm)]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP 1 nm ni
                  rules').toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                rules').name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
                rules').name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = cvA.name.str "_model" from hfself]
            rw [hpres₀ _ ψ₂ (Name.str_ne cvA.name "_model")]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hff₀ n₂ hh,
                hro.2.2 n₂]
      have hfRm₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? (f cvA.name) =
          some (.defnInfo cvm mval) := by
        rw [hfself, Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name.str "_model" from
            fun h => Name.str_ne cvA.name "_model" h.symm)]
        exact hmodel
      have heqne : eqName ≠ cvA.name := by
        intro h
        rw [← h] at hnres
        exact absurd hnres (by decide)
      have heqfind₁ : (⟨.recInfo cvA nP 1 nm ni rules' ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = eqName from fun h => heqne h.symm)]
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
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ''
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
            (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env) ψ'' 0
            (rho0 V) cvt.type := by
        intro ψ''
        obtain ⟨hA1, -⟩ := m.annot_ok _ (find?_mem hthm) ψ''
        exact hAtransM cvt.type hthres ψ'' hA1
      obtain ⟨hCtf, hCtp, -, hCtb, -, -⟩ := m.wf _ (find?_mem hctor)
      have htyw₁ : cvA.type.hasFvar = false := hwf.1
      have hClps₁ : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
          m₀.val (RecRule.ctor r) ψ₁ = m₀.val (RecRule.ctor r) ψ₂ :=
        fun ψ₁ ψ₂ hψ => hvp₁ _ _ hctor₁ ψ₁ ψ₂ (by exact hψ)
      have hl' : args.length = nP + 1 + nm + ni := by simpa using hl
      exact modeled_rule_fold (ni := ni) hro₁ hvp₁ hctor₁ hfRm₁
        (show (ConstantInfo.defnInfo cvm
          mval).toConstantVal.levelParams = cvA.levelParams from hlps)
        hClps₁ heqfind₁ heqval₁ hthm_mem₁ hthm_annot₁ hthw hstripR
        hR_strip hC_strip hclen hS_strip hdomsPre hdomsF hsdoms hsbody
        hrhsf hrhsb hArhs₁ htyw₁ hCtf hCtb
        (show cvj.type.allLevelParamsDefined cvj.levelParams = true from
          hCtp)
        hl' hml htv hpeq hlev hfit1 hfit2 hidx
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni
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
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni
            rules').name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP 1 nm ni [] ::
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
        (⟨.recInfo cvA nP 1 nm ni rules' :: env.consts⟩ : Env).find? n =
        if cvA.name = n then some (.recInfo cvA nP 1 nm ni rules')
        else (⟨.recInfo cvA nP 1 nm ni [] :: env.consts⟩ : Env).find? n := by
      intro n
      rw [Env.find?_cons]
      by_cases h : cvA.name = n
      · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n from h), if_pos h]
      · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni rules').name = n from h), if_neg h,
          Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm ni []).name = n from h)]
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
        obtain ⟨hms, hveq⟩ := mo3 T j (.recInfo cvA nP 1 nm ni [])
          (by rw [Env.find?_cons,
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm ni []).name = projFnName T j from hh)])
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
