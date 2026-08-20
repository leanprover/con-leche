import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall
import Setlec.Model.IndInstall

/-!
# Model extension steps

One lemma per way the checker extends the environment: plain constants
(`extend_model`), pinned basis constants (`extend_basis_one`), opaque
modeled inductive-kind members (`extend_modeled_one`) and modeled
recursors with their checked iota rules (`extend_modeled_rec`,
consuming the `RuleChecked` bundles that `checkIotaRules_inv`
extracts).  `Setlec.Model.Consistency` assembles these into
`checkDecl_sound`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

theorem find?_none_ne {env : Env} {n : Name} (h : env.find? n = none) :
    ∀ c ∈ env.consts, c.name ≠ n := by
  intro c hc
  have := List.find?_eq_none.mp h c hc
  simpa using this

/-- The sibling-availability data `BasisBlocks` preservation needs when
extending by one (fresh) constant: if the constant is a recursor-kind
record, the members of its block are already stored. -/
def SibFinds (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ cv nP nM nm ni rules, c₀ = .recInfo cv nP nM nm ni rules →
    (c₀.name = eqName.str "rec" →
      env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
    (c₀.name = natName.str "rec" →
      env.find? natName = some natA ∧
      env.find? natZeroName = some natZeroA ∧
      env.find? natSuccName = some natSuccA) ∧
    (c₀.name = psigmaName.str "rec" →
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA) ∧
    (c₀.name = punitName.str "rec" →
      env.find? punitName = some punitA ∧
      env.find? punitUnitName = some punitUnitA)

theorem BasisBlocks.cons {env : Env} {c₀ : ConstantInfo}
    (hb : BasisBlocks env) (hfind' : env.find? c₀.name = none)
    (hsib : SibFinds env c₀) :
    BasisBlocks (⟨c₀ :: env.consts⟩ : Env) := by
  have keep : ∀ {s : Name} {X : ConstantInfo}, env.find? s = some X →
      Env.find? ⟨c₀ :: env.consts⟩ s = some X := by
    intro s X hs
    rw [Env.find?_cons_of_isSome hfind' (by rw [hs]; rfl)]
    exact hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨hs, -, -, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.1 cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, hs, -, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2, h3⟩ := hs hn
      exact ⟨keep h1, keep h2, keep h3⟩
    · next hn =>
      obtain ⟨h1, h2, h3⟩ := hb.right.left cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2, keep h3⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, hs, -⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.left cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv nP nM nm ni rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, -, hs⟩ := hsib cv nP nM nm ni rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.right cv nP nM nm ni rules h
      exact ⟨keep h1, keep h2⟩

/-- The fold facts a single (freshly installed) recursor-kind member
must supply, phrased over the extended environment and valuation. -/
def RecMemberOk (env' : Env) (val' : ConstVal V)
    (ci : ConstantInfo) : Prop :=
  ∀ cvR nP nM nm ni rules, ci = .recInfo cvR nP nM nm ni rules →
    ∀ r ∈ rules,
      (∀ ψ : Name → Nat, AnnotOk V val' env' ψ 0 (rho0 V) (RecRule.rhs r)) ∧
      ∀ cvj cnP cnF,
        env'.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) →
        ∀ (ψ ψj : Name → Nat) (args margs : List V) (tv : V),
          args.length = nP + nM + nm + ni →
          margs.length = cnP + cnF →
          ChainSlots V (val' ci.name ψ) (args ++ [tv]) →
          ChainSlots V (val' (RecRule.ctor r) ψj) margs →
          tv = SpineFold V (val' (RecRule.ctor r) ψj) margs →
          margs.take cnP = (args ++ [tv]).take cnP →
          (∀ p ∈ cvj.levelParams, ψj p = ψ p) →
          (∃ (φ' : Name → Nat) (us usj : List Level) (d : Nat) (ρ : Nat → V)
              (d₁ : Nat) (ρ₁ : Nat → V) (rest₁ : Expr)
              (d₂ : Nat) (ρ₂ : Nat → V) (rest₂ : Expr),
            ψ = Level.substFn φ' cvR.levelParams us ∧
            ψj = Level.substFn φ' cvj.levelParams usj ∧
            TeleFit V val' env' φ' d ρ
              (cvR.type.instantiateLevelParams cvR.levelParams us)
              (args ++ [tv]) d₁ ρ₁ rest₁ ∧
            TeleFit V val' env' φ' d₁ ρ₁
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              margs d₂ ρ₂ rest₂) →
          ∃ R, interpClosed V val' env' ψ (RecRule.rhs r) = some R ∧
            SpineFold V (val' ci.name ψ) (args ++ [tv]) =
              SpineFold V R (args.take (nP + nM + nm) ++ margs.drop cnP) ∧
            ChainSlots V R (args.take (nP + nM + nm) ++ margs.drop cnP)

/-- `RecCtorsStored` is preserved by a fresh extension, given the
stored-constructor facts for the new member (vacuous unless it is a
recursor). -/
theorem RecCtorsStored.cons {env : Env} {c₀ : ConstantInfo}
    (hold : RecCtorsStored env) (hfresh : env.find? c₀.name = none)
    (hnew : ∀ cvR nP nM nm ni rules, c₀ = .recInfo cvR nP nM nm ni rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) :
    RecCtorsStored (⟨c₀ :: env.consts⟩ : Env) := by
  intro n cv nP nM nm ni rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    obtain ⟨cvj, cnP, cnF, hf⟩ := hnew _ _ _ _ _ _ hceq r hr
    refine ⟨cvj, cnP, cnF, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf
  · next hn =>
    obtain ⟨cvj, cnP, cnF, hf⟩ := hold n cv nP nM nm ni rules hfp r hr
    refine ⟨cvj, cnP, cnF, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf

/-- `RecRulesOk` is preserved by a fresh extension, given the fold
facts for the new member (vacuous unless it is a recursor). -/
theorem RecRulesOk.cons {env : Env} (m : EnvModel V env)
    {c₀ : ConstantInfo} {val' : ConstVal V}
    (hfind' : env.find? c₀.name = none)
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ)
    (htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e)
    (hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e)
    (hnewrec : RecMemberOk (V := V) ⟨c₀ :: env.consts⟩ val' c₀) :
    RecRulesOk V ⟨c₀ :: env.consts⟩ val' := by
  intro n cvR nP nM nm ni rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    subst hn
    exact hnewrec cvR nP nM nm ni rules hceq r hr
  · next hn =>
    obtain ⟨hA, hfold⟩ := m.rec_rules n cvR nP nM nm ni rules hfp r hr
    obtain ⟨-, -, -, -, -, hrules⟩ := m.wf _ (find?_mem hfp)
    obtain ⟨-, -, hrres, -⟩ := hrules cvR nP nM nm ni rules rfl r hr
    have hvaln : ∀ ψ : Name → Nat, val' n ψ = m.val n ψ :=
      fun ψ => hagree n (by rw [hfp]; rfl) ψ
    refine ⟨fun ψ => hAtrans _ hrres ψ (hA ψ), ?_⟩
    intro cvj cnP cnF hfj ψ ψj args margs tv hl hml hch hmch htv hpeq hlev
      hfit
    rw [Env.find?_cons] at hfj
    split at hfj
    · next hnc =>
      obtain ⟨cvj2, cnP2, cnF2, hfc2⟩ :=
        m.ind_ok.right.right.right.right.right.left n cvR nP nM nm ni rules
          hfp r hr
      rw [← hnc] at hfc2
      rw [hfind'] at hfc2
      exact nomatch hfc2
    · next hnc =>
      have hvalc : ∀ ψ' : Name → Nat,
          val' (RecRule.ctor r) ψ' = m.val (RecRule.ctor r) ψ' :=
        fun ψ' => hagree _ (by rw [hfj]; rfl) ψ'
      rw [hvaln] at hch
      rw [hvalc] at hmch htv
      have hfit' : ∃ (φ' : Name → Nat) (us usj : List Level) (d : Nat)
          (ρ : Nat → V) (d₁ : Nat) (ρ₁ : Nat → V) (rest₁ : Expr)
          (d₂ : Nat) (ρ₂ : Nat → V) (rest₂ : Expr),
          ψ = Level.substFn φ' cvR.levelParams us ∧
          ψj = Level.substFn φ' cvj.levelParams usj ∧
          TeleFit V m.val env φ' d ρ
            (cvR.type.instantiateLevelParams cvR.levelParams us)
            (args ++ [tv]) d₁ ρ₁ rest₁ ∧
          TeleFit V m.val env φ' d₁ ρ₁
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            margs d₂ ρ₂ rest₂ := by
        obtain ⟨φ', us, usj, d, ρ, d₁, ρ₁, rest₁, d₂, ρ₂, rest₂,
          hψ, hψj, hf1, hf2⟩ := hfit
        obtain ⟨-, -, hRres, -, -, -⟩ := m.wf _ (find?_mem hfp)
        obtain ⟨-, -, hCres, -, -, -⟩ := m.wf _ (find?_mem hfj)
        exact ⟨φ', us, usj, d, ρ, d₁, ρ₁, rest₁, d₂, ρ₂, rest₂, hψ, hψj,
          TeleFit.env_shrink hfind' hagree hf1
            (by rw [Expr.constsResolve_instantiateLevelParams]; exact hRres),
          TeleFit.env_shrink hfind' hagree hf2
            (by rw [Expr.constsResolve_instantiateLevelParams]; exact hCres)⟩
      obtain ⟨R, hRi, hfoldEq, hRch⟩ := hfold cvj cnP cnF hfj ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev hfit'
      refine ⟨R, ?_, ?_, hRch⟩
      · rw [htrans _ hrres ψ]
        exact hRi
      · rw [hvaln]
        exact hfoldEq

/-- Inversion for `checkConstantVal`. -/
theorem checkConstantVal_inv {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal env cv = .ok cv') :
    env.find? cv.name = none ∧
    reservedBasisNames.contains cv.name = false ∧
    Name.nodup cv.levelParams = true ∧
    cv.type.looseBVarsBounded 0 = true ∧
    cv.type.hasFvar = false ∧
    ∃ type stype u,
      annotate env 0 cv.type = .ok type ∧
      type.allLevelParamsDefined cv.levelParams = true ∧
      type.constsResolve env = true ∧
      inferType env 0 type = .ok stype ∧
      ensureSort env 0 stype = .ok u ∧
      cv' = { cv with type := type } := by
  simp only [checkConstantVal, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  by_cases hfind : (env.find? cv.name).isSome = true
  case pos => simp [hfind] at h
  simp only [hfind] at h
  by_cases hres : reservedBasisNames.contains cv.name = true
  case pos =>
    rw [if_pos hres] at h
    exact nomatch h
  simp only [hres] at h
  by_cases hnd : Name.nodup cv.levelParams = true
  case neg => simp [hnd] at h
  simp only [hnd] at h
  by_cases hlb : cv.type.looseBVarsBounded 0 = true
  case neg => simp [hlb] at h
  simp only [hlb] at h
  by_cases hif : cv.type.hasFvar = true
  case pos => simp [hif] at h
  simp only [hif] at h
  cases hann : annotate env 0 cv.type with
  | error e => rw [hann] at h; exact nomatch h
  | ok type =>
  rw [hann] at h
  try dsimp only at h
  by_cases htp : type.allLevelParamsDefined cv.levelParams = true
  case neg => simp [htp] at h
  simp only [htp] at h
  by_cases htr : type.constsResolve env = true
  case neg => simp [htr] at h
  simp only [htr] at h
  cases hst : inferType env 0 type with
  | error e => rw [hst] at h; exact nomatch h
  | ok stype =>
  rw [hst] at h
  try dsimp only at h
  cases hsort : ensureSort env 0 stype with
  | error e => rw [hsort] at h; exact nomatch h
  | ok u =>
  rw [hsort] at h
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  have hfind0 : env.find? cv.name = none := by
    revert hfind
    cases env.find? cv.name <;> simp
  exact ⟨hfind0, by simpa using hres, hnd, hlb, by simpa using hif,
    type, stype, u, rfl, htp, htr, hst, hsort, h.symm⟩

/-- The common model-extension argument, for a new constant `c₀` with an
annotated, checked type and value. -/
theorem extend_model {env : Env} (m : EnvModel V env)
    {name : Name} {lps : List Name} {type value : Expr}
    (hfind' : env.find? name = none)
    (htp : type.allLevelParamsDefined lps = true)
    (htf : type.hasFvar = false)
    (htr : type.constsResolve env = true)
    (htb : type.looseBVarsBounded 0 = true)
    (hvp : value.allLevelParamsDefined lps = true)
    (hvf : value.hasFvar = false)
    (hvr : value.constsResolve env = true)
    (hvb : value.looseBVarsBounded 0 = true)
    (hkey : ∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hAval : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value)
    (c₀ : ConstantInfo)
    (hc₀cv : c₀.toConstantVal = ⟨name, lps, type⟩)
    (hc₀name : c₀.name = name)
    (hc₀val : ∀ cv2 value2, c₀ = ConstantInfo.defnInfo cv2 value2 →
      cv2 = ⟨name, lps, type⟩ ∧ value2 = value)
    (hc₀nb : c₀.isBasis = false)
    (hc₀nres : reservedBasisNames.contains name = false) :
    Nonempty (EnvModel V ⟨c₀ :: env.consts⟩) := by
  have hfresh := find?_none_ne hfind'
  obtain ⟨val', hval'⟩ : ∃ val' : ConstVal V, val' = fun n ψ =>
      if n = name
      then (interpClosed V m.val env ψ value).getD SetTheory.empty
      else m.val n ψ := ⟨_, rfl⟩
  have hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ := by
    intro n hn ψ
    have : n ≠ name := by
      intro heq; rw [heq, hfind'] at hn; simp at hn
    simp [hval', this]
  have hc₀fresh : env.find? c₀.name = none := by rw [hc₀name]; exact hfind'
  have htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := val') hc₀fresh hres]
    exact interp_cval_ext hagree e 0 (rho0 V)
  have hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hc₀fresh e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagree n hn ψ').symm) e 0 (rho0 V) ha
  have hwf' : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons m.wf ?_
    rw [ConstWF, hc₀cv]
    refine ⟨htf, htp, Expr.constsResolve_mono htr, htb, ?_, ?_⟩
    · intro cv2 value2 heq
      obtain ⟨rfl, rfl⟩ := hc₀val cv2 value2 heq
      exact ⟨hvf, hvp, Expr.constsResolve_mono hvr, hvb⟩
    · intro cv nP nM nm ni rules heq
      rw [heq] at hc₀nb
      simp [ConstantInfo.isBasis] at hc₀nb
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- val_params
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      have hncv : n = name := by rw [← hn, hc₀name]
      subst hncv
      simp only [hval', if_pos rfl]
      have : interpClosed V m.val env ψ₁ value = interpClosed V m.val env ψ₂ value := by
        unfold interpClosed
        refine interp_params_ext m.val_params ?_ value 0 (rho0 V) hvp
        intro p hp
        refine hψ p ?_
        rw [hc₀cv]
        exact hp
      rw [this]
    · next hn =>
      have hne : n ≠ name := by
        intro heq
        rw [heq, hfind'] at hf
        exact nomatch hf
      simp only [hval', if_neg hne]
      exact m.val_params n ci hf ψ₁ ψ₂ hψ
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨v, T, hv, hT, hmem⟩ := hkey ψ
      refine ⟨T, ?_, ?_⟩
      · rw [hc₀cv]
        exact (htrans type htr ψ).trans hT
      · rw [hc₀name]
        simp only [hval', if_pos rfl, hv, Option.getD_some]
        exact hmem
    · obtain ⟨t, ht, hmem⟩ := m.mem_type c hc ψ
      obtain ⟨-, -, hres, -⟩ := m.wf c hc
      refine ⟨t, ?_, ?_⟩
      · rw [htrans c.toConstantVal.type hres ψ]
        exact ht
      · have hne : c.name ≠ name := hfresh c hc
        simp [hval', hne, hmem]
  · -- defn_eq
    intro cv2 value2 hmem2 ψ
    rcases List.mem_cons.mp hmem2 with heq | hmem2
    · obtain ⟨hcv2, hval2⟩ := hc₀val cv2 value2 heq.symm
      obtain ⟨v, T, hv, -, -⟩ := hkey ψ
      rw [hval2, htrans value hvr ψ, hv, hcv2]
      simp [hval', hv]
    · obtain ⟨-, -, -, -, hvalwf, -⟩ := m.wf _ hmem2
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 rfl
      have := m.defn_eq cv2 value2 hmem2 ψ
      rw [htrans _ hres2 ψ, this]
      have hne : cv2.name ≠ name :=
        hfresh (.defnInfo cv2 value2) hmem2
      simp [hval', hne]
  · -- annot_ok
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · refine ⟨?_, ?_⟩
      · rw [hc₀cv]
        exact hAtrans type htr ψ (hAty ψ)
      · intro cv2 value2 heq
        obtain ⟨-, hval2⟩ := hc₀val cv2 value2 heq
        rw [hval2]
        exact hAtrans value hvr ψ (hAval ψ)
    · obtain ⟨-, -, htyres, -, hvalwf, -⟩ := m.wf c hc
      obtain ⟨hA1, hA2⟩ := m.annot_ok c hc ψ
      refine ⟨hAtrans _ htyres ψ hA1, ?_⟩
      intro cv2 value2 heq
      obtain ⟨-, -, hres2, -⟩ := hvalwf cv2 value2 heq
      exact hAtrans _ hres2 ψ (hA2 cv2 value2 heq)
  · -- ind_ok: the fresh constant is a definition or theorem, so every
    -- inductive-kind lookup still resolves to the old environment, and
    -- the valuation agrees there.
    refine ⟨?_, ?_, ?_, ?_, BasisBlocks.cons m.ind_ok.right.right.right.right.left
      hc₀fresh (fun cv nP nM nm ni rules heq => by
        rw [heq] at hc₀nb
        simp [ConstantInfo.isBasis] at hc₀nb),
      RecCtorsStored.cons m.ind_ok.right.right.right.right.right.left hc₀fresh
        (fun cvR nP nM nm ni rules heq => by
          rw [heq] at hc₀nb
          simp [ConstantInfo.isBasis] at hc₀nb), ?_⟩
    · intro cv hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv hfp
        refine ⟨hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaName ψ = m.val psigmaName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv nP nF hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : psigmaMkName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.ctorInfo cv nP nF).name = psigmaMkName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hnP, hnF, hlp, hfacts⟩ := m.ind_ok.right.left cv nP nF hfp
        refine ⟨hnP, hnF, hlp, fun ψ => ?_⟩
        have hvagree : val' psigmaMkName ψ = m.val psigmaMkName ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hfacts ψ
    · intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : punitName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := find?_none_ne hfind' _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hvagree : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hvagree] at hx
        exact m.ind_ok.right.right.left cv hfp ψ x hx
    · intro n ci hfp hbasis hguard
      have hguard' : env.find? (n.str "_model") = none := by
        rw [Env.find?_cons] at hguard
        revert hguard
        split
        · intro hguard; exact nomatch hguard
        · intro hguard; exact hguard
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        rw [hc₀nb] at hbasis
        exact nomatch hbasis
      · next hn =>
        have hne : n ≠ name := by
          intro hcontra
          rw [hcontra, hfind'] at hfp
          exact nomatch hfp
        obtain ⟨hpi, hpv⟩ := m.ind_ok.right.right.right.left n ci hfp
          hbasis hguard'
        refine ⟨hpi, fun ψ => ?_⟩
        have hvagree : val' n ψ = m.val n ψ := by
          simp [hval', hne]
        rw [hvagree]
        exact hpv ψ
    · -- the Empty type stays uninhabited
      intro ψ x hx
      have hne : emptyName ≠ name := by
        intro hcontra
        rw [← hcontra] at hc₀nres
        exact absurd hc₀nres (by decide)
      have hvagree : val' emptyName ψ = m.val emptyName ψ := by
        simp [hval', hne]
      rw [hvagree] at hx
      exact m.ind_ok.right.right.right.right.right.right ψ x hx
  · -- rec_rules: no recursor is added
    exact RecRulesOk.cons m hc₀fresh
      (fun n hn ψ => hagree n hn ψ)
      (fun e hres ψ => htrans e hres ψ)
      (fun e hres ψ hAe => hAtrans e hres ψ hAe)
      (fun cvR nP nM nm ni rules heq => by
        rw [heq] at hc₀nb
        simp [ConstantInfo.isBasis] at hc₀nb)

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
    (hnewty : ∀ cv, ci = .indInfo cv → ci.name = psigmaName →
      cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairTyFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewmk : ∀ cv nP nF, ci = .ctorInfo cv nP nF → ci.name = psigmaMkName →
      nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairMkFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewunit : ∀ cv, ci = .indInfo cv → ci.name = punitName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → x = pt)
    (hnewempty : ci.name = emptyName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → False)
    (hpin : ci.isBasis = true → env.find? (ci.name.str "_model") = none →
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
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) :
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
  refine ⟨⟨val', hwf', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
    · intro cv hfp
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hlp, hfacts⟩ := hnewty cv rfl hn
        refine ⟨hlp, fun ψ => ?_⟩
        have hval'eq : val' psigmaName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq]
        exact hfacts ψ
      · next hn =>
        have hne : psigmaName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = psigmaName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        obtain ⟨hlp, hfacts⟩ := m.ind_ok.1 cv hfp
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
    · intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        have hval'eq : val' punitName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq] at hx
        exact hnewunit cv rfl hn ψ x hx
      · next hn =>
        have hne : punitName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = punitName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hval'eq : val' punitName ψ = m.val punitName ψ := by
          simp [hval', hne]
        rw [hval'eq] at hx
        exact m.ind_ok.right.right.left cv hfp ψ x hx
    · intro n ci' hfp hbasis hguard
      have hguard' : env.find? (n.str "_model") = none := by
        rw [Env.find?_cons] at hguard
        revert hguard
        split
        · intro hguard; exact nomatch hguard
        · intro hguard; exact hguard
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        obtain ⟨hpi, hpv⟩ := hpin hbasis (by rw [hn]; exact hguard')
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
          hbasis hguard'
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
  · -- the new constant's value
    intro ψ
    simp [hval']
  · -- untouched values
    intro n ψ hne
    simp [hval', hne]

/-- Extend a model by one opaque modeled inductive-kind member (an
inductive type former or constructor; the recursor carries rule
obligations and is handled separately): its value is its `_model`
counterpart's, and its type interprets identically through the block
renaming. -/
theorem extend_modeled_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (f : Name → Name) {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hkind : (∃ cv, ci = .indInfo cv) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv nP nm, ci = .recInfo cv nP 1 nm 0 []))
    (hmodel : env.find? (ci.name.str "_model") = some (.defnInfo cvm mval))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : ci.toConstantVal.type.renameConsts f = cvm.type)
    (hro : RenameOk m.val env f) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = m.val (ci.name.str "_model") ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hmm : ConstantInfo.defnInfo cvm mval ∈ env.consts :=
    List.mem_of_find?_eq_some hmodel
  have hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧
        m.val (ci.name.str "_model") ψ ∈ˢ T := by
    intro ψ
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ hmm ψ
    have hname : cvm.name = ci.name.str "_model" := by
      have := List.find?_some hmodel
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T, ?_, by rw [← hname]; exact hmem⟩
    have hri : interpClosed V m.val env ψ (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ ci.toConstantVal.type :=
      interp_renameConsts hro _ 0 (rho0 V)
    rw [← hri, hren]
    exact hT
  exact extend_basis_one m ci (fun ψ => m.val (ci.name.str "_model") ψ)
    hfind' hwf htyres0
    (fun cv2 value2 => by
      rcases hkind with ⟨cv', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nm', rfl⟩ <;> simp)
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
    (fun cv heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv nP nF heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv heq hn => absurd (hn ▸ hnres) (by decide))
    (fun hn => absurd (hn ▸ hnres) (by decide))
    (fun _ hguard => nomatch (hguard ▸ hmodel))
    (fun cv nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nm', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · exact ⟨fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide)⟩)
    (fun val' _ _ cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nm', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)
    (fun cvR nP nM nm ni rules heq => by
      rcases hkind with ⟨cv', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', nP', nm', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4 h5 h6
        subst h6
        intro r hr
        cases hr)

/-- The kernel-checked data of one modeled recursor rule: the
hypothesis kit its fold obligation consumes.  `env` is the environment
before the recursor's installation, `env₀` the provisional one with
the rules-free recursor (in which the rule's right-hand side was
annotated). -/
def RuleChecked (env env₀ : Env) (f : Name → Name)
    (cvA : ConstantVal) (nP nm : Nat) (r : RecRule) : Prop :=
  ∃ (cvj : ConstantVal) (cnF : Nat) (raw : Expr)
    (rbinders tbinders cbinders sbinders :
      List (Name × Expr × BinderMeta))
    (rbody tybody cbody sbody : Expr)
    (thmName : Name) (cvt : ConstantVal) (tval : Expr) (ℓA : Level),
    env.find? (RecRule.ctor r) = some (.ctorInfo cvj nP cnF) ∧
    r.nfields = cnF ∧
    annotate env₀ 0 raw = .ok (RecRule.rhs r) ∧
    raw.hasFvar = false ∧ raw.looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).hasFvar = false ∧
    (RecRule.rhs r).looseBVarsBounded 0 = true ∧
    (RecRule.rhs r).stripLams (nP + 1 + nm + cnF) =
      some (rbinders, rbody) ∧
    cvA.type.stripPis (nP + 1 + nm + 1) = some (tbinders, tybody) ∧
    cvj.type.stripPis (nP + cnF) = some (cbinders, cbody) ∧
    cvt.type.stripPis ((nP + (1 + nm)) + cnF) = some (sbinders, sbody) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      i < nP + 1 + nm →
      rbinders[i]? = some b → tbinders[i]? = some b' →
      b.2.1 = b'.2.1) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      rbinders[(nP + (1 + nm)) + i]? = some b →
      cbinders[nP + i]? = some b' →
      b.2.1 = (b'.2.1).liftLooseBVars (1 + nm) i) ∧
    (∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
      sbinders[i]? = some b → rbinders[i]? = some b' →
      b.2.1 = (b'.2.1).renameConsts f) ∧
    sbody = Expr.mkAppN (.const eqName [ℓA])
      [.app (.bvar (cnF + nm))
        (Expr.mkAppN (.const (f (RecRule.ctor r))
            (cvj.levelParams.map .param))
          (((List.range nP).map fun k =>
              Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
           ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))),
       Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
        ((((List.range nP).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
          ((List.range (1 + nm)).map fun k =>
            Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))) ++
         [Expr.mkAppN (.const (f (RecRule.ctor r))
             (cvj.levelParams.map .param))
           (((List.range nP).map fun k =>
               Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
            ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))]),
       rbody.renameConsts f] ∧
    env.find? thmName = some (.thmInfo cvt tval) ∧
    cvt.levelParams = cvA.levelParams ∧
    (RecRule.rhs r).allLevelParamsDefined cvA.levelParams = true ∧
    (RecRule.rhs r).constsResolve env₀ = true

theorem domsMatchAux_inv {g : Nat → Expr → Expr}
    {bs₁ bs₂ : List (Name × Expr × BinderMeta)} {o₁ o₂ n : Nat}
    (h : domsMatchAux g bs₁ bs₂ o₁ o₂ n = true)
    {i : Nat} (hi : i < n) {b b' : Name × Expr × BinderMeta}
    (hb : bs₁[o₁ + i]? = some b) (hb' : bs₂[o₂ + i]? = some b') :
    b.2.1 = g i b'.2.1 := by
  have hone := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hb, hb'] at hone
  exact eq_of_beq hone

/-- Invert a successful `checkIotaRules` run: every returned rule
carries the full `RuleChecked` hypothesis kit. -/
theorem checkIotaRules_inv {env' envSelf : Env} {f : Name → Name}
    {cvA : ConstantVal} {nP nm : Nat} :
    ∀ (j : Nat) (rules rules' : List RecRule),
    checkIotaRules env' envSelf f cvA.name cvA.levelParams cvA.type
      nP 1 nm j rules = .ok rules' →
    ∀ r' ∈ rules', RuleChecked env' envSelf f cvA nP nm r' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h r' hr'
    simp only [checkIotaRules, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact nomatch hr'
  | cons r rest ih =>
    intro rules' h r' hr'
    simp only [checkIotaRules, Bind.bind, Except.bind] at h
    revert h
    match hfc : env'.find? r.ctor with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
    | some (.ctorInfo cvj cnP cnF) => ?_
    intro h
    dsimp only at h
    by_cases hcnP : cnP = nP
    case neg => rw [if_neg hcnP] at h; exact nomatch h
    rw [if_pos hcnP] at h
    subst cnP
    try dsimp only at h
    by_cases hnf : r.nfields = cnF
    case neg => rw [if_neg hnf] at h; exact nomatch h
    rw [if_pos hnf] at h
    try dsimp only at h
    by_cases hrb : r.rhs.looseBVarsBounded 0 = true
    case neg => rw [if_neg hrb] at h; exact nomatch h
    rw [if_pos hrb] at h
    try dsimp only at h
    by_cases hrf : r.rhs.hasFvar = true
    case pos => rw [if_pos hrf] at h; exact nomatch h
    rw [if_neg hrf] at h
    have hrfF : r.rhs.hasFvar = false := by
      revert hrf; cases r.rhs.hasFvar <;> simp
    try dsimp only at h
    cases hann : annotate envSelf 0 r.rhs with
    | error e => rw [hann] at h; exact nomatch h
    | ok rhsA =>
    rw [hann] at h
    try dsimp only at h
    by_cases hrlp : rhsA.allLevelParamsDefined cvA.levelParams = true
    case neg => rw [if_neg hrlp] at h; exact nomatch h
    rw [if_pos hrlp] at h
    try dsimp only at h
    by_cases hrres : rhsA.constsResolve envSelf = true
    case neg => rw [if_neg hrres] at h; exact nomatch h
    rw [if_pos hrres] at h
    try dsimp only at h
    revert h
    match hstR : rhsA.stripLams (nP + 1 + nm + cnF) with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨rbinders, rbody⟩ := pr
    dsimp only at h
    revert h
    match hstT : cvA.type.stripPis (nP + 1 + nm + 1) with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨tbinders, tybody⟩ := pr
    dsimp only at h
    revert h
    match hstC : cvj.type.stripPis (nP + cnF) with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨cbinders, cbody⟩ := pr
    dsimp only at h
    by_cases hallPre : domsMatchAux (fun _ e => e) rbinders tbinders 0 0
        (nP + 1 + nm) = true
    case neg => rw [if_neg hallPre] at h; exact nomatch h
    rw [if_pos hallPre] at h
    try dsimp only at h
    by_cases hallF : domsMatchAux (fun i e => e.liftLooseBVars (1 + nm) i)
        rbinders cbinders (nP + 1 + nm) nP cnF = true
    case neg => rw [if_neg hallF] at h; exact nomatch h
    rw [if_pos hallF] at h
    try dsimp only at h
    cases hity : inferType envSelf 0 rhsA with
    | error e => rw [hity] at h; exact nomatch h
    | ok rhsTy =>
    rw [hity] at h
    try dsimp only at h
    revert h
    match hbuild : buildIotaStmt f cvA.name r.ctor cvA.levelParams
        cvj.levelParams nP 1 nm cnF cvA.type cvj.type r.rhs with
    | none => intro h; exact nomatch h
    | some stmtRaw => ?_
    intro h
    dsimp only at h
    cases hstmtA : annotate env' 0 stmtRaw with
    | error e => rw [hstmtA] at h; exact nomatch h
    | ok stmtA =>
    rw [hstmtA] at h
    try dsimp only at h
    revert h
    match hfthm : env'.find? ((cvA.name.str "_model").str s!"iota_{j}") with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _) => intro h; exact nomatch h
    | some (.indInfo _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
    | some (.thmInfo cvt tval) => ?_
    intro h
    dsimp only at h
    by_cases hlpt : cvt.levelParams = cvA.levelParams
    case neg => rw [if_neg hlpt] at h; exact nomatch h
    rw [if_pos hlpt] at h
    try dsimp only at h
    by_cases hbeq : (cvt.type == stmtA) = true
    case neg => rw [if_neg hbeq] at h; exact nomatch h
    rw [if_pos hbeq] at h
    try dsimp only at h
    revert h
    match hstS : cvt.type.stripPis (nP + 1 + nm + cnF) with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨sbinders, sbody⟩ := pr
    dsimp only at h
    by_cases hallS : domsMatchAux (fun _ e => e.renameConsts f)
        sbinders rbinders 0 0 (nP + 1 + nm + cnF) = true
    case neg => rw [if_neg hallS] at h; exact nomatch h
    rw [if_pos hallS] at h
    try dsimp only at h
    revert h
    match hmb : rbinders[nP]? with
    | none => intro h; exact nomatch h
    | some pr => ?_
    intro h
    obtain ⟨mna, mdomA, mbm⟩ := pr
    dsimp only at h
    revert h
    match hms : mdomA.resultSort with
    | none => intro h; exact nomatch h
    | some ℓA => ?_
    intro h
    dsimp only at h
    by_cases hsbeq : (sbody == Expr.mkAppN (.const eqName [ℓA])
        [.app (.bvar (cnF + nm + (1 - 1)))
          (Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
            (((List.range nP).map fun k =>
                Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
             ((List.range cnF).map fun k => Expr.bvar (cnF - 1 - k)))),
         Expr.mkAppN (.const (f cvA.name) (cvA.levelParams.map .param))
          ((((List.range nP).map fun k =>
              Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
            ((List.range (1 + nm)).map fun k =>
              Expr.bvar (nP + 1 + nm + cnF - 1 - nP - k))) ++
           [Expr.mkAppN (.const (f r.ctor) (cvj.levelParams.map .param))
             (((List.range nP).map fun k =>
                 Expr.bvar (nP + 1 + nm + cnF - 1 - k)) ++
              ((List.range cnF).map fun k =>
                Expr.bvar (cnF - 1 - k)))]),
         rbody.renameConsts f]) = true
    case neg => rw [if_neg hsbeq] at h; exact nomatch h
    rw [if_pos hsbeq] at h
    try dsimp only at h
    cases hrec : checkIotaRules env' envSelf f cvA.name cvA.levelParams
        cvA.type nP 1 nm (j + 1) rest with
    | error e => rw [hrec] at h; exact nomatch h
    | ok rest' =>
    rw [hrec] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    case inr => exact ih (j + 1) rest' hrec r' hr'
    -- the head rule
    unfold RuleChecked
    have hrlen : rbinders.length = nP + 1 + nm + cnF :=
      Expr.stripLams_length _ hstR
    have htlen : tbinders.length = nP + 1 + nm + 1 :=
      Expr.stripPis_length _ hstT
    have hclen : cbinders.length = nP + cnF :=
      Expr.stripPis_length _ hstC
    have hslen : sbinders.length = nP + 1 + nm + cnF :=
      Expr.stripPis_length _ hstS
    refine ⟨cvj, cnF, r.rhs, rbinders, tbinders, cbinders, sbinders,
      rbody, tybody, cbody, sbody,
      (cvA.name.str "_model").str s!"iota_{j}", cvt, tval, ℓA,
      hfc, hnf, hann, hrfF, hrb, ?_, ?_, hstR, hstT, hstC, ?_,
      ?_, ?_, ?_, ?_, hfthm, hlpt, hrlp, hrres⟩
    · -- rhsA has no fvars
      exact not_hasFvar_of_fvarsBelow_zero
        ((annotate_WScoped _ hann (WScoped.of_not_hasFvar hrfF)).fvarsBelow)
    · -- rhsA stays closed
      exact annotate_looseBVars _ hann hrb
    · -- statement strip at the reassociated arity
      rw [show (nP + (1 + nm)) + cnF = nP + 1 + nm + cnF from by omega]
      exact hstS
    · -- prefix domains
      intro i b b' hi hb hb'
      exact domsMatchAux_inv hallPre hi
        (by rw [Nat.zero_add]; exact hb) (by rw [Nat.zero_add]; exact hb')
    · -- field domains
      intro i b b' hbF hcF
      have hicnF : i < cnF := by
        rcases Nat.lt_or_ge i cnF with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hcF
          exact nomatch hcF
      exact domsMatchAux_inv hallF hicnF
        (by rw [show nP + 1 + nm + i = (nP + (1 + nm)) + i from by omega]
            exact hbF) hcF
    · -- statement domains
      intro i b b' hsb hrbi
      have hi : i < nP + 1 + nm + cnF := by
        rcases Nat.lt_or_ge i (nP + 1 + nm + cnF) with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at hsb
          exact nomatch hsb
      exact domsMatchAux_inv hallS hi
        (by rw [Nat.zero_add]; exact hsb) (by rw [Nat.zero_add]; exact hrbi)
    · -- the pinned equation body
      exact eq_of_beq hsbeq

/-- Extend a model by an opaque modeled *recursor*: its value is its
`_model`'s, and every rule's fold obligation is discharged by the
checked `iota` theorem (`modeled_rule_fold`).  Two-phase: the rule
right-hand sides were annotated against the provisional rules-free
recursor, whose model exists trivially; the final environment differs
only in the attached rule list, which the interpretation never
reads. -/
theorem extend_modeled_rec {env : Env} (m : EnvModel V env)
    (cvA : ConstantVal) (nP nm : Nat) (rules' : List RecRule)
    (f : Name → Name) {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? cvA.name = none)
    (hnres : reservedBasisNames.contains cvA.name = false)
    (hwf : ConstWF ⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩
      (.recInfo cvA nP 1 nm 0 rules'))
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
    (hrules : ∀ r ∈ rules', RuleChecked env
      ⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ f cvA nP nm r) :
    ∃ m' : EnvModel V ⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩,
      (∀ ψ, m'.val cvA.name ψ = m.val (cvA.name.str "_model") ψ) ∧
      (∀ n ψ, n ≠ cvA.name → m'.val n ψ = m.val n ψ) := by
  -- phase 0: install the rules-free provisional recursor
  have hisoRes : ∀ n,
      ((⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env).find? n).isSome := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
          rules').name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
          []).name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
          rules').name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
          []).name = n from h)]
  have hwf₀ : ConstWF (⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env)
      (.recInfo cvA nP 1 nm 0 []) := by
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
    (.recInfo cvA nP 1 nm 0 []) f₀ hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, nm, rfl⟩)) hmodel hlps hren₀ hro
  have henv01 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases h : cvA.name = n
    · rw [if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
          []).name = n from h),
        if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
          rules').name = n from h)]
      rfl
    · rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
          []).name = n from h),
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
          rules').name = n from h)]
  -- shared transports between the provisional and final environments
  have hfindEq : ∀ n, n ≠ cvA.name →
      (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env).find? n =
      (⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env).find? n := by
    intro n hn
    rw [Env.find?_cons, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0 rules').name = n
        from fun h => hn h.symm),
      if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0 []).name = n
        from fun h => hn h.symm)]
  have hitrans : ∀ (e : Expr) (ψ : Name → Nat),
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m₀.val
        (⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env) ψ e := by
    intro e ψ
    exact (interp_env_ext henv01 e 0 (rho0 V)).symm
  have hAtrans01 : ∀ (e : Expr) (ψ : Name → Nat) (d : Nat) (ρ : Nat → V),
      AnnotOk V m₀.val (⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env)
        ψ d ρ e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ d ρ e :=
    fun e ψ d ρ h => AnnotOk.env_ext henv01 e d ρ h
  have hCWtrans : ∀ c,
      ConstWF (⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env) c →
      ConstWF (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) c := by
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
      (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) := by
    intro n ci hf ψ₁ ψ₂ hψ
    rw [Env.find?_cons] at hf
    split at hf
    · next hn =>
      obtain rfl := Option.some.inj hf
      exact m₀.val_params n (.recInfo cvA nP 1 nm 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0 []).name = n
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
        (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ e =
      interpClosed V m.val env ψ e := by
    intro e hres ψ
    rw [interpClosed_mono (cval := m₀.val) hfind' hres]
    exact interp_cval_ext hagreeM e 0 (rho0 V)
  have hAtransM : ∀ (e : Expr), e.constsResolve env = true →
      ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V m₀.val
        (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ 0
        (rho0 V) e := by
    intro e hres ψ ha
    refine AnnotOk.mono hfind' e 0 (rho0 V) hres ?_
    exact AnnotOk.cval_ext (fun n hn ψ' => (hagreeM n hn ψ').symm)
      e 0 (rho0 V) ha
  have henv10 : ∀ n,
      ((⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP 1 nm 0 [] :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) :=
    fun n => (henv01 n).symm
  refine ⟨⟨m₀.val, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
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
      exact m₀.val_params n (.recInfo cvA nP 1 nm 0 [])
        (by rw [Env.find?_cons,
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0 []).name = n
            from hn)]) ψ₁ ψ₂ (by exact hψ)
    · next hn =>
      refine m₀.val_params n ci ?_ ψ₁ ψ₂ hψ
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0 []).name = n
          from hn)]
      exact hf
  · -- mem_type
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain ⟨t, ht, hmem⟩ := m₀.mem_type (.recInfo cvA nP 1 nm 0 [])
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
    · obtain ⟨hA1, hA2⟩ := m₀.annot_ok (.recInfo cvA nP 1 nm 0 [])
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
    · intro cv hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i1 cv hfp
    · intro cv nP' nF' hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i2 cv nP' nF' hfp
    · intro cv hfp
      rw [hfindEq _ (hneName _ (by decide))] at hfp
      exact i3 cv hfp
    · -- decl_ok
      intro n ci hfp hbasis hguard
      by_cases hn : cvA.name = n
      · exfalso
        subst hn
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = cvA.name.str "_model" from
            fun h => Name.str_ne cvA.name "_model" h.symm)] at hguard
        rw [hguard] at hmodel
        exact nomatch hmodel
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm 0 [] ::
            env.consts⟩ : Env).find? n = some ci := by
          rw [← hfindEq n (fun h => hn h.symm)]
          exact hfp
        have hguard₀ : (⟨.recInfo cvA nP 1 nm 0 [] ::
            env.consts⟩ : Env).find? (n.str "_model") = none := by
          rw [Env.find?_cons] at hguard ⊢
          split at hguard
          · exact nomatch hguard
          · next hh =>
            rw [if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
              []).name = n.str "_model" from hh)]
            exact hguard
        exact i4 n ci hfp₀ hbasis hguard₀
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
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = cvA.name from rfl)] at hfp
        obtain heq := Option.some.inj hfp
        injection heq with e1 e2 e3 e4 e5 e6
        subst e6
        obtain ⟨cvj, cnF, _, _, _, _, _, _, _, _, _, _, _, _, _, hctor,
          hnf, -⟩ := hrules r hr
        refine ⟨cvj, nP, cnF, ?_⟩
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = RecRule.ctor r from ?_)]
        · exact hctor
        · intro h
          have h2 := find?_none_ne hfind' _ (find?_mem hctor)
          have h3 : (ConstantInfo.ctorInfo cvj nP cnF).name =
              RecRule.ctor r := by
            have h4 := List.find?_some hctor
            simpa using h4
          exact h2 (by rw [h3, ← h]; rfl)
      · have hfp₀ : (⟨.recInfo cvA nP 1 nm 0 [] ::
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
            if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
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
        hR_strip, hC_strip, hS_strip, hdomsPre, hdomsF, hsdoms,
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
            (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ 0
            (rho0 V) (RecRule.rhs r) := by
        intro ψ
        refine hAtrans01 _ ψ 0 (rho0 V) ?_
        exact annotate_sound m₀ raw hann (WScoped.of_not_hasFvar hrawf)
          hrawb (Expr.LeavesBounded.of_not_hasFvar hrawf) (rho0 V)
          (FvarsOk.of_not_hasFvar hrawf)
      refine ⟨hArhs₁, ?_⟩
      intro cvj' cnP' cnF' hfj ψ ψj args margs tv hl hml hch hmch htv
        hpeq hlev hfit
      have hctor₁ : (⟨.recInfo cvA nP 1 nm 0 rules' ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj nP cnF) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = RecRule.ctor r from fun h => hncc h.symm)]
        exact hctor
      rw [hctor₁] at hfj
      obtain hje := Option.some.inj hfj
      injection hje with j1 j2 j3
      subst j1 j2 j3
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2⟩ := hfit
      subst hψeq hψjeq
      have hro₁ : RenameOk m₀.val
          (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) f := by
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
                if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
                  rules').name = cvA.name.str "_model" from
                  fun h => Name.str_ne cvA.name "_model" h.symm)]
              exact hmodel
            · show cvm.levelParams = _
              rw [hlps]
              exact (show cvA.levelParams =
                (ConstantInfo.recInfo cvA nP 1 nm 0
                  rules').toConstantVal.levelParams from rfl)
          · next hh =>
            obtain ⟨ci₃, hf₃, hlp₃⟩ := hro.1 n₂ ci₂ hf₂
            refine ⟨ci₃, ?_, hlp₃⟩
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
                rules').name = f₀ n₂ from fun h => hfnot n₂
                  (by rw [hff₀ n₂ (fun he => hh he.symm)]; exact h.symm))]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [hff₀ n₂ (fun he => hh he.symm), Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
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
      have hfRm₁ : (⟨.recInfo cvA nP 1 nm 0 rules' ::
          env.consts⟩ : Env).find? (f cvA.name) =
          some (.defnInfo cvm mval) := by
        rw [hfself, Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = cvA.name.str "_model" from
            fun h => Name.str_ne cvA.name "_model" h.symm)]
        exact hmodel
      have heqne : eqName ≠ cvA.name := by
        intro h
        rw [← h] at hnres
        exact absurd hnres (by decide)
      have heqfind₁ : (⟨.recInfo cvA nP 1 nm 0 rules' ::
          env.consts⟩ : Env).find? eqName = some eqA := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
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
            (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ''
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
            (⟨.recInfo cvA nP 1 nm 0 rules' :: env.consts⟩ : Env) ψ'' 0
            (rho0 V) cvt.type := by
        intro ψ''
        obtain ⟨hA1, -⟩ := m.annot_ok _ (find?_mem hthm) ψ''
        exact hAtransM cvt.type hthres ψ'' hA1
      obtain ⟨hCtf, hCtp, -, -, -, -⟩ := m.wf _ (find?_mem hctor)
      have htyw₁ : cvA.type.hasFvar = false := hwf.1
      have hClps₁ : ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ p ∈ cvj.levelParams, ψ₁ p = ψ₂ p) →
          m₀.val (RecRule.ctor r) ψ₁ = m₀.val (RecRule.ctor r) ψ₂ :=
        fun ψ₁ ψ₂ hψ => hvp₁ _ _ hctor₁ ψ₁ ψ₂ (by exact hψ)
      have hl' : args.length = nP + 1 + nm := by simpa using hl
      exact modeled_rule_fold hro₁ hvp₁ hctor₁ hfRm₁
        (show (ConstantInfo.defnInfo cvm
          mval).toConstantVal.levelParams = cvA.levelParams from hlps)
        hClps₁ heqfind₁ heqval₁ hthm_mem₁ hthm_annot₁ hthw hstripR
        hR_strip hC_strip hS_strip hdomsPre hdomsF hsdoms hsbody hrhsf
        hrhsb hArhs₁ htyw₁ hCtf
        (show cvj.type.allLevelParamsDefined cvj.levelParams = true from
          hCtp)
        hl' hml htv hpeq hlev hfit1 hfit2
    · next hn =>
      have hfp₀ : (⟨.recInfo cvA nP 1 nm 0 [] ::
          env.consts⟩ : Env).find? n =
          some (.recInfo cvR nP' nM' nm' ni' rules) := by
        rw [Env.find?_cons,
          if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
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
          if_pos (show (ConstantInfo.recInfo cvA nP 1 nm 0
            rules').name = cvA.name from rfl)] at hfj
        exact nomatch (Option.some.inj hfj)
      have hfj₀ : (⟨.recInfo cvA nP 1 nm 0 [] ::
          env.consts⟩ : Env).find? (RecRule.ctor r) =
          some (.ctorInfo cvj' cnP' cnF') := by
        rw [← hfindEq _ hncc]
        exact hfj
      obtain ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
        hψeq, hψjeq, hfit1, hfit2⟩ := hfit
      obtain ⟨R', hRi, hfoldEq, hRch⟩ := hfold cvj' cnP' cnF' hfj₀ ψ ψj
        args margs tv hl hml hch hmch htv hpeq hlev
        ⟨φ', us, usj, dd, ρρ, dd₁, ρρ₁, rest₁, dd₂, ρρ₂, rest₂,
          hψeq, hψjeq, TeleFit.env_levelext henv10 hfit1,
          TeleFit.env_levelext henv10 hfit2⟩
      refine ⟨R', ?_, hfoldEq, hRch⟩
      rw [hitrans]
      exact hRi

end Setlec
