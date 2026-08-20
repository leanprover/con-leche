import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall
import Setlec.Model.IndInstall

/-!
# Consistency of the checker

The headline results:

* `checkDecl_sound`: checking a declaration preserves having a model.
* `checkDecls_sound`: every environment accepted by `checkDecls` has a
  set-theoretic model (`EnvModel`).

Both are parametric in a model `V` of the target set theory: assuming
Tarski–Grothendieck set theory is consistent (i.e. a `SetTheory` instance
exists), no accepted environment can prove `False` — the concrete
"no proof of `Empty` is accepted" corollary lands once `Empty` is in the
supported fragment.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

private theorem find?_none_ne {env : Env} {n : Name} (h : env.find? n = none) :
    ∀ c ∈ env.consts, c.name ≠ n := by
  intro c hc
  have := List.find?_eq_none.mp h c hc
  simpa using this

/-- The sibling-availability data `BasisBlocks` preservation needs when
extending by one (fresh) constant: if the constant is a recursor-kind
record, the members of its block are already stored. -/
private def SibFinds (env : Env) (c₀ : ConstantInfo) : Prop :=
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

private theorem BasisBlocks.cons {env : Env} {c₀ : ConstantInfo}
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
private def RecMemberOk (env' : Env) (val' : ConstVal V)
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
private theorem RecCtorsStored.cons {env : Env} {c₀ : ConstantInfo}
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
private theorem RecRulesOk.cons {env : Env} (m : EnvModel V env)
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
private theorem checkConstantVal_inv {env : Env} {cv cv' : ConstantVal}
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
private theorem extend_model {env : Env} (m : EnvModel V env)
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
private theorem extend_basis_one {env : Env} (m : EnvModel V env)
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
private theorem extend_modeled_one {env : Env} (m : EnvModel V env)
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
private def RuleChecked (env env₀ : Env) (f : Name → Name)
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
    cvt.levelParams = cvA.levelParams

private theorem domsMatchAux_inv {g : Nat → Expr → Expr}
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
private theorem checkIotaRules_inv {env' envSelf : Env} {f : Name → Name}
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
    by_cases hrlp : r.rhs.allLevelParamsDefined cvA.levelParams = true
    case neg => rw [if_neg hrlp] at h; exact nomatch h
    rw [if_pos hrlp] at h
    try dsimp only at h
    by_cases hrres : r.rhs.constsResolve envSelf = true
    case neg => rw [if_neg hrres] at h; exact nomatch h
    rw [if_pos hrres] at h
    try dsimp only at h
    cases hann : annotate envSelf 0 r.rhs with
    | error e => rw [hann] at h; exact nomatch h
    | ok rhsA =>
    rw [hann] at h
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
      ?_, ?_, ?_, ?_, hfthm, hlpt⟩
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
private theorem extend_modeled_rec {env : Env} (m : EnvModel V env)
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
    (hro : RenameOk m.val env f)
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
  obtain ⟨m₀, hval₀, hpres₀⟩ := extend_modeled_one m
    (.recInfo cvA nP 1 nm 0 []) f hfind' hnres hwf₀ htyres0
    (Or.inr (Or.inr ⟨cvA, nP, nm, rfl⟩)) hmodel hlps hren hro
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
        hsbody, hthm, hlpt⟩ := hrules r hr
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
            rw [Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
                rules').name = f n₂ from fun h => hfnot n₂ h.symm)]
            exact hf₃
        · intro n₂ hf₂
          rw [Env.find?_cons] at hf₂
          split at hf₂
          · exact nomatch hf₂
          · next hh =>
            rw [Env.find?_cons,
              if_neg (show ¬(ConstantInfo.recInfo cvA nP 1 nm 0
                rules').name = f n₂ from fun h => hfnot n₂ h.symm)]
            exact hro.2.1 n₂ hf₂
        · intro n₂ ψ₂
          by_cases hh : n₂ = cvA.name
          · subst hh
            rw [show f cvA.name = cvA.name.str "_model" from hfself]
            rw [hpres₀ _ ψ₂ (Name.str_ne cvA.name "_model")]
            exact (hval₀ ψ₂).symm
          · by_cases hh₂ : f n₂ = cvA.name
            · exact absurd hh₂ (hfnot n₂)
            · rw [hpres₀ _ ψ₂ hh₂, hpres₀ _ ψ₂ hh, hro.2.2 n₂]
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

/-- The common inversion + semantic-fact assembly for a checked value
against a checked (annotated) type. -/
private theorem value_facts {env : Env} (m : EnvModel V env)
    {value value' type vtype : Expr}
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotate env 0 value = .ok value')
    (hvt : inferType env 0 value' = .ok vtype)
    (hde : isDefEq env 0 vtype type = .ok true)
    (htf : type.hasFvar = false)
    (htb : type.looseBVarsBounded 0 = true)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type)
    (hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T) :
    value'.hasFvar = false ∧
    (∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value') ∧
    (∀ ψ : Name → Nat, ∃ v T,
      interpClosed V m.val env ψ value' = some v ∧
      interpClosed V m.val env ψ type = some T ∧ v ∈ˢ T) := by
  have hwv : WScoped 0 value := WScoped.of_not_hasFvar hivf
  have hvf' : value'.hasFvar = false := by
    rw [← Expr.LeafEquiv.hasFvar_eq value value' (annotate_leafEquiv value hannv hwv hlbv)]
    exact hivf
  have hbv' : value'.looseBVarsBounded 0 = true := annotate_looseBVars value hannv hlbv
  have hAv : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) value' := fun ψ =>
    annotate_sound m value hannv hwv hlbv (Expr.LeavesBounded.of_not_hasFvar hivf)
      (rho0 V) (FvarsOk.of_not_hasFvar hivf)
  refine ⟨hvf', hAv, fun ψ => ?_⟩
  obtain ⟨⟨v, tv, hv, htv, hmem⟩, hwvt, hAvt⟩ :=
    inferType_sound (φ := ψ) m hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
      (FvarsOk.of_not_hasFvar hvf') (hAv ψ)
  obtain ⟨T, hT⟩ := hkeyT ψ
  have hbvt : vtype.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') hbv'
      (Expr.LeavesBounded.of_not_hasFvar hvf')
  have hLbvt : Expr.LeavesBounded vtype := fun l hl =>
    Expr.LeavesBounded.of_not_hasFvar hvf' l
      (inferTypeCore_fvarLeaves m.wf checkFuel hvt (WScoped.of_not_hasFvar hvf') l hl)
  have htveq : tv = T :=
    isDefEq_sound (φ := ψ) m hde hwvt (WScoped.of_not_hasFvar htf)
      hbvt htb hLbvt (Expr.LeavesBounded.of_not_hasFvar htf)
      (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf checkFuel hvt
        (WScoped.of_not_hasFvar hvf')) (FvarsOk.of_not_hasFvar hvf'))
      (FvarsOk.of_not_hasFvar htf)
      hAvt (hAty ψ) htv hT
  exact ⟨v, T, hv, hT, htveq ▸ hmem⟩

private theorem max_ne_zero_r'' {u v : Nat} (h : v ≠ 0) : Nat.max u v ≠ 0 :=
  fun hc => h (Nat.le_zero.mp (hc ▸ Nat.le_max_right u v))

/-- Checking a declaration preserves having a model. -/
theorem checkDecl_sound {env env' : Env} {d : Declaration}
    (h : checkDecl env d = .ok env') (m : EnvModel V env) : Nonempty (EnvModel V env') := by
  cases d with
  | axiomDecl cv => exact nomatch h
  | indDecl block => exact nomatch h
  | basisDecl kind =>
    match kind, h with
    | .natK, h => ?_
    | .psigmaK, h => ?_
    | .eqK, h => ?_
    | .punitK, h => ?_
    | .emptyK, h => ?_
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Nat
      by_cases h1 : (env.find? natA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Nat.zero
      by_cases h2 : ((⟨natA :: env.consts⟩ : Env).find? natZeroA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Nat.succ
      by_cases h3 : ((⟨natZeroA :: natA :: env.consts⟩ : Env).find? natSuccA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 4: Nat.rec
      by_cases h4 : ((⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find? natRecA.name).isNone
      case neg => simp [h4, pure, Except.pure] at h
      simp only [h4, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the four model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m natA (fun _ => omega)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => nat_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 natZeroA
        (fun _ => natzero)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natZeroA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natZeroA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natZero_key rfl (fun ψ' => hval1 ψ'))
        (fun _ _ _ => rfl)
        (fun ψ => by simp [natZeroA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natZeroA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natZeroA]))
      have hvalN2 : ∀ ψ' : Name → Nat, m2.val natName ψ' = omega := fun ψ' => by
        rw [hpres2 natName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 natSuccA
        (fun ψ => natSuccVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natSuccA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [natSuccA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natSucc_key rfl hvalN2)
        (fun _ _ _ => rfl)
        (fun ψ => annotOk_natSucc_type rfl hvalN2)
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [natSuccA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [natSuccA]))
      have hvalN3 : ∀ ψ' : Name → Nat, m3.val natName ψ' = omega := fun ψ' => by
        rw [hpres3 natName ψ' (by decide)]
        exact hvalN2 ψ'
      have hvalZ3 : ∀ ψ' : Name → Nat, m3.val natZeroName ψ' = natzero := fun ψ' => by
        rw [hpres3 natZeroName ψ' (by decide)]
        exact hval2 ψ'
      obtain ⟨m4, hval4, hpres4⟩ := extend_basis_one m3 natRecA
        (fun ψ => natRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h4)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [natRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [natRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => natRec_key rfl hvalN3 rfl hvalZ3 rfl (fun ψ' => hval3 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [natRecVal]
          rw [hψ uN (by simp [natRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_natRec_type rfl hvalN3 rfl hvalZ3 rfl
          (fun ψ' => hval3 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_neg (by decide), Env.find?_cons, if_pos (by decide)],
            by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalN' : ∀ ψ' : Name → Nat, val' natName ψ' = omega := by
            intro ψ'
            rw [hv2 natName ψ' (by decide)]
            exact hvalN3 ψ'
          have hvalZ' : ∀ ψ' : Name → Nat, val' natZeroName ψ' = natzero := by
            intro ψ'
            rw [hv2 natZeroName ψ' (by decide)]
            exact hvalZ3 ψ'
          have hvalSc' : ∀ ψ' : Name → Nat,
              val' natSuccName ψ' = natSuccVal V ψ' := by
            intro ψ'
            rw [hv2 natSuccName ψ' (by decide)]
            exact hval3 ψ'
          have hvalRc' : ∀ ψ' : Name → Nat,
              val' (natName.str "rec") ψ' = natRecVal V ψ' :=
            fun ψ' => hv1 ψ'
          have hfN' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natName = some natA := rfl
          have hfZ' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natZeroName = some natZeroA := rfl
          have hfSc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              natSuccName = some natSuccA := rfl
          have hfRc' : Env.find?
              (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
              (natName.str "rec") = some natRecA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · -- zero rule
            refine ⟨fun ψ => annotOk_natRecZero_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natZeroA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            have htv' : tv = natzero := by
              rw [htv, hv2 _ _ (by decide)]
              exact hvalZ3 ψj
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩⟩ :=
              natZeroIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3 htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩, trivial⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · -- successor rule
            refine ⟨fun ψ => annotOk_natRecSucc_rhs (cval := val') (ψ := ψ)
              rfl hvalN' rfl hvalZ' rfl hvalSc' hfRc' hvalRc', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [natSuccA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Mv, _ | ⟨zv, _ | ⟨sv, _ | ⟨x, rest⟩⟩⟩⟩ <;>
              simp at hlen
            rcases margs with _ | ⟨y1, _ | ⟨y2, ys⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            rw [hv1] at hp1 hp2 hp3
            obtain ⟨hms1, -⟩ := hmch
            obtain ⟨vE', A', B', hq', hn', hf'⟩ := hms1
            have hsucceq : ∀ ψ'' : Name → Nat,
                val' ((Name.anonymous.str "Nat").str "succ") ψ'' =
                natSuccVal V ψ := by
              intro ψ''
              rw [hv2 _ _ (by decide)]
              exact hval3 ψ''
            rw [hsucceq] at hq'
            have htv' : tv = SetTheory.app (natSuccVal V ψ) y1 := by
              rw [htv, show SpineFold V (val'
                  ((Name.anonymous.str "Nat").str "succ") ψj) [y1] =
                  SetTheory.app (val'
                    ((Name.anonymous.str "Nat").str "succ") ψj) y1 from rfl,
                hsucceq]
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              natSuccIota_claims (cval := val') (ψ := ψ)
                hfN' hvalN' hfZ' hvalZ' hfSc' hvalSc' hfRc' hvalRc'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE' := vE') (A' := A') (B' := B') hq' hn' htv'
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' natRecA.name ψ)
                  ([Mv, zv, sv] ++ [tv]) = SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' natRecA.name ψ) Mv) zv) sv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [natRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "zero") = some natZeroA := by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Nat").str "succ") = some natSuccA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m4⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: PSigma'
      by_cases h1 : (env.find? psigmaA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: PSigma'.mk
      by_cases h2 : ((⟨psigmaA :: env.consts⟩ : Env).find? psigmaMkA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: PSigma'.rec
      by_cases h3 : ((⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env).find? psigmaRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- the semantic pair facts the environment invariant records
      have htyfacts : ∀ ψ' : Name → Nat,
          PairTyFacts V (psigmaVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_⟩
        · intro vE A₀ B₀ x hmem hx
          simp only [psigmaVal] at hmem
          exact lam_pi_dom hmem
            (max_ne_zero_r'' (Nat.succ_ne_zero (Nat.max (ψ' uN) (ψ' vN)))) hx
        · intro vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaVal_app hvA] at hmem
          exact lam_pi_dom hmem (Nat.succ_ne_zero _) hx
        · intro vA vB hvA hvB
          exact psigmaVal_fold hvA hvB
      have hmkfacts : ∀ ψ' : Name → Nat,
          PairMkFacts V (psigmaMkVal V ψ') (ψ' uN) (ψ' vN) := by
        intro ψ'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro hw vE A₀ B₀ x hmem hx
          simp only [psigmaMkVal] at hmem
          refine lam_pi_dom hmem ?_ hx
          rw [if_neg hw]
          exact max_ne_zero_r'' (Nat.succ_ne_zero (ψ' vN))
        · intro hw vA vE A₁ B₁ x hvA hmem hx
          rw [psigmaMkVal_app hvA] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB vE A₂ B₂ x hvA hvB hmem hx
          rw [psigmaMkVal_app₂ hvA hvB] at hmem
          exact lam_pi_dom hmem hw hx
        · intro hw vA vB va vE A₃ B₃ x hvA hvB hva hmem hx
          rw [psigmaMkVal_app₃ hvA hvB hva] at hmem
          exact lam_pi_dom hmem hw hx
        · intro vA vB va vb hvA hvB hva hvb
          exact psigmaMkVal_fold hvA hvB hva hvb
        · intro hw x y z w'
          simp only [psigmaMkVal]
          rw [if_pos hw, lam_zero, app_pt, app_pt, app_pt, app_pt]
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m psigmaA
        (fun ψ => psigmaVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigma_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaVal]
          rw [hψ uN (by simp [psigmaA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigma_type)
        (fun cv hx _ => ⟨by cases hx; rfl, htyfacts⟩)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 psigmaMkA
        (fun ψ => psigmaMkVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaMkA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [psigmaMkA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaMk_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaMkVal]
          rw [hψ uN (by simp [psigmaMkA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaMkA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaMk_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => by
          cases hx
          exact ⟨rfl, rfl, rfl, hmkfacts⟩)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [psigmaMkA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [psigmaMkA]))
      have hvalS2 : ∀ ψ' : Name → Nat, m2.val psigmaName ψ' = psigmaVal V ψ' :=
        fun ψ' => by
          rw [hpres2 psigmaName ψ' (by decide)]
          exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 psigmaRecA
        (fun ψ => psigmaRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [psigmaRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [psigmaRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => psigmaRec_key rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [psigmaRecVal]
          rw [hψ uN (by simp [psigmaRecA, ConstantInfo.toConstantVal, uN]),
            hψ vN (by simp [psigmaRecA, ConstantInfo.toConstantVal, vN])])
        (fun ψ => annotOk_psigmaRec_type rfl hvalS2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalS' : ∀ ψ' : Name → Nat,
              val' psigmaName ψ' = psigmaVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaName ψ' (by decide)]
            exact hvalS2 ψ'
          have hvalM' : ∀ ψ' : Name → Nat,
              val' psigmaMkName ψ' = psigmaMkVal V ψ' := by
            intro ψ'
            rw [hv2 psigmaMkName ψ' (by decide)]
            exact hval2 ψ'
          have hfS' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaName = some psigmaA := rfl
          have hfM' : Env.find?
              (⟨psigmaRecA :: psigmaMkA :: psigmaA :: env.consts⟩ : Env)
              psigmaMkName = some psigmaMkA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_psigmaRec_rhs (cval := val') (ψ := ψ)
              rfl hvalS' rfl hvalM', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [psigmaMkA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨Bv, _ | ⟨Mv, _ | ⟨mkv,
              _ | ⟨x, rest⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨av, _ | ⟨bv,
              _ | ⟨y, ys⟩⟩⟩⟩⟩ <;> simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨hms1, hms2, hms3, hms4, -⟩ := hmch
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hms3
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hms4
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
              ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
              ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩⟩ :=
              psigmaIota_claims (cval := val') (ψ := ψ)
                (Av := Av) (Bv := Bv) (Mv := Mv) (mkv := mkv) (tv := tv)
                (av := av) (bv := bv)
                hfS' hvalS' hfM' hvalM' hm1 hm2 hm3 hm4 hm5 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' psigmaRecA.name ψ)
                  ([Av, Bv, Mv, mkv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (val' psigmaRecA.name ψ) Av) Bv)
                    Mv) mkv) tv from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩,
                ⟨vS5, AS5, BS5, hq13, hq14, hq15⟩,
                ⟨vS6, AS6, BS6, hq16, hq17, hq18⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [psigmaRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨psigmaMkA :: psigmaA :: env.consts⟩ : Env)
                ((Name.anonymous.str "PSigma'").str "mk") =
                some psigmaMkA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
      -- step 1: Eq
      by_cases h1 : (env.find? eqA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Eq.refl
      by_cases h2 : ((⟨eqA :: env.consts⟩ : Env).find? eqReflA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 3: Eq.rec
      by_cases h3 : ((⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqRecA.name).isNone
      case neg => simp [h3, pure, Except.pure] at h
      simp only [h3, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      -- chain the three model extensions
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m eqA (fun ψ => eqVal V ψ)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eq_key)
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqVal]
          rw [hψ uN (by simp [eqA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eq_type)
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqA]))
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 eqReflA
        (fun ψ => eqReflVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqReflA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [eqReflA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRefl_key rfl (fun ψ' => hval1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqReflVal]
          rw [hψ uN (by simp [eqReflA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRefl_type rfl (fun ψ' => hval1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx hn => absurd hn (by decide))
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [eqReflA]))
        (fun _ _ _ _ _ _ hx =>
          absurd hx (by simp [eqReflA]))
      have hvalE2 : ∀ ψ' : Name → Nat, m2.val eqName ψ' = eqVal V ψ' := fun ψ' => by
        rw [hpres2 eqName ψ' (by decide)]
        exact hval1 ψ'
      obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 eqRecA
        (fun ψ => eqRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h3)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [eqRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [eqRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => eqRec_key rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [eqRecVal]
          rw [hψ u1N (by simp [eqRecA, ConstantInfo.toConstantVal, u1N]),
            hψ uN (by simp [eqRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_eqRec_type rfl hvalE2 rfl (fun ψ' => hval2 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩,
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          have hvalE' : ∀ ψ' : Name → Nat, val' eqName ψ' = eqVal V ψ' := by
            intro ψ'
            rw [hv2 eqName ψ' (by decide)]
            exact hvalE2 ψ'
          have hvalR' : ∀ ψ' : Name → Nat,
              val' eqReflName ψ' = eqReflVal V ψ' := by
            intro ψ'
            rw [hv2 eqReflName ψ' (by decide)]
            exact hval2 ψ'
          have hfE' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqName = some eqA := rfl
          have hfR' : Env.find?
              (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env)
              eqReflName = some eqReflA := rfl
          rcases List.mem_cons.mp hr with rfl | hr
          · refine ⟨fun ψ => annotOk_eqRec_rhs (cval := val') (ψ := ψ)
              rfl hvalE' rfl hvalR', ?_⟩
            intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
              htv _hpeq _hlev _hfit
            have hje := Option.some.inj hfj
            simp only [eqReflA] at hje
            injection hje with hj1 hj2 hj3
            subst hj1 hj2 hj3
            rcases args with _ | ⟨Av, _ | ⟨av, _ | ⟨Mv, _ | ⟨rv,
              _ | ⟨bv, _ | ⟨x, rest⟩⟩⟩⟩⟩⟩ <;> simp at hlen
            rcases margs with _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, ys⟩⟩⟩ <;>
              simp at hmlen
            obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, -⟩ := hch
            obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
            obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
            obtain ⟨vE3, A3, B3, hp3, hm3, hf3⟩ := hs3
            obtain ⟨vE4, A4, B4, hp4, hm4, hf4⟩ := hs4
            obtain ⟨vE5, A5, B5, hp5, hm5, hf5⟩ := hs5
            obtain ⟨vE6, A6, B6, hp6, hm6, hf6⟩ := hs6
            rw [hv1] at hp1 hp2 hp3 hp4 hp5 hp6
            obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
              ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
              ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩⟩ :=
              eqIota_claims (cval := val') (ψ := ψ)
                hfE' hvalE' hfR' hvalR'
                (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
                (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2
                (vE3 := vE3) (A3 := A3) (B3 := B3) hp3 hm3
                (vE4 := vE4) (A4 := A4) (B4 := B4) hp4 hm4
                (vE5 := vE5) (A5 := A5) (B5 := B5) hp5 hm5
                (vE6 := vE6) (A6 := A6) (B6 := B6) hp6 hm6
            refine ⟨R, hRi, ?_, ?_⟩
            · rw [show SpineFold V (val' eqRecA.name ψ)
                  ([Av, av, Mv, rv, bv] ++ [tv]) =
                  SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
                    (SetTheory.app (SetTheory.app
                      (val' eqRecA.name ψ) Av) av) Mv) rv) bv) tv
                  from rfl]
              rw [hv1]
              exact hfold
            · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
                ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩,
                ⟨vS3, AS3, BS3, hq7, hq8, hq9⟩,
                ⟨vS4, AS4, BS4, hq10, hq11, hq12⟩, trivial⟩
          · cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [eqRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h1 h2 h3 h4 h5 h6
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · have hf : Env.find?
                (⟨eqReflA :: eqA :: env.consts⟩ : Env)
                ((Name.anonymous.str "Eq").str "refl") = some eqReflA := by
              rw [Env.find?_cons, if_pos (by decide)]
            exact ⟨_, _, _, hf⟩
          · cases hr)
      exact ⟨m3⟩
    simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind, Except.bind] at h
    -- step 1: PUnit
    by_cases h1 : (env.find? punitA.name).isNone
    case neg => simp [h1, pure, Except.pure] at h
    simp only [h1, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 2: PUnit.unit
    by_cases h2 : ((⟨punitA :: env.consts⟩ : Env).find? punitUnitA.name).isNone
    case neg => simp [h2, pure, Except.pure] at h
    simp only [h2, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    try dsimp only at h
    -- step 3: PUnit.rec
    by_cases h3 : ((⟨punitUnitA :: punitA :: env.consts⟩ : Env).find? punitRecA.name).isNone
    case neg => simp [h3, pure, Except.pure] at h
    simp only [h3, if_true, ↓reduceIte] at h
    try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    simp only [Except.ok.injEq] at h
    subst h
    -- chain the three model extensions
    obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m punitA (fun _ => unitSet)
      (Option.isNone_iff_eq_none.mp h1)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punit_key)
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx hn => absurd hn (by decide))
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv _ _ ψ x hx => mem_unitSet hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitA]))
    obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 punitUnitA (fun _ => pt)
      (Option.isNone_iff_eq_none.mp h2)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitUnitA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [punitUnitA])⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitUnit_key rfl (fun ψ' => hval1 ψ'))
      (fun _ _ _ => rfl)
      (fun ψ => by simp [punitUnitA, ConstantInfo.toConstantVal, AnnotOk])
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx hn => absurd hn (by decide))
      (fun cv hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
      (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
        absurd hx (by simp [punitUnitA]))
      (fun _ _ _ _ _ _ hx =>
        absurd hx (by simp [punitUnitA]))
    have hvalP2 : ∀ ψ' : Name → Nat, m2.val punitName ψ' = unitSet := fun ψ' => by
      rw [hpres2 punitName ψ' (by decide)]
      exact hval1 ψ'
    obtain ⟨m3, hval3, hpres3⟩ := extend_basis_one m2 punitRecA
      (fun ψ => punitRecVal V ψ)
      (Option.isNone_iff_eq_none.mp h3)
      ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [punitRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [punitRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h1 h2 h3 h4 h5 h6
            first
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))
            | (rcases List.mem_cons.mp hr with rfl | hr
               · exact ⟨by decide, by decide,
                   (by simp +decide [Expr.constsResolve, Env.find?, List.find?,
                     natRecA, natSuccA, natZeroA, natA, psigmaRecA,
                     psigmaMkA, psigmaA, eqRecA, eqReflA, eqA, punitRecA,
                     punitUnitA, punitA, ConstantInfo.name,
                     ConstantInfo.toConstantVal]),
                   by decide⟩
               exact absurd hr (by simp))⟩
      rfl
      (fun _ _ hx => nomatch hx)
      (fun ψ => punitRec_key rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun ψ₁ ψ₂ hψ => by
        simp only [punitRecVal]
        rw [hψ u1N (by simp [punitRecA, ConstantInfo.toConstantVal, u1N]),
          hψ uN (by simp [punitRecA, ConstantInfo.toConstantVal, uN])])
      (fun ψ => annotOk_punitRec_type rfl hvalP2 rfl (fun ψ' => hval2 ψ'))
      (fun cv hx _ => nomatch hx)
      (fun cv nP nF hx _ => nomatch hx)
      (fun cv hx _ => nomatch hx)
      (fun hn => absurd hn (by decide))
      (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun _ => ⟨by
              rw [Env.find?_cons, if_neg (by decide), Env.find?_cons,
                if_pos (by decide)],
            by
              rw [Env.find?_cons, if_pos (by decide)]⟩⟩)
      (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        have hvalP' : ∀ ψ' : Name → Nat, val' punitName ψ' = unitSet := by
          intro ψ'
          rw [hv2 punitName ψ' (by decide)]
          exact hvalP2 ψ'
        have hvalU' : ∀ ψ' : Name → Nat, val' punitUnitName ψ' = pt := by
          intro ψ'
          rw [hv2 punitUnitName ψ' (by decide)]
          exact hval2 ψ'
        rcases List.mem_cons.mp hr with rfl | hr
        · refine ⟨fun ψ => annotOk_punitRec_rhs (cval := val') (ψ := ψ)
            rfl hvalP' rfl hvalU', ?_⟩
          intro cvj cnP cnF hfj ψ ψj args margs tv hlen hmlen hch hmch
            htv _hpeq _hlev _hfit
          have hje := Option.some.inj hfj
          simp only [punitUnitA] at hje
          injection hje with hj1 hj2 hj3
          subst hj1 hj2 hj3
          rcases args with _ | ⟨Mv, _ | ⟨mv, _ | ⟨x, rest⟩⟩⟩ <;>
            simp at hlen
          rcases margs with _ | ⟨y, ys⟩ <;> simp at hmlen
          obtain ⟨hs1, hs2, hs3, -⟩ := hch
          obtain ⟨vE1, A1, B1, hp1, hm1, hf1⟩ := hs1
          obtain ⟨vE2, A2, B2, hp2, hm2, hf2⟩ := hs2
          rw [hv1] at hp1 hp2
          have htv' : tv = pt := by
            rw [htv, hv2 _ _ (by decide)]
            exact hval2 ψj
          have hfP' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitName = some punitA := rfl
          have hfU' : Env.find?
              (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ : Env)
              punitUnitName = some punitUnitA := rfl
          obtain ⟨R, hRi, hfold, ⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
            ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩⟩ :=
            punitIota_claims (cval := val') (ψ := ψ) hfP' hvalP' hfU' hvalU'
              (vE1 := vE1) (A1 := A1) (B1 := B1) hp1 hm1
              (vE2 := vE2) (A2 := A2) (B2 := B2) hp2 hm2 htv'
          refine ⟨R, hRi, ?_, ?_⟩
          · rw [show SpineFold V (val' punitRecA.name ψ)
                ([Mv, mv] ++ [tv]) = SetTheory.app (SetTheory.app
                  (SetTheory.app (val' punitRecA.name ψ) Mv) mv) tv
                from rfl]
            rw [hv1]
            exact hfold
          · exact ⟨⟨vS1, AS1, BS1, hq1, hq2, hq3⟩,
              ⟨vS2, AS2, BS2, hq4, hq5, hq6⟩, trivial⟩
        · cases hr)
      (fun cvR nP nM nm ni rules heq => by
        simp only [punitRecA] at heq
        injection heq with h1 h2 h3 h4 h5 h6
        subst h1 h2 h3 h4 h5 h6
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · have hf : Env.find?
              (⟨punitUnitA :: punitA :: env.consts⟩ : Env)
              ((Name.anonymous.str "PUnit").str "unit") =
              some punitUnitA := by
            rw [Env.find?_cons, if_pos (by decide)]
          exact ⟨_, _, _, hf⟩
        · cases hr)
    exact ⟨m3⟩
    case _ =>
      simp only [checkDecl, BasisKind.declsA, List.foldlM, Bind.bind,
        Except.bind] at h
      -- step 1: Empty
      by_cases h1 : (env.find? emptyA.name).isNone
      case neg => simp [h1, pure, Except.pure] at h
      simp only [h1, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      try dsimp only at h
      -- step 2: Empty.rec
      by_cases h2 : ((⟨emptyA :: env.consts⟩ : Env).find?
        emptyRecA.name).isNone
      case neg => simp [h2, pure, Except.pure] at h
      simp only [h2, if_true, ↓reduceIte] at h
      try simp only [Bind.bind, Except.bind, pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨m1, hval1, hpres1⟩ := extend_basis_one m emptyA
        (fun _ => SetTheory.empty)
        (Option.isNone_iff_eq_none.mp h1)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [emptyA]),
          fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA])⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => empty_key)
        (fun _ _ _ => rfl)
        (fun ψ => by simp [emptyA, ConstantInfo.toConstantVal, AnnotOk])
        (fun cv hx hn => absurd hn (by decide))
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx hn => absurd hn (by decide))
        (fun _ ψ x hx' => not_mem_empty x hx')
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun _ _ _ _ _ _ hx => nomatch hx)
        (fun _val' _h1 _h2 cvR nP nM nm ni rules hx =>
          absurd hx (by simp [emptyA]))
        (fun _ _ _ _ _ _ hx => absurd hx (by simp [emptyA]))
      have hvalE1 : ∀ ψ' : Name → Nat, m1.val emptyName ψ' =
          SetTheory.empty := fun ψ' => hval1 ψ'
      obtain ⟨m2, hval2, hpres2⟩ := extend_basis_one m1 emptyRecA
        (fun ψ => emptyRecVal V ψ)
        (Option.isNone_iff_eq_none.mp h2)
        ⟨rfl, rfl, rfl, rfl,
          fun _ _ hx => absurd hx (by simp [emptyRecA]),
          fun cv nP nM nm ni rules heq r hr => by
            simp only [emptyRecA] at heq
            injection heq with h1 h2 h3 h4 h5 h6
            subst h6
            cases hr⟩
        rfl
        (fun _ _ hx => nomatch hx)
        (fun ψ => emptyRec_key rfl (fun ψ' => hvalE1 ψ'))
        (fun ψ₁ ψ₂ hψ => by
          simp only [emptyRecVal]
          rw [hψ uN (by simp [emptyRecA, ConstantInfo.toConstantVal, uN])])
        (fun ψ => annotOk_emptyRec_type rfl (fun ψ' => hvalE1 ψ'))
        (fun cv hx _ => nomatch hx)
        (fun cv nP nF hx _ => nomatch hx)
        (fun cv hx _ => nomatch hx)
        (fun hn => absurd hn (by decide))
        (fun _ _ => ⟨rfl, fun _ => rfl⟩)
        (fun cv nP nM nm ni rules heq =>
          ⟨fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide),
           fun hn => absurd hn (by decide)⟩)
        (fun val' hv1 hv2 cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
        (fun cvR nP nM nm ni rules heq => by
          simp only [emptyRecA] at heq
          injection heq with h1 h2 h3 h4 h5 h6
          subst h6
          intro r hr
          cases hr)
      exact ⟨m2⟩
  | defnDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    -- semantic facts about the annotated type
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.defnInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => by injection heq with h1 h2; exact ⟨h1.symm, h2.symm⟩)
      rfl
      hres'
  | thmDecl cv value =>
    simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    -- the theorem-specific proposition check re-runs inference on the type
    cases hst2 : inferType env 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSort env 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    have hwt : WScoped 0 cv.type := WScoped.of_not_hasFvar hitf
    have htf : type.hasFvar = false := by
      rw [← Expr.LeafEquiv.hasFvar_eq cv.type type (annotate_leafEquiv cv.type hann hwt hlbt)]
      exact hitf
    have hbt' : type.looseBVarsBounded 0 = true := annotate_looseBVars cv.type hann hlbt
    have hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) type := fun ψ =>
      annotate_sound m cv.type hann hwt hlbt (Expr.LeavesBounded.of_not_hasFvar hitf)
        (rho0 V) (FvarsOk.of_not_hasFvar hitf)
    have hkeyT : ∀ ψ : Name → Nat, ∃ T, interpClosed V m.val env ψ type = some T := by
      intro ψ
      obtain ⟨⟨T, sT, hT, -, -⟩, -, -⟩ :=
        inferType_sound (φ := ψ) m hst (WScoped.of_not_hasFvar htf) hbt'
          (Expr.LeavesBounded.of_not_hasFvar htf)
          (FvarsOk.of_not_hasFvar htf) (hAty ψ)
      exact ⟨T, hT⟩
    obtain ⟨hvf', hAval, hkey⟩ :=
      value_facts m hlbv (by simpa using hivf) hannv hvt hde htf hbt' hAty hkeyT
    exact extend_model m hfind' htp htf htr (annotate_looseBVars cv.type hann hlbt)
      hvp hvf' hvr (annotate_looseBVars value hannv hlbv) hkey hAty hAval
      (ConstantInfo.thmInfo { cv with type := type } value') rfl rfl
      (fun cv2 value2 heq => nomatch heq)
      rfl
      hres'

private theorem foldlM_sound {env' : Env} :
    ∀ (ds : List Declaration) (env : Env), Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' → Nonempty (EnvModel V env')
  | [], env, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      exact foldlM_sound ds env1 (checkDecl_sound hd m) h

/-- Soundness: every accepted environment has a set-theoretic model. -/
theorem checkDecls_sound {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env') : Nonempty (EnvModel V env') :=
  foldlM_sound ds Env.empty ⟨EnvModel.empty V⟩ h

/-- Model-level core of the consistency corollary: a modeled
environment stores no constant of type `Empty`. -/
private theorem no_constant_of_Empty {env : Env} (m : EnvModel V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨T, hTi, hmem⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty] at hTi
  simp only [interpClosed, interpExpr] at hTi
  split at hTi
  · split at hTi
    · obtain rfl := Option.some.inj hTi
      exact m.ind_ok.right.right.right.right.right.right _ _ hmem
    · exact nomatch hTi
  · exact nomatch hTi

/-- A checked `def` or `theorem` stores a constant carrying the
annotated declared type. -/
private theorem checkDecl_stores {env env₁ : Env} {cv : ConstantVal}
    {value : Expr} {d : Declaration}
    (h : checkDecl env d = .ok env₁)
    (hd : d = .defnDecl cv value ∨ d = .thmDecl cv value) :
    ∃ type, annotate env 0 cv.type = .ok type ∧
      ∃ c ∈ env₁.consts, c.toConstantVal = ⟨cv.name, cv.levelParams, type⟩ := by
  rcases hd with rfl | rfl
  · simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩
  · simp only [checkDecl, Bind.bind, Except.bind] at h
    cases hccv : checkConstantVal env cv with
    | error e => rw [hccv] at h; exact nomatch h
    | ok cv' =>
    rw [hccv] at h
    try dsimp only at h
    obtain ⟨hfind', hres', hnd, hlbt, hitf, type, stype, u, hann, htp, htr, hst, hsort, rfl⟩ :=
      checkConstantVal_inv hccv
    simp only [Pure.pure, Except.pure] at h
    cases hst2 : inferType env 0 type with
    | error e => rw [hst2] at h; exact nomatch h
    | ok stype2 =>
    rw [hst2] at h
    try dsimp only at h
    cases hsort2 : ensureSort env 0 stype2 with
    | error e => rw [hsort2] at h; exact nomatch h
    | ok u2 =>
    rw [hsort2] at h
    try dsimp only at h
    cases hpz : Level.isEquiv u2 Level.zero with
    | none => rw [hpz] at h; simp [liftFueled] at h
    | some bz =>
    rw [hpz] at h
    cases bz with
    | false => simp [liftFueled, pure, Except.pure] at h
    | true =>
    simp only [liftFueled, pure, Except.pure] at h
    try dsimp only at h
    by_cases hlbv : value.looseBVarsBounded 0 = true
    case neg => simp [hlbv] at h
    simp only [hlbv] at h
    by_cases hivf : value.hasFvar = true
    case pos => simp [hivf] at h
    simp only [hivf] at h
    cases hannv : annotate env 0 value with
    | error e => rw [hannv] at h; exact nomatch h
    | ok value' =>
    rw [hannv] at h
    try dsimp only at h
    by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
    case neg => simp [hvp] at h
    simp only [hvp] at h
    by_cases hvr : value'.constsResolve env = true
    case neg => simp [hvr] at h
    simp only [hvr] at h
    cases hvt : inferType env 0 value' with
    | error e => rw [hvt] at h; exact nomatch h
    | ok vtype =>
    rw [hvt] at h
    try dsimp only at h
    cases hde : isDefEq env 0 vtype type with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h
    cases b with
    | false => exact nomatch h
    | true =>
    simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    exact ⟨type, hann, _, List.mem_cons_self .., rfl⟩

/-- If any `def`/`theorem` in the input claims type `Empty`, the fold
rejects: at the step that checks it, the extended environment would
store a constant of type `Empty`, contradicting its model. -/
private theorem foldlM_no_Empty_decl :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      ds.foldlM checkDecl env = .ok env' →
      ∀ {cv : ConstantVal} {value : Expr},
        (Declaration.defnDecl cv value ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds) →
        cv.type = .const emptyName [] → False
  | [], _, _, _, _, _, _, hd, _ => by
    rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, cv, value, hd, hty => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨m⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        simpa [annotate, pure, Except.pure] using hann
      obtain ⟨m1⟩ := checkDecl_sound hdd m
      exact no_constant_of_Empty m1 c hc (by rw [hcv])
    · have hd' : Declaration.defnDecl cv value ∈ ds ∨
          Declaration.thmDecl cv value ∈ ds := by
        rcases hd with hd | hd
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inl rfl) hdis
          · exact Or.inl hmem
        · rcases List.mem_cons.mp hd with rfl | hmem
          · exact absurd (Or.inr rfl) hdis
          · exact Or.inr hmem
      exact foldlM_no_Empty_decl ds env1 (checkDecl_sound hdd m) h hd' hty

/-- **Input-level consistency corollary**: the checker never accepts a
declaration list containing a `def` or `theorem` whose stated type is
`Empty` — no reference to the resulting environment needed. -/
theorem no_proof_of_Empty_input (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env')
    {cv : ConstantVal} {value : Expr}
    (hd : Declaration.defnDecl cv value ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_decl ds Env.empty ⟨EnvModel.empty V⟩ h hd hty

/-- **No proof of `Empty` is ever accepted.**  If the checker accepts a
declaration list, then no constant in the resulting environment has
type `Empty`.  The name `Empty` is reserved: input declarations cannot
redefine it, so the only thing it can ever denote is the pinned empty
inductive, modeled by the empty set.  Together with the realizability
of the `SetTheory` interface this is the consistency statement: an
accepted proof of the empty type would exhibit a member of the empty
set. -/
theorem no_proof_of_Empty (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound (V := V) h
  exact no_constant_of_Empty m c hc hty

end Setlec
