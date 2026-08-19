import Setlec.Kernel.Checker
import Setlec.Model.Annotate
import Setlec.Model.BasisInstall

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
    intro cvj cnP cnF hfj ψ ψj args margs tv hl hml hch hmch htv hpeq
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
      obtain ⟨R, hRi, hfoldEq, hRch⟩ := hfold cvj cnP cnF hfj ψ ψj
        args margs tv hl hml hch hmch htv hpeq
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
    (hc₀nb : c₀.isBasis = false) :
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
      intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        exact absurd hc₀nb (by simp [ConstantInfo.isBasis])
      · next hn =>
        have hne : emptyName ≠ name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = emptyName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hvagree : val' emptyName ψ = m.val emptyName ψ := by
          simp [hval', hne]
        rw [hvagree] at hx
        exact m.ind_ok.right.right.right.right.right.right cv hfp ψ x hx
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
    (hnewempty : ∀ cv, ci = .indInfo cv → ci.name = emptyName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → False)
    (hpin : ci.isBasis = true → ci = pinnedInfo ci.name ∧
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
        obtain ⟨hpi, hpv⟩ := hpin hbasis
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
      intro cv hfp ψ x hx
      rw [Env.find?_cons] at hfp
      split at hfp
      · next hn =>
        obtain rfl := Option.some.inj hfp
        have hval'eq : val' emptyName ψ = v₀ ψ := by
          simp [hval', hn.symm]
        rw [hval'eq] at hx
        exact hnewempty cv rfl hn ψ x hx
      · next hn =>
        have hne : emptyName ≠ ci.name := by
          intro hcontra
          have hmem := List.mem_of_find?_eq_some hfp
          have hname : (ConstantInfo.indInfo cv).name = emptyName := by
            have := List.find?_some hfp
            simpa using this
          have := hfresh _ hmem
          rw [hname, hcontra] at this
          exact this rfl
        have hval'eq : val' emptyName ψ = m.val emptyName ψ := by
          simp [hval', hne]
        rw [hval'eq] at hx
        exact m.ind_ok.right.right.right.right.right.right cv hfp ψ x hx
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
                (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
              htv _hpeq
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
              htv _hpeq
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
                (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
              htv _hpeq
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
                (fun cv hx hn => absurd hn (by decide))
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
                (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
              htv _hpeq
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
            (fun cv hx hn => absurd hn (by decide))
      (fun _ => ⟨rfl, fun _ => rfl⟩)
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
            (fun cv hx _ => nomatch hx)
      (fun _ => ⟨rfl, fun _ => rfl⟩)
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
            (fun cv hx _ => nomatch hx)
      (fun _ => ⟨rfl, fun _ => rfl⟩)
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
            htv _hpeq
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
        (fun cv hx _ => fun ψ x hx' => not_mem_empty x hx')
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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
        (fun cv hx _ => nomatch hx)
        (fun _ => ⟨rfl, fun _ => rfl⟩)
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

/-- **No proof of `Empty` is ever accepted.**  If the checker accepts a
declaration list whose resulting environment stores the `Empty`
inductive (necessarily the pinned basis block — inductive-kind
constants are only ever installed pinned), then no stored constant of
any kind has type `Empty`.  Together with the realizability of the
`SetTheory` interface this is the consistency statement: an accepted
proof of the empty type would exhibit a member of the empty set. -/
theorem no_proof_of_Empty (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls ds = .ok env')
    {cvE : ConstantVal}
    (hE : env'.find? emptyName = some (.indInfo cvE))
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound (V := V) h
  obtain ⟨T, hTi, hmem⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty] at hTi
  simp only [interpClosed, interpExpr, hE] at hTi
  split at hTi
  case isFalse => exact nomatch hTi
  obtain rfl := Option.some.inj hTi
  exact m.ind_ok.right.right.right.right.right.right cvE hE _ _ hmem

end Setlec
