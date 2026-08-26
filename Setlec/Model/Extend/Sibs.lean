import Setlec.Verify.Extend.Sibs
import Setlec.Verify.InstSpine
import Setlec.Model.Extend.Inversions

/-!
# Sibs — split out of `Setlec.Model.Extend`

Per-clause preservation (`.cons`) lemmas for extending an
environment by one fresh constant: `BasisBlocks`, `RecCtorsStored`,
`RecRulesOk` and `CapsOk`, with the head obligations (`SibFinds`,
`RecMemberOk`) they consume.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The fold facts a single (freshly installed) recursor-kind member
must supply, phrased over the extended environment and valuation:
the total λ-equality clause of `RecRulesOk` for each of its rules. -/
def RecMemberOk (env' : Env) (val' : ConstVal V)
    (ci : ConstantInfo) : Prop :=
  ∀ cvR mI rP rules, ci = .recInfo cvR mI rP rules →
    ∀ r ∈ rules,
      (∀ ψ : Name → Nat, AnnotOk V val' env' ψ 0 (rho0 V) (RecRule.rhs r)) ∧
      (RecRule.fire r ≠ .inert → rP ≤ mI) ∧
      (RecRule.fire r = .plain → RecRule.ctorParams r ≤ rP) ∧
      (∀ lvls pins, RecRule.fire r = .nested lvls pins →
        pins.length = RecRule.ctorParams r) ∧
      ∀ cvj cnP cnF,
        env'.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) →
        RecRule.fire r ≠ .inert →
        ∃ fvms bL, ruleLhsParts ci.name cvR rP r cvj = some (fvms, bL) ∧
          FrameWf 0 fvms bL ∧
          fvms.length = rP + RecRule.nfields r ∧
          (closeLamsAt fvms bL).constsResolve env' = true ∧
          ∀ ψ : Name → Nat,
            AnnotOk V val' env' ψ 0 (rho0 V) (closeLamsAt fvms bL) ∧
            ∃ Rv, interpClosed V val' env' ψ (closeLamsAt fvms bL) = some Rv ∧
              interpClosed V val' env' ψ (RecRule.rhs r) = some Rv

/-- `RecRulesOk` is preserved by a fresh extension, given the fold
facts for the new member (vacuous unless it is a recursor).  The
canonical left-hand side is built from stored data alone
(`ruleLhsParts` never reads the environment), so the transport is pure
interpretation/annotation stability plus resolution monotonicity. -/
theorem RecRulesOk.cons {env : Env} (m : EnvModel V env)
    {c₀ : ConstantInfo} {val' : ConstVal V}
    (hfind' : env.find? c₀.name = none)
    (_hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat,
      val' n ψ = m.val n ψ)
    (htrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      interpClosed V val' (⟨c₀ :: env.consts⟩ : Env) ψ e =
        interpClosed V m.val env ψ e)
    (hAtrans : ∀ (e : Expr), e.constsResolve env = true → ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) e →
      AnnotOk V val' (⟨c₀ :: env.consts⟩ : Env) ψ 0 (rho0 V) e)
    (hnewrec : RecMemberOk (V := V) ⟨c₀ :: env.consts⟩ val' c₀) :
    RecRulesOk V ⟨c₀ :: env.consts⟩ val' := by
  intro n cvR mI rP rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    subst hn
    exact hnewrec cvR mI rP rules hceq r hr
  · next hn =>
    obtain ⟨hA, hle, hple, hpinsLen, hfold⟩ :=
      m.rec_rules n cvR mI rP rules hfp r hr
    obtain ⟨-, -, -, -, -, hrules, -⟩ := m.wf _ (find?_mem hfp)
    obtain ⟨-, -, hrres, -, -⟩ := hrules cvR mI rP rules rfl r hr
    refine ⟨fun ψ => hAtrans _ hrres ψ (hA ψ), hle, hple, hpinsLen, ?_⟩
    intro cvj cnP cnF hfj hfire
    rw [Env.find?_cons] at hfj
    split at hfj
    · next hnc =>
      obtain ⟨cvj2, cnP2, cnF2, hfc2⟩ :=
        m.ind_ok.right.right.right.right.right.left n cvR mI rP rules
          hfp r hr
      rw [← hnc] at hfc2
      rw [hfind'] at hfc2
      exact nomatch hfc2
    · next hnc =>
      obtain ⟨fvms, bL, hparts, hwf, hlen, hres, hψ⟩ :=
        hfold cvj cnP cnF hfj hfire
      have hle' : ∀ nn : Name, (env.find? nn).isSome = true →
          ((⟨c₀ :: env.consts⟩ : Env).find? nn).isSome = true := by
        intro nn hnn
        rw [Env.find?_cons_of_isSome hfind' hnn]
        exact hnn
      refine ⟨fvms, bL, hparts, hwf, hlen,
        Expr.constsResolve_le hle' hres, ?_⟩
      intro ψ
      obtain ⟨hAL, Rv, hLi, hRi⟩ := hψ ψ
      exact ⟨hAtrans _ hres ψ hAL, Rv,
        by rw [htrans _ hres ψ]; exact hLi,
        by rw [htrans _ hrres ψ]; exact hRi⟩

/-- The eta head obligation of `CapsOk.cons` is vacuous for a head
that is neither an inductive former, nor a constructor, nor a
recursor-kind constant (definitions, theorems, axioms, projection
table entries): the family premises pin those kinds. -/
theorem capsEtaHead_of_kinds {env : Env} {c₀ : ConstantInfo}
    {val' : ConstVal V}
    (hind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hctor : ∀ cv cnP cnF, c₀ ≠ .ctorInfo cv cnP cnF)
    (hrec : ∀ cv mI rP rules, c₀ ≠ .recInfo cv mI rP rules) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLaw V ⟨c₀ :: env.consts⟩ val' T cvT caps := by
  intro T cvT caps hfT hcape hres hfam hpart
  exfalso
  rcases hpart with rfl | hC | ⟨j, hj, hP⟩
  · rw [Env.find?_cons, if_pos rfl] at hfT
    exact hind cvT caps (Option.some.inj hfT)
  · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
    rw [hC, Env.find?_cons, if_pos rfl] at hfC
    exact hctor cvC caps.etaParams caps.etaFields (Option.some.inj hfC)
  · obtain ⟨-, -, hfP⟩ := hfam
    obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
    rw [hP, Env.find?_cons, if_pos rfl] at hf2
    exact hrec cv2 mI2 rP2 rules2 (Option.some.inj hf2)

/-- The eta head obligation of `CapsOk.cons` is vacuous for a
recursor-kind head whose name is not projection-function-shaped
(a modeled block's recursor member: `checkConstantVal` refuses the
shape). -/
theorem capsEtaHead_of_rec_shape {env : Env} {c₀ : ConstantInfo}
    {val' : ConstVal V}
    (hind : ∀ cv caps, c₀ ≠ .indInfo cv caps)
    (hctor : ∀ cv cnP cnF, c₀ ≠ .ctorInfo cv cnP cnF)
    (hshape : c₀.name.isProjFnShape = false) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLaw V ⟨c₀ :: env.consts⟩ val' T cvT caps := by
  intro T cvT caps hfT hcape hres hfam hpart
  exfalso
  rcases hpart with rfl | hC | ⟨j, hj, hP⟩
  · rw [Env.find?_cons, if_pos rfl] at hfT
    exact hind cvT caps (Option.some.inj hfT)
  · obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
    rw [hC, Env.find?_cons, if_pos rfl] at hfC
    exact hctor cvC caps.etaParams caps.etaFields (Option.some.inj hfC)
  · rw [← hP] at hshape
    simp [Name.isProjFnShape, projFnName] at hshape

/-- Extending with a fresh constant preserves the capability laws.
The single eta head obligation (`hheadEta`) is owed exactly when the
head *participates* in a (now complete) eta family — it is the former
itself, its capability constructor, or one of its projection
functions; the complement is pure transport.  The unit obligation is
owed only for a freshly installed unit-like former (the law mentions
no other name). -/
theorem CapsOk.cons {env : Env} {val val' : ConstVal V}
    {c₀ : ConstantInfo}
    (h : CapsOk V env val)
    (hwfe : EnvWF env)
    (hfresh : env.find? c₀.name = none)
    (hpres : ∀ (n : Name) (ψ : Name → Nat), n ≠ c₀.name →
      val' n ψ = val n ψ)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLaw V ⟨c₀ :: env.consts⟩ val' T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps →
      caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLaw V ⟨c₀ :: env.consts⟩ val' c₀.name cv caps) :
    CapsOk V ⟨c₀ :: env.consts⟩ val' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  have hagree : ∀ n, (env.find? n).isSome = true →
      ∀ ψ' : Name → Nat, val' n ψ' = val n ψ' := by
    intro n hnf ψ'
    refine hpres n ψ' ?_
    intro he
    rw [he, hfresh] at hnf
    exact nomatch hnf
  refine ⟨?_, ?_⟩
  · intro T cvT caps hf hcape hres hfam
    by_cases hpart : T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name
    · exact hheadEta T cvT caps hf hcape hres hfam hpart
    · -- the head is not part of the family: pure transport
      have hnT : T ≠ c₀.name := fun hh => hpart (Or.inl hh)
      have hnC : caps.etaCtor ≠ c₀.name :=
        fun hh => hpart (Or.inr (Or.inl hh))
      have hnP : ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name :=
        fun j hj hh => hpart (Or.inr (Or.inr ⟨j, hj, hh⟩))
      rw [hfind _ hnT] at hf
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      rw [hfind _ hnC] at hfC
      have hfam₀ : EtaFamilyStored env T caps := by
        refine ⟨hCres, ⟨cvC, hfC⟩, ?_⟩
        intro j hj
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
        rw [hfind _ (hnP j hj)] at hf2
        exact ⟨cv2, mI2, rP2, rules2, hf2⟩
      have hlaw := h.1 T cvT caps hf hcape hres hfam₀
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        exact h3
      intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
      have hfit' := TeleFit.env_shrink hfresh hagree hfit
        (by rw [Expr.constsResolve_instantiateLevelParams]
            exact hTres)
      have hx' : x ∈ˢ SpineFold V
          (val T (Level.substFn φ'' cvT.levelParams us)) ps := by
        rw [← hpres T _ hnT]
        exact hx
      have h1 := hlaw φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx' hfit'
      rw [← hpres _ _ hnC] at h1
      have h2 : ((List.range caps.etaFields).map fun j =>
          SpineFold V (val (projFnName T j)
            (Level.substFn φ'' cvT.levelParams us)) (ps ++ [x])) =
          ((List.range caps.etaFields).map fun j =>
          SpineFold V (val' (projFnName T j)
            (Level.substFn φ'' cvT.levelParams us)) (ps ++ [x])) := by
        refine List.map_congr_left ?_
        intro j hj
        rw [hpres _ _ (hnP j (List.mem_range.mp hj))]
      rw [h2] at h1
      exact h1
  · intro T cvT caps hf hcapu hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadUnit cvT caps (Option.some.inj hf) hcapu hres
    · rw [hfind _ hn] at hf
      have hlaw := h.2 T cvT caps hf hcapu hres
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        exact h3
      intro φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx hy hfit
      have hfit' := TeleFit.env_shrink hfresh hagree hfit
        (by rw [Expr.constsResolve_instantiateLevelParams]
            exact hTres)
      have hx' : x ∈ˢ SpineFold V
          (val T (Level.substFn φ'' cvT.levelParams us)) ps := by
        rw [← hpres T _ hn]
        exact hx
      have hy' : y ∈ˢ SpineFold V
          (val T (Level.substFn φ'' cvT.levelParams us)) ps := by
        rw [← hpres T _ hn]
        exact hy
      exact hlaw φ'' us ps x y d₁ ρ₁ d₂ ρ₂ rest hlen hx' hy' hfit'

end Setlec
