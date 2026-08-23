import Setlec.Verify.InstSpine
import Setlec.Model.Extend.Inversions

/-!
# Sibs — split out of `Setlec.Model.Extend`

Per-clause preservation (`.cons`) lemmas for extending an
environment by one fresh constant: `BasisBlocks`, `RecCtorsStored`,
`RecRulesOk` and `ModeledOk`, with the head obligations (`SibFinds`,
`RecMemberOk`) they consume.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- The sibling-availability data `BasisBlocks` preservation needs when
extending by one (fresh) constant: if the constant is a recursor-kind
record, the members of its block are already stored. -/
def SibFinds (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
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
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨hs, -, -, -⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.1 cv mI rP rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, hs, -, -⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2, h3⟩ := hs hn
      exact ⟨keep h1, keep h2, keep h3⟩
    · next hn =>
      obtain ⟨h1, h2, h3⟩ := hb.right.left cv mI rP rules h
      exact ⟨keep h1, keep h2, keep h3⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, hs, -⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.left cv mI rP rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, -, hs⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right.right cv mI rP rules h
      exact ⟨keep h1, keep h2⟩

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

/-- `RecCtorsStored` is preserved by a fresh extension, given the
stored-constructor facts for the new member (vacuous unless it is a
recursor). -/
theorem RecCtorsStored.cons {env : Env} {c₀ : ConstantInfo}
    (hold : RecCtorsStored env) (hfresh : env.find? c₀.name = none)
    (hnew : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) :
    RecCtorsStored (⟨c₀ :: env.consts⟩ : Env) := by
  intro n cv mI rP rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    obtain ⟨cvj, cnP, cnF, hf⟩ := hnew _ _ _ _ hceq r hr
    refine ⟨cvj, cnP, cnF, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf
  · next hn =>
    obtain ⟨cvj, cnP, cnF, hf⟩ := hold n cv mI rP rules hfp r hr
    refine ⟨cvj, cnP, cnF, ?_⟩
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf

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

/-- Extending with a fresh constant preserves the modeled-value
bridges, given the head's own obligations. -/
theorem ModeledOk.cons {env : Env} {val val' : ConstVal V}
    {c₀ : ConstantInfo}
    (h : ModeledOk V env val)
    (hwfe : EnvWF env)
    (hfresh : env.find? c₀.name = none)
    (hpres : ∀ (n : Name) (ψ : Name → Nat), n ≠ c₀.name →
      val' n ψ = val n ψ)
    (hheadCtor : ∀ cv cnP cnF, c₀ = .ctorInfo cv cnP cnF →
      reservedBasisNames.contains c₀.name = false →
      ((⟨c₀ :: env.consts⟩ : Env).find? (c₀.name.str "_model")).isSome
        = true →
      ∀ ψ : Name → Nat, val' c₀.name ψ = val' (c₀.name.str "_model") ψ)
    (hheadProj : ∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule), c₀.name = projFnName T j →
      c₀ = .recInfo cv mI rP rules →
      ((⟨c₀ :: env.consts⟩ : Env).find? (projModelName T j)).isSome
        = true →
      ∀ ψ : Name → Nat,
        val' (projFnName T j) ψ = val' (projModelName T j) ψ)
    -- the *companion* side of the linkage: installing an `X._model`
    -- for an already-stored `X` would activate the clause for a
    -- constant whose value was fixed without it.  The checker rejects
    -- that (`checkConstantVal`'s model-family guard), so every call
    -- site discharges this by contradiction.
    (hheadCompanionCtor : ∀ (n : Name) cv cnP cnF,
      c₀.name = n.str "_model" →
      env.find? n = some (.ctorInfo cv cnP cnF) →
      reservedBasisNames.contains n = false →
      ∀ ψ : Name → Nat, val' n ψ = val' (n.str "_model") ψ)
    (hheadCompanionProj : ∀ (T : Name) (j : Nat) cv mI rP rules,
      c₀.name = projModelName T j →
      (env.find? T).isSome = true →
      env.find? (projFnName T j) = some (.recInfo cv mI rP rules) →
      ∀ ψ : Name → Nat,
        val' (projFnName T j) ψ = val' (projModelName T j) ψ)
    (hheadEta : ∀ cv caps, c₀ = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains c₀.name = false →
      ((⟨c₀ :: env.consts⟩ : Env).find?
        (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        ((⟨c₀ :: env.consts⟩ : Env).find?
          (projModelName c₀.name j)).isSome = true) ∧
      EtaLaw V ⟨c₀ :: env.consts⟩ val' c₀.name cv caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps →
      caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLaw V ⟨c₀ :: env.consts⟩ val' c₀.name cv caps)
    (hheadParent : ∀ (T : Name) (j : Nat) cv mI rP rules,
      c₀.name = projFnName T j → c₀ = .recInfo cv mI rP rules →
      ((⟨c₀ :: env.consts⟩ : Env).find? T).isSome = true) :
    ModeledOk V ⟨c₀ :: env.consts⟩ val' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n cv cnP cnF hf hres hmsN
    by_cases hn : n = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadCtor cv cnP cnF (Option.some.inj hf) hres hmsN
    · rw [hfind n hn] at hf
      by_cases hmne : n.str "_model" = c₀.name
      · exact hheadCompanionCtor n cv cnP cnF hmne.symm hf hres
      · rw [hfind _ hmne] at hmsN
        intro ψ
        rw [hpres _ ψ hn, hpres _ ψ hmne]
        exact h.1 n cv cnP cnF hf hres hmsN ψ
  · intro T cvT capsT j cv2 mI2 rP2 rules2 hfT hf hmsP
    by_cases hn : projFnName T j = c₀.name
    · have hc₀ : c₀ = .recInfo cv2 mI2 rP2 rules2 := by
        rw [Env.find?_cons, if_pos hn.symm] at hf
        exact Option.some.inj hf
      exact hheadProj T j cv2 mI2 rP2 rules2 hn.symm hc₀ hmsP
    · rw [hfind _ hn] at hf
      by_cases hnT : T = c₀.name
      · -- the parent would be the constant being installed, but a
        -- stored projection function's parent is stored already
        exfalso
        have := h.2.2.2.2 T j cv2 mI2 rP2 rules2 hf
        rw [hnT, hfresh] at this
        exact nomatch this
      · rw [hfind _ hnT] at hfT
        by_cases hmne : projModelName T j = c₀.name
        · exact hheadCompanionProj T j cv2 mI2 rP2 rules2 hmne.symm
            (by rw [hfT]; rfl) hf
        · rw [hfind _ hmne] at hmsP
          intro ψ
          rw [hpres _ ψ hn, hpres _ ψ hmne]
          exact h.2.1 T cvT capsT j cv2 mI2 rP2 rules2 hfT hf hmsP ψ
  · intro T cvT caps hf hcape hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadEta cvT caps (Option.some.inj hf) hcape hres
    · rw [hfind _ hn] at hf
      obtain ⟨hmsC, hmsP, hlaw⟩ := h.2.2.1 T cvT caps hf hcape hres
      have hCne : caps.etaCtor.str "_model" ≠ c₀.name := by
        intro he
        rw [he, hfresh] at hmsC
        exact nomatch hmsC
      have hPne : ∀ j, j < caps.etaFields →
          projModelName T j ≠ c₀.name := by
        intro j hj he
        have := hmsP j hj
        rw [he, hfresh] at this
        exact nomatch this
      have hagree : ∀ n, (env.find? n).isSome = true →
          ∀ ψ' : Name → Nat, val' n ψ' = val n ψ' := by
        intro n hnf ψ'
        refine hpres n ψ' ?_
        intro he
        rw [he, hfresh] at hnf
        exact nomatch hnf
      have hTres : cvT.type.constsResolve env = true := by
        obtain ⟨-, -, h3, -⟩ := hwfe _ (find?_mem hf)
        exact h3
      refine ⟨?_, ?_, ?_⟩
      · rw [hfind _ hCne]
        exact hmsC
      · intro j hj
        rw [hfind _ (hPne j hj)]
        exact hmsP j hj
      · intro φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx hfit
        have hfit' := TeleFit.env_shrink hfresh hagree hfit
          (by rw [Expr.constsResolve_instantiateLevelParams]
              exact hTres)
        have hx' : x ∈ˢ SpineFold V
            (val T (Level.substFn φ'' cvT.levelParams us)) ps := by
          rw [← hpres T _ hn]
          exact hx
        have h1 := hlaw φ'' us ps x d₁ ρ₁ d₂ ρ₂ rest hlen hx' hfit'
        rw [← hpres _ _ hCne] at h1
        have h2 : ((List.range caps.etaFields).map fun j =>
            SpineFold V (val (projModelName T j)
              (Level.substFn φ'' cvT.levelParams us)) (ps ++ [x])) =
            ((List.range caps.etaFields).map fun j =>
            SpineFold V (val' (projModelName T j)
              (Level.substFn φ'' cvT.levelParams us)) (ps ++ [x])) := by
          refine List.map_congr_left ?_
          intro j hj
          rw [hpres _ _ (hPne j (List.mem_range.mp hj))]
        rw [h2] at h1
        exact h1
  · intro T cvT caps hf hcapu hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadUnit cvT caps (Option.some.inj hf) hcapu hres
    · rw [hfind _ hn] at hf
      have hlaw := h.2.2.2.1 T cvT caps hf hcapu hres
      have hagree : ∀ n, (env.find? n).isSome = true →
          ∀ ψ' : Name → Nat, val' n ψ' = val n ψ' := by
        intro n hnf ψ'
        refine hpres n ψ' ?_
        intro he
        rw [he, hfresh] at hnf
        exact nomatch hnf
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
  · intro T j cv2 mI2 rP2 rules2 hf
    by_cases hn : projFnName T j = c₀.name
    · have hc₀ : c₀ = .recInfo cv2 mI2 rP2 rules2 := by
        rw [Env.find?_cons, if_pos hn.symm] at hf
        exact Option.some.inj hf
      exact hheadParent T j cv2 mI2 rP2 rules2 hn.symm hc₀
    · rw [hfind _ hn] at hf
      have hp := h.2.2.2.2 T j cv2 mI2 rP2 rules2 hf
      by_cases hnT : T = c₀.name
      · rw [hnT, Env.find?_cons, if_pos rfl]; rfl
      · rw [hfind _ hnT]; exact hp

end Setlec
