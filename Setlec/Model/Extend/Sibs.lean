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
must supply, phrased over the extended environment and valuation. -/
def RecMemberOk (env' : Env) (val' : ConstVal V)
    (ci : ConstantInfo) : Prop :=
  ∀ cvR mI rP rules, ci = .recInfo cvR mI rP rules →
    ∀ r ∈ rules,
      (∀ ψ : Name → Nat, AnnotOk V val' env' ψ 0 (rho0 V) (RecRule.rhs r)) ∧
      (RecRule.fire r ≠ .inert → rP ≤ mI) ∧
      ∀ cvj cnP cnF,
        env'.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) →
        ∀ (ψ ψj : Name → Nat) (args margs : List V) (tv : V),
          args.length = mI →
          margs.length = RecRule.ctorParams r + RecRule.nfields r →
          ChainSlots V (val' ci.name ψ) (args ++ [tv]) →
          ChainSlots V (val' (RecRule.ctor r) ψj) margs →
          tv = SpineFold V (val' (RecRule.ctor r) ψj) margs →
          (RecRule.fire r = .plain →
            margs.take (RecRule.ctorParams r) =
              (args ++ [tv]).take (RecRule.ctorParams r) ∧
            (∀ p ∈ cvj.levelParams, ψj p = ψ p)) →
          RecRule.fire r ≠ .inert →
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
              margs d₂ ρ₂ rest₂ ∧
            (rest₂.getAppArgs.drop (RecRule.ctorParams r)).mapM
              (interpExpr V val' env' φ' d₂ ρ₂) =
              some (args.drop rP) ∧
            (∀ lvls pins, RecRule.fire r = .nested lvls pins →
              mI = rP ∧
              (∀ p ∈ cvj.levelParams,
                ψj p = Level.substFn ψ cvj.levelParams lvls p) ∧
              ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
                FvarSpine dP ρP spineP args ∧
                (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
                (pins.map fun pin => Expr.instSeq spineP
                  (spineP.length - 1)
                  (pin.instantiateLevelParams cvR.levelParams us)).mapM
                  (interpExpr V val' env' φ' dP ρP) =
                  some (margs.take (RecRule.ctorParams r)))) →
          ∃ R, interpClosed V val' env' ψ (RecRule.rhs r) = some R ∧
            SpineFold V (val' ci.name ψ) (args ++ [tv]) =
              SpineFold V R
                (args.take rP ++ margs.drop (RecRule.ctorParams r)) ∧
            ChainSlots V R
              (args.take rP ++ margs.drop (RecRule.ctorParams r))

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
  intro n cvR mI rP rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    subst hn
    exact hnewrec cvR mI rP rules hceq r hr
  · next hn =>
    obtain ⟨hA, hle, hfold⟩ := m.rec_rules n cvR mI rP rules hfp r hr
    obtain ⟨-, -, -, -, -, hrules, -⟩ := m.wf _ (find?_mem hfp)
    obtain ⟨-, -, hrres, -, -⟩ := hrules cvR mI rP rules rfl r hr
    have hvaln : ∀ ψ : Name → Nat, val' n ψ = m.val n ψ :=
      fun ψ => hagree n (by rw [hfp]; rfl) ψ
    refine ⟨fun ψ => hAtrans _ hrres ψ (hA ψ), hle, ?_⟩
    intro cvj cnP cnF hfj ψ ψj args margs tv hl hml hch hmch htv hpeq
      hplain hfit
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
            margs d₂ ρ₂ rest₂ ∧
          ((rest₂.getAppArgs.drop (RecRule.ctorParams r)).mapM
            (interpExpr V m.val env φ' d₂ ρ₂) =
            some (args.drop rP) ∧
          (∀ lvls pins, RecRule.fire r = .nested lvls pins →
            mI = rP ∧
            (∀ p ∈ cvj.levelParams,
              ψj p = Level.substFn ψ cvj.levelParams lvls p) ∧
            ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
              FvarSpine dP ρP spineP args ∧
              (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
              (pins.map fun pin => Expr.instSeq spineP
                (spineP.length - 1)
                (pin.instantiateLevelParams cvR.levelParams us)).mapM
                (interpExpr V m.val env φ' dP ρP) =
                some (margs.take (RecRule.ctorParams r)))) := by
        obtain ⟨φ', us, usj, d, ρ, d₁, ρ₁, rest₁, d₂, ρ₂, rest₂,
          hψ, hψj, hf1, hf2, hidx, hnest⟩ := hfit
        obtain ⟨-, -, hRres, -, -, -⟩ := m.wf _ (find?_mem hfp)
        obtain ⟨-, -, hCres, -, -, -⟩ := m.wf _ (find?_mem hfj)
        have hCres' : (cvj.type.instantiateLevelParams cvj.levelParams
            usj).constsResolve env = true := by
          rw [Expr.constsResolve_instantiateLevelParams]
          exact hCres
        have hrres2 : rest₂.constsResolve env = true :=
          TeleFit.rest_resolve hf2 hCres'
        have htrans : ∀ (dX : Nat) (ρX : Nat → V) (l : List Expr),
            (∀ x ∈ l, x.constsResolve env = true) →
            l.mapM (interpExpr V m.val env φ' dX ρX) =
            l.mapM (interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) φ' dX
              ρX) := by
          intro dX ρX l
          induction l with
          | nil => intro _; rfl
          | cons x l ihl =>
            intro hres
            have hx' : interpExpr V m.val env φ' dX ρX x =
                interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) φ' dX ρX x := by
              rw [← interp_cval_ext hagree x dX ρX,
                ← interp_mono hfind' x dX ρX (hres x List.mem_cons_self)]
            simp only [List.mapM_cons, hx',
              ihl (fun y hy => hres y (List.mem_cons_of_mem _ hy))]
        refine ⟨φ', us, usj, d, ρ, d₁, ρ₁, rest₁, d₂, ρ₂, rest₂, hψ, hψj,
          TeleFit.env_shrink hfind' hagree hf1
            (by rw [Expr.constsResolve_instantiateLevelParams]; exact hRres),
          TeleFit.env_shrink hfind' hagree hf2 hCres', ?_, ?_⟩
        · rw [← hidx]
          exact htrans _ _ _ (fun x hx =>
            Expr.constsResolve_getAppArgs hrres2 x (List.mem_of_mem_drop hx))
        · intro lvls pins hfr
          obtain ⟨hmIrP, hlvl, dP, ρP, spineP, hFv, hsh, hmapM⟩ :=
            hnest lvls pins hfr
          refine ⟨hmIrP, hlvl, dP, ρP, spineP, hFv, hsh, ?_⟩
          rw [← hmapM]
          refine htrans _ _ _ ?_
          intro x hx
          obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp hx
          obtain ⟨-, -, -, -, hnestW⟩ := hrules cvR mI rP rules rfl r hr
          obtain ⟨-, -, hpinsW, -⟩ := hnestW lvls pins hfr
          rw [← Expr.instSpine_eq_instSeq]
          refine instSpine_constsResolve _ ?_ ?_
          · rw [Expr.constsResolve_instantiateLevelParams]
            exact (hpinsW pin hpin).2.2.1
          · intro a ha
            obtain ⟨i, nm, rfl⟩ := hsh a ha
            simp [Expr.constsResolve]
      obtain ⟨R, hRi, hfoldEq, hRch⟩ := hfold cvj cnP cnF hfj ψ ψj
        args margs tv hl hml hch hmch htv hpeq hplain hfit'
      refine ⟨R, ?_, ?_, hRch⟩
      · rw [htrans _ hrres ψ]
        exact hRi
      · rw [hvaln]
        exact hfoldEq

/-- Extending with a fresh constant preserves the modeled-value
bridges, given the head's own obligations. -/
theorem ModeledOk.cons {env : Env} {val val' : ConstVal V}
    {c₀ : ConstantInfo}
    (h : ModeledOk V env val)
    (hwfe : EnvWF env)
    (hfresh : env.find? c₀.name = none)
    (hpres : ∀ (n : Name) (ψ : Name → Nat), n ≠ c₀.name →
      val' n ψ = val n ψ)
    (hheadInd : ∀ cv caps, c₀ = .indInfo cv caps →
      reservedBasisNames.contains c₀.name = false →
      ((⟨c₀ :: env.consts⟩ : Env).find? (c₀.name.str "_model")).isSome
        = true ∧
      ∀ ψ : Name → Nat, val' c₀.name ψ = val' (c₀.name.str "_model") ψ)
    (hheadCtor : ∀ cv cnP cnF, c₀ = .ctorInfo cv cnP cnF →
      reservedBasisNames.contains c₀.name = false →
      ((⟨c₀ :: env.consts⟩ : Env).find? (c₀.name.str "_model")).isSome
        = true ∧
      ∀ ψ : Name → Nat, val' c₀.name ψ = val' (c₀.name.str "_model") ψ)
    (hheadProj : ∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule), c₀.name = projFnName T j →
      c₀ = .recInfo cv mI rP rules →
      ((⟨c₀ :: env.consts⟩ : Env).find? (projModelName T j)).isSome
        = true ∧
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
      UnitLaw V ⟨c₀ :: env.consts⟩ val' c₀.name cv caps) :
    ModeledOk V ⟨c₀ :: env.consts⟩ val' := by
  have hfind : ∀ n, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n cv caps hf hres
    by_cases hn : n = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadInd cv caps (Option.some.inj hf) hres
    · rw [hfind n hn] at hf
      obtain ⟨hms, hveq⟩ := h.1 n cv caps hf hres
      have hmne : n.str "_model" ≠ c₀.name := by
        intro he
        rw [he, hfresh] at hms
        exact nomatch hms
      refine ⟨?_, ?_⟩
      · rw [hfind _ hmne]
        exact hms
      · intro ψ
        rw [hpres _ ψ hn, hpres _ ψ hmne, hveq ψ]
  · intro n cv cnP cnF hf hres
    by_cases hn : n = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadCtor cv cnP cnF (Option.some.inj hf) hres
    · rw [hfind n hn] at hf
      obtain ⟨hms, hveq⟩ := h.2.1 n cv cnP cnF hf hres
      have hmne : n.str "_model" ≠ c₀.name := by
        intro he
        rw [he, hfresh] at hms
        exact nomatch hms
      refine ⟨?_, ?_⟩
      · rw [hfind _ hmne]
        exact hms
      · intro ψ
        rw [hpres _ ψ hn, hpres _ ψ hmne, hveq ψ]
  · intro T j cv2 mI2 rP2 rules2 hf
    by_cases hn : projFnName T j = c₀.name
    · have hc₀ : c₀ = .recInfo cv2 mI2 rP2 rules2 := by
        rw [Env.find?_cons, if_pos hn.symm] at hf
        exact Option.some.inj hf
      exact hn ▸ hheadProj T j cv2 mI2 rP2 rules2 hn.symm hc₀
    · rw [hfind _ hn] at hf
      obtain ⟨hms, hveq⟩ := h.2.2.1 T j cv2 mI2 rP2 rules2 hf
      have hmne : projModelName T j ≠ c₀.name := by
        intro he
        rw [he, hfresh] at hms
        exact nomatch hms
      refine ⟨?_, ?_⟩
      · rw [hfind _ hmne]
        exact hms
      · intro ψ
        rw [hpres _ ψ hn, hpres _ ψ hmne, hveq ψ]
  · intro T cvT caps hf hcape hres
    by_cases hn : T = c₀.name
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact hheadEta cvT caps (Option.some.inj hf) hcape hres
    · rw [hfind _ hn] at hf
      obtain ⟨hmsC, hmsP, hlaw⟩ := h.2.2.2.1 T cvT caps hf hcape hres
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
      have hlaw := h.2.2.2.2 T cvT caps hf hcapu hres
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

end Setlec
