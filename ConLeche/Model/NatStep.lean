module

public import ConLeche.Model.NatWf

public section

/-!
# `ReduceNatStep`/`PQ`, discharged (task #161, literal tier)

The literal tier's semantic rows, closed.  `Bridge/ReduceNat.lean`'s
branch analysis at the validated-annotation currency, standing on the
sixteen numeral transports (`NatSemP.lean`, `NatWfP.lean`) instead of
`Red.sound` — which is what the wall record said the P lane would have
to do, because `Red`'s soundness consumes `EnvSHyp.nat_ops` at the
*collapse* currency and the erasure factoring is refuted at the stored
operations' λ-towers.

The three pieces the seal-II record scoped as owed are all in place:
`EnvModelM.nat_ops` and `EnvModelM.div_mod` (the recurrence laws, from the
run certificates), the transports, and the whnf IH — which the
consumer chain now carries (`WhnfInputs.nat`/`TierInputsAt.nat_step`
take a `WhnfClaim` at the same fuel; `whnfStep_of` was already
discarding exactly that argument).

The reduct's reading, grading and frame conditions are unchanged from
`Steps/Nat.lean`'s leaf analysis, which was always premise-free; what
lands here is the `interp` equality, and with it the wall.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported natOpResult reduceNatFueled)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The pieces the branch analysis reads -/

/-- Whatever `rawNatLit?` accepts reads to the numeral spine it
reports — its two shapes are the literal itself and the `Nat.zero`
constant, and `natLit … 0` *is* the `Nat.zero` leaf
(`denote_rawNatLitR`'s mirror). -/
theorem denoteMeta_rawNatLit (m : EnvModel V env)
    (hs : natLitSupported env = true) {a0 : Expr} {n : Nat}
    (h : ConLeche.rawNatLit? a0 = some n) (d : Nat) :
    denoteMeta m.acval env φ d a0 = some (natLit m φ n) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hs
  match a0, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denoteMeta_natLit_spine m hs d k
  | .const c [], h =>
    simp only [ConLeche.rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      rw [natLit_zero]
      exact denoteMeta_levelless_const hfZ
        (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          = [] from hlpZ)
    · exact nomatch h

/-- An application's grading splits. -/
theorem wellDenotedV_app_inv {ρ : Nat → V} {fa aa : AnnotTerm}
    (h : WellDenotedV V ρ (.app fa aa)) :
    WellDenotedV V ρ fa ∧ WellDenotedV V ρ aa := by
  obtain ⟨h1, h2⟩ := h
  rw [WellDenoted_app] at h1
  rw [AnnotValid_app] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2⟩⟩

/-- The frame conditions of a unary application's argument
(`frame_app1R`'s mirror). -/
theorem frame_app1 {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {c : Name} {a : Expr}
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOk m φ d Δa (.app (.const c []) a)) :
    Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a ∧ CtxOk m φ d Δa a := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]),
    hC.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])⟩

/-- The frame conditions of a binary application's two arguments
(`frame_app2R`'s mirror). -/
theorem frame_app2 {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {c : Name} {a b : Expr}
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOk m φ d Δa (.app (.app (.const c []) a) b)) :
    (Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a ∧ CtxOk m φ d Δa a) ∧
      (Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b ∧ CtxOk m φ d Δa b) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨⟨hws.1.2, hb.1.2, fun l hl => hLb l ?_,
      hC.of_subset (fun l hl => ?_)⟩,
    hws.2, hb.2, fun l hl => hLb l ?_, hC.of_subset (fun l hl => ?_)⟩ <;>
    simp [Expr.fvarLeaves, hl]

/-- **An argument whose head normal form `rawNatLit?` reads as a
literal interprets as that numeral** — `arg_natLitR`'s mirror, through
the whnf IH the consumer chain now carries. -/
theorem argNatLit {m : EnvModel V env} {fuel : Nat}
    (ihw : WhnfClaim μ m φ fuel) (hs : natLitSupported env = true)
    {d : Nat} {Δa : List AnnotTerm} {a a0 : Expr} {n : Nat} {aa : AnnotTerm}
    (hwa : ConLeche.whnf μ env fuel d a = .ok a0)
    (hraw : ConLeche.rawNatLit? a0 = some n)
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOk m φ d Δa a)
    (haa : denoteMeta m.acval env φ d a = some aa)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ aa = interp V ρ (natLit m φ n) :=
  (ihw hwa hws hb hLb hC haa (denoteMeta_rawNatLit m hs hraw d) hok).2
    ρ hρ

/-- A stored level-monomorphic head's reading, inverted. -/
theorem denoteMeta_head {m : EnvModel V env} {d : Nat} {c : Name}
    {ci : ConstantInfo} {fa : AnnotTerm}
    (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = [])
    (h : denoteMeta m.acval env φ d (.const c []) = some fa) :
    fa = m.acval c φ :=
  (Option.some.inj ((denoteMeta_levelless_const hf hlp).symm.trans h)).symm

/-! ## The unary clause

`Nat.succ` packing — the only unary operation official's `reduce_nat`
folds, and since the audit's S1 the only one ours folds either. -/

/-- The `.app (.const c []) a` clause's `interp` equality. -/
theorem reduceNatSem_unary (mp : EnvModelM V μ env) {fuel : Nat}
    (ihw : WhnfClaim μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {c : Name} {a e₂ : Expr}
    {ea ea₂ : AnnotTerm}
    (h : reduceNatFueled μ env fuel d (.app (.const c []) a)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOk mp.base2 φ d Δa (.app (.const c []) a))
    (hea : denoteMeta mp.base2.acval env φ d (.app (.const c []) a)
      = some ea)
    (hea₂ : denoteMeta mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ ea = interp V ρ ea₂ := by
  obtain ⟨hwsa, hba, hLa, hCa⟩ := frame_app1 hws hb hLb hC
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hea
  have hokA : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' aa :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hok ρ' hρ')).2
  simp only [reduceNatFueled, ConLeche.reduceNat, Bind.bind, Except.bind,
    ConLeche.whnf_def] at h
  split at h
  · -- `Nat.succ` packing
    next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n =>
      rw [hra] at h
      simp only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at h
      subst h
      obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS,
        hlpN, hlpZ, hlpS, -⟩ := ConLeche.natLitSupported_inv hnat
      obtain rfl : fa = mp.base2.acval ConLeche.natSuccName φ :=
        denoteMeta_head hfS
          (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
            = [] from hlpS) hfa
      obtain rfl : ea₂ = natLit mp.base2 φ (n + 1) :=
        Option.some.inj
          (hea₂.symm.trans (denoteMeta_natLit_spine mp.base2 hnat d (n + 1)))
      rw [interp_app,
        argNatLit ihw hnat hwa hra hwsa hba hLa hCa haa hokA ρ hρ,
        natLit_succ, interp_app]
  · simp [pure, Except.pure] at h

/-! ## The binary clause

The fourteen certified operations, and the WF-pin safety net (which
throws on literal arguments). -/

set_option maxHeartbeats 1600000 in
/-- The `.app (.app (.const c []) a) b` clause's `interp` equality. -/
theorem reduceNatSem_binary (mp : EnvModelM V μ env) {fuel : Nat}
    (ihw : WhnfClaim μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {c : Name} {a b e₂ : Expr}
    {ea ea₂ : AnnotTerm}
    (h : reduceNatFueled μ env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOk mp.base2 φ d Δa (.app (.app (.const c []) a) b))
    (hea : denoteMeta mp.base2.acval env φ d
      (.app (.app (.const c []) a) b) = some ea)
    (hea₂ : denoteMeta mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ ea = interp V ρ ea₂ := by
  obtain ⟨⟨hwsa, hba, hLa, hCa⟩, hwsb, hbb, hLb', hCb⟩ :=
    frame_app2 hws hb hLb hC
  obtain ⟨fab, ba, hfab, hba', rfl⟩ := denoteMeta_app_inv hea
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteMeta_app_inv hfab
  have hokB : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' ba :=
    fun ρ' hρ' => (wellDenotedV_app_inv (hok ρ' hρ')).2
  have hokA : ∀ ρ' : Nat → V, Sat V Δa ρ' → WellDenotedV V ρ' aa :=
    fun ρ' hρ' =>
      (wellDenotedV_app_inv (wellDenotedV_app_inv (hok ρ' hρ')).1).2
  simp only [reduceNatFueled, ConLeche.reduceNat, Bind.bind, Except.bind,
    ConLeche.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨h14, hstored⟩ := hcond
    have hmemN : c ∈ ConLeche.natOpNames ∨ c ∈ ConLeche.natDivModNames := by
      rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
    have hguard := natOpGuardLaw_of mp _ hmemN hstored
    obtain ⟨hnat, hdeps, hbool⟩ := ConLeche.natOpGuard_inv hguard
    have hself : c ∈ ConLeche.natOpDeps c := by
      rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl <;> decide
    obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps c hself
    -- first argument first; the second only behind a literal (D15)
    cases hwa : ConLeche.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : ConLeche.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    rw [hra] at h
    dsimp only at h
    cases hwb : ConLeche.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hrb : ConLeche.rawNatLit? b0 with
    | none => rw [hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hrb] at h
      dsimp only at h
      cases hres : natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        subst h
        obtain rfl : fa = mp.base2.acval c φ :=
          denoteMeta_head hfc
            (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
              = [] from hlpc) hfa
        have hA := argNatLit ihw hnat hwa hra hwsa hba hLa hCa haa
          hokA ρ hρ
        have hB := argNatLit ihw hnat hwb hrb hwsb hbb hLb' hCb hba'
          hokB ρ hρ
        have close : ∀ K : Nat, r = .lit (.natVal K) →
            SetTheory.app (SetTheory.app
              (interp V ρ (mp.base2.acval c φ))
              (interp V ρ (natLit mp.base2 φ n₁)))
              (interp V ρ (natLit mp.base2 φ n₂))
              = interp V ρ (natLit mp.base2 φ K) →
            interp V ρ ((.app (.app (mp.base2.acval c φ) aa) ba
              : AnnotTerm)) = interp V ρ ea₂ := by
          intro K hr hop
          subst hr
          obtain rfl : ea₂ = natLit mp.base2 φ K :=
            Option.some.inj (hea₂.symm.trans
              (denoteMeta_natLit_spine mp.base2 hnat d K))
          rw [interp_app, interp_app, hA, hB]
          exact hop
        have closeB : (c = ConLeche.natBeqName ∨ c = ConLeche.natBleName) →
            ∀ bn : Name,
            (bn = ConLeche.boolTrueName ∨ bn = ConLeche.boolFalseName) →
            r = .const bn [] →
            SetTheory.app (SetTheory.app
              (interp V ρ (mp.base2.acval c φ))
              (interp V ρ (natLit mp.base2 φ n₁)))
              (interp V ρ (natLit mp.base2 φ n₂))
              = interp V ρ (mp.base2.acval bn φ) →
            interp V ρ ((.app (.app (mp.base2.acval c φ) aa) ba
              : AnnotTerm)) = interp V ρ ea₂ := by
          intro hcb bn hbn hr hop
          subst hr
          obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool
            (by rcases hcb with rfl | rfl
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl))
          obtain rfl : ea₂ = mp.base2.acval bn φ := by
            rcases hbn with rfl | rfl
            · exact Option.some.inj (hea₂.symm.trans
                (denoteMeta_levelless_const hfT hlpT))
            · exact Option.some.inj (hea₂.symm.trans
                (denoteMeta_levelless_const hfF hlpF))
          rw [interp_app, interp_app, hA, hB]
          exact hop
        rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
          rfl|rfl|rfl
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_add mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValid hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_sub mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValid hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_mul mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValid hfc ρ n₁ n₂)
        · -- `pow`: the reduct exists only below the official exponent cap
          exact close _ (by
              have hres' := hres
              simp +decide [natOpResult] at hres'
              exact hres'.2.symm)
            (natOpV_pow mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValid hfc ρ n₁ n₂)
        · refine closeB (Or.inl rfl)
            (if n₁ = n₂ then ConLeche.boolTrueName
              else ConLeche.boolFalseName)
            (by by_cases hh : n₁ = n₂ <;> simp [hh])
            (by simpa +decide [natOpResult] using hres.symm) ?_
          exact natOpV_beq mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
            mp.acvalValid hfc ρ n₁ n₂
        · refine closeB (Or.inr rfl)
            (if n₁ ≤ n₂ then ConLeche.boolTrueName
              else ConLeche.boolFalseName)
            (by by_cases hh : n₁ ≤ n₂ <;> simp [hh])
            (by simpa +decide [natOpResult] using hres.symm) ?_
          exact natOpV_ble mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
            mp.acvalValid hfc ρ n₁ n₂
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_div (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_mod (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_gcd (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_land (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_lor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_xor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_shiftLeft (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV_shiftRight (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValid
              (mp.div_mod φ) hfc ρ n₁ n₂)
  · split at h
    · -- the WF-pin safety net: it throws
      cases hwa : ConLeche.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : ConLeche.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      rw [hra] at h
      dsimp only at h
      cases hwb : ConLeche.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hrb : ConLeche.rawNatLit? b0 with
      | none => rw [hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-! ## The two rows, discharged -/

/-- **Literal acceleration preserves the interpretation.**  The
statement `NatOpSemP` isolated at the seal-II wall, now a theorem. -/
theorem reduceNatSem (mp : EnvModelM V μ env) {fuel : Nat}
    (ihw : WhnfClaim μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {e e₂ : Expr} {ea ea₂ : AnnotTerm}
    (h : reduceNatFueled μ env fuel d e = .ok (some e₂))
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOk mp.base2 φ d Δa e)
    (hea : denoteMeta mp.base2.acval env φ d e = some ea)
    (hea₂ : denoteMeta mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) :
    interp V ρ ea = interp V ρ ea₂ := by
  match e, h, hws, hb, hLb, hC, hea, hok with
  | .app (.const c []) a, h, hws, hb, hLb, hC, hea, hok =>
    exact reduceNatSem_unary mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ
  | .app (.app (.const c []) a) b, h, hws, hb, hLb, hC, hea, hok =>
    exact reduceNatSem_binary mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ
  | .bvar _, h, _, _, _, _, _, _ | .fvar _ _, h, _, _, _, _, _, _
  | .sort _, h, _, _, _, _, _, _ | .lam _ _ _, h, _, _, _, _, _, _
  | .forallE _ _ _, h, _, _, _, _, _, _
  | .letE _ _ _, h, _, _, _, _, _, _
  | .lit _, h, _, _, _, _, _, _ | .proj _ _ _, h, _, _, _, _, _, _
  | .const _ _, h, _, _, _, _, _, _ =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h, _, _, _, _, _, _
  | .app (.fvar _ _) _, h, _, _, _, _, _, _
  | .app (.sort _) _, h, _, _, _, _, _, _
  | .app (.lam _ _ _) _, h, _, _, _, _, _, _
  | .app (.forallE _ _ _) _, h, _, _, _, _, _, _
  | .app (.letE _ _ _) _, h, _, _, _, _, _, _
  | .app (.lit _) _, h, _, _, _, _, _, _
  | .app (.proj _ _ _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h, _, _, _, _, _, _ =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h, _, _, _, _, _, _
  | .app (.app (.fvar _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.sort _) _) _, h, _, _, _, _, _, _
  | .app (.app (.app _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.lam _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.forallE _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.letE _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.lit _) _) _, h, _, _, _, _, _, _
  | .app (.app (.proj _ _ _) _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatFueled, ConLeche.reduceNat, pure, Except.pure] at h

/-- **`ReduceNatStep`, proved.**  The reduct's reading, grading and
frame conditions are `Steps/Nat.lean`'s premise-free leaf analysis;
the `interp` equality is `reduceNatSem`. -/
theorem reduceNatStep_of (mp : EnvModelM V μ env) {fuel : Nat}
    (ihw : WhnfClaim μ mp.base2 φ fuel) :
    ReduceNatStep μ mp.base2 φ fuel := by
  intro d e e₂ Δa h hws hb hLb ea hC hea hok
  have hleaf := reduceNat_natLeaf (natOpGuardLaw_of mp) h
  obtain ⟨ea₂, hea₂⟩ :=
    denoteMeta_of_natLeaf (acval := mp.base2.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeaf (d := d) hleaf
  exact ⟨ea₂, hea₂,
    fun ρ _ => wellDenotedV_of_natLeaf mp.base2 (mp.nat_heads φ)
      mp.acvalValid hleaf hea₂ ρ,
    fun ρ hρ => reduceNatSem mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ,
    hws₂, hb₂, hLb₂, ctxOk_of_natLeaf hleaf hC⟩

/-- **`ReduceNatStepPQ`, proved** — the defeq quarter's row differs
from the whnf quarter's only in where the subject's annotation is
bound. -/
theorem reduceNatStepPQ_of (mp : EnvModelM V μ env) {fuel : Nat}
    (ihw : WhnfClaim μ mp.base2 φ fuel) :
    ReduceNatStepPQ μ mp.base2 φ fuel := by
  intro d e e₂ Δa ea h hws hb hLb hC hea hok
  exact reduceNatStep_of mp ihw h hws hb hLb hC hea hok

end ConLeche.Model
