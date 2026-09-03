import Setlec.SetP.NatWfP

/-!
# `ReduceNatStepP`/`PQ`, discharged (task #161, literal tier)

The literal tier's semantic rows, closed.  `Bridge/ReduceNat.lean`'s
branch analysis at the validated-annotation currency, standing on the
sixteen numeral transports (`NatSemP.lean`, `NatWfP.lean`) instead of
`Red.sound` — which is what the wall record said the P lane would have
to do, because `Red`'s soundness consumes `EnvSHyp.nat_ops` at the
*collapse* currency and the erasure factoring is refuted at the stored
operations' λ-towers.

The three pieces the seal-II record scoped as owed are all in place:
`EnvS2PM.nat_ops` and `EnvS2PM.div_mod` (the recurrence laws, from the
run certificates), the transports, and the whnf IH — which the
consumer chain now carries (`WhnfInputsP.nat`/`TierInputsAtP.nat_step`
take a `WhnfClaims2P` at the same fuel; `whnfStepP_of` was already
discarding exactly that argument).

The reduct's reading, grading and frame conditions are unchanged from
`Step2/NatP.lean`'s leaf analysis, which was always premise-free; what
lands here is the `interp2` equality, and with it the wall.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported natOpResult reduceNatP)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The pieces the branch analysis reads -/

/-- Whatever `rawNatLit?` accepts reads to the numeral spine it
reports — its two shapes are the literal itself and the `Nat.zero`
constant, and `natLitP … 0` *is* the `Nat.zero` leaf
(`denote_rawNatLitR`'s mirror). -/
theorem denoteP_rawNatLitP (m : EnvS2Core V env)
    (hs : natLitSupported env = true) {a0 : Expr} {n : Nat}
    (h : Setlec.rawNatLit? a0 = some n) (d : Nat) :
    denoteP m.acval env φ d a0 = some (natLitP m φ n) := by
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS, hlpN,
    hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hs
  match a0, h with
  | .lit (.natVal k), h =>
    obtain rfl : k = n := Option.some.inj h
    exact denoteP_natLitP m hs d k
  | .const c [], h =>
    simp only [Setlec.rawNatLit?] at h
    split at h
    · next hc =>
      subst hc
      obtain rfl : (0 : Nat) = n := Option.some.inj h
      rw [natLitP_zero]
      exact denoteP_levelless_const hfZ
        (show (ConstantInfo.ctorInfo cv0 i0 j0).toConstantVal.levelParams
          = [] from hlpZ)
    · exact nomatch h

/-- An application's grading splits. -/
theorem annotOkP_app_inv {ρ : Nat → V} {fa aa : AVExpr}
    (h : AnnotOkP V ρ (.app fa aa)) :
    AnnotOkP V ρ fa ∧ AnnotOkP V ρ aa := by
  obtain ⟨h1, h2⟩ := h
  rw [AnnotOk2_app] at h1
  rw [AnnotValidV_app] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2⟩⟩

/-- The frame conditions of a unary application's argument
(`frame_app1R`'s mirror). -/
theorem frame_app1P {m : EnvS2Core V env} {d : Nat}
    {Δa : List AVExpr} {c : Name} {a : Expr}
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOkP m φ d Δa (.app (.const c []) a)) :
    Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a ∧ CtxOkP m φ d Δa a := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hws.2, hb.2, fun l hl => hLb l (by simp [Expr.fvarLeaves, hl]),
    hC.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl])⟩

/-- The frame conditions of a binary application's two arguments
(`frame_app2R`'s mirror). -/
theorem frame_app2P {m : EnvS2Core V env} {d : Nat}
    {Δa : List AVExpr} {c : Name} {a b : Expr}
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOkP m φ d Δa (.app (.app (.const c []) a) b)) :
    (Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a ∧ CtxOkP m φ d Δa a) ∧
      (Expr.WScoped d b ∧ b.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded b ∧ CtxOkP m φ d Δa b) := by
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  refine ⟨⟨hws.1.2, hb.1.2, fun l hl => hLb l ?_,
      hC.of_subset (fun l hl => ?_)⟩,
    hws.2, hb.2, fun l hl => hLb l ?_, hC.of_subset (fun l hl => ?_)⟩ <;>
    simp [Expr.fvarLeaves, hl]

/-- **An argument whose head normal form `rawNatLit?` reads as a
literal interprets as that numeral** — `arg_natLitR`'s mirror, through
the whnf IH the consumer chain now carries. -/
theorem argNatLitP {m : EnvS2Core V env} {fuel : Nat}
    (ihw : WhnfClaims2P μ m φ fuel) (hs : natLitSupported env = true)
    {d : Nat} {Δa : List AVExpr} {a a0 : Expr} {n : Nat} {aa : AVExpr}
    (hwa : Setlec.whnf μ env fuel d a = .ok a0)
    (hraw : Setlec.rawNatLit? a0 = some n)
    (hws : Expr.WScoped d a) (hb : a.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded a) (hC : CtxOkP m φ d Δa a)
    (haa : denoteP m.acval env φ d a = some aa)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ aa)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ aa = interp2 V ρ (natLitP m φ n) :=
  (ihw hwa hws hb hLb hC haa (denoteP_rawNatLitP m hs hraw d) hok).2
    ρ hρ

/-- A stored level-monomorphic head's reading, inverted. -/
theorem denoteP_headP {m : EnvS2Core V env} {d : Nat} {c : Name}
    {ci : ConstantInfo} {fa : AVExpr}
    (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = [])
    (h : denoteP m.acval env φ d (.const c []) = some fa) :
    fa = m.acval c φ :=
  (Option.some.inj ((denoteP_levelless_const hf hlp).symm.trans h)).symm

/-! ## The unary clause

`Nat.succ` packing, `Nat.pred`, the certified `Nat.log2`, and the
capless `log2` safety net (which throws on a literal, so it cannot
reach here). -/

/-- The `.app (.const c []) a` clause's `interp2` equality. -/
theorem reduceNatSemP_unary (mp : EnvS2PM V μ env) {fuel : Nat}
    (ihw : WhnfClaims2P μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AVExpr} {c : Name} {a e₂ : Expr}
    {ea ea₂ : AVExpr}
    (h : reduceNatP μ env fuel d (.app (.const c []) a)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.const c []) a))
    (hb : (Expr.app (.const c []) a).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (.app (.const c []) a))
    (hC : CtxOkP mp.base2 φ d Δa (.app (.const c []) a))
    (hea : denoteP mp.base2.acval env φ d (.app (.const c []) a)
      = some ea)
    (hea₂ : denoteP mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ea = interp2 V ρ ea₂ := by
  obtain ⟨hwsa, hba, hLa, hCa⟩ := frame_app1P hws hb hLb hC
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv hea
  have hokA : ∀ ρ' : Nat → V, Sat2 V Δa ρ' → AnnotOkP V ρ' aa :=
    fun ρ' hρ' => (annotOkP_app_inv (hok ρ' hρ')).2
  simp only [reduceNatP, Setlec.reduceNat, Bind.bind, Except.bind,
    Setlec.whnf_def] at h
  split at h
  · -- `Nat.succ` packing
    next hcond =>
    obtain ⟨rfl, hnat⟩ := hcond
    cases hwa : Setlec.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hra : Setlec.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n =>
      rw [hra] at h
      simp only [pure, Except.pure, Except.ok.injEq,
        Option.some.injEq] at h
      subst h
      obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hfN, hfZ, hfS,
        hlpN, hlpZ, hlpS, -⟩ := Setlec.natLitSupported_inv hnat
      obtain rfl : fa = mp.base2.acval Setlec.natSuccName φ :=
        denoteP_headP hfS
          (show (ConstantInfo.ctorInfo cv1 i1 j1).toConstantVal.levelParams
            = [] from hlpS) hfa
      obtain rfl : ea₂ = natLitP mp.base2 φ (n + 1) :=
        Option.some.inj
          (hea₂.symm.trans (denoteP_natLitP mp.base2 hnat d (n + 1)))
      rw [interp2_app,
        argNatLitP ihw hnat hwa hra hwsa hba hLa hCa haa hokA ρ hρ,
        natLitP_succ, interp2_app]
  · split at h
    · -- `Nat.pred`
      next hcond =>
      obtain ⟨rfl, hstored⟩ := hcond
      have hguard := natOpGuardLawP_of mp _ (Or.inl (by decide)) hstored
      obtain ⟨hnat, hdeps, -⟩ := Setlec.natOpGuard_inv hguard
      obtain ⟨cvp, vp, hp, hfp, hlpp⟩ :=
        hdeps Setlec.natPredName (by decide)
      cases hwa : Setlec.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hra : Setlec.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n =>
        rw [hra] at h
        dsimp only at h
        cases hres : natOpResult Setlec.natPredName n 0 with
        | none => rw [hres] at h; simp [pure, Except.pure] at h
        | some r =>
          rw [hres] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h
          subst h
          obtain rfl : r = .lit (.natVal (n - 1)) := by
            simpa +decide [natOpResult] using hres.symm
          obtain rfl : fa = mp.base2.acval Setlec.natPredName φ :=
            denoteP_headP hfp
              (show (ConstantInfo.defnInfo cvp vp hp).toConstantVal.levelParams
                = [] from hlpp) hfa
          obtain rfl : ea₂ = natLitP mp.base2 φ (n - 1) :=
            Option.some.inj
              (hea₂.symm.trans
                (denoteP_natLitP mp.base2 hnat d (n - 1)))
          rw [interp2_app,
            argNatLitP ihw hnat hwa hra hwsa hba hLa hCa haa hokA ρ hρ]
          exact natOpV2_pred mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
            mp.acvalValidP hfp ρ n
    · split at h
      · -- the certified `Nat.log2`
        next hcond =>
        obtain ⟨rfl, hstored⟩ := hcond
        have hguard := natOpGuardLawP_of mp _ (Or.inr (by decide)) hstored
        obtain ⟨hnat, hdeps, -⟩ := Setlec.natOpGuard_inv hguard
        obtain ⟨cvl, vl, hl, hfl, hlpl⟩ :=
          hdeps Setlec.natLog2Name (by decide)
        cases hwa : Setlec.whnf μ env fuel d a with
        | error err => rw [hwa] at h; exact nomatch h
        | ok a0 =>
        rw [hwa] at h
        dsimp only at h
        cases hra : Setlec.rawNatLit? a0 with
        | none => rw [hra] at h; simp [pure, Except.pure] at h
        | some n =>
          rw [hra] at h
          dsimp only at h
          cases hres : natOpResult Setlec.natLog2Name n 0 with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            subst h
            obtain rfl : r = .lit (.natVal (Nat.log2 n)) := by
              simpa +decide [natOpResult] using hres.symm
            obtain rfl : fa = mp.base2.acval Setlec.natLog2Name φ :=
              denoteP_headP hfl
                (show (ConstantInfo.defnInfo cvl vl hl).toConstantVal.levelParams
                  = [] from hlpl) hfa
            obtain rfl : ea₂ = natLitP mp.base2 φ (Nat.log2 n) :=
              Option.some.inj
                (hea₂.symm.trans
                  (denoteP_natLitP mp.base2 hnat d (Nat.log2 n)))
            rw [interp2_app,
              argNatLitP ihw hnat hwa hra hwsa hba hLa hCa haa hokA ρ
                hρ]
            exact natOpV2_log2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValidP (mp.div_mod φ) hfl ρ n
      · split at h
        · -- the capless `log2` safety net: it throws
          cases hwa : Setlec.whnf μ env fuel d a with
          | error err => rw [hwa] at h; exact nomatch h
          | ok a0 =>
          rw [hwa] at h
          dsimp only at h
          cases hra : Setlec.rawNatLit? a0 with
          | none => rw [hra] at h; simp [pure, Except.pure] at h
          | some n =>
            rw [hra] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [pure, Except.pure] at h

/-! ## The binary clause

The fourteen certified operations, and the WF-pin safety net (which
throws on literal arguments). -/

set_option maxHeartbeats 1600000 in
/-- The `.app (.app (.const c []) a) b` clause's `interp2` equality. -/
theorem reduceNatSemP_binary (mp : EnvS2PM V μ env) {fuel : Nat}
    (ihw : WhnfClaims2P μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AVExpr} {c : Name} {a b e₂ : Expr}
    {ea ea₂ : AVExpr}
    (h : reduceNatP μ env fuel d (.app (.app (.const c []) a) b)
      = .ok (some e₂))
    (hws : Expr.WScoped d (.app (.app (.const c []) a) b))
    (hb : (Expr.app (.app (.const c []) a) b).looseBVarsBounded 0
      = true)
    (hLb : Expr.LeavesBounded (.app (.app (.const c []) a) b))
    (hC : CtxOkP mp.base2 φ d Δa (.app (.app (.const c []) a) b))
    (hea : denoteP mp.base2.acval env φ d
      (.app (.app (.const c []) a) b) = some ea)
    (hea₂ : denoteP mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ea = interp2 V ρ ea₂ := by
  obtain ⟨⟨hwsa, hba, hLa, hCa⟩, hwsb, hbb, hLb', hCb⟩ :=
    frame_app2P hws hb hLb hC
  obtain ⟨fab, ba, hfab, hba', rfl⟩ := denoteP_app_inv hea
  obtain ⟨fa, aa, hfa, haa, rfl⟩ := denoteP_app_inv hfab
  have hokB : ∀ ρ' : Nat → V, Sat2 V Δa ρ' → AnnotOkP V ρ' ba :=
    fun ρ' hρ' => (annotOkP_app_inv (hok ρ' hρ')).2
  have hokA : ∀ ρ' : Nat → V, Sat2 V Δa ρ' → AnnotOkP V ρ' aa :=
    fun ρ' hρ' =>
      (annotOkP_app_inv (annotOkP_app_inv (hok ρ' hρ')).1).2
  simp only [reduceNatP, Setlec.reduceNat, Bind.bind, Except.bind,
    Setlec.whnf_def] at h
  split at h
  · next hcond =>
    obtain ⟨h14, hstored⟩ := hcond
    have hmemN : c ∈ Setlec.natOpNames ∨ c ∈ Setlec.natDivModNames := by
      rcases h14 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
    have hguard := natOpGuardLawP_of mp _ hmemN hstored
    obtain ⟨hnat, hdeps, hbool⟩ := Setlec.natOpGuard_inv hguard
    have hself : c ∈ Setlec.natOpDeps c := by
      rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
        rfl|rfl <;> decide
    obtain ⟨cvc, vc, hcnt, hfc, hlpc⟩ := hdeps c hself
    cases hwa : Setlec.whnf μ env fuel d a with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a0 =>
    rw [hwa] at h
    dsimp only at h
    cases hwb : Setlec.whnf μ env fuel d b with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b0 =>
    rw [hwb] at h
    dsimp only at h
    cases hra : Setlec.rawNatLit? a0 with
    | none => rw [hra] at h; simp [pure, Except.pure] at h
    | some n₁ =>
    cases hrb : Setlec.rawNatLit? b0 with
    | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
    | some n₂ =>
      rw [hra, hrb] at h
      dsimp only at h
      cases hres : natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        subst h
        obtain rfl : fa = mp.base2.acval c φ :=
          denoteP_headP hfc
            (show (ConstantInfo.defnInfo cvc vc hcnt).toConstantVal.levelParams
              = [] from hlpc) hfa
        have hA := argNatLitP ihw hnat hwa hra hwsa hba hLa hCa haa
          hokA ρ hρ
        have hB := argNatLitP ihw hnat hwb hrb hwsb hbb hLb' hCb hba'
          hokB ρ hρ
        have close : ∀ K : Nat, r = .lit (.natVal K) →
            SetTheory.app (SetTheory.app
              (interp2 V ρ (mp.base2.acval c φ))
              (interp2 V ρ (natLitP mp.base2 φ n₁)))
              (interp2 V ρ (natLitP mp.base2 φ n₂))
              = interp2 V ρ (natLitP mp.base2 φ K) →
            interp2 V ρ ((.app (.app (mp.base2.acval c φ) aa) ba
              : AVExpr)) = interp2 V ρ ea₂ := by
          intro K hr hop
          subst hr
          obtain rfl : ea₂ = natLitP mp.base2 φ K :=
            Option.some.inj (hea₂.symm.trans
              (denoteP_natLitP mp.base2 hnat d K))
          rw [interp2_app, interp2_app, hA, hB]
          exact hop
        have closeB : (c = Setlec.natBeqName ∨ c = Setlec.natBleName) →
            ∀ bn : Name,
            (bn = Setlec.boolTrueName ∨ bn = Setlec.boolFalseName) →
            r = .const bn [] →
            SetTheory.app (SetTheory.app
              (interp2 V ρ (mp.base2.acval c φ))
              (interp2 V ρ (natLitP mp.base2 φ n₁)))
              (interp2 V ρ (natLitP mp.base2 φ n₂))
              = interp2 V ρ (mp.base2.acval bn φ) →
            interp2 V ρ ((.app (.app (mp.base2.acval c φ) aa) ba
              : AVExpr)) = interp2 V ρ ea₂ := by
          intro hcb bn hbn hr hop
          subst hr
          obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool
            (by rcases hcb with rfl | rfl
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl))
          obtain rfl : ea₂ = mp.base2.acval bn φ := by
            rcases hbn with rfl | rfl
            · exact Option.some.inj (hea₂.symm.trans
                (denoteP_levelless_const hfT hlpT))
            · exact Option.some.inj (hea₂.symm.trans
                (denoteP_levelless_const hfF hlpF))
          rw [interp2_app, interp2_app, hA, hB]
          exact hop
        rcases h14 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
          rfl|rfl|rfl
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_add mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValidP hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_sub mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValidP hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_mul mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValidP hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_pow mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
              mp.acvalValidP hfc ρ n₁ n₂)
        · refine closeB (Or.inl rfl)
            (if n₁ = n₂ then Setlec.boolTrueName
              else Setlec.boolFalseName)
            (by by_cases hh : n₁ = n₂ <;> simp [hh])
            (by simpa +decide [natOpResult] using hres.symm) ?_
          exact natOpV2_beq mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
            mp.acvalValidP hfc ρ n₁ n₂
        · refine closeB (Or.inr rfl)
            (if n₁ ≤ n₂ then Setlec.boolTrueName
              else Setlec.boolFalseName)
            (by by_cases hh : n₁ ≤ n₂ <;> simp [hh])
            (by simpa +decide [natOpResult] using hres.symm) ?_
          exact natOpV2_ble mp.base2 (mp.nat_ops φ) (mp.nat_heads φ)
            mp.acvalValidP hfc ρ n₁ n₂
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_div (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_mod (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_gcd (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_land (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_lor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_xor (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_shiftLeft (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
        · exact close _ (by simpa +decide [natOpResult] using hres.symm)
            (natOpV2_shiftRight (mp.nat_ops φ) (mp.nat_heads φ) mp.acvalValidP
              (mp.div_mod φ) hfc ρ n₁ n₂)
  · split at h
    · -- the WF-pin safety net: it throws
      cases hwa : Setlec.whnf μ env fuel d a with
      | error err => rw [hwa] at h; exact nomatch h
      | ok a0 =>
      rw [hwa] at h
      dsimp only at h
      cases hwb : Setlec.whnf μ env fuel d b with
      | error err => rw [hwb] at h; exact nomatch h
      | ok b0 =>
      rw [hwb] at h
      dsimp only at h
      cases hra : Setlec.rawNatLit? a0 with
      | none => rw [hra] at h; simp [pure, Except.pure] at h
      | some n₁ =>
      cases hrb : Setlec.rawNatLit? b0 with
      | none => rw [hra, hrb] at h; simp [pure, Except.pure] at h
      | some n₂ =>
        rw [hra, hrb] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [pure, Except.pure] at h

/-! ## The two rows, discharged -/

/-- **Literal acceleration preserves the interpretation.**  The
statement `NatOpSemP` isolated at the seal-II wall, now a theorem. -/
theorem reduceNatSemP (mp : EnvS2PM V μ env) {fuel : Nat}
    (ihw : WhnfClaims2P μ mp.base2 φ fuel)
    {d : Nat} {Δa : List AVExpr} {e e₂ : Expr} {ea ea₂ : AVExpr}
    (h : reduceNatP μ env fuel d e = .ok (some e₂))
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkP mp.base2 φ d Δa e)
    (hea : denoteP mp.base2.acval env φ d e = some ea)
    (hea₂ : denoteP mp.base2.acval env φ d e₂ = some ea₂)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea)
    (ρ : Nat → V) (hρ : Sat2 V Δa ρ) :
    interp2 V ρ ea = interp2 V ρ ea₂ := by
  match e, h, hws, hb, hLb, hC, hea, hok with
  | .app (.const c []) a, h, hws, hb, hLb, hC, hea, hok =>
    exact reduceNatSemP_unary mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ
  | .app (.app (.const c []) a) b, h, hws, hb, hLb, hC, hea, hok =>
    exact reduceNatSemP_binary mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ
  | .bvar _, h, _, _, _, _, _, _ | .fvar _ _ _, h, _, _, _, _, _, _
  | .sort _, h, _, _, _, _, _, _ | .lam _ _ _ _, h, _, _, _, _, _, _
  | .forallE _ _ _ _, h, _, _, _, _, _, _
  | .letE _ _ _ _, h, _, _, _, _, _, _
  | .lit _, h, _, _, _, _, _, _ | .proj _ _ _, h, _, _, _, _, _, _
  | .const _ _, h, _, _, _, _, _, _ =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _, h, _, _, _, _, _, _
  | .app (.fvar _ _ _) _, h, _, _, _, _, _, _
  | .app (.sort _) _, h, _, _, _, _, _, _
  | .app (.lam _ _ _ _) _, h, _, _, _, _, _, _
  | .app (.forallE _ _ _ _) _, h, _, _, _, _, _, _
  | .app (.letE _ _ _ _) _, h, _, _, _, _, _, _
  | .app (.lit _) _, h, _, _, _, _, _, _
  | .app (.proj _ _ _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _, h, _, _, _, _, _, _ =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _, h, _, _, _, _, _, _
  | .app (.app (.fvar _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.sort _) _) _, h, _, _, _, _, _, _
  | .app (.app (.app _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.lam _ _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.forallE _ _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.letE _ _ _ _) _) _, h, _, _, _, _, _, _
  | .app (.app (.lit _) _) _, h, _, _, _, _, _, _
  | .app (.app (.proj _ _ _) _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _, h, _, _, _, _, _, _ =>
    simp [reduceNatP, Setlec.reduceNat, pure, Except.pure] at h

/-- **`ReduceNatStepP`, proved.**  The reduct's reading, grading and
frame conditions are `Step2/NatP.lean`'s premise-free leaf analysis;
the `interp2` equality is `reduceNatSemP`. -/
theorem reduceNatStepP_of (mp : EnvS2PM V μ env) {fuel : Nat}
    (ihw : WhnfClaims2P μ mp.base2 φ fuel) :
    ReduceNatStepP μ mp.base2 φ fuel := by
  intro d e e₂ Δa h hws hb hLb ea hC hea hok
  have hleaf := reduceNat_natLeafP (natOpGuardLawP_of mp) h
  obtain ⟨ea₂, hea₂⟩ :=
    denoteP_of_natLeafP (acval := mp.base2.acval) hleaf d
  obtain ⟨hws₂, hb₂, hLb₂⟩ := frame_of_natLeafP (d := d) hleaf
  exact ⟨ea₂, hea₂,
    fun ρ _ => annotOkP_of_natLeafP mp.base2 (mp.nat_heads φ)
      mp.acvalValidP hleaf hea₂ ρ,
    fun ρ hρ => reduceNatSemP mp ihw h hws hb hLb hC hea hea₂ hok ρ hρ,
    hws₂, hb₂, hLb₂, ctxOkP_of_natLeafP hleaf hC⟩

/-- **`ReduceNatStepPQ`, proved** — the defeq quarter's row differs
from the whnf quarter's only in where the subject's annotation is
bound. -/
theorem reduceNatStepPQ_of (mp : EnvS2PM V μ env) {fuel : Nat}
    (ihw : WhnfClaims2P μ mp.base2 φ fuel) :
    ReduceNatStepPQ μ mp.base2 φ fuel := by
  intro d e e₂ Δa ea h hws hb hLb hC hea hok
  exact reduceNatStepP_of mp ihw h hws hb hLb hC hea hok

end Setlec.SetR.Interp2
