import Setlec.SetR.Install.DeclIndS

/-!
# The pinned basis blocks, [set] lane (task #148, T5)

`DeclBasisS`, the fifth of `declStepS`'s six cases.

`BasisInstallR` is already a *relation* — a chain of fresh conses of
the pinned declarations — so, unlike the TT lane, no fold inversion is
needed.  The whole case is one `EnvS.cons` per pinned constant.

## Where the [set] lane is cheaper than the TT lane

`TTVerify/DeclBasis.lean` proves each constant's front door as a
`HasType [] (val φ) t` derivation.  **`HasType.sound` turns any such
derivation into the membership `interp ρ (val φ) ∈ˢ interp ρ t`**
(`Setlec/TT/Semantics/Soundness.lean`), which is exactly what
`EnvS.cons`'s `htype` wants — so the per-constant type computations are
the *same* work in both lanes, and the [set] lane pays only the extra
`AnnotOkV` conjunct, which is a leaf for every pinned valuation (they
are all `.const` applications).

The lanes are **not** coupled: `Setlec/SetR/*` does not import
`Setlec/TTVerify/*` and must not (the two soundness routes are
independent by design, memory `verification-architecture`).  What is
shared is `Setlec/TT/*` — the judgment and its soundness — which both
lanes already sit on.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reserved case, factored

Twenty of the twenty-two pinned constants have **reserved** names, and
for those the eta and unit-like head obligations are vacuous by
computation on that list.  The other two are the pinned pair's
projection functions, whose names are `Name.num` nodes and therefore
never reserved (`projFnName_ne_reserved`). -/

/-- A reserved-named install completes no eta family. -/
theorem basisEtaVacuousS {env : Env} (m : EnvS V env)
    {ci : ConstantInfo} {val : (Name → Nat) → VExpr}
    (hres : reservedBasisNames.contains ci.name = true) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
      (T = ci.name ∨ caps.etaCtor = ci.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
      EtaLawV V ⟨ci :: env.consts⟩ (cvalWith m.cval ci.name val)
        T cvT caps := by
  intro T cvT caps hf hcape hresT hfam hpart
  rcases hpart with hT | hC | ⟨j, hj, hP⟩
  · rw [← hT] at hres; rw [hres] at hresT; exact nomatch hresT
  · have hf1 := hfam.1
    rw [hC, hres] at hf1
    exact nomatch hf1
  · exact absurd hP (projFnName_ne_reserved hres)

/-- …and owes no unit-like law. -/
theorem basisUnitVacuousS {env : Env} (m : EnvS V env)
    {ci : ConstantInfo} {val : (Name → Nat) → VExpr}
    (hres : reservedBasisNames.contains ci.name = true) :
    ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      UnitLawV V ⟨ci :: env.consts⟩ (cvalWith m.cval ci.name val)
        ci.name cv caps := by
  intro cv caps heq hunit hnres
  rw [hres] at hnres; exact nomatch hnres

/-- A stored reserved constant is valued by its direct pin. -/
theorem cvalS_pinned {env : Env} (m : EnvS V env) {n : Name}
    (hres : reservedBasisNames.contains n = true)
    (hst : (env.find? n).isSome = true) (ψ : Name → Nat) {t : VExpr}
    (hpin : pinnedDirectT n ψ = some t) : m.cval n ψ = t := by
  cases hf : env.find? n with
  | none => rw [hf] at hst; exact nomatch hst
  | some ci => exact (m.basis_pinned n ci hf hres).2 t ψ hpin

/-! ## The per-constant install -/

set_option maxHeartbeats 1600000 in
/-- **One pinned basis constant, installed.**  Every obligation that is
not about *this* constant is discharged here. -/
theorem extendBasisS {env : Env} (m : EnvS V env) {ci : ConstantInfo}
    {val : (Name → Nat) → VExpr}
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
      (T = ci.name ∨ caps.etaCtor = ci.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
      EtaLawV V ⟨ci :: env.consts⟩ (cvalWith m.cval ci.name val)
        T cvT caps)
    (hheadUnit : ∀ cv caps, ci = .indInfo cv caps →
      caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      UnitLawV V ⟨ci :: env.consts⟩ (cvalWith m.cval ci.name val)
        ci.name cv caps)
    (hpin : ConstantInfo.isBasis ci = true → ci = pinnedInfo ci.name)
    (hdirect : ∀ (ψ : Name → Nat) (t : VExpr),
      pinnedDirectT ci.name ψ = some t → val ψ = t)
    (hfresh : env.find? ci.name = none)
    (hwf : EnvWF ⟨ci :: env.consts⟩)
    (hclosed : ∀ ψ : Name → Nat, VExpr.Closed (val ψ))
    (hparams : ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      val φ₁ = val φ₂)
    (hannot : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOkV V ρ (val ψ))
    (htype : ∀ φ : Name → Nat, ∃ t,
      denoteClosed (cvalWith m.cval ci.name val) ⟨ci :: env.consts⟩ φ
        ci.toConstantVal.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (val φ) ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t)
    (hnodefn : ∀ cv v h, ci ≠ .defnInfo cv v h)
    (hnothm : ∀ cv v, ci ≠ .thmInfo cv v)
    -- **not** `ci ≠ .axiomInfo cv`: `Quot.sound` is a stored axiom
    (hnoax : ∀ cv, ci = .axiomInfo cv → ci.name ∈ reduceOpNames → False)
    (hempty : ci.name = emptyName →
      ∀ ψ : Name → Nat, ∃ u, val ψ = emptyT u)
    (hheadCtors : ∀ cv mI rP rules, ci = .recInfo cv mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hheadRec : ∀ cv mI rP rules, ci = .recInfo cv mI rP rules →
      ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      ∀ φ : Name → Nat,
        RecRuleLawV V ⟨ci :: env.consts⟩
          (cvalWith m.cval ci.name val) φ ci.name cv mI rP rl)
    (hheadProj : ∀ entry, ci = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hheadProjPair : ∀ i entry, ci = .projInfo entry →
      ci.name = projFnName psigmaName i → entry.native = true)
    (hheadEq : ci.name = eqName →
      EqLawV V ⟨ci :: env.consts⟩ (cvalWith m.cval ci.name val)) :
    ∃ m' : EnvS V ⟨ci :: env.consts⟩,
      m'.cval = cvalWith m.cval ci.name val := by
  have hi : Installs env m.cval (cvalWith m.cval ci.name val) ci :=
    Installs.of_fresh hfresh (fun n hn => (cvalWith_ne hn).symm)
  have hself : cvalWith m.cval ci.name val ci.name = val :=
    cvalWith_self
  refine ⟨EnvS.cons m hi hwf ?_ ?_ ?_ ?_
    (fun cv v h heq => absurd heq (hnodefn cv v h))
    (fun cv v heq => absurd heq (hnothm cv v))
    (fun hn ψ => by rw [← hn, hself]; exact hempty hn ψ)
    hheadCtors
    (fun cv mI rP rules heq rl hrl hfire =>
      ⟨(hheadRec cv mI rP rules heq rl hrl hfire (fun _ => 0)).1,
       fun φ us hus =>
         (hheadRec cv mI rP rules heq rl hrl hfire φ).2 us hus⟩)
    hheadEta hheadUnit hheadProj hheadProjPair hheadEq
    (fun _ => ⟨hpin, fun ψ t hp => by rw [hself]; exact hdirect ψ t hp⟩)
    (fun cv v h heq => absurd heq (hnodefn cv v h))
    (fun cv v h heq => absurd heq (hnodefn cv v h))
    (fun cv heq hmem => absurd (hnoax cv heq hmem) (fun h => h)),
    rfl⟩
  · intro ψ; rw [hself]; exact hclosed ψ
  · intro φ₁ φ₂ hp; rw [hself]; exact hparams φ₁ φ₂ hp
  · intro ψ ρ; rw [hself]; exact hannot ψ ρ
  · intro φ
    obtain ⟨t, ht, hfacts⟩ := htype φ
    exact ⟨t, ht, by rw [hself]; exact hfacts⟩

/-! ## `Empty`

The pilot block: two constants, and `Empty.rec`'s rule list is `[]`, so
the iota obligation does not exist.  What it validates is the driver,
the shape of a `htype` computation, and — the [set] lane's only extra
over the TT lane — the shape of an `AnnotOkV` computation. -/

/-- `Empty`, installed. -/
theorem extendEmptyS {env : Env} (m : EnvS V env)
    (hfresh : env.find? emptyName = none)
    (hwf : EnvWF ⟨emptyA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨emptyA :: env.consts⟩,
      m'.cval = cvalWith m.cval emptyA.name (fun _ => emptyT 1) := by
  refine extendBasisS m (val := fun _ => emptyT 1)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide) ?_ hfresh hwf (fun _ => trivial)
    (fun _ _ _ => rfl) (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ ψ => ⟨1, rfl⟩)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro ψ t hp
    simp only [pinnedDirectT, emptyA, ConstantInfo.name] at hp ⊢
    exact (Option.some.inj hp).symm ▸ rfl
  · intro φ
    refine ⟨.sort 1, ?_, fun ρ => ?_⟩
    · rw [denoteClosed,
        show (emptyA.toConstantVal.type) = .sort (.succ .zero) from rfl,
        denote_sort]
      rfl
    · exact ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        trivial⟩

set_option maxHeartbeats 1600000 in
/-- `Empty.rec`, installed.  Its rule list is empty, so both recursor
obligations are vacuous and the whole content is the type computation
— plus, in this lane, its truthfulness, which the empty domain makes
vacuous at the one application node. -/
theorem extendEmptyRecS {env : Env} (m : EnvS V env)
    (hE : env.find? emptyName = some emptyA)
    (hfresh : env.find? (emptyName.str "rec") = none)
    (hwf : EnvWF ⟨emptyRecA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨emptyRecA :: env.consts⟩,
      m'.cval = cvalWith m.cval emptyRecA.name
        (fun ψ => VExpr.const .emptyRec [1, ψ uN]) := by
  have hpd : ∀ φ : Name → Nat,
      pinnedDirectT emptyName φ = some (VExpr.const .empty [1]) := by
    intro φ
    simp only [pinnedDirectT]
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_true]
  have hEv : ∀ φ : Name → Nat, m.cval emptyName φ = emptyT 1 := fun φ =>
    cvalS_pinned m (by decide) (by rw [hE]; rfl) φ (hpd φ)
  have hEc : ∀ d : Nat, ∀ φ : Name → Nat,
      denote (cvalWith m.cval emptyRecA.name
        (fun ψ => VExpr.const .emptyRec [1, ψ uN]))
        ⟨emptyRecA :: env.consts⟩ φ d (.const emptyName [])
        = some (emptyT 1) := by
    intro d φ
    rw [denote_const, Env.find?_cons,
      if_neg (show ¬(ConstantInfo.name emptyRecA = emptyName)
        by decide)]
    rw [hE]
    simp only [show emptyA.toConstantVal.levelParams = [] from rfl,
      List.length_nil, if_true]
    rw [cvalWith_ne (show emptyName ≠ emptyRecA.name by decide), hEv]
  refine extendBasisS m (val := fun ψ => .const .emptyRec [1, ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide) ?_ hfresh hwf (fun _ => trivial) ?_
    (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => by
      injection heq with _ _ _ h4
      subst h4
      intro r hr; exact nomatch hr)
    (fun _ _ _ _ heq => by
      injection heq with _ _ _ h4
      subst h4
      intro rl hrl; exact nomatch hrl)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro ψ t hp
    have hpr : pinnedDirectT (emptyName.str "rec") ψ
        = some (VExpr.const .emptyRec [1, ψ uN]) := by
      simp only [pinnedDirectT]
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_neg (by decide), if_neg (by decide),
        if_neg (by decide), if_true]
    rw [show ConstantInfo.name emptyRecA = emptyName.str "rec" from rfl,
      hpr] at hp
    exact (Option.some.inj hp)
  · intro φ₁ φ₂ hp
    have h1 : φ₁ uN = φ₂ uN := hp uN (by
      show uN ∈ [uN]
      exact List.mem_cons_self)
    rw [h1]
  · intro φ
    refine ⟨.pi (.pi (emptyT 1) (.sort (φ uN)))
      (.pi (emptyT 1) (.app (.bvar 1) (.bvar 0))), ?_, fun ρ => ?_⟩
    · rw [denoteClosed,
        show emptyRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.const emptyName []) (.sort (.param uN))
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "t")
                (.const emptyName []) (.app (.bvar 1) (.bvar 0))
                { bi := .default })
              { bi := .default } from rfl,
        denote_forallE, denote_forallE]
      rw [hEc 0 φ]
      simp [Expr.instantiate1, denote_sort, Level.eval, denote_forallE,
        hEc 1 φ, denote_app, denote_fvar]
    · refine ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ), ?_⟩
      -- truthfulness: the one application node sits under a binder
      -- ranging over the *empty* set
      refine ⟨⟨trivial, fun _ _ => trivial⟩, fun x _ => ?_⟩
      refine ⟨trivial, fun y hy => ?_⟩
      exact absurd hy (SetTheory.not_mem_empty y)

/-- **The `Empty` block, installed.**  The chain is two links and the
driver walks it. -/
theorem declBasisS_emptyK {env env₂ : Env} (m : EnvS V env)
    (h : BasisInstallR env BasisKind.emptyK.declsA env₂) :
    Nonempty (EnvS V env₂) := by
  rw [show BasisKind.emptyK.declsA = [emptyA, emptyRecA] from rfl] at h
  obtain ⟨h1, h2, hnil⟩ := h
  subst hnil
  have hwf1 : EnvWF ⟨emptyA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ :=
    extendEmptyS m (Option.isNone_iff_eq_none.mp h1) hwf1
  have hE : (⟨emptyA :: env.consts⟩ : Env).find? emptyName
      = some emptyA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨emptyRecA :: emptyA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq),
      (fun _ _ _ _ heq => by
        injection heq with _ _ _ h4
        subst h4
        intro r hr; exact nomatch hr),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ emptyRecA.toConstantVal.type = true
    simp only [show emptyRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.sort (.param uN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "t") (.const emptyName [])
              (.app (.bvar 1) (.bvar 0)) { bi := .default })
            { bi := .default } from rfl,
      Expr.constsResolve, Bool.and_eq_true, Option.isSome_iff_exists]
    have hf : (⟨emptyRecA :: emptyA :: env.consts⟩ : Env).find?
        emptyName = some emptyA := by
      rw [Env.find?_cons,
        if_neg (show ¬(ConstantInfo.name emptyRecA = emptyName) by
          decide)]
      exact hE
    rw [hf]
    simp
  obtain ⟨m2, -⟩ := extendEmptyRecS m1 (by rw [hm1] at *; exact hE)
    (Option.isNone_iff_eq_none.mp h2) hwf2
  exact ⟨m2⟩

end Setlec.SetR
