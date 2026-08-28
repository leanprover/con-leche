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

/-- A pinned constant already stored denotes to its pin: if the name a
type mentions is a *reserved* one already stored, the constant just
installed by this block resolves in the extended environment, its
level list has the declared length, and its valuation is its pin. -/
theorem denote_const_pinS {env : Env} (m : EnvS V env)
    {ci₀ ci : ConstantInfo} {n : Name} {us : List Level} {t : VExpr}
    {φ : Name → Nat} {val : (Name → Nat) → VExpr}
    (hne : ci₀.name ≠ n)
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hres : reservedBasisNames.contains n = true)
    (hpin : pinnedDirectT n
      (Level.substFn φ ci.toConstantVal.levelParams us) = some t)
    (d : Nat) :
    denote (cvalWith m.cval ci₀.name val) ⟨ci₀ :: env.consts⟩ φ d
      (.const n us) = some t := by
  rw [denote_const, Env.find?_cons, if_neg hne, hf]
  simp only [if_pos hlen]
  rw [cvalWith_ne (Ne.symm hne)]
  exact congrArg some (cvalS_pinned m hres (by rw [hf]; rfl) _ hpin)

/-! ## Every pinned type is truthful

`EnvS.cons`'s `htype` asks for `AnnotOkV ρ t` beside the membership,
and for a pinned constant `t` is `BConst.type c us`.  That is **one
lemma for the whole basis**. -/

set_option maxHeartbeats 3200000 in
theorem AnnotOkV_bconst_type (c : BConst) (us : List Nat)
    (ρ : Nat → V) : AnnotOkV V ρ (BConst.type c us) := by
  cases c <;>
    simp only [BConst.type, arrow, AnnotOkV_pi, AnnotOkV_sort,
      AnnotOkV_const, AnnotOkV_app, AnnotOkV_bvar, AnnotOkV_eqE,
      interp_pi, interp_const, interp_sort, interp_bvar,
      interp_app, cons, natT, natZeroT, punitT, punitUnitT, emptyT,
      psigmaT, quotT, relT, quotMkT, VExpr.mkAppN, VExpr.lift,
      VExpr.liftN, true_and, and_true] <;>
    (repeat' first
      | trivial
      | exact ⟨_, _, ‹_›, ‹_›⟩
      | exact ⟨_, _, ‹_›, natzero_mem⟩
      | exact ⟨_, _, ‹_›, pt_mem_unitSet⟩
      | apply And.intro
      | intro _)
  -- **the twenty-four residual goals, longhand.**  Every one is
  -- `∃ A B, F ∈ˢ piC A B ∧ a ∈ˢ A`; `F` is a bound motive, a layer
  -- constant, or a partial application of one, and `bval_mem_type`
  -- composed with `app_mem_piC` once per argument already consumed
  -- supplies it.  Written out rather than closed by a generic tactic:
  -- two attempts at one failed to fire (the `∃ A B` metavariables are
  -- not solved through `interp (BConst.type …)`'s unfolding).
  case natRec.right.right.left.right.left.right.right =>
    exact ⟨_, _, bval_mem_type V .natSucc [] ρ,
      ‹_›⟩
  case natRec.right.right.left.right.right =>
    exact ⟨_, _, ‹_›,
      app_mem_piC (bval_mem_type V .natSucc [] ρ) ‹_›⟩
  case psigmaMk.right.right.left =>
    exact ⟨_, _, bval_mem_type V .psigma [lv us 0, lv us 1] ρ,
      ‹_›⟩
  case psigmaMk.right.right.right =>
    exact ⟨_, _,
      app_mem_piC (bval_mem_type V .psigma [lv us 0, lv us 1] ρ) ‹_›,
      ‹_›⟩
  case quotMk.right.left =>
    exact ⟨_, _, bval_mem_type V .quot [lv us 0] ρ,
      ‹_›⟩
  case quotMk.right.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quot [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotLift.right.right.left.left.right =>
    -- the head is the *relation* applied to one side; naming the
    -- binders is what an anonymous `assumption` cannot get right
    rename_i A hA r hr B hB f hf a ha b hb
    exact ⟨_, _, app_mem_piC hr ha, hb⟩
  case quotLift.right.right.right.left.left =>
    exact ⟨_, _, bval_mem_type V .quot [lv us 0] ρ,
      ‹_›⟩
  case quotLift.right.right.right.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quot [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotInd.right.left.left.left =>
    exact ⟨_, _, bval_mem_type V .quot [lv us 0] ρ,
      ‹_›⟩
  case quotInd.right.left.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quot [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotInd.right.right.left.left.left.left =>
    exact ⟨_, _, bval_mem_type V .quotMk [lv us 0] ρ,
      ‹_›⟩
  case quotInd.right.right.left.left.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotInd.right.right.left.left.right =>
    exact ⟨_, _, app_mem_piC
      (app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›) ‹_›,
      ‹_›⟩
  case quotInd.right.right.left.right =>
    exact ⟨_, _, ‹_›,
      app_mem_piC (app_mem_piC
      (app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›) ‹_›) ‹_›⟩
  case quotInd.right.right.right.left.left =>
    exact ⟨_, _, bval_mem_type V .quot [lv us 0] ρ,
      ‹_›⟩
  case quotInd.right.right.right.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quot [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotSound.right.left.right =>
    rename_i A hA r hr a ha b hb
    exact ⟨_, _, app_mem_piC hr ha, hb⟩
  case quotSound.right.right.left.left.left =>
    exact ⟨_, _, bval_mem_type V .quotMk [lv us 0] ρ,
      ‹_›⟩
  case quotSound.right.right.left.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotSound.right.right.left.right =>
    exact ⟨_, _, app_mem_piC
      (app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›) ‹_›,
      ‹_›⟩
  case quotSound.right.right.right.left.left =>
    exact ⟨_, _, bval_mem_type V .quotMk [lv us 0] ρ,
      ‹_›⟩
  case quotSound.right.right.right.left.right =>
    exact ⟨_, _, app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›,
      ‹_›⟩
  case quotSound.right.right.right.right =>
    exact ⟨_, _, app_mem_piC
      (app_mem_piC (bval_mem_type V .quotMk [lv us 0] ρ) ‹_›) ‹_›,
      ‹_›⟩

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

/-! ## `PUnit`

The first block with a rule, and the smallest one that exercises the
whole of `hheadRec`. -/

/-- `PUnit`, installed. -/
theorem extendPUnitS {env : Env} (m : EnvS V env)
    (hfresh : env.find? punitName = none)
    (hwf : EnvWF ⟨punitA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨punitA :: env.consts⟩,
      m'.cval = cvalWith m.cval punitA.name
        (fun ψ => punitT (ψ uN)) := by
  refine extendBasisS m (val := fun ψ => punitT (ψ uN))
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitA = punitName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨.sort (φ uN), ?_, fun ρ => ?_⟩
    · rw [denoteClosed, show punitA.toConstantVal.type
        = Expr.sort (.param uN) from rfl, denote_sort]
      rfl
    · exact ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        trivial⟩

/-- `PUnit.unit`, installed. -/
theorem extendPUnitUnitS {env : Env} (m : EnvS V env)
    (hP : env.find? punitName = some punitA)
    (hfresh : env.find? punitUnitName = none)
    (hwf : EnvWF ⟨punitUnitA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨punitUnitA :: env.consts⟩,
      m'.cval = cvalWith m.cval punitUnitA.name
        (fun ψ => punitUnitT (ψ uN)) := by
  refine extendBasisS m (val := fun ψ => punitUnitT (ψ uN))
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitUnitA = punitUnitName
        from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨punitT (φ uN), ?_, fun ρ => ?_⟩
    · rw [denoteClosed, show punitUnitA.toConstantVal.type
        = Expr.const punitName [.param uN] from rfl]
      refine denote_const_pinS m (by decide) hP rfl (by decide) ?_ 0
      simp +decide [pinnedDirectT]
      rfl
    · exact ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        trivial⟩

set_option maxHeartbeats 12800000 in
/-- `PUnit.rec`, installed — the block's whole content, and the lane's
first recursor.

**The denotation is derived natively at depth 0.**  The TT lane's
`hheadRec` speaks `denote … φ d` at an arbitrary depth and its tactic
does not transpose: `RecRuleLawV` speaks `denoteClosed`, i.e. depth
`0`, so the λ-tower is walked by hand — `denote_lam`/`denote_forallE`
expose a `match` whose scrutinee must be rewritten before it reduces,
and at depth 0 each scrutinee is one of the two pinned constants. -/
theorem extendPUnitRecS {env : Env} (m : EnvS V env)
    (hP : env.find? punitName = some punitA)
    (hU : env.find? punitUnitName = some punitUnitA)
    (hfresh : env.find? (punitName.str "rec") = none)
    (hwf : EnvWF ⟨punitRecA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨punitRecA :: env.consts⟩,
      m'.cval = cvalWith m.cval punitRecA.name
        (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]) := by
  have hPc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalWith m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitName [l])
        = some (punitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pinS m (by decide) hP rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  have hUc : ∀ (d : Nat) (φ : Name → Nat) (l : Level),
      denote (cvalWith m.cval punitRecA.name
          (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N]))
        ⟨punitRecA :: env.consts⟩ φ d (.const punitUnitName [l])
        = some (punitUnitT (l.eval φ)) := by
    intro d φ l
    refine denote_const_pinS m (by decide) hU rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  refine extendBasisS m
    (val := fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name punitRecA = punitName.str "rec"
        from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · -- the valuation reads only `u` and `u_1`
    intro φ₁ φ₂ hp
    rw [hp uN (by
        show uN ∈ [u1N, uN]
        exact List.mem_cons_of_mem _ List.mem_cons_self),
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self)]
  · -- the pinned type, denoted; its truthfulness is lever 2
    intro φ
    refine ⟨_, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        AnnotOkV_bconst_type (V := V) _ _ ρ⟩⟩
    rw [denoteClosed,
      show punitRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t")
              (.const punitName [.param uN]) (.sort (.param u1N))
              { bi := .default })
            (Expr.forallE (Name.anonymous.str "unit")
              (.app (.bvar 0) (.const punitUnitName [.param uN]))
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN])
                (.app (.bvar 2) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Expr.instantiate1, Level.eval, hPc, hUc, BConst.type, arrow,
      punitT, punitUnitT]
    exact ⟨⟨rfl, rfl⟩, rfl⟩
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨punitUnitA.toConstantVal, 0, 0, hU⟩
    · exact nomatch hr'
  · -- the iota rule
    intro cv mI rP rules heq
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    intro rl hrl hfire φ
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro us hus
      obtain ⟨w1, w2, rfl⟩ : ∃ a b, us = [a, b] := by
        match us, hus with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      -- **expanded** level names: the abbreviations do not match
      have hsu : Level.subst [Name.anonymous.str "u_1",
          Name.anonymous.str "u"] [w1, w2]
          (.param (Name.anonymous.str "u")) = w2 := by
        simp [Level.subst, Level.subst.go]
      have hsu1 : Level.subst [Name.anonymous.str "u_1",
          Name.anonymous.str "u"] [w1, w2]
          (.param (Name.anonymous.str "u_1")) = w1 := by
        simp [Level.subst, Level.subst.go]
      -- and the same for the constants' names
      have hPc' := fun (d : Nat) (φ' : Name → Nat) (l : Level) =>
        hPc d φ' l
      have hUc' := fun (d : Nat) (φ' : Name → Nat) (l : Level) =>
        hUc d φ' l
      simp only [punitName, punitUnitName] at hPc' hUc'
      refine ⟨.lam (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
        (.lam (.app (.bvar 0) (punitUnitT (w2.eval φ))) (.bvar 0)),
        ?_, ?_⟩
      · -- walked by hand at depth 0
        rw [denoteClosed]
        simp only [Expr.instantiateLevelParams, List.map_cons,
          List.map_nil, hsu, hsu1]
        rw [denote_lam, denote_forallE, hPc' 0 φ w2]
        simp only [Expr.instantiate1_sort, denote_sort]
        simp only [Expr.instantiate1_lam, Expr.instantiate1_app,
          Expr.instantiate1_bvar, Expr.instantiate1_const,
          Nat.reduceAdd, reduceIte]
        rw [denote_lam, denote_app, denote_fvar, hUc' 1 φ w2]
        simp [Expr.instantiate1_bvar, denote_fvar]
      · intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys
          husj hlev hplain hnested hidx hTV hTVj hR hC
        have hU'' := hU
        simp only [punitUnitName, punitName] at hU''
        rw [Env.find?_cons, if_neg (by decide), hU''] at hfj
        obtain ⟨rfl, rfl, rfl⟩ :
            cvj = punitUnitA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
          injection Option.some.inj hfj with h1 h2 h3
          exact ⟨h1.symm, h2.symm, h3.symm⟩
        obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
        obtain ⟨M, mm, rfl⟩ : ∃ a b, xs = [a, b] := by
          match xs, hxs with
          | [a, b], _ => exact ⟨a, b, rfl⟩
        obtain ⟨l0, rfl⟩ : ∃ a, usj = [a] := by
          match usj, husj with
          | [a], _ => exact ⟨a, rfl⟩
        -- the recursor's own type, denoted at the actual levels
        obtain rfl : TV = .pi (.pi (punitT (w2.eval φ))
            (.sort (w1.eval φ)))
            (.pi (.app (.bvar 0) (punitUnitT (w2.eval φ)))
              (.pi (punitT (w2.eval φ)) (.app (.bvar 2) (.bvar 0))))
            := by
          rw [denoteClosed] at hTV
          simp [denote_forallE, denote_sort, denote_app, denote_fvar,
            Expr.instantiate1, hPc', hUc', punitT,
            punitUnitT, Expr.instantiateLevelParams, hsu, hsu1] at hTV
          exact hTV.symm
        -- the two valuations the law's sides read
        have hrecV : cvalWith m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            punitRecA.name (Level.substFn φ
              [Name.anonymous.str "u_1", Name.anonymous.str "u"]
              [w1, w2])
            = VExpr.const .punitRec [w2.eval φ, w1.eval φ] := by
          rw [cvalWith_self]
          simp [Level.substFn, uN, u1N]
        have hctorV : cvalWith m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ punitUnitA.toConstantVal.levelParams [l0])
            = punitUnitT (w2.eval φ) := by
          rw [cvalWith_ne (by decide), hlev]
          refine cvalS_pinned m (by decide) (by rw [hU'']; rfl) _ ?_
          simp +decide [pinnedDirectT]
          rfl
        cases hR with | cons hM hR =>
        cases hR with | cons hm hR =>
        cases hR with | cons hct hR =>
        simp only [VExpr.inst_app, VExpr.inst_bvar,
          VExpr.liftN_zero, punitT, punitUnitT, VExpr.inst_const,
          reduceIte] at hm hct
        rw [hrecV]
        rw [show (VExpr.mkAppN (cvalWith m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ
              punitUnitA.toConstantVal.levelParams [l0])) [])
          = cvalWith m.cval punitRecA.name
            (fun ψ => VExpr.const .punitRec [ψ uN, ψ u1N])
            ((Name.anonymous.str "PUnit").str "unit")
            (Level.substFn φ
              punitUnitA.toConstantVal.levelParams [l0]) from rfl,
          hctorV]
        simp only [punitT, interp_pi, interp_const,
          interp_sort, bval, interp_app, Nat.lt_irrefl,
          if_false] at hM hm
        refine ⟨?_, ?_⟩
        · -- **the layer's own law**, plus two β-steps
          simp only [List.take, List.drop, List.cons_append,
            List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
            interp_app, interp_const, interp_lam, interp_pi,
            interp_sort, punitT, punitUnitT, bval, lv, interp_bvar,
            cons, List.getD_cons_zero, List.getD_cons_succ]
          rw [punitRecV_app V hM hm pt_mem_unitSet, app_lamC hM,
            app_lamC hm]
        · -- the truthfulness transport: two `AnnotOkV_app` steps, each
          -- fed by the binder membership the fit already supplies
          intro hxsA hysA
          have hMA : AnnotOkV V ρ M := hxsA M (by simp)
          have hmA : AnnotOkV V ρ mm := hxsA mm (by simp)
          have hRA : AnnotOkV V ρ
              (VExpr.lam (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
                (.lam (.app (.bvar 0) (punitUnitT (w2.eval φ)))
                  (.bvar 0))) := by
            refine ⟨⟨trivial, fun _ _ => trivial⟩, fun x hx => ?_⟩
            refine ⟨⟨trivial, trivial, unitSet,
              fun _ => univ (w1.eval φ), ?_, pt_mem_unitSet⟩,
              fun _ _ => trivial⟩
            simpa [punitT, bval] using hx
          have hRm : interp V ρ
              (VExpr.lam (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ)))
                (.lam (.app (.bvar 0) (punitUnitT (w2.eval φ)))
                  (.bvar 0)))
              ∈ˢ piC (interp V ρ
                  (.pi (punitT (w2.eval φ)) (.sort (w1.eval φ))))
                (fun x => piC (interp V (cons V x ρ)
                    (.app (.bvar 0) (punitUnitT (w2.eval φ))))
                  (fun _ => interp V (cons V x ρ)
                    (.app (.bvar 0) (punitUnitT (w2.eval φ))))) := by
            refine lamC_mem (fun x hx => lamC_mem (fun y hy => hy))
          simp only [List.take, List.drop, List.append_nil,
            VExpr.mkAppN_cons, VExpr.mkAppN_nil, AnnotOkV_app]
          refine ⟨⟨hRA, hMA, _, _, hRm, hM⟩, hmA,
            interp V (cons V (interp V ρ M) ρ)
              (.app (.bvar 0) (punitUnitT (w2.eval φ))),
            (fun _ => interp V (cons V (interp V ρ M) ρ)
              (.app (.bvar 0) (punitUnitT (w2.eval φ)))), ?_, ?_⟩
          · exact app_mem_piC hRm hM
          · simpa [interp_app, interp_bvar, cons, punitUnitT, bval]
              using hm
    · exact nomatch hr'

/-! ## `Nat`

Four constants, and the level question does not arise: `Nat.zero` and
`Nat.succ` bind **no** level parameters, so a fired rule's `usj` is
forced to `[]`.  `Nat.rec` is the block's content and the recipe's
second application — two rules this time. -/

/-- `Nat`, installed. -/
theorem extendNatS {env : Env} (m : EnvS V env)
    (hfresh : env.find? natName = none)
    (hwf : EnvWF ⟨natA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨natA :: env.consts⟩,
      m'.cval = cvalWith m.cval natA.name (fun _ => natT) := by
  refine extendBasisS m (val := fun _ => natT)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natA = natName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl)
    (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨.sort 1, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ), trivial⟩⟩
    rw [denoteClosed, show natA.toConstantVal.type
      = Expr.sort (.succ .zero) from rfl, denote_sort]
    rfl

/-- `Nat.zero`, installed. -/
theorem extendNatZeroS {env : Env} (m : EnvS V env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natZeroName = none)
    (hwf : EnvWF ⟨natZeroA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨natZeroA :: env.consts⟩,
      m'.cval = cvalWith m.cval natZeroA.name (fun _ => natZeroT) := by
  refine extendBasisS m (val := fun _ => natZeroT)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natZeroA = natZeroName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl)
    (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨natT, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ), trivial⟩⟩
    rw [denoteClosed, show natZeroA.toConstantVal.type
      = Expr.const natName [] from rfl]
    refine denote_const_pinS m (by decide) hN rfl (by decide) ?_ 0
    simp +decide [pinnedDirectT]
    rfl

/-- `Nat.succ`, installed. -/
theorem extendNatSuccS {env : Env} (m : EnvS V env)
    (hN : env.find? natName = some natA)
    (hfresh : env.find? natSuccName = none)
    (hwf : EnvWF ⟨natSuccA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨natSuccA :: env.consts⟩,
      m'.cval = cvalWith m.cval natSuccA.name
        (fun _ => VExpr.const .natSucc []) := by
  have hNc : ∀ d : Nat, ∀ φ : Name → Nat,
      denote (cvalWith m.cval natSuccA.name
        (fun _ => VExpr.const .natSucc []))
        ⟨natSuccA :: env.consts⟩ φ d (.const natName [])
        = some natT := by
    intro d φ
    refine denote_const_pinS m (by decide) hN rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  refine extendBasisS m (val := fun _ => VExpr.const .natSucc [])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natSuccA = natSuccName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) (fun _ _ _ => rfl)
    (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ
    refine ⟨.pi natT natT, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        ⟨trivial, fun _ _ => trivial⟩⟩⟩
    rw [denoteClosed, show natSuccA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "n") (.const natName [])
          (.const natName []) { bi := .default } from rfl]
    simp [denote_forallE, Expr.instantiate1, hNc]

/-- The `Nat` block's earlier constants, denoted in the environment
`Nat.rec` is going into. -/
theorem denote_natRec_constsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    (∀ d : Nat, denote (cvalWith m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natName []) = some natT) ∧
    (∀ d : Nat, denote (cvalWith m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natZeroName [])
        = some natZeroT) ∧
    (∀ d : Nat, denote (cvalWith m.cval natRecA.name val)
        ⟨natRecA :: env.consts⟩ φ d (.const natSuccName [])
        = some (VExpr.const .natSucc [])) := by
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_⟩
  · refine denote_const_pinS m (by decide) hN rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  · refine denote_const_pinS m (by decide) hZ rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]
    rfl
  · refine denote_const_pinS m (by decide) hS rfl (by decide) ?_ d
    simp +decide [pinnedDirectT]

/-- **`Nat.rec`'s pinned type, denoted at any depth and any level.** -/
theorem denote_natRec_typeS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalWith m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ
      d
        (natRecA.toConstantVal.type.instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.pi (.pi natT (.sort (w.eval φ)))
        (.pi (.app (.bvar 0) natZeroT)
          (.pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar
                1)))))
            (.pi natT (.app (.bvar 3) (.bvar 0)))))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_constsS m (val := val) φ hN
    hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl,
    show natRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "t") (.const natName [])
            (.sort (.param uN)) { bi := .default })
          (Expr.forallE (Name.anonymous.str "zero")
            (.app (.bvar 0) (.const natZeroName []))
            (Expr.forallE (Name.anonymous.str "succ")
              (Expr.forallE (Name.anonymous.str "n") (.const natName [])
                (Expr.forallE (Name.anonymous.str "n_ih")
                  (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (.const natSuccName []) (.bvar 1)))
                  { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "t") (.const natName [])
                (.app (.bvar 3) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
  simp [Expr.instantiateLevelParams, hsu, denote_forallE, denote_sort,
    denote_app, denote_fvar, hNc, hZc, hSc]


/-- `Nat.rec`'s two stored rules. -/
def natRecZeroRule : RecRule :=
  { ctor := natZeroName, nfields := 0, ctorParams := 0, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t") (.const natName [])
        (.sort (.param uN)) { bi := .default })
      (Expr.lam (Name.anonymous.str "zero")
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam (Name.anonymous.str "succ")
          (Expr.forallE (Name.anonymous.str "n") (.const natName [])
            (Expr.forallE (Name.anonymous.str "n_ih") (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { bi := .default })
            { bi := .default })
          (.bvar 1) { bi := .default })
        { bi := .default })
      { bi := .default } }

def natRecSuccRule : RecRule :=
  { ctor := natSuccName, nfields := 1, ctorParams := 0, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "motive")
      (Expr.forallE (Name.anonymous.str "t") (.const natName [])
        (.sort (.param uN)) { bi := .default })
      (Expr.lam (Name.anonymous.str "zero")
        (.app (.bvar 0) (.const natZeroName []))
        (Expr.lam (Name.anonymous.str "succ")
          (Expr.forallE (Name.anonymous.str "n") (.const natName [])
            (Expr.forallE (Name.anonymous.str "n_ih") (.app (.bvar 2)
              (.bvar 0))
              (.app (.bvar 3) (.app (.const natSuccName []) (.bvar 1)))
              { bi := .default })
            { bi := .default })
          (Expr.lam (Name.anonymous.str "n") (.const natName [])
            (.app (.app (.bvar 1) (.bvar 0))
              (.app (.app (.app (.app (.const (natName.str "rec")
                [.param uN]) (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar
                  0)))
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

theorem natRecA_eq :
    natRecA = .recInfo natRecA.toConstantVal 3 3
      [natRecZeroRule, natRecSuccRule] := rfl

/-- The `zero` rule's right-hand side, denoted. -/
theorem denote_natRec_zeroRhsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalWith m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ
      d
        ((RecRule.rhs natRecZeroRule).instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.lam (.pi natT (.sort (w.eval φ)))
        (.lam (.app (.bvar 0) natZeroT)
          (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar
                1)))))
            (.bvar 1)))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_constsS m (val := val) φ hN
    hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl]
  simp only [natRecZeroRule]
  simp [Expr.instantiateLevelParams, hsu, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hNc, hZc, hSc]


/-- **The `succ` rule's right-hand side, denoted** — the first stored
rule in any block whose right-hand side mentions the recursor being
installed.  It resolves to `cval'`, the post-install valuation, which
`hheadRec` has always been stated at. -/
theorem denote_natRec_succRhsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA) :
    denote (cvalWith m.cval natRecA.name val) ⟨natRecA :: env.consts⟩ φ
      d
        ((RecRule.rhs natRecSuccRule).instantiateLevelParams
          natRecA.toConstantVal.levelParams [w])
      = some (.lam (.pi natT (.sort (w.eval φ)))
        (.lam (.app (.bvar 0) natZeroT)
          (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
              (.app (.bvar 3) (.app (VExpr.const .natSucc []) (.bvar
                1)))))
            (.lam natT
              (.app (.app (.bvar 1) (.bvar 0))
                (VExpr.mkAppN (val (Level.substFn φ [uN] [w]))
                  [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))))) := by
  obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_constsS m (val := val) φ hN
    hZ hS
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go]
  have hRc : ∀ e : Nat,
      denote (cvalWith m.cval natRecA.name val) ⟨natRecA :: env.consts⟩
        φ e
        (.const (natName.str "rec") [w])
        = some (val (Level.substFn φ [uN] [w])) := by
    intro e
    rw [denote_const, Env.find?_cons,
      if_pos (show ConstantInfo.name natRecA = natName.str "rec" from
        rfl)]
    simp only [show ([w] : List Level).length
      = natRecA.toConstantVal.levelParams.length from rfl, if_true]
    rw [show cvalWith m.cval natRecA.name val (natName.str "rec") = val
      from
      cvalWith_self (n := natRecA.name)]
    rfl
  rw [show natRecA.toConstantVal.levelParams = [uN] from rfl]
  simp only [natRecSuccRule]
  simp [Expr.instantiateLevelParams, hsu, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hNc, hZc, hSc, hRc,
    VExpr.mkAppN]

set_option maxHeartbeats 12800000 in
/-- **`Nat.rec`, installed.**  Two rules; the `succ` one is recursive
in the constant being installed, which the *self* valuation
(`cvalWith_self`) supplies. -/
theorem extendNatRecS {env : Env} (m : EnvS V env)
    (hN : env.find? natName = some natA)
    (hZ : env.find? natZeroName = some natZeroA)
    (hS : env.find? natSuccName = some natSuccA)
    (hfresh : env.find? (natName.str "rec") = none)
    (hwf : EnvWF ⟨natRecA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨natRecA :: env.consts⟩,
      m'.cval = cvalWith m.cval natRecA.name
        (fun ψ => VExpr.const .natRec [ψ uN]) := by
  refine extendBasisS m (val := fun ψ => VExpr.const .natRec [ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name natRecA = natName.str "rec"
        from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        AnnotOkV_bconst_type (V := V) _ _ ρ⟩⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        natRecA.toConstantVal.levelParams natRecA.toConstantVal.type,
      show natRecA.toConstantVal.levelParams.map Level.param
        = [Level.param uN] from rfl,
      denote_natRec_typeS m (val := fun ψ => VExpr.const .natRec [ψ uN])
        φ 0 (.param uN) hN hZ hS]
    rfl
  · -- both rules' constructors are stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨natZeroA.toConstantVal, 0, 0, hZ⟩
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · exact ⟨natSuccA.toConstantVal, 0, 1, hS⟩
      · exact nomatch hr''
  · -- the two iota rules
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h1'; subst h2'; subst h3'; subst h4'
    intro rl hrl _ φ
    refine ⟨by omega, ?_⟩
    intro us hus
    obtain ⟨w, rfl⟩ : ∃ a, us = [a] := by
      match us, hus with
      | [a], _ => exact ⟨a, rfl⟩
    obtain ⟨hNc, hZc, hSc⟩ := denote_natRec_constsS m
      (val := fun ψ => VExpr.const .natRec [ψ uN]) φ hN hZ hS
    rcases List.mem_cons.mp hrl with rfl | hr'
    · -- `Nat.rec … Nat.zero ↦ zero`
      refine ⟨_, denote_natRec_zeroRhsS m
        (val := fun ψ => VExpr.const .natRec [ψ uN]) φ 0 w hN hZ hS, ?_⟩
      intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys husj
        hlev hplain hnested hidx hTV hTVj hfitR hfitC
      have hZu := hZ
      simp only [natZeroName, natName] at hZu
      rw [Env.find?_cons, if_neg (by decide), hZu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = natZeroA.toConstantVal ∧ cnP = 0 ∧ cnF = 0 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hys
      obtain ⟨xM, xz, xs', rfl⟩ : ∃ a b c, xs = [a, b, c] := by
        match xs, hxs with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain rfl : TV = .pi (.pi natT (.sort (w.eval φ)))
          (.pi (.app (.bvar 0) natZeroT)
            (.pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                (.app (.bvar 3)
                  (.app (VExpr.const .natSucc []) (.bvar 1)))))
              (.pi natT (.app (.bvar 3) (.bvar 0))))) := by
        have hty := denote_natRec_typeS m
          (val := fun ψ => VExpr.const .natRec [ψ uN]) φ 0 w hN hZ hS
        rw [denoteClosed] at hTV
        exact (Option.some.inj (hty.symm.trans hTV)).symm
      have hctorV : cvalWith m.cval natRecA.name
          (fun ψ => VExpr.const .natRec [ψ uN])
          ((Name.anonymous.str "Nat").str "zero")
          (Level.substFn φ natZeroA.toConstantVal.levelParams usj)
          = natZeroT := by
        rw [cvalWith_ne (by decide)]
        refine cvalS_pinned m (by decide) (by rw [hZu]; rfl) _ ?_
        simp +decide [pinnedDirectT]
        rfl
      have hrecV : cvalWith m.cval natRecA.name
          (fun ψ => VExpr.const .natRec [ψ uN]) natRecA.name
          (Level.substFn φ [Name.anonymous.str "u"] [w])
          = VExpr.const .natRec [w.eval φ] := by
        rw [cvalWith_self]
        simp [Level.substFn, uN]
      cases hfitR with | cons t1 hfitR =>
      cases hfitR with | cons t2 hfitR =>
      cases hfitR with | cons t3 hfitR =>
      cases hfitR with | cons t4 hfitR =>
      rw [hrecV]
      rw [show (VExpr.mkAppN (cvalWith m.cval natRecA.name
          (fun ψ => VExpr.const .natRec [ψ uN])
          ((Name.anonymous.str "Nat").str "zero")
          (Level.substFn φ natZeroA.toConstantVal.levelParams usj)) [])
        = cvalWith m.cval natRecA.name
          (fun ψ => VExpr.const .natRec [ψ uN])
          ((Name.anonymous.str "Nat").str "zero")
          (Level.substFn φ natZeroA.toConstantVal.levelParams usj)
        from rfl, hctorV] at t4 ⊢
      -- the three memberships, in the layer's own vocabulary
      have t1' : interp V ρ xM ∈ˢ piC (omega : V)
          (fun _ => univ (w.eval φ)) := by
        simpa [natT, interp_pi, interp_const, interp_sort, bval]
          using t1
      have t2' : interp V ρ xz ∈ˢ app (interp V ρ xM) natzero := by
        simpa [natZeroT, VExpr.inst, VExpr.liftN_zero, interp_app,
          interp_const, bval] using t2
      have t3' : interp V ρ xs' ∈ˢ natStepSpace V (interp V ρ xM) := by
        rw [← interp_natStepT]
        have hstep : VExpr.inst (VExpr.inst
            (VExpr.pi natT (VExpr.pi
              (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
              (VExpr.app (VExpr.bvar 3)
                (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar 1)))))
            xM (0 + 1)) xz 0 = natStepT xM := by
          rw [natStepT, natSuccT]
          simp only [VExpr.inst, Nat.zero_add, Nat.reduceAdd]
          rw [if_neg (show ¬((2:Nat) < 2) by omega),
            if_pos (show (0:Nat) < 2 by omega),
            if_neg (show ¬((3:Nat) < 3) by omega), if_true, if_true]
          rw [VExpr.inst_liftN_absorb xM (Nat.zero_le _)
              (Nat.le_refl 1) xz,
            VExpr.inst_liftN_absorb xM (Nat.zero_le _)
              (show (2:Nat) ≤ 0 + 2 by omega) xz]
          simp [VExpr.inst, natT]
        rw [hstep] at t3
        exact t3
      have t4' : (natzero : V) ∈ˢ (omega : V) := natzero_mem
      refine ⟨?_, ?_⟩
      · simp only [List.take, List.drop, List.cons_append,
          List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
          interp_app, interp_const, interp_lam, interp_pi, interp_sort,
          natT, natZeroT, bval, lv, List.getD_cons_zero, interp_bvar,
          cons]
        have hdom : (piC (omega : V) fun x =>
              piC (app (interp V ρ xM) x)
                fun _ => app (interp V ρ xM) (app (natSuccV V) x))
            = natStepSpace V (interp V ρ xM) := by
          rw [natStepSpace]
          exact piC_congr (fun n hn =>
            piC_congr (fun _ _ => by rw [natSuccV_app (V := V) hn]))
        rw [natRecV_app V t1' t2' t3' t4', natrec_zero]
        rw [app_lamC t1', app_lamC t2', hdom, app_lamC t3']
      · -- truthfulness: three `AnnotOkV_app` steps
        intro hxsA hysA
        have hMA : AnnotOkV V ρ xM := hxsA xM (by simp)
        have hzA : AnnotOkV V ρ xz := hxsA xz (by simp)
        have hsA : AnnotOkV V ρ xs' := hxsA xs' (by simp)
        obtain ⟨hb1, hb2⟩ := AnnotOkV_bconst_type (V := V) .natRec
          [w.eval φ] ρ
        simp only [arrow, lv, List.getD_cons_zero,
          VExpr.lift, VExpr.liftN, AnnotOkV_pi] at hb1 hb2
        have hRA : AnnotOkV V ρ
            (VExpr.lam (.pi natT (.sort (w.eval φ)))
              (.lam (.app (.bvar 0) natZeroT)
                (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (VExpr.const .natSucc []) (.bvar 1)))))
                  (.bvar 1)))) := by
          refine ⟨hb1, fun x hx => ?_⟩
          obtain ⟨h2a, h2b⟩ := hb2 x hx
          refine ⟨h2a, fun y hy => ?_⟩
          obtain ⟨h3a, -⟩ := h2b y hy
          exact ⟨h3a, fun _ _ => trivial⟩
        have hRm : interp V ρ
            (VExpr.lam (.pi natT (.sort (w.eval φ)))
              (.lam (.app (.bvar 0) natZeroT)
                (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (VExpr.const .natSucc []) (.bvar 1)))))
                  (.bvar 1))))
            ∈ˢ piC (interp V ρ (.pi natT (.sort (w.eval φ))))
              (fun x => piC (interp V (cons V x ρ)
                  (.app (.bvar 0) natZeroT))
                (fun y => piC (interp V (cons V y (cons V x ρ))
                    (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                      (.app (.bvar 3)
                        (.app (VExpr.const .natSucc []) (.bvar 1))))))
                  (fun _ => interp V (cons V x ρ)
                    (.app (.bvar 0) natZeroT)))) := by
          exact lamC_mem (fun x hx => lamC_mem (fun y hy =>
            lamC_mem (fun z hz => by
              simpa [interp_bvar, cons] using hy)))
        simp only [List.take, List.drop, List.append_nil,
          VExpr.mkAppN_cons, VExpr.mkAppN_nil, AnnotOkV_app]
        refine ⟨⟨⟨hRA, hMA, _, _, hRm, t1⟩, hzA, _, _,
          app_mem_piC hRm t1, ?_⟩, hsA, _, _,
          app_mem_piC (app_mem_piC hRm t1) ?_, ?_⟩
        · rw [← interp_inst0]; exact t2
        · rw [← interp_inst0]; exact t2
        · have hdom2 : interp V (cons V (interp V ρ xz)
              (cons V (interp V ρ xM) ρ))
              (VExpr.pi natT (VExpr.pi
                (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
                (VExpr.app (VExpr.bvar 3)
                  (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar
                    1)))))
              = natStepSpace V (interp V ρ xM) := by
            simp only [natStepSpace, interp_pi, interp_app, interp_bvar,
              cons, natT, interp_const, bval]
            exact piC_congr (fun n hn => piC_congr (fun _ _ => by
              rw [natSuccV_app (V := V) hn]))
          rw [hdom2]
          exact t3'
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · -- `Nat.rec … (Nat.succ n) ↦ succ n (Nat.rec … n)`
        refine ⟨_, denote_natRec_succRhsS m
          (val := fun ψ => VExpr.const .natRec [ψ uN]) φ 0 w hN hZ hS,
          ?_⟩
        intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys
          husj hlev hplain hnested hidx hTV hTVj hfitR hfitC
        have hSu := hS
        simp only [natSuccName, natName] at hSu
        rw [Env.find?_cons, if_neg (by decide), hSu] at hfj
        obtain ⟨rfl, rfl, rfl⟩ :
            cvj = natSuccA.toConstantVal ∧ cnP = 0 ∧ cnF = 1 := by
          injection Option.some.inj hfj with a1 a2 a3
          exact ⟨a1.symm, a2.symm, a3.symm⟩
        obtain ⟨n, rfl⟩ : ∃ a, ys = [a] := by
          match ys, hys with
          | [a], _ => exact ⟨a, rfl⟩
        obtain ⟨xM, xz, xs', rfl⟩ : ∃ a b c, xs = [a, b, c] := by
          match xs, hxs with
          | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
        obtain rfl : TV = .pi (.pi natT (.sort (w.eval φ)))
            (.pi (.app (.bvar 0) natZeroT)
              (.pi (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (VExpr.const .natSucc []) (.bvar 1)))))
                (.pi natT (.app (.bvar 3) (.bvar 0))))) := by
          have hty := denote_natRec_typeS m
            (val := fun ψ => VExpr.const .natRec [ψ uN]) φ 0 w hN hZ hS
          rw [denoteClosed] at hTV
          exact (Option.some.inj (hty.symm.trans hTV)).symm
        obtain rfl : TVj = .pi natT natT := by
          rw [denoteClosed, show natSuccA.toConstantVal.type
              = Expr.forallE (Name.anonymous.str "n")
                (.const natName []) (.const natName [])
                { bi := .default } from rfl] at hTVj
          simp [denote_forallE, Expr.instantiate1, hNc,
            Expr.instantiateLevelParams] at hTVj
          exact hTVj.symm
        cases hfitC with | cons hn0 hfitC =>
        have hn : interp V ρ n ∈ˢ (omega : V) := by
          simpa [natT, interp_const, bval] using hn0
        have hrecV : cvalWith m.cval natRecA.name
            (fun ψ => VExpr.const .natRec [ψ uN]) natRecA.name
            (Level.substFn φ [Name.anonymous.str "u"] [w])
            = VExpr.const .natRec [w.eval φ] := by
          rw [cvalWith_self]
          simp [Level.substFn, uN]
        have hctorV : cvalWith m.cval natRecA.name
            (fun ψ => VExpr.const .natRec [ψ uN])
            ((Name.anonymous.str "Nat").str "succ")
            (Level.substFn φ natSuccA.toConstantVal.levelParams usj)
            = VExpr.const .natSucc [] := by
          rw [cvalWith_ne (by decide)]
          refine cvalS_pinned m (by decide) (by rw [hSu]; rfl) _ ?_
          simp +decide [pinnedDirectT]
        cases hfitR with | cons t1 hfitR =>
        cases hfitR with | cons t2 hfitR =>
        cases hfitR with | cons t3 hfitR =>
        cases hfitR with | cons t4 hfitR =>
        have t1' : interp V ρ xM ∈ˢ piC (omega : V)
            (fun _ => univ (w.eval φ)) := by
          simpa [natT, interp_pi, interp_const, interp_sort, bval]
            using t1
        have t2' : interp V ρ xz ∈ˢ app (interp V ρ xM) natzero := by
          simpa [natZeroT, VExpr.inst, VExpr.liftN_zero, interp_app,
            interp_const, bval] using t2
        have t3' : interp V ρ xs' ∈ˢ natStepSpace V (interp V ρ xM) :=
          by
          rw [← interp_natStepT]
          have hstep : VExpr.inst (VExpr.inst
              (VExpr.pi natT (VExpr.pi
                (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
                (VExpr.app (VExpr.bvar 3)
                  (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar
                    1)))))
              xM (0 + 1)) xz 0 = natStepT xM := by
            rw [natStepT, natSuccT]
            simp only [VExpr.inst, Nat.zero_add, Nat.reduceAdd]
            rw [if_neg (show ¬((2:Nat) < 2) by omega),
              if_pos (show (0:Nat) < 2 by omega),
              if_neg (show ¬((3:Nat) < 3) by omega), if_true, if_true]
            rw [VExpr.inst_liftN_absorb xM (Nat.zero_le _)
                (Nat.le_refl 1) xz,
              VExpr.inst_liftN_absorb xM (Nat.zero_le _)
                (show (2:Nat) ≤ 0 + 2 by omega) xz]
            simp [VExpr.inst, natT]
          rw [hstep] at t3
          exact t3
        have hdom : (piC (omega : V) fun x =>
              piC (app (interp V ρ xM) x)
                fun _ => app (interp V ρ xM) (app (natSuccV V) x))
            = natStepSpace V (interp V ρ xM) := by
          rw [natStepSpace]
          exact piC_congr (fun n' hn' =>
            piC_congr (fun _ _ => by rw [natSuccV_app (V := V) hn']))
        rw [hrecV, hctorV]
        refine ⟨?_, ?_⟩
        · simp only [List.take, List.drop, List.cons_append,
            List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
            interp_app, interp_const, interp_lam, interp_pi,
              interp_sort,
            natT, natZeroT, bval, lv, List.getD_cons_zero, interp_bvar,
            cons]
          rw [natSuccV_app (V := V) hn,
            natRecV_app V t1' t2' t3' (natsucc_mem hn)]
          rw [natrec_succ _ _ hn]
          rw [app_lamC t1', app_lamC t2', hdom, app_lamC t3',
            app_lamC hn]
          rw [show Level.substFn φ [uN] [w] uN = w.eval φ from by
              simp [Level.substFn, uN],
            natRecV_app V t1' t2' t3' hn]
        · -- truthfulness: four `AnnotOkV_app` steps, and the reduct's
          -- own recursive occurrence is `bval_mem_type` again
          intro hxsA hysA
          have hMA : AnnotOkV V ρ xM := hxsA xM (by simp)
          have hzA : AnnotOkV V ρ xz := hxsA xz (by simp)
          have hsA : AnnotOkV V ρ xs' := hxsA xs' (by simp)
          have hnA : AnnotOkV V ρ n := hysA n (by simp)
          obtain ⟨hb1, hb2⟩ := AnnotOkV_bconst_type (V := V) .natRec
            [w.eval φ] ρ
          simp only [arrow, lv, List.getD_cons_zero,
            VExpr.lift, VExpr.liftN, AnnotOkV_pi] at hb1 hb2
          -- the reduct's own recursive spine, at any assignment
          have hspine : ∀ (ρ' : Nat → V) (x y z n' : V),
              x ∈ˢ piC (omega : V) (fun _ => univ (w.eval φ)) →
              y ∈ˢ app x natzero →
              z ∈ˢ (piC (omega : V) fun k => piC (app x k)
                fun _ => app x (app (natSuccV V) k)) →
              n' ∈ˢ (omega : V) →
              AnnotOkV V (cons V n' (cons V z (cons V y (cons V x ρ'))))
                (VExpr.mkAppN
                  (VExpr.const .natRec [Level.substFn φ [uN] [w] uN])
                  [.bvar 3, .bvar 2, .bvar 1, .bvar 0]) ∧
              interp V (cons V n' (cons V z (cons V y (cons V x ρ'))))
                (VExpr.mkAppN
                  (VExpr.const .natRec [Level.substFn φ [uN] [w] uN])
                  [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
                = natrec y z n' ∧
              app z n' ∈ˢ piC (app x n')
                (fun _ => app x (app (natSuccV V) n')) ∧
              natrec y z n' ∈ˢ app x n' := by
            intro ρ' x y z n' hx hy hz2 hn'
            have hlv : Level.substFn φ [uN] [w] uN = w.eval φ := by
              simp [Level.substFn, uN]
            have hstepEq : (piC (omega : V) fun k => piC (app x k)
                fun _ => app x (app (natSuccV V) k))
                = natStepSpace V x := by
              rw [natStepSpace]
              exact piC_congr (fun k hk => piC_congr (fun _ _ => by
                rw [natSuccV_app (V := V) hk]))
            have hz : z ∈ˢ natStepSpace V x := by
              rw [← hstepEq]; exact hz2
            have hb := bval_mem_type V .natRec [w.eval φ] ρ'
            simp only [lv, List.getD_cons_zero,
              
              bval] at hb
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [VExpr.mkAppN_cons, VExpr.mkAppN_nil,
                AnnotOkV_app, AnnotOkV_const, AnnotOkV_bvar,
                interp_app, interp_const, interp_bvar, cons, hlv,
                true_and]
              exact ⟨⟨⟨⟨_, _, hb, hx⟩, _, _, app_mem_piC hb hx, hy⟩,
                _, _, app_mem_piC (app_mem_piC hb hx) hy, hz2⟩,
                _, _, app_mem_piC (app_mem_piC (app_mem_piC hb hx) hy)
                  hz2, hn'⟩
            · simp only [VExpr.mkAppN_cons, VExpr.mkAppN_nil,
                interp_app, interp_const, interp_bvar, cons, hlv, bval,
                lv, List.getD_cons_zero]
              exact natRecV_app V hx hy hz hn'
            · exact app_mem_piC hz2 hn'
            · exact natRecV_mem_fibre (V := V) hy hz hn'
          have hbody : ∀ x, x ∈ˢ interp V ρ (.pi natT
                (.sort (w.eval φ))) →
              ∀ y, y ∈ˢ interp V (cons V x ρ)
                (.app (.bvar 0) natZeroT) →
              ∀ z, z ∈ˢ interp V (cons V y (cons V x ρ))
                (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                  (.app (.bvar 3)
                    (.app (VExpr.const .natSucc []) (.bvar 1))))) →
              ∀ n', n' ∈ˢ interp V (cons V z (cons V y (cons V x ρ)))
                natT →
              AnnotOkV V (cons V n' (cons V z (cons V y (cons V x ρ))))
                (.app (.app (.bvar 1) (.bvar 0))
                  (VExpr.mkAppN (VExpr.const .natRec
                      [Level.substFn φ [uN] [w] uN])
                    [.bvar 3, .bvar 2, .bvar 1, .bvar 0])) ∧
              interp V (cons V n' (cons V z (cons V y (cons V x ρ))))
                (.app (.app (.bvar 1) (.bvar 0))
                  (VExpr.mkAppN (VExpr.const .natRec
                      [Level.substFn φ [uN] [w] uN])
                    [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))
                ∈ˢ app x (app (natSuccV V) n') := by
            intro x hx y hy z hz n' hn'
            obtain ⟨hsp1, hsp2, hsp3, hsp4⟩ :=
              hspine ρ x y z n' hx hy hz hn'
            constructor
            · simp only [AnnotOkV_app, AnnotOkV_bvar, interp_app,
                interp_bvar, cons]
              exact ⟨⟨trivial, trivial, _, _, hz, hn'⟩, hsp1,
                _, _, hsp3, by rw [hsp2]; exact hsp4⟩
            · simp only [interp_app, interp_bvar, cons]
              rw [hsp2]
              exact app_mem_piC hsp3 hsp4
          have t2'' : interp V ρ xz ∈ˢ interp V (cons V (interp V ρ xM)
            ρ)
              (.app (.bvar 0) natZeroT) := by
            rw [← interp_inst0]; exact t2
          have t3'' : interp V ρ xs' ∈ˢ
              interp V (cons V (interp V ρ xz) (cons V (interp V ρ xM)
                ρ))
                (VExpr.pi natT (VExpr.pi
                (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
                (VExpr.app (VExpr.bvar 3)
                  (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar
                    1))))) := by
            have hdom2 : interp V (cons V (interp V ρ xz)
                (cons V (interp V ρ xM) ρ)) (VExpr.pi natT (VExpr.pi
                (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
                (VExpr.app (VExpr.bvar 3)
                  (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar
                    1)))))
                = natStepSpace V (interp V ρ xM) := by
              simp only [natStepSpace, interp_pi, interp_app,
                interp_bvar, cons, natT, interp_const, bval]
              exact piC_congr (fun k hk => piC_congr (fun _ _ => by
                rw [natSuccV_app (V := V) hk]))
            rw [hdom2]; exact t3'
          have hn'' : interp V ρ n ∈ˢ interp V (cons V (interp V ρ xs')
              (cons V (interp V ρ xz) (cons V (interp V ρ xM) ρ)))
              natT := by
            simpa [natT, interp_const, bval] using hn
          have hRA : AnnotOkV V ρ (VExpr.lam (.pi natT (.sort (w.eval
            φ)))
              (.lam (.app (.bvar 0) natZeroT)
                (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (VExpr.const .natSucc []) (.bvar 1)))))
                  (.lam natT
                    (.app (.app (.bvar 1) (.bvar 0))
                      (VExpr.mkAppN (VExpr.const .natRec
                          [Level.substFn φ [uN] [w] uN])
                        [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))))) := by
            refine ⟨hb1, fun x hx => ?_⟩
            obtain ⟨h2a, h2b⟩ := hb2 x hx
            refine ⟨h2a, fun y hy => ?_⟩
            obtain ⟨h3a, -⟩ := h2b y hy
            refine ⟨h3a, fun z hz => ⟨trivial, fun n' hn' => ?_⟩⟩
            exact (hbody x hx y hy z hz n' hn').1
          have hRm : interp V ρ (VExpr.lam (.pi natT (.sort (w.eval φ)))
              (.lam (.app (.bvar 0) natZeroT)
                (.lam (.pi natT (.pi (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (VExpr.const .natSucc []) (.bvar 1)))))
                  (.lam natT
                    (.app (.app (.bvar 1) (.bvar 0))
                      (VExpr.mkAppN (VExpr.const .natRec
                          [Level.substFn φ [uN] [w] uN])
                        [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))))) ∈ˢ
              piC (interp V ρ (.pi natT (.sort (w.eval φ))))
                (fun x => piC (interp V (cons V x ρ)
                    (.app (.bvar 0) natZeroT))
                  (fun y => piC (interp V (cons V y (cons V x ρ))
                      (VExpr.pi natT (VExpr.pi
                (VExpr.app (VExpr.bvar 2) (VExpr.bvar 0))
                (VExpr.app (VExpr.bvar 3)
                  (VExpr.app (VExpr.const .natSucc []) (VExpr.bvar
                    1))))))
                    (fun z => piC (interp V
                        (cons V z (cons V y (cons V x ρ))) natT)
                      (fun n' => app x (app (natSuccV V) n'))))) := by
            exact lamC_mem (fun x hx => lamC_mem (fun y hy =>
              lamC_mem (fun z hz => lamC_mem (fun n' hn' =>
                (hbody x hx y hy z hz n' hn').2))))
          simp only [List.take, List.drop, List.cons_append,
            List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
            AnnotOkV_app]
          exact ⟨⟨⟨⟨hRA, hMA, _, _, hRm, t1⟩, hzA, _, _,
              app_mem_piC hRm t1, t2''⟩, hsA, _, _,
              app_mem_piC (app_mem_piC hRm t1) t2'', t3''⟩, hnA, _, _,
            app_mem_piC (app_mem_piC (app_mem_piC hRm t1) t2'') t3'',
            hn''⟩
      · exact nomatch hr''

/-! ## `Quot`

Five constants: a stored inductive, its constructor, two stored
recursors, and — uniquely — a stored **axiom**.  Both recursors carry
a `.plain` rule (the earlier note that they were `.inert` was wrong —
the pinned declarations say otherwise), but `Quot.ind`'s iota is
*proof irrelevance*: its motive lands in `Sort 0`, the layer's value
of `.quotInd` is `pt`, and the reduct sits in the motive's fibre,
which `mem_univ_zero` collapses to `pt` as well.  That is the [set]
lane's whole content where the TT lane assembles `HasType.proofIrrel`
plus a β-spine. -/

/-- `Quot`, installed. -/
theorem extendQuotS {env : Env} (m : EnvS V env)
    (hfresh : env.find? quotName = none)
    (hwf : EnvWF ⟨quotA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨quotA :: env.consts⟩,
      m'.cval = cvalWith m.cval quotA.name
        (fun ψ => VExpr.const .quot [ψ uN]) := by
  refine extendBasisS m (val := fun ψ => VExpr.const .quot [ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotA = quotName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        AnnotOkV_bconst_type (V := V) _ _ ρ⟩⟩
    rw [denoteClosed, show quotA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (.sort (.param uN)) { bi := .default })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_fvar, Level.eval]
    rfl

/-- `Quot.mk`, installed. -/
theorem extendQuotMkS {env : Env} (m : EnvS V env)
    (hQ : env.find? quotName = some quotA)
    (hfresh : env.find? quotMkName = none)
    (hwf : EnvWF ⟨quotMkA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨quotMkA :: env.consts⟩,
      m'.cval = cvalWith m.cval quotMkA.name
        (fun ψ => VExpr.const .quotMk [ψ uN]) := by
  have hQc : ∀ (d : Nat) (φ : Name → Nat),
      denote (cvalWith m.cval quotMkA.name
        (fun ψ => VExpr.const .quotMk [ψ uN]))
        ⟨quotMkA :: env.consts⟩ φ d (.const quotName [.param uN])
        = some (VExpr.const .quot [φ uN]) := by
    intro d φ
    refine denote_const_pinS m (by decide) hQ rfl (by decide) ?_ d
    rw [show Level.substFn φ quotA.toConstantVal.levelParams
        [Level.param uN] = φ from Level.substFn_param_self φ [uN]]
    simp +decide [pinnedDirectT]
  refine extendBasisS m (val := fun ψ => VExpr.const .quotMk [ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotMkA = quotMkName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        AnnotOkV_bconst_type (V := V) _ _ ρ⟩⟩
    rw [denoteClosed, show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
    simp [denote_forallE, denote_sort, denote_app, denote_fvar,
      Level.eval, hQc]
    rfl

/-- The `Quot` block's earlier constants, denoted in the environment
`Quot.ind`'s install works in. -/
theorem denote_quotInd_constsS {env : Env} {ci : ConstantInfo}
    (m : EnvS V env) {val : (Name → Nat) → VExpr} (φ : Name → Nat)
    (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hnQ : ci.name ≠ quotName) (hnM : ci.name ≠ quotMkName) :
    (∀ e : Nat,
      denote (cvalWith m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const quotName [w]) = some (VExpr.const .quot [w.eval φ])) ∧
    (∀ e : Nat,
      denote (cvalWith m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const quotMkName [w]) = some (VExpr.const .quotMk [w.eval φ])) := by
  have hQv : ∀ ψ : Name → Nat,
      m.cval quotName ψ = VExpr.const .quot [ψ uN] := fun ψ =>
    cvalS_pinned m (by decide) (by rw [hQ]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  have hMv : ∀ ψ : Name → Nat,
      m.cval quotMkName ψ = VExpr.const .quotMk [ψ uN] := fun ψ =>
    cvalS_pinned m (by decide) (by rw [hM]; rfl) ψ
      (by simp +decide [pinnedDirectT])
  constructor
  · intro e
    rw [denote_const, Env.find?_cons, if_neg hnQ, hQ]
    simp only [show ([w] : List Level).length
      = quotA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (Ne.symm hnQ), hQv]
    rfl
  · intro e
    rw [denote_const, Env.find?_cons, if_neg hnM, hM]
    simp only [show ([w] : List Level).length
      = quotMkA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (Ne.symm hnM), hMv]
    rfl

/-- `Quot.mk`'s pinned type, denoted — the constructor telescope a fire
site's `hfitC` is stated against. -/
theorem denote_quotMk_typeS {env : Env} {ci : ConstantInfo}
    (m : EnvS V env) {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hnQ : ci.name ≠ quotName) (hnM : ci.name ≠ quotMkName) :
    denote (cvalWith m.cval ci.name val) ⟨ci :: env.consts⟩ φ d
        (quotMkA.toConstantVal.type.instantiateLevelParams
          quotMkA.toConstantVal.levelParams [w])
      = some (.pi (.sort (w.eval φ))
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.bvar 1)
            (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
              [.bvar 2, .bvar 1])))) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst]
  obtain ⟨hQc, -⟩ := denote_quotInd_constsS m (val := val) φ w hQ hM hnQ hnM
  rw [show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl,
    show quotMkA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, VExpr.mkAppN, Level.eval]

/-- **`Quot.ind`'s pinned type, denoted at any depth and any level.** -/
theorem denote_quotInd_typeS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (cvalWith m.cval quotIndA.name val) ⟨quotIndA :: env.consts⟩ φ d
        (quotIndA.toConstantVal.type.instantiateLevelParams
          quotIndA.toConstantVal.levelParams [w])
      = some (.pi (.sort (w.eval φ))
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.pi (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
                [.bvar 1, .bvar 0]) (.sort 0))
            (.pi (.pi (.bvar 2)
                (.app (.bvar 1) (VExpr.mkAppN
                  (VExpr.const .quotMk [w.eval φ])
                  [.bvar 3, .bvar 2, .bvar 0])))
              (.pi (VExpr.mkAppN (VExpr.const .quot [w.eval φ])
                  [.bvar 3, .bvar 2])
                (.app (.bvar 2) (.bvar 0))))))) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_constsS m (ci := quotIndA) (val := val)
    φ w hQ hM (by decide) (by decide)
  rw [show quotIndA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "a")
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero) { bi := .default })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "q")
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotIndA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, hMc, VExpr.mkAppN, Level.eval]

/-- `Quot.ind`'s single stored rule. -/
def quotIndRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "r")
        (Expr.forallE Name.anonymous (.bvar 0)
          (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
            { bi := .default }) { bi := .default })
        (Expr.lam (Name.anonymous.str "β")
          (Expr.forallE (Name.anonymous.str "a")
            (.app (.app (.const quotName [.param uN]) (.bvar 1)) (.bvar 0))
            (.sort .zero) { bi := .default })
          (Expr.lam (Name.anonymous.str "mk")
            (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
              (.app (.bvar 1)
                (.app (.app (.app (.const quotMkName [.param uN])
                  (.bvar 3)) (.bvar 2)) (.bvar 0)))
              { bi := .default })
            (Expr.lam (Name.anonymous.str "a") (.bvar 3)
              (.app (.bvar 1) (.bvar 0)) { bi := .default })
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

/-- The stored declaration, with its rule named. -/
theorem quotIndA_eq :
    quotIndA = .recInfo quotIndA.toConstantVal 4 4 [quotIndRule] := rfl

/-- `Quot.ind`'s right-hand side, denoted. -/
def quotIndRhsV (a : Nat) : VExpr :=
  .lam (.sort a)
    (.lam (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.lam (.pi (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 1, .bvar 0])
          (.sort 0))
        (.lam (.pi (.bvar 2)
            (.app (.bvar 1) (VExpr.mkAppN (VExpr.const .quotMk [a])
              [.bvar 3, .bvar 2, .bvar 0])))
          (.lam (.bvar 3) (.app (.bvar 1) (.bvar 0))))))

theorem denote_quotInd_rhsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA) :
    denote (cvalWith m.cval quotIndA.name val) ⟨quotIndA :: env.consts⟩ φ d
        ((RecRule.rhs quotIndRule).instantiateLevelParams
          quotIndA.toConstantVal.levelParams [w])
      = some (quotIndRhsV (w.eval φ)) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_constsS m (ci := quotIndA) (val := val)
    φ w hQ hM (by decide) (by decide)
  rw [show quotIndA.toConstantVal.levelParams = [uN] from rfl]
  simp only [quotIndRule]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hQc, hMc, quotIndRhsV,
    VExpr.mkAppN, Level.eval]


set_option maxHeartbeats 3200000 in
/-- **`Quot.ind`, installed.**  Its stored rule is `.inert`, so
`RecRuleLawV`'s own `fire ≠ .inert` premise discharges the iota
obligation and the whole content is the type computation. -/
theorem extendQuotIndS {env : Env} (m : EnvS V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hfresh : env.find? quotIndName = none)
    (hwf : EnvWF ⟨quotIndA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨quotIndA :: env.consts⟩,
      m'.cval = cvalWith m.cval quotIndA.name
        (fun ψ => VExpr.const .quotInd [ψ uN]) := by
  refine extendBasisS m (val := fun ψ => VExpr.const .quotInd [ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotIndA = quotIndName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨_, ?_, fun ρ =>
      ⟨HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ),
        AnnotOkV_bconst_type (V := V) _ _ ρ⟩⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        quotIndA.toConstantVal.levelParams quotIndA.toConstantVal.type,
      show quotIndA.toConstantVal.levelParams.map Level.param
        = [Level.param uN] from rfl,
      denote_quotInd_typeS m φ 0 (.param uN) hQ hM]
    simp [Level.eval, BConst.type, quotT, quotMkT, relT, lv,
      VExpr.mkAppN]
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨quotMkA.toConstantVal, 2, 1, hM⟩
    · exact nomatch hr'
  · -- the iota rule: *proof irrelevance*, `Quot.ind`'s motive being a
    -- `Prop`.  The layer value of `.quotInd` is `pt`, and the reduct
    -- lands in the motive's fibre, which is a member of `univ 0`.
    intro cv mI rP rules heq
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    intro rl hrl _ φ
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro us hus
      obtain ⟨w, rfl⟩ : ∃ a, us = [a] := by
        match us, hus with
        | [a], _ => exact ⟨a, rfl⟩
      refine ⟨_, denote_quotInd_rhsS m
        (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ 0 w hQ hM, ?_⟩
      intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys
        husj hlev hplain hnested hidx hTV hTVj hR hC
      have hMu := hM
      simp only [quotMkName, quotName] at hMu
      rw [Env.find?_cons, if_neg (by decide), hMu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨y1, y2, ya, rfl⟩ : ∃ a b c, ys = [a, b, c] := by
        match ys, hys with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain ⟨xa, xr, xb, xmk, rfl⟩ : ∃ a b c e, xs = [a, b, c, e] := by
        match xs, hxs with
        | [a, b, c, e], _ => exact ⟨a, b, c, e, rfl⟩
      obtain ⟨v1, rfl⟩ : ∃ a, usj = [a] := by
        match usj, husj with
        | [a], _ => exact ⟨a, rfl⟩
      have hlps : quotMkA.toConstantVal.levelParams = [uN] := rfl
      have hlu : Level.eval φ v1 = Level.eval φ w := by
        have := congrFun hlev uN
        rw [hlps] at this
        simpa [recFireComparands, Level.substFn, Level.subst,
          Level.subst.go, uN] using this
      have hTVc := Option.some.inj (hTV.symm.trans
        (denote_quotInd_typeS m
          (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ 0 w hQ hM))
      have hTVjc := Option.some.inj (hTVj.symm.trans
        (denote_quotMk_typeS m (ci := quotIndA)
          (val := fun ψ => VExpr.const .quotInd [ψ uN]) φ 0 v1 hQ hM
          (by decide) (by decide)))
      subst hTVc; subst hTVjc
      rw [hlu] at hC
      cases hR with | cons ha hR =>
      cases hR with | cons hr hR =>
      cases hR with | cons hb hR =>
      cases hR with | cons hmk hR =>
      cases hR with | cons hq hR =>
      cases hC with | cons hy1 hC =>
      cases hC with | cons hy2 hC =>
      cases hC with | cons hya hC =>
      have hpl := hplain rfl
      have hxa0 : interp V ρ y1 = interp V ρ xa := by
        simpa using hpl 0 (by decide) (by decide)
      have hxr0 : interp V ρ y2 = interp V ρ xr := by
        simpa using hpl 1 (by decide) (by decide)
      have hliftc : ∀ (x : V) (e : VExpr) (ρ' : Nat → V),
          interp V (cons V x ρ') (VExpr.liftN 1 e 0) = interp V ρ' e :=
        fun x e ρ' => interp_lift_cons (V := V) e x ρ'
      have hctorV : cvalWith m.cval quotIndA.name
          (fun ψ => VExpr.const .quotInd [ψ uN])
          ((Name.anonymous.str "Quot").str "mk")
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          = VExpr.const .quotMk [w.eval φ] := by
        rw [cvalWith_ne (by decide)]
        have hv := cvalS_pinned m (n := quotMkName) (by decide)
          (by rw [hM]; rfl)
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          (t := VExpr.const .quotMk
            [Level.substFn φ quotMkA.toConstantVal.levelParams [v1] uN])
          (by simp +decide [pinnedDirectT])
        simp only [quotMkName, quotName] at hv
        rw [hv]
        simp only [show Level.substFn φ quotMkA.toConstantVal.levelParams
          [v1] uN = Level.eval φ v1 from by
            rw [hlps]; simp [Level.substFn, uN], hlu]
      rw [hctorV] at hq
      simp +decide only [VExpr.inst, Nat.reduceAdd,
        Nat.reduceSub, reduceIte, inst_chain1, 
        inst_absorb21, inst_absorb32, VExpr.liftN_zero,
        VExpr.mkAppN, interp_pi, interp_sort, interp_app, interp_const,
        interp_bvar, cons, bval, lv, List.getD_cons_zero,
        hliftc, hxa0, hxr0] at ha hr hb hmk hq hya
      have hred : app (interp V ρ xmk) (interp V ρ ya) = pt :=
        mem_univ_zero (app_mem_piC hb hq) (app_mem_piC hmk hya)
      refine ⟨?_, ?_⟩
      · rw [cvalWith_self]
        simp +decide only [List.take, List.drop, List.cons_append,
          List.nil_append, VExpr.mkAppN, quotIndRhsV, interp_app,
          interp_const, interp_lam, interp_pi, interp_sort, interp_bvar,
          cons, bval, lv, List.getD_cons_zero]
        rw [app_pt, app_pt, app_pt, app_pt, app_pt,
          app_lamC ha, app_lamC hr, app_lamC hb, app_lamC hmk,
          app_lamC hya, hred]
      · intro hxsA hysA
        have haA : AnnotOkV V ρ xa := hxsA xa (by simp)
        have hrA : AnnotOkV V ρ xr := hxsA xr (by simp)
        have hbA : AnnotOkV V ρ xb := hxsA xb (by simp)
        have hmkA : AnnotOkV V ρ xmk := hxsA xmk (by simp)
        have hyaA : AnnotOkV V ρ ya := hysA ya (by simp)
        obtain ⟨hb1, hb2⟩ := AnnotOkV_bconst_type (V := V) .quotInd
          [w.eval φ] ρ
        simp only [lv, List.getD_cons_zero, quotT, relT,
          quotMkT, VExpr.mkAppN, AnnotOkV_pi] at hb1 hb2
        have hRA : AnnotOkV V ρ (quotIndRhsV (w.eval φ)) := by
          refine ⟨hb1, fun x1 h1 => ?_⟩
          obtain ⟨h2a, h2b⟩ := hb2 x1 h1
          refine ⟨h2a, fun x2 h2 => ?_⟩
          obtain ⟨h3a, h3b⟩ := h2b x2 h2
          refine ⟨h3a, fun x3 h3 => ?_⟩
          obtain ⟨h4a, h4b⟩ := h3b x3 h3
          refine ⟨h4a, fun x4 h4 => ⟨trivial, fun x5 h5 => ?_⟩⟩
          simp +decide only [AnnotOkV_app, AnnotOkV_bvar, interp_bvar,
            interp_pi, interp_app, interp_const, cons,
            bval, lv, VExpr.mkAppN, List.getD_cons_zero,
            ] at h4 h5 ⊢
          exact ⟨trivial, trivial, _, _, h4, h5⟩
        have hRm : interp V ρ (quotIndRhsV (w.eval φ)) ∈ˢ
            piC (univ (w.eval φ)) (fun x1 =>
              piC (piC x1 (fun _ => piC x1 (fun _ => univ 0)))
                (fun x2 => piC (piC (app (app (quotV V (w.eval φ)) x1) x2)
                    (fun _ => univ 0))
                  (fun x3 => piC (piC x1 (fun z => app x3
                        (app (app (app (quotMkV V (w.eval φ)) x1) x2) z)))
                    (fun x4 => piC x1 (fun x5 => app x3
                      (app (app (app (quotMkV V (w.eval φ)) x1) x2)
                        x5)))))) := by
          simp +decide only [quotIndRhsV, interp_lam, interp_pi,
            interp_sort, interp_app, interp_const, interp_bvar, cons,
            bval, lv, VExpr.mkAppN, List.getD_cons_zero]
          exact lamC_mem (fun x1 h1 => lamC_mem (fun x2 h2 =>
            lamC_mem (fun x3 h3 => lamC_mem (fun x4 h4 =>
              lamC_mem (fun x5 h5 => app_mem_piC h4 h5)))))
        simp only [List.take, List.drop, List.cons_append,
          List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
          AnnotOkV_app]
        exact ⟨⟨⟨⟨⟨hRA, haA, _, _, hRm, ha⟩, hrA, _, _,
              app_mem_piC hRm ha, hr⟩, hbA, _, _,
              app_mem_piC (app_mem_piC hRm ha) hr, hb⟩, hmkA, _, _,
            app_mem_piC (app_mem_piC (app_mem_piC hRm ha) hr) hb, hmk⟩,
          hyaA, _, _,
          app_mem_piC (app_mem_piC (app_mem_piC
            (app_mem_piC hRm ha) hr) hb) hmk, hya⟩
    · exact nomatch hr'


/-- `Quot.lift`'s invariance premise as the *stored* type denotes it:
the pinned `Eq` former's valuation applied to three arguments, where
`quotInvT` has `.eqE`. -/
def quotInvV (E A r B f : VExpr) : VExpr :=
  .pi A (.pi (A.liftN 1)
    (.pi (VExpr.mkAppN (r.liftN 2) [.bvar 1, .bvar 0])
      (VExpr.mkAppN E [B.liftN 3, .app (f.liftN 3) (.bvar 2),
        .app (f.liftN 3) (.bvar 1)])))

/-- `Quot.lift`'s pinned type, as it denotes: the layer's, with the
stored `Eq` former's valuation in the invariance premise. -/
def quotLiftTyV (E : VExpr) (a b : Nat) : VExpr :=
  .pi (.sort a)
    (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.pi (.sort b)
        (.pi (.pi (.bvar 2) (.bvar 1))
          (.pi (quotInvV E (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
            (.pi (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3])
              (.bvar 3))))))

/-- …and its rule's right-hand side, the same telescope returning
`f a`. -/
def quotLiftRhsV (E : VExpr) (a b : Nat) : VExpr :=
  .lam (.sort a)
    (.lam (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.lam (.sort b)
        (.lam (.pi (.bvar 2) (.bvar 1))
          (.lam (quotInvV E (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
            (.lam (.bvar 4) (.app (.bvar 2) (.bvar 0)))))))

/-- The pinned `Eq` former, denoted at the level `Quot.lift`'s stored
type reads it at. -/
theorem denote_quot_eqConstS {env : Env} {ci : ConstantInfo} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (w : Level)
    (hE : env.find? eqName = some eqA) (hnE : ci.name ≠ eqName) (e : Nat) :
    denote (cvalWith m.cval ci.name val) ⟨ci :: env.consts⟩ φ e
        (.const eqName [w])
      = some (m.cval eqName (Level.substFn φ [uN] [w])) := by
  rw [denote_const, Env.find?_cons, if_neg hnE, hE]
  simp only [show ([w] : List Level).length
    = eqA.toConstantVal.levelParams.length from rfl, if_true]
  rw [cvalWith_ne (Ne.symm hnE)]
  rfl

/-! ### The `Eq` bridge, [set] form

`Quot.lift`'s and `Quot.sound`'s stored types read the *pinned* `Eq`
former where the layer's own constants conclude at `.eqE`.  In the TT
lane the gap is `quotInv_deq`: three `congrPi` binders over §11's
`eq_law`.  Here the gap is an equality of *interpretations*, so the
binders are `piC_congr` and the core is `EqLawV.app₃` — the bridge the
`Nat` record predicted, arriving with the shape it predicted.

Truthfulness does not transport along that equality (`AnnotOkV` is
structural), so the spine's own `AnnotOkV` package is proved
separately.  It needs the `Eq` former's *membership*, which is
already in the bundle: `EnvS.mem_type` at the stored `eqA`.  No new
`EnvS` field is required. -/

/-- `Eq`'s pinned type, denoted ([set] transpose of the TT lane's
`denote_eq_type`). -/
theorem denote_eq_typeS {env : Env} (m : EnvS V env)
    (_hEq : env.find? eqName = some eqA) (ψ : Name → Nat) :
    denote m.cval env ψ 0 eqA.toConstantVal.type =
      some (.pi (.sort (ψ uN))
        (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))) := by
  simp [eqA, ConstantInfo.toConstantVal, denote_forallE, denote_sort,
    Expr.instantiate1, denote_fvar, uN, Level.eval]

/-- **The `Eq` former's own membership.**  Read off `EnvS.mem_type` at
the stored `eqA`; this is what makes the bridged spine truthful. -/
theorem eqV_memS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.cval eqName ψ) ∈ˢ
      piC (univ (ψ uN))
        (fun a => piC a (fun _ => piC a (fun _ => univ 0))) := by
  obtain ⟨t, ht, hm⟩ := m.mem_type eqA (find?_mem hE) ψ
  rw [denoteClosed, denote_eq_typeS m hE ψ] at ht
  obtain rfl := Option.some.inj ht.symm
  have h1 := (hm ρ).1
  rw [show ConstantInfo.name eqA = eqName from rfl] at h1
  simpa [interp_pi, interp_sort, interp_bvar, cons] using h1

/-- Lifting past `k` fresh binders is invisible to `interp`. -/
theorem interp_liftN_cons0 (n : Nat) (e : VExpr) (ρ : Nat → V) :
    interp V ρ (VExpr.liftN n e 0) = interp V (fun i => ρ (i + n)) e := by
  rw [interp_liftN, shiftE_zero]

/-- **The bridge**: the stored `Eq` former's invariance premise and the
layer's `.eqE` one have the same interpretation. -/
theorem quotInv_interpS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    {A r B f : VExpr}
    (hB : interp V ρ B ∈ˢ univ (ψ uN))
    (hf : interp V ρ f ∈ˢ piC (interp V ρ A)
      (fun _ => interp V ρ B)) :
    interp V ρ (quotInvV (m.cval eqName ψ) A r B f)
      = interp V ρ (quotInvT A r B f) := by
  simp only [quotInvV, quotInvT, interp_pi]
  refine piC_congr (fun x hx => ?_)
  refine piC_congr (fun y hy => ?_)
  refine piC_congr (fun z _ => ?_)
  have hshift : (fun i => cons V z (cons V y (cons V x ρ)) (i + 3))
      = ρ := by
    funext i; simp [cons]
  have hB3 : interp V (cons V z (cons V y (cons V x ρ)))
      (VExpr.liftN 3 B 0) = interp V ρ B := by
    rw [interp_liftN_cons0, hshift]
  have hf3 : interp V (cons V z (cons V y (cons V x ρ)))
      (VExpr.liftN 3 f 0) = interp V ρ f := by
    rw [interp_liftN_cons0, hshift]
  have hyA : y ∈ˢ interp V ρ A := by
    have h1 : interp V (cons V x ρ) (VExpr.liftN 1 A 0)
        = interp V ρ A := by
      rw [interp_liftN_cons0]
      have h2 : (fun i => cons V x ρ (i + 1)) = ρ := by
        funext i; simp [cons]
      rw [h2]
    rwa [h1] at hy
  have hx2 : cons V z (cons V y (cons V x ρ)) 2 ∈ˢ interp V ρ A := by
    simpa [cons] using hx
  have hy1 : cons V z (cons V y (cons V x ρ)) 1 ∈ˢ interp V ρ A := by
    simpa [cons] using hyA
  rw [interp_eqE,
    EqLawV.app₃ (V := V) m.eq_lawV hE ψ (cons V z (cons V y (cons V x ρ)))
      (VExpr.liftN 3 B 0) (.app (VExpr.liftN 3 f 0) (.bvar 2))
      (.app (VExpr.liftN 3 f 0) (.bvar 1))
      (by rw [hB3]; exact hB)
      (by rw [interp_app, interp_bvar, hB3, hf3]
          exact app_mem_piC hf hx2)
      (by rw [interp_app, interp_bvar, hB3, hf3]
          exact app_mem_piC hf hy1)]

/-- **The bridged spine is truthful.**  `AnnotOkV` does not transport
along the bridge (it is structural), so the invariance premise's own
package is assembled here: the relation's two applications from the
binder memberships, the `Eq` spine's three from `eqV_memS`. -/
theorem quotInv_annotS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    {A r B f : VExpr}
    (hAA : AnnotOkV V ρ A) (hrA : AnnotOkV V ρ r)
    (hBA : AnnotOkV V ρ B) (hfA : AnnotOkV V ρ f)
    (hrm : interp V ρ r ∈ˢ piC (interp V ρ A)
      (fun _ => piC (interp V ρ A) (fun _ => univ 0)))
    (hB : interp V ρ B ∈ˢ univ (ψ uN))
    (hf : interp V ρ f ∈ˢ piC (interp V ρ A)
      (fun _ => interp V ρ B)) :
    AnnotOkV V ρ (quotInvV (m.cval eqName ψ) A r B f) := by
  have hs1 : ∀ x : V, shiftE V 1 0 (cons V x ρ) = ρ := by
    intro x; funext i; simp [shiftE, cons]
  have hs2 : ∀ x y : V, shiftE V 2 0 (cons V y (cons V x ρ)) = ρ := by
    intro x y; funext i; simp [shiftE, cons]
  have hs3 : ∀ x y z : V,
      shiftE V 3 0 (cons V z (cons V y (cons V x ρ))) = ρ := by
    intro x y z; funext i; simp [shiftE, cons]
  have hi1 : ∀ (x : V) (e : VExpr),
      interp V (cons V x ρ) (VExpr.liftN 1 e 0) = interp V ρ e := by
    intro x e
    rw [interp_liftN_cons0]
    have h : (fun i => cons V x ρ (i + 1)) = ρ := by funext i; simp [cons]
    rw [h]
  have hi2 : ∀ (x y : V) (e : VExpr),
      interp V (cons V y (cons V x ρ)) (VExpr.liftN 2 e 0)
        = interp V ρ e := by
    intro x y e
    rw [interp_liftN_cons0]
    have h : (fun i => cons V y (cons V x ρ) (i + 2)) = ρ := by
      funext i; simp [cons]
    rw [h]
  have hi3 : ∀ (x y z : V) (e : VExpr),
      interp V (cons V z (cons V y (cons V x ρ))) (VExpr.liftN 3 e 0)
        = interp V ρ e := by
    intro x y z e
    rw [interp_liftN_cons0]
    have h : (fun i => cons V z (cons V y (cons V x ρ)) (i + 3)) = ρ := by
      funext i; simp [cons]
    rw [h]
  simp only [quotInvV]
  refine ⟨hAA, fun x hx => ?_⟩
  refine ⟨(AnnotOkV_liftN (V := V) 1 A 0 _).mpr (by rw [hs1]; exact hAA),
    fun y hy => ?_⟩
  rw [hi1] at hy
  refine ⟨?_, fun z _ => ?_⟩
  · -- the relation, applied to the two binders
    have hrm2 : interp V (cons V y (cons V x ρ)) (VExpr.liftN 2 r 0)
        ∈ˢ piC (interp V ρ A)
          (fun _ => piC (interp V ρ A) (fun _ => univ 0)) := by
      rw [hi2 x y r]; exact hrm
    have hx1 : interp V (cons V y (cons V x ρ)) (VExpr.bvar 1)
        ∈ˢ interp V ρ A := by
      rw [interp_bvar]; simpa [cons] using hx
    have hy0 : interp V (cons V y (cons V x ρ)) (VExpr.bvar 0)
        ∈ˢ interp V ρ A := by
      rw [interp_bvar]; simpa [cons] using hy
    simp only [VExpr.mkAppN, AnnotOkV_app, AnnotOkV_bvar]
    exact ⟨⟨(AnnotOkV_liftN (V := V) 2 r 0 _).mpr (by rw [hs2]; exact hrA),
        trivial, _, _, hrm2, hx1⟩,
      trivial, _, _, app_mem_piC hrm2 hx1, hy0⟩
  · -- the `Eq` spine
    have hB3 : interp V (cons V z (cons V y (cons V x ρ)))
        (VExpr.liftN 3 B 0) ∈ˢ univ (ψ uN) := by rw [hi3]; exact hB
    have hf3 : interp V (cons V z (cons V y (cons V x ρ)))
        (VExpr.liftN 3 f 0) ∈ˢ piC (interp V ρ A)
          (fun _ => interp V ρ B) := by rw [hi3 x y z f]; exact hf
    have hx2 : interp V (cons V z (cons V y (cons V x ρ))) (VExpr.bvar 2)
        ∈ˢ interp V ρ A := by rw [interp_bvar]; simpa [cons] using hx
    have hy1 : interp V (cons V z (cons V y (cons V x ρ))) (VExpr.bvar 1)
        ∈ˢ interp V ρ A := by rw [interp_bvar]; simpa [cons] using hy
    have hfx : interp V (cons V z (cons V y (cons V x ρ)))
        (.app (VExpr.liftN 3 f 0) (VExpr.bvar 2))
        ∈ˢ interp V (cons V z (cons V y (cons V x ρ)))
          (VExpr.liftN 3 B 0) := by
      rw [interp_app, hi3 x y z f, hi3 x y z B]
      exact app_mem_piC hf hx2
    have hfy : interp V (cons V z (cons V y (cons V x ρ)))
        (.app (VExpr.liftN 3 f 0) (VExpr.bvar 1))
        ∈ˢ interp V (cons V z (cons V y (cons V x ρ)))
          (VExpr.liftN 3 B 0) := by
      rw [interp_app, hi3 x y z f, hi3 x y z B]
      exact app_mem_piC hf hy1
    have hEm := eqV_memS m hE ψ (cons V z (cons V y (cons V x ρ)))
    have hfA3 : AnnotOkV V (cons V z (cons V y (cons V x ρ)))
        (VExpr.liftN 3 f 0) :=
      (AnnotOkV_liftN (V := V) 3 f 0 _).mpr (by rw [hs3]; exact hfA)
    simp only [VExpr.mkAppN, AnnotOkV_app, AnnotOkV_bvar]
    exact ⟨⟨⟨m.annot_okV eqName ψ _,
          (AnnotOkV_liftN (V := V) 3 B 0 _).mpr (by rw [hs3]; exact hBA),
          _, _, hEm, hB3⟩,
        ⟨hfA3, trivial, _, _, hf3, hx2⟩,
        _, _, app_mem_piC hEm hB3, hfx⟩,
      ⟨hfA3, trivial, _, _, hf3, hy1⟩,
      _, _, app_mem_piC (app_mem_piC hEm hB3) hfx, hfy⟩

/-- **`Quot.lift`'s pinned type, denoted.** -/
theorem denote_quotLift_typeS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w1 w2 : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denote (cvalWith m.cval quotLiftA.name val) ⟨quotLiftA :: env.consts⟩ φ d
        (quotLiftA.toConstantVal.type.instantiateLevelParams
          quotLiftA.toConstantVal.levelParams [w1, w2])
      = some (quotLiftTyV (m.cval eqName (Level.substFn φ [uN] [w2]))
        (w1.eval φ) (w2.eval φ)) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst]
  obtain ⟨hQc, -⟩ := denote_quotInd_constsS m (ci := quotLiftA) (val := val)
    φ w1 hQ hM (by decide) (by decide)
  have hEc := denote_quot_eqConstS m (ci := quotLiftA) (val := val) φ w2 hE
    (by decide)
  rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β") (.sort (.param vN))
              (Expr.forallE (Name.anonymous.str "f")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "a")
                  (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                    (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                      (Expr.forallE (Name.anonymous.str "a")
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1)))
                        { bi := .default }) { bi := .default })
                    { bi := .default })
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3) { bi := .default })
                  { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotLiftA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsv, hsz, denote_forallE,
    denote_sort, denote_app, denote_fvar, hQc, hEc, quotLiftTyV, quotInvV,
    VExpr.mkAppN, VExpr.liftN, Level.eval]

/-- The pinned type, with the invariance premise named. -/
theorem quotLift_type_eq (a b : Nat) :
    BConst.type .quotLift [a, b]
      = .pi (.sort a)
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.sort b)
            (.pi (.pi (.bvar 2) (.bvar 1))
              (.pi (quotInvT (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))
                (.pi (VExpr.mkAppN (VExpr.const .quot [a])
                    [.bvar 4, .bvar 3])
                  (.bvar 3)))))) := rfl

/-- **`Quot.lift`'s stored type interprets to the layer's.**  Four
`piC_congr` binders over the bridge. -/
theorem quotLiftTy_interpS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    (a b : Nat) (hψ : ψ uN = b) :
    interp V ρ (quotLiftTyV (m.cval eqName ψ) a b)
      = interp V ρ (BConst.type .quotLift [a, b]) := by
  rw [quotLift_type_eq]
  simp only [quotLiftTyV, interp_pi]
  refine piC_congr (fun x1 h1 => ?_)
  refine piC_congr (fun x2 h2 => ?_)
  refine piC_congr (fun x3 h3 => ?_)
  refine piC_congr (fun x4 h4 => ?_)
  have hb1 : interp V (cons V x4 (cons V x3 (cons V x2 (cons V x1 ρ))))
      (VExpr.bvar 1) ∈ˢ univ (ψ uN) := by
    rw [interp_bvar, hψ]
    simpa [cons] using h3
  have hb0 : interp V (cons V x4 (cons V x3 (cons V x2 (cons V x1 ρ))))
      (VExpr.bvar 0) ∈ˢ piC (interp V (cons V x4 (cons V x3
          (cons V x2 (cons V x1 ρ)))) (VExpr.bvar 3))
        (fun _ => interp V (cons V x4 (cons V x3 (cons V x2
          (cons V x1 ρ)))) (VExpr.bvar 1)) := by
    simp only [interp_bvar, cons]
    simpa [interp_pi, interp_bvar, cons] using h4
  rw [quotInv_interpS m hE _ _ hb1 hb0]

/-- …and it is truthful.  Everything but the invariance premise is the
layer's own type's package; that one slot is `quotInv_annotS`, and the
last binder crosses on the interpretation equality. -/
theorem quotLiftTy_annotS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    (a b : Nat) (hψ : ψ uN = b) :
    AnnotOkV V ρ (quotLiftTyV (m.cval eqName ψ) a b) := by
  have hc := AnnotOkV_bconst_type (V := V) .quotLift [a, b] ρ
  rw [quotLift_type_eq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [quotLiftTyV]
  refine ⟨hc1, fun x1 h1 => ?_⟩
  obtain ⟨h2a, h2b⟩ := hc2 x1 h1
  refine ⟨h2a, fun x2 h2 => ?_⟩
  obtain ⟨h3a, h3b⟩ := h2b x2 h2
  refine ⟨h3a, fun x3 h3 => ?_⟩
  obtain ⟨h4a, h4b⟩ := h3b x3 h3
  refine ⟨h4a, fun x4 h4 => ?_⟩
  obtain ⟨h5a, h5b⟩ := h4b x4 h4
  have hb1 : interp V (cons V x4 (cons V x3 (cons V x2 (cons V x1 ρ))))
      (VExpr.bvar 1) ∈ˢ univ (ψ uN) := by
    rw [interp_bvar, hψ]
    simpa [cons] using h3
  have hb0 : interp V (cons V x4 (cons V x3 (cons V x2 (cons V x1 ρ))))
      (VExpr.bvar 0) ∈ˢ piC (interp V (cons V x4 (cons V x3
          (cons V x2 (cons V x1 ρ)))) (VExpr.bvar 3))
        (fun _ => interp V (cons V x4 (cons V x3 (cons V x2
          (cons V x1 ρ)))) (VExpr.bvar 1)) := by
    simp only [interp_bvar, cons]
    simpa [interp_pi, interp_bvar, cons] using h4
  refine ⟨quotInv_annotS m hE _ _ trivial trivial trivial trivial ?_
      hb1 hb0, fun x5 h5 => ?_⟩
  · simpa [interp_bvar, cons, interp_pi] using h2
  · exact h5b x5 (by rwa [← quotInv_interpS m hE _ _ hb1 hb0])

/-- `Quot.lift`'s single stored rule. -/
def quotLiftRule : RecRule :=
  { ctor := quotMkName, nfields := 1, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "r")
        (Expr.forallE Name.anonymous (.bvar 0)
          (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
            { bi := .default }) { bi := .default })
        (Expr.lam (Name.anonymous.str "β") (.sort (.param vN))
          (Expr.lam (Name.anonymous.str "f")
            (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
              { bi := .default })
            (Expr.lam (Name.anonymous.str "h")
              (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                    (.app (.app (.app (.const eqName [.param vN])
                      (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                      (.app (.bvar 3) (.bvar 1)))
                    { bi := .default }) { bi := .default })
                { bi := .default })
              (Expr.lam (Name.anonymous.str "a") (.bvar 4)
                (.app (.bvar 2) (.bvar 0)) { bi := .default })
              { bi := .default })
            { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .default } }

theorem quotLiftA_eq :
    quotLiftA = .recInfo quotLiftA.toConstantVal 5 5 [quotLiftRule] := rfl

/-- **`Quot.lift`'s right-hand side, denoted.** -/
theorem denote_quotLift_rhsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w1 w2 : Level)
    (hE : env.find? eqName = some eqA) :
    denote (cvalWith m.cval quotLiftA.name val) ⟨quotLiftA :: env.consts⟩ φ d
        ((RecRule.rhs quotLiftRule).instantiateLevelParams
          quotLiftA.toConstantVal.levelParams [w1, w2])
      = some (quotLiftRhsV (m.cval eqName (Level.substFn φ [uN] [w2]))
        (w1.eval φ) (w2.eval φ)) := by
  have hsu : Level.subst [uN, vN] [w1, w2] (.param uN) = w1 := by
    simp [Level.subst, Level.subst.go, uN]
  have hsv : Level.subst [uN, vN] [w1, w2] (.param vN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, vN]
  have hsz : Level.subst [uN, vN] [w1, w2] .zero = .zero := by
    simp [Level.subst]
  have hEc := denote_quot_eqConstS m (ci := quotLiftA) (val := val) φ w2 hE
    (by decide)
  rw [show quotLiftA.toConstantVal.levelParams = [uN, vN] from rfl]
  simp only [quotLiftRule]
  simp [Expr.instantiateLevelParams, hsu, hsv, hsz, denote_lam,
    denote_forallE, denote_sort, denote_app, denote_fvar, hEc,
    quotLiftRhsV, quotInvV, VExpr.mkAppN, VExpr.liftN, Level.eval]

set_option maxHeartbeats 3200000 in
/-- **`Quot.lift`, installed.**  The type obligation crosses the `Eq`
bridge; the iota is the layer's `quotLiftV_app`/`quotLift_beta` pair
after the parameter test moves the fired major onto the recursor's own
parameters. -/
theorem extendQuotLiftS {env : Env} (m : EnvS V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotLiftName = none)
    (hwf : EnvWF ⟨quotLiftA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨quotLiftA :: env.consts⟩,
      m'.cval = cvalWith m.cval quotLiftA.name
        (fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) := by
  refine extendBasisS m
    (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotLiftA = quotLiftName from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN, vN]; exact List.mem_cons_self),
      hp vN (by
        show vN ∈ [uN, vN]
        exact List.mem_cons_of_mem _ List.mem_cons_self)]
  · intro φ
    refine ⟨quotLiftTyV
      (m.cval eqName (Level.substFn φ [uN] [Level.param vN]))
      (φ uN) (φ vN), ?_, fun ρ => ⟨?_, quotLiftTy_annotS m hE
        (Level.substFn φ [uN] [Level.param vN]) ρ (φ uN) (φ vN) rfl⟩⟩
    · rw [denoteClosed, ← Expr.instantiateLevelParams_self
          quotLiftA.toConstantVal.levelParams quotLiftA.toConstantVal.type,
        show quotLiftA.toConstantVal.levelParams.map Level.param
          = [Level.param uN, Level.param vN] from rfl,
        denote_quotLift_typeS m φ 0 (.param uN) (.param vN) hQ hM hE]
      simp [Level.eval]
    · rw [quotLiftTy_interpS m hE
        (Level.substFn φ [uN] [Level.param vN]) ρ (φ uN) (φ vN) rfl]
      exact HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ)
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨quotMkA.toConstantVal, 2, 1, hM⟩
    · exact nomatch hr'
  · -- the iota rule
    intro cv mI rP rules heq
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    intro rl hrl _ φ
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro us hus
      obtain ⟨w1, w2, rfl⟩ : ∃ a b, us = [a, b] := by
        match us, hus with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      refine ⟨_, denote_quotLift_rhsS m
        (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ 0 w1 w2
        hE, ?_⟩
      intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys
        husj hlev hplain hnested hidx hTV hTVj hR hC
      have hMu := hM
      simp only [quotMkName, quotName] at hMu
      rw [Env.find?_cons, if_neg (by decide), hMu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = quotMkA.toConstantVal ∧ cnP = 2 ∧ cnF = 1 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨y1, y2, ya, rfl⟩ : ∃ a b c, ys = [a, b, c] := by
        match ys, hys with
        | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
      obtain ⟨xa, xr, xb, xf, xh, rfl⟩ :
          ∃ a b c e g, xs = [a, b, c, e, g] := by
        match xs, hxs with
        | [a, b, c, e, g], _ => exact ⟨a, b, c, e, g, rfl⟩
      obtain ⟨v1, rfl⟩ : ∃ a, usj = [a] := by
        match usj, husj with
        | [a], _ => exact ⟨a, rfl⟩
      have hlps : quotMkA.toConstantVal.levelParams = [uN] := rfl
      have hlu : Level.eval φ v1 = Level.eval φ w1 := by
        have h := congrFun hlev uN
        rw [hlps] at h
        simpa [recFireComparands, Level.substFn, Level.subst,
          Level.subst.go, uN, vN] using h
      have hctorV : cvalWith m.cval quotLiftA.name
          (fun ψ => VExpr.const .quotLift [ψ uN, ψ vN])
          ((Name.anonymous.str "Quot").str "mk")
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          = VExpr.const .quotMk [Level.eval φ w1] := by
        rw [cvalWith_ne (by decide)]
        have hv := cvalS_pinned m (n := quotMkName) (by decide)
          (by rw [hM]; rfl)
          (Level.substFn φ quotMkA.toConstantVal.levelParams [v1])
          (t := VExpr.const .quotMk
            [Level.substFn φ quotMkA.toConstantVal.levelParams [v1] uN])
          (by simp +decide [pinnedDirectT])
        simp only [quotMkName, quotName] at hv
        rw [hv]
        simp only [show Level.substFn φ quotMkA.toConstantVal.levelParams
          [v1] uN = Level.eval φ v1 from by
            rw [hlps]; simp [Level.substFn, uN], hlu]
      have hTVc := Option.some.inj (hTV.symm.trans
        (denote_quotLift_typeS m
          (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ 0 w1 w2
          hQ hM hE))
      have hTVjc := Option.some.inj (hTVj.symm.trans
        (denote_quotMk_typeS m (ci := quotLiftA)
          (val := fun ψ => VExpr.const .quotLift [ψ uN, ψ vN]) φ 0 v1
          hQ hM (by decide) (by decide)))
      subst hTVc; subst hTVjc
      rw [hctorV] at hR
      rw [hlu] at hC
      cases hR with | cons ha hR =>
      cases hR with | cons hr hR =>
      cases hR with | cons hb hR =>
      cases hR with | cons hf hR =>
      cases hR with | cons hh hR =>
      cases hR with | cons hq hR =>
      cases hC with | cons hy1 hC =>
      cases hC with | cons hy2 hC =>
      cases hC with | cons hya hC =>
      have hliftc : ∀ (x : V) (e : VExpr) (ρ' : Nat → V),
          interp V (cons V x ρ') (VExpr.liftN 1 e 0) = interp V ρ' e :=
        fun x e ρ' => interp_lift_cons (V := V) e x ρ'
      have hpl := hplain rfl
      have hxa0 : interp V ρ y1 = interp V ρ xa := by
        simpa using hpl 0 (by decide) (by decide)
      have hxr0 : interp V ρ y2 = interp V ρ xr := by
        simpa using hpl 1 (by decide) (by decide)
      have hEclosed := m.cval_closed eqName (Level.substFn φ [uN] [w2])
      have hh0 : interp V ρ xh ∈ˢ interp V ρ
          (quotInvV (m.cval eqName (Level.substFn φ [uN] [w2]))
            xa xr xb xf) := by
        simpa [quotInvV, VExpr.mkAppN, inst_chain1, inst_chain2,
          inst_chain3, inst_absorb21, inst_absorb32, inst_absorb43,
          VExpr.liftN_zero,
          VExpr.inst_eq_self_of_closed hEclosed] using hh
      simp +decide only [VExpr.inst, Nat.reduceAdd,
        Nat.reduceSub, reduceIte, inst_chain1, 
        inst_absorb21, inst_absorb32, VExpr.liftN_zero,
        VExpr.mkAppN, interp_pi, interp_sort, interp_app, interp_const,
        bval, lv, List.getD_cons_zero,
        hliftc, hxa0, hxr0] at ha hr hb hf hq hya
      have hbm : interp V ρ xb ∈ˢ univ (Level.substFn φ [uN] [w2] uN) := by
        simpa [Level.substFn, uN, Level.eval] using hb
      have hfm : interp V ρ xf ∈ˢ piC (interp V ρ xa)
          (fun _ => interp V ρ xb) := hf
      have hhm : interp V ρ xh ∈ˢ quotInvSpace V (interp V ρ xa)
          (interp V ρ xr) (interp V ρ xf) := by
        rw [quotInv_interpS m hE _ ρ hbm hfm, interp_quotInvT] at hh0
        exact hh0
      have hlu1 : Level.substFn φ [Name.anonymous.str "u",
          Name.anonymous.str "v"] [w1, w2] uN = Level.eval φ w1 := by
        simp [Level.substFn, uN]
      have hlu2 : Level.substFn φ [Name.anonymous.str "u",
          Name.anonymous.str "v"] [w1, w2] vN = Level.eval φ w2 := by
        simp [Level.substFn, vN]
      have hb1' : interp V (cons V (interp V ρ xf) (cons V (interp V ρ xb)
            (cons V (interp V ρ xr) (cons V (interp V ρ xa) ρ))))
          (VExpr.bvar 1)
          ∈ˢ univ (Level.substFn φ [uN] [w2] uN) := by
        rw [interp_bvar]
        simpa [cons, Level.substFn, uN] using hb
      have hb0' : interp V (cons V (interp V ρ xf) (cons V (interp V ρ xb)
            (cons V (interp V ρ xr) (cons V (interp V ρ xa) ρ))))
          (VExpr.bvar 0)
          ∈ˢ piC (interp V (cons V (interp V ρ xf)
              (cons V (interp V ρ xb) (cons V (interp V ρ xr)
                (cons V (interp V ρ xa) ρ)))) (VExpr.bvar 3))
            (fun _ => interp V (cons V (interp V ρ xf)
              (cons V (interp V ρ xb) (cons V (interp V ρ xr)
                (cons V (interp V ρ xa) ρ)))) (VExpr.bvar 1)) := by
        simp only [interp_bvar, cons]
        exact hf
      have h5 : interp V ρ xh ∈ˢ interp V (cons V (interp V ρ xf)
          (cons V (interp V ρ xb) (cons V (interp V ρ xr)
            (cons V (interp V ρ xa) ρ))))
          (quotInvV (m.cval eqName (Level.substFn φ [uN] [w2]))
            (VExpr.bvar 3) (VExpr.bvar 2) (VExpr.bvar 1)
            (VExpr.bvar 0)) := by
        rw [quotInv_interpS m hE _ _ hb1' hb0', interp_quotInvT]
        simpa [interp_bvar, cons] using hhm
      refine ⟨?_, ?_⟩
      · rw [cvalWith_self]
        simp +decide only [List.take, List.drop, List.cons_append,
          List.nil_append, VExpr.mkAppN, quotLiftRhsV, interp_app,
          interp_const, interp_lam, interp_pi, interp_sort, interp_bvar,
          cons, bval, lv, List.getD_cons_zero,
          List.getD_cons_succ, hxa0, hxr0, hctorV, hlu1, hlu2]
        rw [quotLiftV_app V ha hr hb hf hhm, quotMkV_app V ha hr hya,
          quotLift_beta ha hya (quotInv_of_mem V hhm),
          app_lamC ha, app_lamC hr, app_lamC hb, app_lamC hf,
          app_lamC h5, app_lamC hya]
      · intro hxsA hysA
        have haA : AnnotOkV V ρ xa := hxsA xa (by simp)
        have hrA : AnnotOkV V ρ xr := hxsA xr (by simp)
        have hbA : AnnotOkV V ρ xb := hxsA xb (by simp)
        have hfA : AnnotOkV V ρ xf := hxsA xf (by simp)
        have hhA : AnnotOkV V ρ xh := hxsA xh (by simp)
        have hyaA : AnnotOkV V ρ ya := hysA ya (by simp)
        have hRA : AnnotOkV V ρ (quotLiftRhsV
            (m.cval eqName (Level.substFn φ [uN] [w2]))
            (Level.eval φ w1) (Level.eval φ w2)) := by
          refine ⟨trivial, fun x1 h1 => ⟨?_, fun x2 h2 =>
            ⟨trivial, fun x3 h3 => ⟨?_, fun x4 h4 => ⟨?_,
              fun x5 h5' => ⟨trivial, fun x6 h6 => ?_⟩⟩⟩⟩⟩⟩
          · simp [AnnotOkV_pi]
          · simp [AnnotOkV_pi]
          · refine quotInv_annotS m hE _ _ trivial trivial trivial
              trivial ?_ ?_ ?_
            · simpa [interp_bvar, interp_pi, cons] using h2
            · rw [interp_bvar]
              simpa [cons, Level.substFn, uN] using h3
            · simp only [interp_bvar, cons]
              simpa [interp_pi, interp_bvar, cons] using h4
          · have h4' : x4 ∈ˢ piC x1 (fun _ => x3) := by
              simpa [interp_pi, interp_bvar, cons] using h4
            have h6' : x6 ∈ˢ x1 := by
              simpa [interp_bvar, cons] using h6
            simp only [AnnotOkV_app, AnnotOkV_bvar, interp_bvar, cons]
            exact ⟨trivial, trivial, x1, fun _ => x3, h4', h6'⟩
        have hRm : interp V ρ (quotLiftRhsV
              (m.cval eqName (Level.substFn φ [uN] [w2]))
              (Level.eval φ w1) (Level.eval φ w2)) ∈ˢ
            piC (univ (Level.eval φ w1)) (fun x1 =>
              piC (piC x1 (fun _ => piC x1 (fun _ => univ 0)))
                (fun x2 => piC (univ (Level.eval φ w2)) (fun x3 =>
                  piC (piC x1 (fun _ => x3)) (fun x4 =>
                    piC (interp V (cons V x4 (cons V x3 (cons V x2
                        (cons V x1 ρ))))
                        (quotInvV (m.cval eqName
                          (Level.substFn φ [uN] [w2]))
                          (VExpr.bvar 3) (VExpr.bvar 2) (VExpr.bvar 1)
                          (VExpr.bvar 0)))
                      (fun _ => piC x1 (fun _ => x3)))))) := by
          simp only [quotLiftRhsV, interp_lam, interp_pi, interp_sort,
            interp_bvar, cons]
          exact lamC_mem (fun x1 h1 => lamC_mem (fun x2 h2 =>
            lamC_mem (fun x3 h3 => lamC_mem (fun x4 h4 =>
              lamC_mem (fun x5 h5' => lamC_mem (fun x6 h6 =>
                app_mem_piC h4 h6))))))
        simp only [List.take, List.drop, List.cons_append,
          List.nil_append, VExpr.mkAppN_cons, VExpr.mkAppN_nil,
          AnnotOkV_app]
        exact ⟨⟨⟨⟨⟨⟨hRA, haA, _, _, hRm, ha⟩, hrA, _, _,
                  app_mem_piC hRm ha, hr⟩, hbA, _, _,
                app_mem_piC (app_mem_piC hRm ha) hr, hb⟩, hfA, _, _,
              app_mem_piC (app_mem_piC (app_mem_piC hRm ha) hr) hb,
              hf⟩, hhA, _, _,
            app_mem_piC (app_mem_piC (app_mem_piC
              (app_mem_piC hRm ha) hr) hb) hf, h5⟩,
          hyaA, _, _,
          app_mem_piC (app_mem_piC (app_mem_piC (app_mem_piC
            (app_mem_piC hRm ha) hr) hb) hf) h5, hya⟩
    · exact nomatch hr'

/-- `Quot.sound`'s pinned type, as it denotes. -/
def quotSoundTyV (E : VExpr) (a : Nat) : VExpr :=
  .pi (.sort a)
    (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
      (.pi (.bvar 1)
        (.pi (.bvar 2)
          (.pi (VExpr.mkAppN (.bvar 2) [.bvar 1, .bvar 0])
            (VExpr.mkAppN E
              [VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3],
               VExpr.mkAppN (VExpr.const .quotMk [a])
                 [.bvar 4, .bvar 3, .bvar 2],
               VExpr.mkAppN (VExpr.const .quotMk [a])
                 [.bvar 4, .bvar 3, .bvar 1]])))))

/-- The pinned type with its `Eq` conclusion named. -/
theorem quotSound_type_eq (a : Nat) :
    BConst.type .quotSound [a]
      = .pi (.sort a)
        (.pi (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0)))
          (.pi (.bvar 1)
            (.pi (.bvar 2)
              (.pi (VExpr.mkAppN (VExpr.bvar 2) [.bvar 1, .bvar 0])
                (.eqE
                  (VExpr.mkAppN (VExpr.const .quot [a])
                    [.bvar 4, .bvar 3])
                  (VExpr.mkAppN (VExpr.const .quotMk [a])
                    [.bvar 4, .bvar 3, .bvar 2])
                  (VExpr.mkAppN (VExpr.const .quotMk [a])
                    [.bvar 4, .bvar 3, .bvar 1])))))) := rfl

/-- **`Quot.sound`'s stored type interprets to the layer's.**  Five
`piC_congr` binders and one `EqLawV.app₃`; the spine's three arguments
are the quotient set and two of its classes. -/
theorem quotSoundTy_interpS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    (a : Nat) (hψ : ψ uN = a) :
    interp V ρ (quotSoundTyV (m.cval eqName ψ) a)
      = interp V ρ (BConst.type .quotSound [a]) := by
  rw [quotSound_type_eq]
  simp only [quotSoundTyV, interp_pi]
  refine piC_congr (fun x1 h1 => ?_)
  refine piC_congr (fun x2 h2 => ?_)
  refine piC_congr (fun x3 h3 => ?_)
  refine piC_congr (fun x4 h4 => ?_)
  refine piC_congr (fun x5 _ => ?_)
  have hal : x1 ∈ˢ (univ a : V) := by simpa [interp_sort] using h1
  have hrel : x2 ∈ˢ relSpace V x1 := by
    simpa [relSpace, interp_pi, interp_bvar, interp_sort, cons] using h2
  have h3' : x3 ∈ˢ x1 := by simpa [interp_bvar, cons] using h3
  have h4' : x4 ∈ˢ x1 := by simpa [interp_bvar, cons] using h4
  have hqty : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3])
      ∈ˢ univ (ψ uN) := by
    rw [hψ]
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel]
    exact quotSet_mem_univ hal
  have hmk1 : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quotMk [a]) [.bvar 4, .bvar 3, .bvar 2])
      ∈ˢ interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3]) := by
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel, quotMkV_app V hal hrel h3']
    exact quotClass_mem h3'
  have hmk2 : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quotMk [a]) [.bvar 4, .bvar 3, .bvar 1])
      ∈ˢ interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3]) := by
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel, quotMkV_app V hal hrel h4']
    exact quotClass_mem h4'
  rw [interp_eqE, EqLawV.app₃ (V := V) m.eq_lawV hE ψ _ _ _ _
    hqty hmk1 hmk2]

/-- …and it is truthful: the `Eq` spine's package from `eqV_memS`. -/
theorem quotSoundTy_annotS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA) (ψ : Name → Nat) (ρ : Nat → V)
    (a : Nat) (hψ : ψ uN = a) :
    AnnotOkV V ρ (quotSoundTyV (m.cval eqName ψ) a) := by
  have hc := AnnotOkV_bconst_type (V := V) .quotSound [a] ρ
  rw [quotSound_type_eq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  simp only [quotSoundTyV]
  refine ⟨hc1, fun x1 h1 => ?_⟩
  obtain ⟨h2a, h2b⟩ := hc2 x1 h1
  refine ⟨h2a, fun x2 h2 => ?_⟩
  obtain ⟨h3a, h3b⟩ := h2b x2 h2
  refine ⟨h3a, fun x3 h3 => ?_⟩
  obtain ⟨h4a, h4b⟩ := h3b x3 h3
  refine ⟨h4a, fun x4 h4 => ?_⟩
  obtain ⟨h5a, h5b⟩ := h4b x4 h4
  refine ⟨h5a, fun x5 h5 => ?_⟩
  obtain ⟨hqA, hmA⟩ := h5b x5 h5
  have hal : x1 ∈ˢ (univ a : V) := by simpa [interp_sort] using h1
  have hrel : x2 ∈ˢ relSpace V x1 := by
    simpa [relSpace, interp_pi, interp_bvar, interp_sort, cons] using h2
  have h3' : x3 ∈ˢ x1 := by simpa [interp_bvar, cons] using h3
  have h4' : x4 ∈ˢ x1 := by simpa [interp_bvar, cons] using h4
  have hqty : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3])
      ∈ˢ univ (ψ uN) := by
    rw [hψ]
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel]
    exact quotSet_mem_univ hal
  have hmk1 : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quotMk [a]) [.bvar 4, .bvar 3, .bvar 2])
      ∈ˢ interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3]) := by
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel, quotMkV_app V hal hrel h3']
    exact quotClass_mem h3'
  have hmk2 : interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quotMk [a]) [.bvar 4, .bvar 3, .bvar 1])
      ∈ˢ interp V (cons V x5 (cons V x4 (cons V x3
        (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3]) := by
    simp only [VExpr.mkAppN, interp_app, interp_const, interp_bvar,
      bval, lv, List.getD_cons_zero, cons]
    rw [quotV_app V hal hrel, quotMkV_app V hal hrel h4']
    exact quotClass_mem h4'
  have hqtyA : AnnotOkV V (cons V x5 (cons V x4 (cons V x3
      (cons V x2 (cons V x1 ρ)))))
      (VExpr.mkAppN (VExpr.const .quot [a]) [.bvar 4, .bvar 3]) := by
    have hqv := bval_mem_type V .quot [a] (cons V x5 (cons V x4
      (cons V x3 (cons V x2 (cons V x1 ρ)))))
    simp only [BConst.type, lv, List.getD_cons_zero, interp_pi,
      interp_relT, interp_sort, interp_bvar, cons] at hqv
    simp only [VExpr.mkAppN, AnnotOkV_app, AnnotOkV_const,
      AnnotOkV_bvar, interp_const, interp_bvar, cons]
    exact ⟨⟨trivial, trivial, _, _, hqv, hal⟩, trivial, _, _,
      app_mem_piC hqv hal, hrel⟩
  have hEm := eqV_memS m hE ψ (cons V x5 (cons V x4 (cons V x3
    (cons V x2 (cons V x1 ρ)))))
  simp only [VExpr.mkAppN, AnnotOkV_app]
  exact ⟨⟨⟨m.annot_okV eqName ψ _, hqtyA, _, _, hEm, hqty⟩,
      hqA, _, _, app_mem_piC hEm hqty, hmk1⟩,
    hmA, _, _, app_mem_piC (app_mem_piC hEm hqty) hmk1, hmk2⟩

/-- **`Quot.sound`'s pinned type, denoted.** -/
theorem denote_quotSound_typeS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat) (w : Level)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA) :
    denote (cvalWith m.cval quotSoundA.name val) ⟨quotSoundA :: env.consts⟩ φ d
        (quotSoundA.toConstantVal.type.instantiateLevelParams
          quotSoundA.toConstantVal.levelParams [w])
      = some (quotSoundTyV (m.cval eqName (Level.substFn φ [uN] [w]))
        (w.eval φ)) := by
  have hsu : Level.subst [uN] [w] (.param uN) = w := by
    simp [Level.subst, Level.subst.go, uN]
  have hsz : Level.subst [uN] [w] .zero = .zero := by
    simp [Level.subst]
  obtain ⟨hQc, hMc⟩ := denote_quotInd_constsS m (ci := quotSoundA) (val := val)
    φ w hQ hM (by decide) (by decide)
  have hEc := denote_quot_eqConstS m (ci := quotSoundA) (val := val) φ w hE
    (by decide)
  rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "b") (.bvar 2)
                (Expr.forallE Name.anonymous
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { bi := .default }) { bi := .implicit })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show quotSoundA.toConstantVal.levelParams = [uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsz, denote_forallE, denote_sort,
    denote_app, denote_fvar, hQc, hMc, hEc, quotSoundTyV, VExpr.mkAppN,
    Level.eval]




/-! ## `Eq`

The block the layer *derives* rather than carries: `Eq` is the `.eqE`
former eta-expanded, `Eq.refl` is `.prf` under two binders, and
`Eq.rec` returns its minor premise — its stored rule is `.inert`, so
the block has no iota obligation at all.  What it does have, uniquely,
is `hheadEq`: this install is where `EqLawV` enters the bundle.

(The `Eq`-former helpers `denote_eq_typeS`/`eqV_memS` sit with the
`Quot` block above, where the bridge that consumes them lives.) -/

/-- `Eq`'s valuation: the former, eta-expanded. -/
def eqValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) (.lam (.bvar 1)
    (.eqE (.bvar 2) (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s valuation. -/
def eqReflValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN)) (.lam (.bvar 0) .prf)

/-- The tower is closed. -/
theorem eqValT_closed (ψ : Name → Nat) : VExpr.Closed (eqValT ψ) := by
  simp only [eqValT, VExpr.Closed, VExpr.bvarsBelow]
  exact ⟨trivial, by omega, by omega, by omega, by omega, by omega⟩

/-- `Eq.refl`'s tower is closed. -/
theorem eqReflValT_closed (ψ : Name → Nat) : VExpr.Closed (eqReflValT ψ) := by
  simp only [eqReflValT, VExpr.Closed, VExpr.bvarsBelow]
  exact ⟨trivial, by omega, trivial⟩

/-- `Eq.rec`'s valuation: the minor premise, returned.  Transport is
the identity — `eqRec_derivable` (`Setlec/TT/Examples.lean`), which is
why the layer does not carry `Eq.rec` at all. -/
def eqRecValT (ψ : Name → Nat) : VExpr :=
  .lam (.sort (ψ uN))
    (.lam (.bvar 0)
      (.lam (.pi (.bvar 1)
          (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam (.app (.app (.bvar 0) (.bvar 1))
            (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
          (.lam (.bvar 3)
            (.lam (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))

/-- `Eq.rec`'s tower is closed. -/
theorem eqRecValT_closed (ψ : Name → Nat) : VExpr.Closed (eqRecValT ψ) := by
  simp only [eqRecValT, VExpr.Closed, VExpr.bvarsBelow, VExpr.mkAppN,
    eqValT, eqReflValT]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- **`Eq`'s tower, interpreted.**  A three-deep `lamC` over the
layer's truth-set former. -/
theorem eqValT_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValT ψ)
      = lamC (univ (ψ uN))
        (fun a => lamC a (fun x => lamC a (fun y => eqv x y))) := by
  simp [eqValT, interp_lam, interp_sort, interp_bvar, interp_eqE, cons]

/-- **`EqLawV`'s equation, from the tower** — two `app_lamC`s where
the TT lane needs three β-steps and their lift absorptions. -/
theorem eqValT_lawS (ψ : Name → Nat) (ρ : Nat → V) (A a : VExpr)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A) :
    SetTheory.app (SetTheory.app (interp V ρ (eqValT ψ))
        (interp V ρ A)) (interp V ρ a)
      = lamC (interp V ρ A) (fun y => eqv (interp V ρ a) y) := by
  rw [eqValT_interp, app_lamC hA, app_lamC ha]

/-- …and `EqLawV`'s rigidity clause: the tower is never the proof
point, witnessed at the unit proposition. -/
theorem eqValT_ne_pt (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValT ψ) ≠ pt := by
  rw [eqValT_interp]
  refine lamC_ne_pt_of_witness (x := unitSet) (unitSet_mem_univ _) ?_
  refine lamC_ne_pt_of_witness (x := pt) pt_mem_unitSet ?_
  refine lamC_ne_pt_of_witness (x := pt) pt_mem_unitSet ?_
  unfold SetTheory.eqv
  exact truthVal_ne_pt _

/-- The tower inhabits `Eq`'s denoted type. -/
theorem eqValT_memS (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValT ψ) ∈ˢ piC (univ (ψ uN))
      (fun a => piC a (fun _ => piC a (fun _ => univ 0))) := by
  rw [eqValT_interp]
  exact lamC_mem (fun _a _ => lamC_mem (fun _x _ =>
    lamC_mem (fun _y _ => eqv_mem_univ _ _)))

theorem eqValT_annotS (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkV V ρ (eqValT ψ) := by
  simp [eqValT, AnnotOkV_lam, AnnotOkV_eqE, AnnotOkV_bvar, AnnotOkV_sort]

/-- The full spine's value. -/
theorem eqValT_app₃S (ψ : Name → Nat) (ρ : Nat → V) (A a b : VExpr)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A)
    (hb : interp V ρ b ∈ˢ interp V ρ A) :
    interp V ρ (VExpr.mkAppN (eqValT ψ) [A, a, b])
      = eqv (interp V ρ a) (interp V ρ b) := by
  show interp V ρ (.app (.app (.app (eqValT ψ) A) a) b) = _
  rw [interp_app, interp_app, interp_app, eqValT_lawS ψ ρ A a hA ha,
    app_lamC hb]

/-- …and the spine is truthful. -/
theorem eqValT_app₃_annotS (ψ : Name → Nat) (ρ : Nat → V)
    (A a b : VExpr) (hAA : AnnotOkV V ρ A) (haA : AnnotOkV V ρ a)
    (hbA : AnnotOkV V ρ b)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A)
    (hb : interp V ρ b ∈ˢ interp V ρ A) :
    AnnotOkV V ρ (VExpr.mkAppN (eqValT ψ) [A, a, b]) := by
  have hm := eqValT_memS (V := V) ψ ρ
  simp only [VExpr.mkAppN, AnnotOkV_app]
  exact ⟨⟨⟨eqValT_annotS ψ ρ, hAA, _, _, hm, hA⟩, haA, _, _,
      app_mem_piC hm hA, ha⟩,
    hbA, _, _, app_mem_piC (app_mem_piC hm hA) ha, hb⟩

/-- The towers read the assignment only at their own level names. -/
theorem eqValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValT ψ₁ = eqValT ψ₂ := by rw [eqValT, eqValT, h]

theorem eqReflValT_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqReflValT ψ₁ = eqReflValT ψ₂ := by rw [eqReflValT, eqReflValT, h]

/-- `Eq.refl`'s tower, interpreted. -/
theorem eqReflValT_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValT ψ)
      = lamC (univ (ψ uN)) (fun a => lamC a (fun _ => pt)) := by
  simp [eqReflValT, interp_lam, interp_sort, interp_bvar, interp_prf,
    cons]

theorem eqReflValT_app₂S (ψ : Name → Nat) (ρ : Nat → V) (A a : VExpr)
    (hA : interp V ρ A ∈ˢ univ (ψ uN))
    (ha : interp V ρ a ∈ˢ interp V ρ A) :
    interp V ρ (VExpr.mkAppN (eqReflValT ψ) [A, a]) = pt := by
  show interp V ρ (.app (.app (eqReflValT ψ) A) a) = _
  rw [interp_app, interp_app, eqReflValT_interp, app_lamC hA,
    app_lamC ha]

theorem eqReflValT_memS (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValT ψ) ∈ˢ
      piC (univ (ψ uN)) (fun a => piC a (fun x => eqv x x)) := by
  rw [eqReflValT_interp]
  exact lamC_mem (fun _a _ => lamC_mem (fun x _ => pt_mem_eqv_self x))

theorem eqReflValT_annotS (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkV V ρ (eqReflValT ψ) := by
  simp [eqReflValT, AnnotOkV_lam, AnnotOkV_bvar, AnnotOkV_sort,
    AnnotOkV_prf]

/-- `Eq.rec`'s pinned type, as it denotes at the declaration's own
level parameters. -/
def eqRecTyV (ψ : Name → Nat) : VExpr :=
  .pi (.sort (ψ uN))
    (.pi (.bvar 0)
      (.pi (.pi (.bvar 1)
          (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.pi (.app (.app (.bvar 0) (.bvar 1))
            (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]))
          (.pi (.bvar 3)
            (.pi (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))

/-- **`Eq.rec`'s tower inhabits its type** — where the TT lane needs
`proofIrrel` and a `congrApp` pair, the [set] lane reads the transport
straight off the hypothesis: a member of `eqv a b` *is* a proof that
`a = b`, and it is `pt`. -/
theorem eqRecValT_memS (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqRecValT ψ) ∈ˢ interp V ρ (eqRecTyV ψ) := by
  simp only [eqRecValT, eqRecTyV, interp_lam, interp_pi, interp_sort,
    interp_bvar, interp_app, cons]
  refine lamC_mem (fun xa hxa => lamC_mem (fun xv hxv =>
    lamC_mem (fun xM hxM => lamC_mem (fun xh hxh =>
      lamC_mem (fun xb hxb => lamC_mem (fun xt hxt => ?_))))))
  have het : interp V (cons V xb (cons V xh (cons V xM
      (cons V xv (cons V xa ρ)))))
      (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
      = eqv xv xb := by
    rw [eqValT_app₃S ψ _ (.bvar 4) (.bvar 3) (.bvar 0)
      (by simpa [interp_bvar, cons] using hxa)
      (by simpa [interp_bvar, cons] using hxv)
      (by simpa [interp_bvar, cons] using hxb)]
    simp [interp_bvar, cons]
  rw [het] at hxt
  have hvb : xv = xb := mem_eqv hxt
  have hpt : xt = pt := mem_univ_zero (eqv_mem_univ _ _) hxt
  have herefl : interp V (cons V xM (cons V xv (cons V xa ρ)))
      (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]) = pt :=
    eqReflValT_app₂S ψ _ (.bvar 2) (.bvar 1)
      (by simpa [interp_bvar, cons] using hxa)
      (by simpa [interp_bvar, cons] using hxv)
  rw [herefl] at hxh
  rw [← hvb, hpt]
  simpa [interp_bvar, cons] using hxh

/-- …and the type is truthful. -/
theorem eqRecTyV_annotS (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkV V ρ (eqRecTyV ψ) := by
  simp only [eqRecTyV]
  refine ⟨trivial, fun xa hxa => ⟨trivial, fun xv hxv => ⟨?_,
    fun xM hxM => ⟨?_, fun xh _ => ⟨trivial, fun xb hxb => ⟨?_,
      fun xt hxt => ?_⟩⟩⟩⟩⟩⟩
  · -- the motive's type
    refine ⟨trivial, fun xb hxb => ⟨?_, fun _ _ => trivial⟩⟩
    exact eqValT_app₃_annotS ψ _ (.bvar 2) (.bvar 1) (.bvar 0)
      trivial trivial trivial
      (by simpa [interp_bvar, cons] using hxa)
      (by simpa [interp_bvar, cons] using hxv)
      (by simpa [interp_bvar, cons] using hxb)
  · -- the minor premise's type
    have het : interp V (cons V xv (cons V xv (cons V xa ρ)))
        (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
        = eqv xv xv := by
      rw [eqValT_app₃S ψ _ (.bvar 2) (.bvar 1) (.bvar 0)
        (by simpa [interp_bvar, cons] using hxa)
        (by simpa [interp_bvar, cons] using hxv)
        (by simpa [interp_bvar, cons] using hxv)]
      simp [interp_bvar, cons]
    have hxM' : xM ∈ˢ piC (interp V (cons V xv (cons V xa ρ))
          (VExpr.bvar 1))
        (fun xb' => piC (interp V (cons V xb' (cons V xv (cons V xa ρ)))
            (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0]))
          (fun _ => univ (ψ u1N))) := by
      simpa [interp_pi, interp_bvar, cons] using hxM
    have hxv0 : xv ∈ˢ interp V (cons V xv (cons V xa ρ))
        (VExpr.bvar 1) := by simpa [interp_bvar, cons] using hxv
    have hMapp : SetTheory.app xM xv ∈ˢ piC (eqv xv xv)
        (fun _ => univ (ψ u1N)) := by
      have h := app_mem_piC hxM' hxv0
      rwa [het] at h
    have hRm := eqReflValT_memS (V := V) ψ
      (cons V xM (cons V xv (cons V xa ρ)))
    have hxa' : interp V (cons V xM (cons V xv (cons V xa ρ)))
        (VExpr.bvar 2) ∈ˢ univ (ψ uN) := by
      simpa [interp_bvar, cons] using hxa
    have hxv' : interp V (cons V xM (cons V xv (cons V xa ρ)))
        (VExpr.bvar 1) ∈ˢ interp V (cons V xM (cons V xv
          (cons V xa ρ))) (VExpr.bvar 2) := by
      simpa [interp_bvar, cons] using hxv
    have hRA : AnnotOkV V (cons V xM (cons V xv (cons V xa ρ)))
        (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1]) := by
      simp only [VExpr.mkAppN, AnnotOkV_app]
      exact ⟨⟨eqReflValT_annotS ψ _, trivial, _, _, hRm, hxa'⟩,
        trivial, _, _, app_mem_piC hRm hxa', hxv'⟩
    have hRmem : interp V (cons V xM (cons V xv (cons V xa ρ)))
        (VExpr.mkAppN (eqReflValT ψ) [.bvar 2, .bvar 1])
        ∈ˢ eqv xv xv :=
      app_mem_piC (B := fun x => eqv x x)
        (app_mem_piC hRm hxa') hxv'
    simp only [AnnotOkV_app, AnnotOkV_bvar]
    exact ⟨⟨trivial, trivial, _, _, hxM', hxv0⟩, hRA,
      eqv xv xv, fun _ => univ (ψ u1N), hMapp, hRmem⟩
  · -- the hypothesis' type
    exact eqValT_app₃_annotS ψ _ (.bvar 4) (.bvar 3) (.bvar 0)
      trivial trivial trivial
      (by simpa [interp_bvar, cons] using hxa)
      (by simpa [interp_bvar, cons] using hxv)
      (by simpa [interp_bvar, cons] using hxb)
  · -- the conclusion
    have hxM' : xM ∈ˢ piC (interp V (cons V xv (cons V xa ρ))
          (VExpr.bvar 1))
        (fun xb' => piC (interp V (cons V xb' (cons V xv (cons V xa ρ)))
            (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0]))
          (fun _ => univ (ψ u1N))) := by
      simpa [interp_pi, interp_bvar, cons] using hxM
    have hxb' : xb ∈ˢ interp V (cons V xv (cons V xa ρ))
        (VExpr.bvar 1) := by simpa [interp_bvar, cons] using hxb
    have het2 : interp V (cons V xb (cons V xv (cons V xa ρ)))
        (VExpr.mkAppN (eqValT ψ) [.bvar 2, .bvar 1, .bvar 0])
        = eqv xv xb := by
      rw [eqValT_app₃S ψ _ (.bvar 2) (.bvar 1) (.bvar 0)
        (by simpa [interp_bvar, cons] using hxa)
        (by simpa [interp_bvar, cons] using hxv)
        (by simpa [interp_bvar, cons] using hxb)]
      simp [interp_bvar, cons]
    have het3 : interp V (cons V xb (cons V xh (cons V xM
          (cons V xv (cons V xa ρ)))))
        (VExpr.mkAppN (eqValT ψ) [.bvar 4, .bvar 3, .bvar 0])
        = eqv xv xb := by
      rw [eqValT_app₃S ψ _ (.bvar 4) (.bvar 3) (.bvar 0)
        (by simpa [interp_bvar, cons] using hxa)
        (by simpa [interp_bvar, cons] using hxv)
        (by simpa [interp_bvar, cons] using hxb)]
      simp [interp_bvar, cons]
    rw [het3] at hxt
    have hMapp2 : SetTheory.app xM xb ∈ˢ piC (eqv xv xb)
        (fun _ => univ (ψ u1N)) := by
      have h := app_mem_piC hxM' hxb'
      rwa [het2] at h
    simp only [AnnotOkV_app, AnnotOkV_bvar]
    exact ⟨⟨trivial, trivial, _, _, hxM', hxb'⟩, trivial,
      eqv xv xb, fun _ => univ (ψ u1N), hMapp2, hxt⟩

/-- `Eq.rec`'s tower is truthful: its lam domains are exactly the
type's pi domains, and its body is a variable. -/
theorem eqRecValT_annotS (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotOkV V ρ (eqRecValT ψ) := by
  obtain ⟨c1, c2⟩ := eqRecTyV_annotS (V := V) ψ ρ
  refine ⟨c1, fun x1 h1 => ?_⟩
  obtain ⟨d1, d2⟩ := c2 x1 h1
  refine ⟨d1, fun x2 h2 => ?_⟩
  obtain ⟨e1, e2⟩ := d2 x2 h2
  refine ⟨e1, fun x3 h3 => ?_⟩
  obtain ⟨f1, f2⟩ := e2 x3 h3
  refine ⟨f1, fun x4 h4 => ?_⟩
  obtain ⟨g1, g2⟩ := f2 x4 h4
  refine ⟨g1, fun x5 h5 => ?_⟩
  obtain ⟨i1, -⟩ := g2 x5 h5
  exact ⟨i1, fun _ _ => trivial⟩

/-- **`Eq`, installed** — and with it `EqLawV`, discharged from the
tower rather than assumed. -/
theorem extendEqS {env : Env} (m : EnvS V env)
    (hfresh : env.find? eqName = none)
    (hwf : EnvWF ⟨eqA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨eqA :: env.consts⟩,
      m'.cval = cvalWith m.cval eqA.name eqValT := by
  refine extendBasisS m (val := eqValT)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqA = eqName from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun ψ => eqValT_closed ψ) ?_
    (fun ψ ρ => eqValT_annotS ψ ρ) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq) ?_
  · intro φ₁ φ₂ hp
    exact eqValT_congr (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self))
  · intro φ
    refine ⟨.pi (.sort (φ uN)) (.pi (.bvar 0) (.pi (.bvar 1) (.sort 0))),
      ?_, fun ρ => ⟨?_, by simp [AnnotOkV_pi]⟩⟩
    · rw [denoteClosed,
        show eqA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
              (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
                (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                  (.sort .zero) { bi := .default }) { bi := .default })
              { bi := .implicit } from rfl]
      simp [denote_forallE, denote_sort, denote_fvar, Level.eval]
    · simpa [interp_pi, interp_sort, interp_bvar, cons]
        using eqValT_memS (V := V) φ ρ
  · -- **`EqLawV`**: the tower's two `app_lamC`s, plus its rigidity
    intro _ _ ψ
    rw [show cvalWith m.cval eqA.name eqValT eqName = eqValT from
      cvalWith_self (n := eqA.name)]
    exact ⟨fun ρ => eqValT_ne_pt ψ ρ,
      fun ρ A a hA ha => eqValT_lawS ψ ρ A a hA ha⟩

/-- **`Eq.refl`, installed** — `.prf` under two binders; its type is
the tower's own spine at a reflexive pair. -/
theorem extendEqReflS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hfresh : env.find? eqReflName = none)
    (hwf : EnvWF ⟨eqReflA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨eqReflA :: env.consts⟩,
      m'.cval = cvalWith m.cval eqReflA.name eqReflValT := by
  have hEc : ∀ (d : Nat) (φ : Name → Nat),
      denote (cvalWith m.cval eqReflA.name eqReflValT)
        ⟨eqReflA :: env.consts⟩ φ d (.const eqName [.param uN])
        = some (eqValT φ) := by
    intro d φ
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([Level.param uN] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (by decide),
      show Level.substFn φ eqA.toConstantVal.levelParams [Level.param uN]
        = φ from Level.substFn_param_self φ [uN], hEv]
  refine extendBasisS m (val := eqReflValT)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqReflA = eqReflName from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun ψ => eqReflValT_closed ψ) ?_
    (fun _ _ => by simp [eqReflValT, AnnotOkV_lam, AnnotOkV_bvar,
      AnnotOkV_sort, AnnotOkV_prf]) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    exact eqReflValT_congr
      (hp uN (by show uN ∈ [uN]; exact List.mem_cons_self))
  · intro φ
    refine ⟨.pi (.sort (φ uN)) (.pi (.bvar 0)
      (VExpr.mkAppN (eqValT φ) [.bvar 1, .bvar 0, .bvar 0])),
      ?_, fun ρ => ⟨?_, ?_⟩⟩
    · rw [denoteClosed,
        show eqReflA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
              (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
                (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.bvar 0)) { bi := .default })
              { bi := .implicit } from rfl]
      simp [denote_forallE, denote_sort, denote_app, denote_fvar,
        Level.eval, hEc, VExpr.mkAppN]
    · simp only [eqReflValT, interp_lam, interp_pi, interp_sort,
        interp_bvar, cons]
      refine lamC_mem (fun a ha => lamC_mem (fun x hx => ?_))
      rw [eqValT_app₃S φ (cons V x (cons V a ρ)) (.bvar 1) (.bvar 0)
        (.bvar 0) (by simpa [interp_bvar, cons] using ha)
        (by simpa [interp_bvar, cons] using hx)
        (by simpa [interp_bvar, cons] using hx)]
      exact pt_mem_eqv_self _
    · refine ⟨trivial, fun a ha => ⟨trivial, fun x hx => ?_⟩⟩
      exact eqValT_app₃_annotS φ (cons V x (cons V a ρ)) (.bvar 1)
        (.bvar 0) (.bvar 0) trivial trivial trivial
        (by simpa [interp_bvar, cons] using ha)
        (by simpa [interp_bvar, cons] using hx)
        (by simpa [interp_bvar, cons] using hx)


/-- **`Eq.rec`'s pinned type, denoted at any depth and any levels.**

The general form is the one `hheadRec` supplies at a fire site — depth
`d`, the recursor's own `us` — and the install's own `htype` is its
special case at depth `0` and the declaration's own parameters
(`Level.substFn_param_self`).  Written once for the same reason `BetaSpine`
and the `instantiate1` kit were: every block needs exactly this
shape. -/
theorem denote_eqRec_typeS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ) :
    denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ d
        (eqRecA.toConstantVal.type.instantiateLevelParams
          eqRecA.toConstantVal.levelParams [w1, w2])
      = some (.pi (.sort (w2.eval φ))
        (.pi (.bvar 0)
          (.pi (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.pi (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]))
              (.pi (.bvar 3)
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                    [.bvar 4, .bvar 3, .bvar 0])
                  (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)))))))) := by
  have hsu : Level.subst [u1N, uN] [w1, w2] (.param uN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, u1N]
  have hsu1 : Level.subst [u1N, uN] [w1, w2] (.param u1N) = w1 := by
    simp [Level.subst, Level.subst.go, u1N]
  have hEc : ∀ e : Nat,
      denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uN]) (.bvar 4))
                      (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default })
                  { bi := .implicit })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl,
    show eqRecA.toConstantVal.levelParams = [u1N, uN] from rfl]
  simp [Expr.instantiateLevelParams, hsu, hsu1, denote_forallE, denote_sort,
    denote_app, denote_fvar, hEc, hRc, VExpr.mkAppN]

/-- `Eq.rec`'s single stored rule. -/
def eqRecRule : RecRule :=
  { ctor := eqReflName, nfields := 0, ctorParams := 2, fire := .plain,
    rhs := Expr.lam (Name.anonymous.str "α") (.sort (.param uN))
      (Expr.lam (Name.anonymous.str "a") (.bvar 0)
        (Expr.lam (Name.anonymous.str "motive")
          (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
            (Expr.forallE (Name.anonymous.str "t")
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                (.bvar 1)) (.bvar 0))
              (.sort (.param u1N)) { bi := .default })
            { bi := .default })
          (Expr.lam (Name.anonymous.str "refl")
            (.app (.app (.bvar 0) (.bvar 1))
              (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                (.bvar 1)))
            (.bvar 0) { bi := .default })
          { bi := .default })
        { bi := .default })
      { bi := .implicit } }

/-- The stored declaration, with its rule named. -/
theorem eqRecA_eq :
    eqRecA = .recInfo eqRecA.toConstantVal 5 4 [eqRecRule] := rfl

/-- **`Eq.rec`'s rule right-hand side, denoted** — the same four
domains the type has, over the minor premise. -/
theorem denote_eqRec_rhsS {env : Env} (m : EnvS V env)
    {val : (Name → Nat) → VExpr} (φ : Name → Nat) (d : Nat)
    (w1 w2 : Level)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ) :
    denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ d
        ((RecRule.rhs eqRecRule).instantiateLevelParams
          eqRecA.toConstantVal.levelParams [w1, w2])
      = some (.lam (.sort (w2.eval φ))
        (.lam (.bvar 0)
          (.lam (.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (w1.eval φ))))
            (.lam (.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]))
              (.bvar 0))))) := by
  have hsu : Level.subst [u1N, uN] [w1, w2] (.param uN) = w2 := by
    simp [Level.subst, Level.subst.go, uN, u1N]
  have hsu1 : Level.subst [u1N, uN] [w1, w2] (.param u1N) = w1 := by
    simp [Level.subst, Level.subst.go, u1N]
  have hEc : ∀ e : Nat,
      denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqName [w2]) = some (eqValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hE]
    simp only [show ([w2] : List Level).length
      = eqA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (by decide), hEv]
    rfl
  have hRc : ∀ e : Nat,
      denote (cvalWith m.cval eqRecA.name val) ⟨eqRecA :: env.consts⟩ φ e
        (.const eqReflName [w2])
        = some (eqReflValT (Level.substFn φ [uN] [w2])) := by
    intro e
    rw [denote_const, Env.find?_cons, if_neg (by decide), hR]
    simp only [show ([w2] : List Level).length
      = eqReflA.toConstantVal.levelParams.length from rfl, if_true]
    rw [cvalWith_ne (by decide), hRv]
    rfl
  rw [show eqRecA.toConstantVal.levelParams = [u1N, uN] from rfl]
  simp only [eqRecRule]
  simp [Expr.instantiateLevelParams, hsu, hsu1, denote_lam, denote_forallE,
    denote_sort, denote_app, denote_fvar, hEc, hRc, VExpr.mkAppN]

set_option maxHeartbeats 1600000 in
/-- **`Eq.rec`, installed** — the block's whole iota is β, because the
layer derives the eliminator rather than carrying it.  Six `app_lamC`s
on the left, four on the right, meeting at the minor premise. -/
theorem extendEqRecS {env : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA)
    (hR : env.find? eqReflName = some eqReflA)
    (hEv : ∀ ψ : Name → Nat, m.cval eqName ψ = eqValT ψ)
    (hRv : ∀ ψ : Name → Nat, m.cval eqReflName ψ = eqReflValT ψ)
    (hfresh : env.find? (eqName.str "rec") = none)
    (hwf : EnvWF ⟨eqRecA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨eqRecA :: env.consts⟩,
      m'.cval = cvalWith m.cval eqRecA.name eqRecValT := by
  refine extendBasisS m (val := eqRecValT)
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun _ => by decide)
    (fun ψ t hp => by
      rw [show ConstantInfo.name eqRecA = eqName.str "rec" from rfl] at hp
      simp +decide [pinnedDirectT] at hp)
    hfresh hwf (fun ψ => eqRecValT_closed ψ) ?_
    (fun ψ ρ => eqRecValT_annotS ψ ρ) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun heq => nomatch heq) ?_ ?_
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · -- the valuation reads only `u` and `u_1`
    intro φ₁ φ₂ hp
    have hu : φ₁ uN = φ₂ uN := hp uN (by
      show uN ∈ [u1N, uN]
      exact List.mem_cons_of_mem _ List.mem_cons_self)
    rw [eqRecValT, eqRecValT, hu,
      hp u1N (by show u1N ∈ [u1N, uN]; exact List.mem_cons_self),
      eqValT_congr hu, eqReflValT_congr hu]
  · -- the pinned type, denoted
    intro φ
    refine ⟨eqRecTyV φ, ?_, fun ρ =>
      ⟨eqRecValT_memS (V := V) φ ρ, eqRecTyV_annotS (V := V) φ ρ⟩⟩
    rw [denoteClosed, ← Expr.instantiateLevelParams_self
        eqRecA.toConstantVal.levelParams eqRecA.toConstantVal.type,
      show eqRecA.toConstantVal.levelParams.map Level.param
        = [Level.param u1N, Level.param uN] from rfl,
      denote_eqRec_typeS m φ 0 (.param u1N) (.param uN) hE hR hEv hRv,
      show Level.substFn φ [uN] [Level.param uN] = φ from
        Level.substFn_param_self φ [uN]]
    rfl
  · -- the rule's constructor is stored
    intro cv mI rP rules heq
    injection heq with _ _ _ h4
    subst h4
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨eqReflA.toConstantVal, 2, 0, hR⟩
    · exact nomatch hr'
  · -- the iota rule
    intro cv mI rP rules heq
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    intro rl hrl _ φ
    rcases List.mem_cons.mp hrl with rfl | hr'
    · refine ⟨by omega, ?_⟩
      intro us hus
      obtain ⟨w1, w2, rfl⟩ : ∃ a b, us = [a, b] := by
        match us, hus with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      refine ⟨_, denote_eqRec_rhsS m (val := eqRecValT) φ 0 w1 w2 hE hR
        hEv hRv, ?_⟩
      intro cvj cnP cnF hfj usj ρ xs ys TV TVj restR restC hxs hys
        husj hlev hplain hnested hidx hTV hTVj hR' hC
      have hRu := hR
      simp only [eqReflName, eqName] at hRu
      rw [Env.find?_cons, if_neg (by decide), hRu] at hfj
      obtain ⟨rfl, rfl, rfl⟩ :
          cvj = eqReflA.toConstantVal ∧ cnP = 2 ∧ cnF = 0 := by
        injection Option.some.inj hfj with a1 a2 a3
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      obtain ⟨q1, q2, rfl⟩ : ∃ a b, ys = [a, b] := by
        match ys, hys with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      obtain ⟨xa, xv, xM, xh, xb, rfl⟩ :
          ∃ a b c e f, xs = [a, b, c, e, f] := by
        match xs, hxs with
        | [a, b, c, e, f], _ => exact ⟨a, b, c, e, f, rfl⟩
      have hTVc := Option.some.inj (hTV.symm.trans
        (denote_eqRec_typeS m (val := eqRecValT) φ 0 w1 w2 hE hR hEv hRv))
      subst hTVc
      have hctor : cvalWith m.cval eqRecA.name eqRecValT
          ((Name.anonymous.str "Eq").str "refl")
          (Level.substFn φ eqReflA.toConstantVal.levelParams usj)
          = eqReflValT (Level.substFn φ [uN] [w2]) := by
        have hRv' := hRv
        simp only [eqReflName, eqName] at hRv'
        rw [cvalWith_ne (by decide), hRv']
        refine eqReflValT_congr ?_
        have h := congrFun hlev uN
        simp only [recFireComparands] at h
        rw [h]
        rfl
      rw [hctor] at hR'
      cases hR' with | cons t1 hR' =>
      cases hR' with | cons t2 hR' =>
      cases hR' with | cons t3 hR' =>
      cases hR' with | cons t4 hR' =>
      cases hR' with | cons t5 hR' =>
      cases hR' with | cons t6 hR' =>
      simp +decide only [VExpr.mkAppN, VExpr.inst, 
        Nat.reduceAdd, Nat.reduceSub, reduceIte,
        inst_chain1, inst_absorb21,
        inst_absorb32, inst_absorb43, VExpr.liftN_zero,
        VExpr.inst_eq_self_of_closed
          (eqValT_closed (Level.substFn φ [uN] [w2])),
        VExpr.inst_eq_self_of_closed
          (eqReflValT_closed (Level.substFn φ [uN] [w2]))] at t1 t2 t3 t4 t5 t6
      have hu2 : Level.substFn φ [Name.anonymous.str "u_1",
          Name.anonymous.str "u"] [w1, w2] uN = Level.eval φ w2 := by
        simp [Level.substFn, uN]
      have hu1 : Level.substFn φ [Name.anonymous.str "u_1",
          Name.anonymous.str "u"] [w1, w2] u1N = Level.eval φ w1 := by
        simp [Level.substFn, u1N]
      have hψ2 : Level.substFn φ [uN] [w2] uN = Level.eval φ w2 := by
        simp [Level.substFn, uN]
      have hEV : eqValT (Level.substFn φ [Name.anonymous.str "u_1",
            Name.anonymous.str "u"] [w1, w2])
          = eqValT (Level.substFn φ [uN] [w2]) :=
        eqValT_congr (by rw [hu2, hψ2])
      have hRV : eqReflValT (Level.substFn φ [Name.anonymous.str "u_1",
            Name.anonymous.str "u"] [w1, w2])
          = eqReflValT (Level.substFn φ [uN] [w2]) :=
        eqReflValT_congr (by rw [hu2, hψ2])
      have hA2g : interp V (cons V (interp V ρ xa) ρ) (VExpr.bvar 0)
          = interp V ρ xa := by simp [interp_bvar, cons]
      have hA5g : interp V (cons V (interp V ρ xh) (cons V (interp V ρ xM)
            (cons V (interp V ρ xv) (cons V (interp V ρ xa) ρ))))
            (VExpr.bvar 3) = interp V ρ xa := by simp [interp_bvar, cons]
      -- the motive's space, in the layer's vocabulary
      have hA3t : interp V ρ (VExpr.pi xa
            (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                [VExpr.liftN 1 xa 0, VExpr.liftN 1 xv 0, .bvar 0])
              (.sort (Level.eval φ w1))))
          = piC (interp V ρ xa) (fun b => piC (eqv (interp V ρ xv) b)
              (fun _ => univ (Level.eval φ w1))) := by
        simp only [interp_pi, interp_sort]
        refine piC_congr (fun b hb => ?_)
        congr 1
        rw [eqValT_app₃S (Level.substFn φ [uN] [w2]) (cons V b ρ)
          (VExpr.liftN 1 xa 0) (VExpr.liftN 1 xv 0) (.bvar 0)
          (by rw [interp_lift_cons (V := V) xa b ρ, hψ2]; simpa using t1)
          (by rw [interp_lift_cons (V := V) xv b ρ,
                interp_lift_cons (V := V) xa b ρ]; exact t2)
          (by rw [interp_lift_cons (V := V) xa b ρ, interp_bvar]
              simpa [cons] using hb)]
        rw [interp_lift_cons (V := V) xv b ρ, interp_bvar]
        simp [cons]
      have hA3g : interp V (cons V (interp V ρ xv)
            (cons V (interp V ρ xa) ρ))
            (VExpr.pi (.bvar 1)
              (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0])
                (.sort (Level.eval φ w1))))
          = piC (interp V ρ xa) (fun b => piC (eqv (interp V ρ xv) b)
              (fun _ => univ (Level.eval φ w1))) := by
        simp only [interp_pi, interp_sort, interp_bvar, cons]
        refine piC_congr (fun b hb => ?_)
        congr 1
        rw [eqValT_app₃S (Level.substFn φ [uN] [w2])
          (cons V b (cons V (interp V ρ xv) (cons V (interp V ρ xa) ρ)))
          (.bvar 2) (.bvar 1) (.bvar 0)
          (by rw [interp_bvar, hψ2]; simpa [cons] using t1)
          (by rw [interp_bvar, interp_bvar]; simpa [cons] using t2)
          (by rw [interp_bvar, interp_bvar]; simpa [cons] using hb)]
        simp [interp_bvar, cons]
      -- the minor premise's space
      have hA4t : interp V ρ (VExpr.app (.app xM xv)
            (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
              [xa, xv]))
          = SetTheory.app (SetTheory.app (interp V ρ xM) (interp V ρ xv))
            pt := by
        rw [interp_app, interp_app,
          eqReflValT_app₂S (Level.substFn φ [uN] [w2]) ρ xa xv
            (by rw [hψ2]; simpa using t1) t2]
      have hA4g : interp V (cons V (interp V ρ xM)
            (cons V (interp V ρ xv) (cons V (interp V ρ xa) ρ)))
            (VExpr.app (.app (.bvar 0) (.bvar 1))
              (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                [.bvar 2, .bvar 1]))
          = SetTheory.app (SetTheory.app (interp V ρ xM) (interp V ρ xv))
            pt := by
        rw [interp_app, interp_app,
          eqReflValT_app₂S (Level.substFn φ [uN] [w2]) _ (.bvar 2)
            (.bvar 1) (by rw [interp_bvar, hψ2]; simpa [cons] using t1)
            (by rw [interp_bvar, interp_bvar]; simpa [cons] using t2)]
        simp [interp_bvar, cons]
      -- the hypothesis' space, and the equation it forces
      have hA6t : interp V ρ (VExpr.mkAppN
            (eqValT (Level.substFn φ [uN] [w2])) [xa, xv, xb])
          = eqv (interp V ρ xv) (interp V ρ xb) :=
        eqValT_app₃S (Level.substFn φ [uN] [w2]) ρ xa xv xb
          (by rw [hψ2]; simpa using t1) t2 t5
      have hA6g : interp V (cons V (interp V ρ xb)
            (cons V (interp V ρ xh) (cons V (interp V ρ xM)
              (cons V (interp V ρ xv) (cons V (interp V ρ xa) ρ)))))
            (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
              [.bvar 4, .bvar 3, .bvar 0])
          = eqv (interp V ρ xv) (interp V ρ xb) := by
        rw [eqValT_app₃S (Level.substFn φ [uN] [w2]) _ (.bvar 4)
          (.bvar 3) (.bvar 0)
          (by rw [interp_bvar, hψ2]; simpa [cons] using t1)
          (by rw [interp_bvar, interp_bvar]; simpa [cons] using t2)
          (by rw [interp_bvar, interp_bvar]; simpa [cons] using t5)]
        simp [interp_bvar, cons]
      simp only [VExpr.mkAppN] at hA3t hA4t hA6t hA3g hA4g hA6g
      have hA4g0 := hA4g
      simp only [interp_app] at hA4g hA6g
      rw [hA3t] at t3
      rw [hA4t] at t4
      rw [hA6t] at t6
      simp only [interp_app] at t6
      refine ⟨?_, ?_⟩
      · rw [cvalWith_self, hctor]
        simp only [List.take, List.drop, List.cons_append,
          List.nil_append]
        refine Eq.trans (b := interp V ρ xh) ?_ (Eq.symm ?_)
        · simp only [eqRecValT, hu2, hu1, hEV, hRV, VExpr.mkAppN,
            interp_lam, interp_app]
          rw [app_lamC t1, hA2g, app_lamC t2, hA3g, app_lamC t3, hA4g,
            app_lamC t4, hA5g, app_lamC t5, hA6g, app_lamC t6]
          simp [interp_bvar, cons]
        · simp only [VExpr.mkAppN, interp_lam, interp_app]
          rw [app_lamC t1, hA2g, app_lamC t2, hA3g, app_lamC t3, hA4g,
            app_lamC t4]
          simp [interp_bvar, cons]
      · intro hxsA hysA
        have haA : AnnotOkV V ρ xa := hxsA xa (by simp)
        have hvA : AnnotOkV V ρ xv := hxsA xv (by simp)
        have hMA : AnnotOkV V ρ xM := hxsA xM (by simp)
        have hhA : AnnotOkV V ρ xh := hxsA xh (by simp)
        have m2 : interp V ρ xv ∈ˢ
            interp V (cons V (interp V ρ xa) ρ) (VExpr.bvar 0) := by
          rw [hA2g]; exact t2
        have m3 : interp V ρ xM ∈ˢ
            interp V (cons V (interp V ρ xv) (cons V (interp V ρ xa) ρ))
              (VExpr.pi (.bvar 1)
                (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                    [.bvar 2, .bvar 1, .bvar 0])
                  (.sort (Level.eval φ w1)))) := by
          simp only [VExpr.mkAppN]
          rw [hA3g]; exact t3
        have m4 : interp V ρ xh ∈ˢ
            interp V (cons V (interp V ρ xM) (cons V (interp V ρ xv)
              (cons V (interp V ρ xa) ρ)))
              (VExpr.app (.app (.bvar 0) (.bvar 1))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1])) := by
          simp only [VExpr.mkAppN]
          rw [hA4g0]; exact t4
        have hRA : AnnotOkV V ρ
            (VExpr.lam (.sort (Level.eval φ w2))
              (.lam (.bvar 0)
                (.lam (.pi (.bvar 1)
                    (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                        [.bvar 2, .bvar 1, .bvar 0])
                      (.sort (Level.eval φ w1))))
                  (.lam (.app (.app (.bvar 0) (.bvar 1))
                      (VExpr.mkAppN
                        (eqReflValT (Level.substFn φ [uN] [w2]))
                        [.bvar 2, .bvar 1]))
                    (.bvar 0))))) := by
          refine ⟨trivial, fun x1 h1 => ⟨trivial, fun x2 h2 => ⟨?_,
            fun x3 h3 => ⟨?_, fun _ _ => trivial⟩⟩⟩⟩
          · refine ⟨trivial, fun b hb => ⟨?_, fun _ _ => trivial⟩⟩
            exact eqValT_app₃_annotS (Level.substFn φ [uN] [w2]) _
              (.bvar 2) (.bvar 1) (.bvar 0) trivial trivial trivial
              (by rw [interp_bvar, hψ2]; simpa [cons] using h1)
              (by rw [interp_bvar, interp_bvar]; simpa [cons] using h2)
              (by rw [interp_bvar, interp_bvar]; simpa [cons] using hb)
          · have hRm2 := eqReflValT_memS (V := V)
              (Level.substFn φ [uN] [w2])
              (cons V x3 (cons V x2 (cons V x1 ρ)))
            have hx1' : interp V (cons V x3 (cons V x2 (cons V x1 ρ)))
                (VExpr.bvar 2) ∈ˢ univ (Level.substFn φ [uN] [w2] uN) := by
              rw [interp_bvar, hψ2]; simpa [cons] using h1
            have hx2' : interp V (cons V x3 (cons V x2 (cons V x1 ρ)))
                (VExpr.bvar 1) ∈ˢ interp V (cons V x3 (cons V x2
                  (cons V x1 ρ))) (VExpr.bvar 2) := by
              rw [interp_bvar, interp_bvar]; simpa [cons] using h2
            have hx3' : x3 ∈ˢ piC (interp V (cons V x2 (cons V x1 ρ))
                  (VExpr.bvar 1))
                (fun b => piC (interp V (cons V b (cons V x2
                    (cons V x1 ρ)))
                    (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                      [.bvar 2, .bvar 1, .bvar 0]))
                  (fun _ => univ (Level.eval φ w1))) := by
              simpa [interp_pi, interp_sort] using h3
            have het : interp V (cons V x2 (cons V x2 (cons V x1 ρ)))
                (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1, .bvar 0]) = eqv x2 x2 := by
              rw [eqValT_app₃S (Level.substFn φ [uN] [w2]) _ (.bvar 2)
                (.bvar 1) (.bvar 0)
                (by rw [interp_bvar, hψ2]; simpa [cons] using h1)
                (by rw [interp_bvar, interp_bvar]; simpa [cons] using h2)
                (by rw [interp_bvar, interp_bvar]; simpa [cons] using h2)]
              simp [interp_bvar, cons]
            have hx2b : x2 ∈ˢ interp V (cons V x2 (cons V x1 ρ))
                (VExpr.bvar 1) := by simpa [interp_bvar, cons] using h2
            have hMapp : SetTheory.app x3 x2 ∈ˢ piC (eqv x2 x2)
                (fun _ => univ (Level.eval φ w1)) := by
              have h := app_mem_piC hx3' hx2b
              rwa [het] at h
            have hRmem : interp V (cons V x3 (cons V x2 (cons V x1 ρ)))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]) ∈ˢ eqv x2 x2 :=
              app_mem_piC (B := fun x => eqv x x)
                (app_mem_piC hRm2 hx1') hx2'
            have hRA2 : AnnotOkV V (cons V x3 (cons V x2 (cons V x1 ρ)))
                (VExpr.mkAppN (eqReflValT (Level.substFn φ [uN] [w2]))
                  [.bvar 2, .bvar 1]) := by
              simp only [VExpr.mkAppN, AnnotOkV_app]
              exact ⟨⟨eqReflValT_annotS _ _, trivial, _, _, hRm2, hx1'⟩,
                trivial, _, _, app_mem_piC hRm2 hx1', hx2'⟩
            simp only [AnnotOkV_app, AnnotOkV_bvar]
            exact ⟨⟨trivial, trivial, _, _, hx3', hx2b⟩, hRA2,
              eqv x2 x2, fun _ => univ (Level.eval φ w1), hMapp, hRmem⟩
        have hRm : interp V ρ
            (VExpr.lam (.sort (Level.eval φ w2))
              (.lam (.bvar 0)
                (.lam (.pi (.bvar 1)
                    (.pi (VExpr.mkAppN (eqValT (Level.substFn φ [uN] [w2]))
                        [.bvar 2, .bvar 1, .bvar 0])
                      (.sort (Level.eval φ w1))))
                  (.lam (.app (.app (.bvar 0) (.bvar 1))
                      (VExpr.mkAppN
                        (eqReflValT (Level.substFn φ [uN] [w2]))
                        [.bvar 2, .bvar 1]))
                    (.bvar 0))))) ∈ˢ
            piC (interp V ρ (VExpr.sort (Level.eval φ w2))) (fun x1 =>
              piC (interp V (cons V x1 ρ) (VExpr.bvar 0)) (fun x2 =>
                piC (interp V (cons V x2 (cons V x1 ρ))
                    (VExpr.pi (.bvar 1)
                      (.pi (VExpr.mkAppN
                          (eqValT (Level.substFn φ [uN] [w2]))
                          [.bvar 2, .bvar 1, .bvar 0])
                        (.sort (Level.eval φ w1))))) (fun x3 =>
                  piC (interp V (cons V x3 (cons V x2 (cons V x1 ρ)))
                      (VExpr.app (.app (.bvar 0) (.bvar 1))
                        (VExpr.mkAppN
                          (eqReflValT (Level.substFn φ [uN] [w2]))
                          [.bvar 2, .bvar 1])))
                    (fun _ => interp V (cons V x3 (cons V x2
                        (cons V x1 ρ)))
                      (VExpr.app (.app (.bvar 0) (.bvar 1))
                        (VExpr.mkAppN
                          (eqReflValT (Level.substFn φ [uN] [w2]))
                          [.bvar 2, .bvar 1])))))) := by
          simp only [interp_lam]
          exact lamC_mem (fun _ _ => lamC_mem (fun _ _ =>
            lamC_mem (fun _ _ => lamC_mem (fun _ h4 => h4))))
        simp only [List.take, List.drop, List.append_nil,
          VExpr.mkAppN_cons, VExpr.mkAppN_nil, AnnotOkV_app]
        exact ⟨⟨⟨⟨hRA, haA, _, _, hRm, t1⟩, hvA, _, _,
              app_mem_piC hRm t1, m2⟩, hMA, _, _,
            app_mem_piC (app_mem_piC hRm t1) m2, m3⟩, hhA, _, _,
          app_mem_piC (app_mem_piC (app_mem_piC hRm t1) m2) m3, m4⟩
    · exact nomatch hr'

/-- **The `Eq` block, installed.**  Two `BetaSpine`s meeting at the
minor premise are the whole of its iota — the block whose eliminator
the layer derives is the block whose install has no computation
obligation. -/
theorem declBasisS_eqK {env env₁ : Env} (m : EnvS V env)
    (h : BasisInstallR env BasisKind.eqK.declsA env₁) :
    Nonempty (EnvS V env₁) := by
  rw [show BasisKind.eqK.declsA = [eqA, eqReflA, eqRecA] from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hwf1 : EnvWF ⟨eqA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ := extendEqS m (Option.isNone_iff_eq_none.mp h1) hwf1
  have hE1 : (⟨eqA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hEv1 : ∀ ψ : Name → Nat, m1.cval eqName ψ = eqValT ψ := by
    intro ψ; rw [hm1]; rfl
  have hwf2 : EnvWF ⟨eqReflA :: eqA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ eqReflA.toConstantVal.type = true
    have hf : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE1
    rw [show eqReflA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
            (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
              (.app (.app (.app (.const eqName [.param uN]) (.bvar 1))
                (.bvar 0)) (.bvar 0)) { bi := .default })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, hm2⟩ := extendEqReflS m1 hE1 hEv1 (Option.isNone_iff_eq_none.mp h2) hwf2
  have hE2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE1
  have hR2 : (⟨eqReflA :: eqA :: env.consts⟩ : Env).find? eqReflName
      = some eqReflA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hEv2 : ∀ ψ : Name → Nat, m2.cval eqName ψ = eqValT ψ := by
    intro ψ
    rw [hm2, cvalWith_ne (by decide)]
    exact hEv1 ψ
  have hRv2 : ∀ ψ : Name → Nat, m2.cval eqReflName ψ = eqReflValT ψ := by
    intro ψ; rw [hm2]; rfl
  have hwf3 : EnvWF ⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ eqRecA.toConstantVal.type = true
    have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find? eqName
        = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
        eqReflName = some eqReflA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hR2
    rw [show eqRecA.toConstantVal.type = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "a") (.bvar 0)
            (Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "b") (.bvar 1)
                (Expr.forallE (Name.anonymous.str "t")
                  (.app (.app (.app (.const eqName [.param uN]) (.bvar 2))
                    (.bvar 1)) (.bvar 0))
                  (.sort (.param u1N)) { bi := .default })
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "refl")
                (.app (.app (.bvar 0) (.bvar 1))
                  (.app (.app (.const eqReflName [.param uN]) (.bvar 2))
                    (.bvar 1)))
                (Expr.forallE (Name.anonymous.str "b") (.bvar 3)
                  (Expr.forallE (Name.anonymous.str "t")
                    (.app (.app (.app (.const eqName [.param uN]) (.bvar 4))
                      (.bvar 3)) (.bvar 0))
                    (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
                    { bi := .default })
                  { bi := .implicit })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfE, hfR]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h4'
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
      · subst h1'; rfl
      · have hfE : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
            eqName = some eqA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hE2
        have hfR : (⟨eqRecA :: eqReflA :: eqA :: env.consts⟩ : Env).find?
            eqReflName = some eqReflA := by
          rw [Env.find?_cons, if_neg (by decide)]; exact hR2
        show Expr.constsResolve _ (RecRule.rhs eqRecRule) = true
        simp [Expr.constsResolve, eqRecRule, hfE, hfR]
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendEqRecS m2 hE2 hR2 hEv2 hRv2 (Option.isNone_iff_eq_none.mp h3) hwf3
  exact ⟨m3⟩

/-- **`Quot.sound`, installed** — the block's stored *axiom*.  No
rules; the whole content is the `Eq`-bridged type. -/
theorem extendQuotSoundS {env : Env} (m : EnvS V env)
    (hQ : env.find? quotName = some quotA)
    (hM : env.find? quotMkName = some quotMkA)
    (hE : env.find? eqName = some eqA)
    (hfresh : env.find? quotSoundName = none)
    (hwf : EnvWF ⟨quotSoundA :: env.consts⟩) :
    ∃ m' : EnvS V ⟨quotSoundA :: env.consts⟩,
      m'.cval = cvalWith m.cval quotSoundA.name
        (fun ψ => VExpr.const .quotSound [ψ uN]) := by
  refine extendBasisS m (val := fun ψ => VExpr.const .quotSound [ψ uN])
    (basisEtaVacuousS m (by decide)) (basisUnitVacuousS m (by decide))
    (fun h => nomatch h)
    (fun ψ t hp => by
      rw [show ConstantInfo.name quotSoundA = quotSoundName
        from rfl] at hp
      simp +decide [pinnedDirectT] at hp
      exact hp)
    hfresh hwf (fun _ => trivial) ?_ (fun _ _ => trivial) ?_
    (fun _ _ _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun _ _ hmem => absurd hmem (by decide)) (fun heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
    (fun heq => nomatch heq)
  · intro φ₁ φ₂ hp
    rw [hp uN (by show uN ∈ [uN]; exact List.mem_cons_self)]
  · intro φ
    refine ⟨quotSoundTyV
      (m.cval eqName (Level.substFn φ [uN] [Level.param uN])) (φ uN),
      ?_, fun ρ => ⟨?_, quotSoundTy_annotS m hE
        (Level.substFn φ [uN] [Level.param uN]) ρ (φ uN) rfl⟩⟩
    · rw [denoteClosed, ← Expr.instantiateLevelParams_self
          quotSoundA.toConstantVal.levelParams
          quotSoundA.toConstantVal.type,
        show quotSoundA.toConstantVal.levelParams.map Level.param
          = [Level.param uN] from rfl,
        denote_quotSound_typeS m φ 0 (.param uN) hQ hM hE]
      simp [Level.eval]
    · rw [quotSoundTy_interpS m hE
        (Level.substFn φ [uN] [Level.param uN]) ρ (φ uN) rfl]
      exact HasType.sound (V := V) HasType.const ρ (Sat_nil V ρ)


theorem declBasisS_quotK {env env₁ : Env} (m : EnvS V env)
    (hE : env.find? eqName = some eqA)
    (h : BasisInstallR env BasisKind.quotK.declsA env₁) :
    Nonempty (EnvS V env₁) := by
  rw [show BasisKind.quotK.declsA
    = [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] from rfl] at h
  obtain ⟨h1, h2, h3, h4, h5, hnil⟩ := h
  subst hnil
  have hwf1 : EnvWF ⟨quotA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendQuotS m (Option.isNone_iff_eq_none.mp h1) hwf1
  have hQ1 : (⟨quotA :: env.consts⟩ : Env).find? quotName = some quotA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hE1 : (⟨quotA :: env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE
  have hwf2 : EnvWF ⟨quotMkA :: quotA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ quotMkA.toConstantVal.type = true
    have hf : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
        = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ1
    rw [show quotMkA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (.app (.app (.const quotName [.param uN]) (.bvar 2))
                (.bvar 1)) { bi := .default })
            { bi := .default })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, -⟩ := extendQuotMkS m1 hQ1 (Option.isNone_iff_eq_none.mp h2) hwf2
  have hQ2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotName
      = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ1
  have hM2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? quotMkName
      = some quotMkA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hE2 : (⟨quotMkA :: quotA :: env.consts⟩ : Env).find? eqName
      = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE1
  have hwf3 : EnvWF ⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec3,
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ quotLiftA.toConstantVal.type = true
    have hfQ : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
    have hfE : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    rw [show quotLiftA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β") (.sort (.param vN))
              (Expr.forallE (Name.anonymous.str "f")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2) (.bvar 1)
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "a")
                  (Expr.forallE (Name.anonymous.str "a") (.bvar 3)
                    (Expr.forallE (Name.anonymous.str "b") (.bvar 4)
                      (Expr.forallE (Name.anonymous.str "a")
                        (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
                        (.app (.app (.app (.const eqName [.param vN])
                          (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
                          (.app (.bvar 3) (.bvar 1)))
                        { bi := .default }) { bi := .default })
                    { bi := .default })
                  (Expr.forallE (Name.anonymous.str "a")
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3))
                    (.bvar 3) { bi := .default })
                  { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfE]
  case rec3 =>
    intro cv mI rP rules heq
    injection heq with h1' _ _ h4'
    subst h1'; subst h4'
    have hfQ : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
    have hfE : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
        eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE2
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨rfl, rfl, by
        show Expr.constsResolve _ (RecRule.rhs quotLiftRule) = true
        simp [Expr.constsResolve, quotLiftRule, hfE], rfl,
        fun lvls pins heqf => nomatch heqf⟩
    · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendQuotLiftS m2 hQ2 hM2 hE2 (Option.isNone_iff_eq_none.mp h3) hwf3
  have hQ3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotName = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ2
  have hM3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      quotMkName = some quotMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM2
  have hE3 : (⟨quotLiftA :: quotMkA :: quotA :: env.consts⟩ : Env).find?
      eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE2
  have hwf4 : EnvWF ⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ :=
    EnvWF.cons hwf3 ⟨rfl, rfl, ?res4, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec4,
      (fun _ _ heq => nomatch heq)⟩
  case res4 =>
    show Expr.constsResolve _ quotIndA.toConstantVal.type = true
    have hfQ : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
    have hfM : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM3
    rw [show quotIndA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "a")
                (.app (.app (.const quotName [.param uN]) (.bvar 1))
                  (.bvar 0)) (.sort .zero) { bi := .default })
              (Expr.forallE (Name.anonymous.str "mk")
                (Expr.forallE (Name.anonymous.str "a") (.bvar 2)
                  (.app (.bvar 1)
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 3)) (.bvar 2)) (.bvar 0)))
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "q")
                  (.app (.app (.const quotName [.param uN]) (.bvar 3))
                    (.bvar 2))
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfM]
  case rec4 =>
    intro cv mI rP rules heq
    injection heq with h1' _ _ h4'
    subst h1'; subst h4'
    have hfQ : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
    have hfM : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM3
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact ⟨rfl, rfl, by
        show Expr.constsResolve _ (RecRule.rhs quotIndRule) = true
        simp [Expr.constsResolve, quotIndRule, hfQ, hfM], rfl,
        fun lvls pins heqf => nomatch heqf⟩
    · exact nomatch hr'
  obtain ⟨m4, -⟩ := extendQuotIndS m3 hQ3 hM3 (Option.isNone_iff_eq_none.mp h4) hwf4
  have hQ4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? quotName = some quotA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hQ3
  have hM4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? quotMkName = some quotMkA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hM3
  have hE4 : (⟨quotIndA :: quotLiftA :: quotMkA :: quotA ::
      env.consts⟩ : Env).find? eqName = some eqA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hE3
  have hwf5 : EnvWF ⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA ::
      quotA :: env.consts⟩ :=
    EnvWF.cons hwf4 ⟨rfl, rfl, ?res5, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res5 =>
    show Expr.constsResolve _ quotSoundA.toConstantVal.type = true
    have hfQ : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotName = some quotA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hQ4
    have hfM : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? quotMkName = some quotMkA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hM4
    have hfE : (⟨quotSoundA :: quotIndA :: quotLiftA :: quotMkA :: quotA ::
        env.consts⟩ : Env).find? eqName = some eqA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hE4
    rw [show quotSoundA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "α") (.sort (.param uN))
          (Expr.forallE (Name.anonymous.str "r")
            (Expr.forallE Name.anonymous (.bvar 0)
              (Expr.forallE Name.anonymous (.bvar 1) (.sort .zero)
                { bi := .default }) { bi := .default })
            (Expr.forallE (Name.anonymous.str "a") (.bvar 1)
              (Expr.forallE (Name.anonymous.str "b") (.bvar 2)
                (Expr.forallE Name.anonymous
                  (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))
                  (.app (.app (.app (.const eqName [.param uN])
                    (.app (.app (.const quotName [.param uN]) (.bvar 4))
                      (.bvar 3)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 2)))
                    (.app (.app (.app (.const quotMkName [.param uN])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)))
                  { bi := .default }) { bi := .implicit })
              { bi := .implicit })
            { bi := .implicit })
          { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfQ, hfM, hfE]
  obtain ⟨m5, -⟩ := extendQuotSoundS m4 hQ4 hM4 hE4 (Option.isNone_iff_eq_none.mp h5) hwf5
  exact ⟨m5⟩

/-- **The `Nat` block, installed.** -/
theorem declBasisS_natK {env env₁ : Env} (m : EnvS V env)
    (h : BasisInstallR env BasisKind.natK.declsA env₁) :
    Nonempty (EnvS V env₁) := by
  rw [show BasisKind.natK.declsA = [natA, natZeroA, natSuccA, natRecA]
    from rfl] at h
  obtain ⟨h1, h2, h3, h4, hnil⟩ := h
  subst hnil
  have hwf1 : EnvWF ⟨natA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, -⟩ := extendNatS m (Option.isNone_iff_eq_none.mp h1) hwf1
  have hN1 : (⟨natA :: env.consts⟩ : Env).find? natName = some natA :=
    by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨natZeroA :: natA :: env.consts⟩ :=
    EnvWF.cons hwf1 ⟨rfl, rfl, ?res2, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res2 =>
    show Expr.constsResolve _ natZeroA.toConstantVal.type = true
    have hf : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
        = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN1
    rw [show natZeroA.toConstantVal.type = Expr.const natName [] from
      rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m2, -⟩ := extendNatZeroS m1 hN1 (Option.isNone_iff_eq_none.mp
    h2) hwf2
  have hN2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natName
      = some natA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hN1
  have hZ2 : (⟨natZeroA :: natA :: env.consts⟩ : Env).find? natZeroName
      = some natZeroA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf3 : EnvWF ⟨natSuccA :: natZeroA :: natA :: env.consts⟩ :=
    EnvWF.cons hwf2 ⟨rfl, rfl, ?res3, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  case res3 =>
    show Expr.constsResolve _ natSuccA.toConstantVal.type = true
    have hf : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
        natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN2
    rw [show natSuccA.toConstantVal.type
      = Expr.forallE (Name.anonymous.str "n") (.const natName [])
        (.const natName []) { bi := .default } from rfl]
    simp [Expr.constsResolve, hf]
  obtain ⟨m3, -⟩ := extendNatSuccS m2 hN2 (Option.isNone_iff_eq_none.mp
    h3) hwf3
  have hN3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natName = some natA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hN2
  have hZ3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natZeroName = some natZeroA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hZ2
  have hS3 : (⟨natSuccA :: natZeroA :: natA :: env.consts⟩ : Env).find?
      natSuccName = some natSuccA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf4 : EnvWF ⟨natRecA :: natSuccA :: natZeroA :: natA ::
    env.consts⟩ :=
    EnvWF.cons hwf3 ⟨rfl, rfl, ?res4, rfl,
      (fun _ _ _ heq => nomatch heq), ?rec4,
      (fun _ _ heq => nomatch heq)⟩
  case res4 =>
    show Expr.constsResolve _ natRecA.toConstantVal.type = true
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natZeroName = some natZeroA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natSuccName = some natSuccA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hS3
    rw [show natRecA.toConstantVal.type
        = Expr.forallE (Name.anonymous.str "motive")
            (Expr.forallE (Name.anonymous.str "t") (.const natName [])
              (.sort (.param uN)) { bi := .default })
            (Expr.forallE (Name.anonymous.str "zero")
              (.app (.bvar 0) (.const natZeroName []))
              (Expr.forallE (Name.anonymous.str "succ")
                (Expr.forallE (Name.anonymous.str "n") (.const natName
                  [])
                  (Expr.forallE (Name.anonymous.str "n_ih")
                    (.app (.bvar 2) (.bvar 0))
                    (.app (.bvar 3)
                      (.app (.const natSuccName []) (.bvar 1)))
                    { bi := .default })
                  { bi := .default })
                (Expr.forallE (Name.anonymous.str "t") (.const natName
                  [])
                  (.app (.bvar 3) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .default })
            { bi := .implicit } from rfl]
    simp [Expr.constsResolve, hfN, hfZ, hfS]
  case rec4 =>
    intro cv mI rP rules heq
    injection heq with h1' h2' h3' h4'
    subst h4'
    have hfN : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natName = some natA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hN3
    have hfZ : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natZeroName = some natZeroA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hZ3
    have hfS : (⟨natRecA :: natSuccA :: natZeroA :: natA :: env.consts⟩
      :
        Env).find? natSuccName = some natSuccA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hS3
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
      · subst h1'; rfl
      · show Expr.constsResolve _ (RecRule.rhs natRecZeroRule) = true
        simp [Expr.constsResolve, natRecZeroRule, hfN, hfZ, hfS]
    · rcases List.mem_cons.mp hr' with rfl | hr''
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ (RecRule.rhs natRecSuccRule) = true
          have hfR : (⟨natRecA :: natSuccA :: natZeroA :: natA ::
              env.consts⟩ : Env).find? (natName.str "rec")
              = some natRecA := by
            rw [Env.find?_cons]; exact if_pos rfl
          simp [Expr.constsResolve, natRecSuccRule, hfN, hfZ, hfS, hfR]
      · exact nomatch hr''
  obtain ⟨m4, -⟩ := extendNatRecS m3 hN3 hZ3 hS3
    (Option.isNone_iff_eq_none.mp h4) hwf4
  exact ⟨m4⟩

/-- **The `PUnit` block, installed.** -/
theorem declBasisS_punitK {env env₂ : Env} (m : EnvS V env)
    (h : BasisInstallR env BasisKind.punitK.declsA env₂) :
    Nonempty (EnvS V env₂) := by
  rw [show BasisKind.punitK.declsA = [punitA, punitUnitA, punitRecA]
    from rfl] at h
  obtain ⟨h1, h2, h3, hnil⟩ := h
  subst hnil
  have hwf1 : EnvWF ⟨punitA :: env.consts⟩ :=
    EnvWF.cons m.wf ⟨rfl, rfl, rfl, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
  obtain ⟨m1, hm1⟩ :=
    extendPUnitS m (Option.isNone_iff_eq_none.mp h1) hwf1
  have hP1 : (⟨punitA :: env.consts⟩ : Env).find? punitName
      = some punitA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hwf2 : EnvWF ⟨punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf1 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), (fun _ _ _ _ heq => nomatch heq),
      (fun _ _ heq => nomatch heq)⟩
    show Expr.constsResolve _ punitUnitA.toConstantVal.type = true
    have hf : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
        punitName = some punitA := by
      rw [Env.find?_cons, if_neg (by decide)]; exact hP1
    simp only [show punitUnitA.toConstantVal.type
        = Expr.const punitName [.param uN] from rfl,
      Expr.constsResolve, hf]
    rfl
  obtain ⟨m2, hm2⟩ := extendPUnitUnitS m1 hP1
    (Option.isNone_iff_eq_none.mp h2) hwf2
  have hP2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitName = some punitA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP1
  have hU2 : (⟨punitUnitA :: punitA :: env.consts⟩ : Env).find?
      punitUnitName = some punitUnitA := by
    rw [Env.find?_cons]; exact if_pos rfl
  have hfP : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitName = some punitA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hP2
  have hfU : (⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩
      : Env).find? punitUnitName = some punitUnitA := by
    rw [Env.find?_cons, if_neg (by decide)]; exact hU2
  have hwf3 : EnvWF
      ⟨punitRecA :: punitUnitA :: punitA :: env.consts⟩ := by
    refine EnvWF.cons hwf2 ⟨rfl, rfl, ?_, rfl,
      (fun _ _ _ heq => nomatch heq), ?_,
      (fun _ _ heq => nomatch heq)⟩
    · show Expr.constsResolve _ punitRecA.toConstantVal.type = true
      rw [show punitRecA.toConstantVal.type
          = Expr.forallE (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN]) (.sort (.param u1N))
                { bi := .default })
              (Expr.forallE (Name.anonymous.str "unit")
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (Expr.forallE (Name.anonymous.str "t")
                  (.const punitName [.param uN])
                  (.app (.bvar 2) (.bvar 0)) { bi := .default })
                { bi := .default })
              { bi := .implicit } from rfl]
      simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
        Bool.and_self]
    · intro cv mI rP rules heq
      injection heq with h1' h2' h3' h4'
      subst h4'
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · refine ⟨rfl, ?_, ?_, rfl, fun lvls pins heqf => nomatch heqf⟩
        · subst h1'; rfl
        · show Expr.constsResolve _ (Expr.lam
              (Name.anonymous.str "motive")
              (Expr.forallE (Name.anonymous.str "t")
                (.const punitName [.param uN]) (.sort (.param u1N))
                { bi := .default })
              (Expr.lam (Name.anonymous.str "unit")
                (.app (.bvar 0) (.const punitUnitName [.param uN]))
                (.bvar 0) { bi := .default })
              { bi := .default }) = true
          simp only [Expr.constsResolve, hfP, hfU, Option.isSome_some,
            Bool.and_self]
      · exact nomatch hr'
  obtain ⟨m3, -⟩ := extendPUnitRecS m2 (by rw [hm2] at *; exact hP2)
    (by rw [hm2] at *; exact hU2)
    (Option.isNone_iff_eq_none.mp h3) hwf3
  exact ⟨m3⟩

end Setlec.SetR
