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
