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
