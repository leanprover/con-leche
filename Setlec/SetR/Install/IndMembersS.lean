import Setlec.SetR.Install.IndMemberS
import Setlec.SetR.Install.EtaLawS
import Setlec.Verify.Extend.Block
import Setlec.Verify.Extend.Iota

/-!
# The block-member fold (task #148, T5, `declIndS` stage 2)

`indMembersS` runs `indMemberS` along `IndMembersR`, carrying the
running valuation (finding 5's resolution) and the block invariant
`BlockInstalledTT` — the [set] lane reuses the TT lane's, verbatim,
since it is `TConstVal`-stated and V-free.

Two obligations stay named, because their suppliers sit outside the
fold:

* `MemberKeyS` — the member's *semantic* content: the model
  artifact's value inhabits the member's (renamed) type.  Supplier:
  the model definition's own `mem_type`, transported across
  `MemberValR`'s `eqUpToNames` pin using the block invariant to
  identify the public names' valuations with the model names'.
* `MemberEtaS` / `MemberUnitS` — the capability head obligations
  `EnvS.cons` asks of *any* install that could complete an eta or
  unit-like family.  They are vacuous at every member but the one that
  completes the family (`EtaFamilyStored` is false until then), and at
  that member the block assembly discharges them through
  `etaLawKeyS`/`unitLawKeyS`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The block member's key**: the model artifact's value inhabits
the checked member's type, truthfully, at the running valuation. -/
def MemberKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (m : EnvS V env) {cv cvA : ConstantVal},
    MemberValR μ F env m.cval blockNames cv cvA →
    BlockInstalledTT blockNames env m.cval →
    ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cvA.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.cval (cvA.name.str "_model") ψ) ∈ˢ interp V ρ t ∧
        AnnotOkV V ρ t

/-- **The eta head obligation at a member install.** -/
def MemberEtaS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cvA : ConstantVal}, c₀.name = cvA.name →
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawV V ⟨c₀ :: env.consts⟩ (cvalModeled m.cval cvA.name)
        T cvT caps

/-- **The unit-like head obligation at a member install** (T5 stage 4).

Re-signed with the premises its discharge needs.  The `caps` an
install stores are not free data — they are `indBlockCaps`' output,
whose two Booleans invert to the checked artifacts' shape pins.  That
inversion is `EtaPins`, and without it `caps.unitlike = true` says
nothing at all.  The block fold carries it (`EtaPins.step` at each
member); `DeclIndR`'s `indBlockCaps` binding is where it is created. -/
def MemberUnitS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (m : EnvS V env) {cv cvA : ConstantVal} {caps : IndCaps},
    MemberValR μ F env m.cval blockNames cv cvA →
    BlockInstalledTT blockNames env m.cval →
    blockNames.contains cvA.name = true →
    EtaPins μ env cvA.name cvA.levelParams caps →
    caps.unitlike = true →
    reservedBasisNames.contains cvA.name = false →
    UnitLawV V ⟨.indInfo cvA caps :: env.consts⟩
      (cvalModeled m.cval cvA.name) cvA.name cvA caps

set_option maxHeartbeats 1600000 in
/-- **`MemberUnitS`, discharged** (T5 stage 4): `unitLawKeyS`, run one
environment ahead (finding 6), over `EtaPins`' unit half.

Nothing here is a case split — the unit-like law is the *easy* half of
the pair, because it fabricates no side: both of its subjects are
given, so the only work is moving the model's facts onto the installed
valuation and handing `unitLawKeyS` its pins. -/
theorem memberUnitS : MemberUnitS V := by
  intro μ F blockNames env m cv cvA caps hmv hI hbn hpins hcapu hnres
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, -, -, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  -- the install this member is
  have hi : Installs env m.cval (cvalModeled m.cval cvA.name)
      (.indInfo cvA caps) :=
    Installs.of_fresh hfreshA (fun n hn => by
      rw [cvalModeled, cvalWith_ne (show n ≠ cvA.name from hn)])
  have hcl : ∀ (n : Name) (ψ : Name → Nat),
      VExpr.Closed (cvalModeled m.cval cvA.name n ψ) := by
    intro n ψ
    by_cases hn : n = cvA.name
    · subst hn
      rw [cvalModeled, cvalWith_self]
      exact m.cval_closed _ _
    · rw [cvalModeled, cvalWith_ne hn]
      exact m.cval_closed _ _
  have hresT : ∀ us : List Level,
      (cvA.type.instantiateLevelParams cvA.levelParams us).constsResolve
        env = true := by
    intro us
    rw [Expr.constsResolve_instantiateLevelParams, htypeA]
    exact htr
  -- the public/model identification at the head
  have hvT : ∀ ψ : Name → Nat,
      cvalModeled m.cval cvA.name cvA.name ψ
        = cvalModeled m.cval cvA.name (cvA.name.str "_model") ψ := by
    intro ψ
    simp only [cvalModeled, cvalWith_ne (Name.str_ne cvA.name "_model"),
      cvalWith_self]
  -- the block renaming, on the installed valuation
  have hroB := renameOkT_cvalStep hi
    (fun n hn => by simp only [hn]; rfl) hI.renameOkT
  have hrenT : RenEqT (fun n => if (env.find? n).isSome = true then
      (if blockNames.contains n then n.str "_model" else n) else n)
      cvA.type cvm.type := by
    unfold RenEqT
    rw [htypeA, Expr.renameConsts_congr_resolve
      (g := fun n => if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ htr, ← htypeA]
    exact Expr.ErasedEq.of_eqUpToNames hren
  obtain ⟨-, hunitPins⟩ := hpins
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, heqfE, hSstrip,
    hTstrip, hsdoms, hxdom, hydom, hsbody, htySlot, -⟩ :=
    hunitPins hcapu
  -- the two lookups of `T._model` agree
  have hcvmEq : cvm = cvmT := by
    obtain ⟨h1, -, -⟩ :=
      ConstantInfo.defnInfo.inj (Option.some.inj (hmE.symm.trans hTmE))
    exact h1
  rw [hcvmEq] at hrenT
  exact unitLawKeyS (V := V) m hi hcl hresT rfl rfl hthmE htlps hTmE
    hTmlps heqfE hSstrip hTstrip hsdoms hxdom hydom hsbody htySlot hvT
    hroB hrenT

/-- **One member installed, with the block invariant carried**: the
shared step of both block folds (the non-recursor members and the
recursor provisioning, whose entries are rule-less). -/
theorem memberInstallS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env : Env} (m : EnvS V env)
    {cv cvA : ConstantVal} {c₀ : ConstantInfo}
    (hmv : MemberValR μ F env m.cval blockNames cv cvA)
    (hI : BlockInstalledTT blockNames env m.cval)
    (hbn : blockNames.contains cvA.name = true)
    -- the block's capability artifacts, at *this* accumulator; the
    -- fold steps them up with `EtaPins.step` (T5 stage 4)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cv.name cv.levelParams caps)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP [])) :
    ∃ m₁ : EnvS V ⟨c₀ :: env.consts⟩,
      m₁.cval = cvalModeled m.cval cvA.name ∧
      BlockInstalledTT blockNames ⟨c₀ :: env.consts⟩
        (cvalModeled m.cval cvA.name) := by
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, -⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]
    exact Option.isNone_iff_eq_none.mp hfind
  have hnresA : reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres
  have hwf : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc₀cv, htypeA]; exact htf'
    · rw [hc₀cv, htypeA, hlpsA]; exact htp
    · rw [hc₀cv, htypeA]; exact Expr.constsResolve_mono htr
    · rw [hc₀cv, htypeA]; exact hbt'
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 h2 heq <;> exact nomatch heq
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 mI2 rP2 rules2 heq
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with _ _ _ h4
        intro r hr
        rw [← h4] at hr
        exact nomatch hr
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 heq <;> exact nomatch heq
  obtain ⟨m₁, hm₁⟩ := indMemberS m hc₀name hkind hfreshA hwf hnresA
    hmE hmlps (hkey m hmv hI) (heta m hc₀name)
    (fun cv2 caps2 hceq hcapu2 _ => by
      have hcv2 : cv2 = cvA := by rw [← hc₀cv, hceq]; rfl
      subst hcv2
      rw [hceq]
      exact memberUnitS m hmv hI hbn
        (by rw [hnameA, hlpsA]; exact hpins caps2 hceq) hcapu2 hnresA)
  refine ⟨m₁, hm₁, ?_⟩
  refine BlockInstalledTT.step hI (by rw [hc₀name]; exact hms)
    (by rw [hc₀name]; exact hmE)
    (by rw [hc₀cv]; exact hmlps)
    (by rw [hc₀cv]; exact hren)
    (fun ψ => by
      rw [hc₀name]
      exact congrFun cvalWith_self ψ)
    (fun n ψ hn => by
      rw [hc₀name] at hn
      exact congrFun (cvalWith_ne hn) ψ)

/-! ## The member fold's syntactic residue

The `DeclIndS` assembly needs to know what the fold *preserves*, not
just that it produces a model.  These two are the [set] analogues of
`checkIndFold_mono` / `checkIndMember_fold_names`
(`Verify/Extend/Ind.lean`); they are V-free and prove by the same
freshness chain `provisionRecsS_mono` uses. -/

/-- The member fold only extends. -/
theorem indMembersR_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (n : Name) (ci : ConstantInfo),
        env.find? n = some ci → env₂.find? n = some ci := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h n ci hf
    obtain ⟨rfl, rfl⟩ := h
    exact hf
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h n ci hf
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hfresh : env.find? cvA.name = none := by
      rw [show cvA.name = ci₀.toConstantVal.name by rw [hcvA]]
      exact Option.isNone_iff_eq_none.mp hcv.1
    cases ci₀ with
    | indInfo cv caps' =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .indInfo cvA caps) hfresh hf)
    | ctorInfo cv nP nF =>
      exact ih hmatch n ci
        (Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF) hfresh hf)
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- Every member the fold walks is stored at its end. -/
theorem indMembersR_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, (env₂.find? ci.name).isSome = true := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]
      cases ci₀ with
      | indInfo cv caps' =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.indInfo cvA caps) from
          indMembersR_mono rest hmatch _ _
            (Env.find?_cons_self (.indInfo cvA caps) env)]
        rfl
      | ctorInfo cv nP nF =>
        rw [show (env₂.find? cvA.name)
            = some (ConstantInfo.ctorInfo cvA nP nF) from
          indMembersR_mono rest hmatch _ _
            (Env.find?_cons_self (.ctorInfo cvA nP nF) env)]
        rfl
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- No member is stored *before* the fold runs. -/
theorem indMembersR_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, env.find? ci.name = none := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · -- a later member is fresh in the *accumulator*, hence here
      rcases hf : env.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        cases ci₀ with
        | indInfo cv caps' =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .indInfo cvA caps)
            hfresh hf] at hnone
          exact nomatch hnone
        | ctorInfo cv nP nF =>
          have hnone := ih hmatch ci hci'
          rw [Env.find?_cons_of_fresh (c := .ctorInfo cvA nP nF)
            hfresh hf] at hnone
          exact nomatch hnone
        | axiomInfo cv => exact nomatch hmatch
        | defnInfo cv v hint => exact nomatch hmatch
        | thmInfo cv v => exact nomatch hmatch
        | recInfo cv mI rP rules => exact nomatch hmatch
        | projInfo e => exact nomatch hmatch

/-- Each member's name passes `ConstantValR`'s two name guards. -/
theorem indMembersR_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ ci ∈ members, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h ci hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · cases ci₀ with
      | indInfo cv caps' => exact ih hmatch ci hci'
      | ctorInfo cv nP nF => exact ih hmatch ci hci'
      | axiomInfo cv => exact nomatch hmatch
      | defnInfo cv v hint => exact nomatch hmatch
      | thmInfo cv v => exact nomatch hmatch
      | recInfo cv mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- The former the fold walks is stored as an `.indInfo` at the
*block's* capability record, under an annotated `ConstantVal` with the
same name and level parameters. -/
theorem indMembersR_indEntry {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} {cval : TConstVal}
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env cval members env₂ cval₂ →
      ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        ∃ cvA : ConstantVal, cvA.name = cv.name ∧
          cvA.levelParams = cv.levelParams ∧
          env₂.find? cv.name = some (.indInfo cvA caps) := by
  intro members
  induction members with
  | nil =>
    intro env cval env₂ cval₂ h cv caps₂ hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro env cval env₂ cval₂ h cv caps₂ hci
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvA]
    have hlpsA : cvA.levelParams = ci₀.toConstantVal.levelParams := by
      rw [hcvA]
    have hfresh : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · subst heq
      refine ⟨cvA, hnameA, hlpsA, ?_⟩
      rw [show cv.name = cvA.name from hnameA.symm]
      exact indMembersR_mono rest hmatch _ _
        (Env.find?_cons_self (.indInfo cvA caps) env)
    · cases ci₀ with
      | indInfo cv' caps' => exact ih hmatch cv caps₂ hci'
      | ctorInfo cv' nP nF => exact ih hmatch cv caps₂ hci'
      | axiomInfo cv' => exact nomatch hmatch
      | defnInfo cv' v hint => exact nomatch hmatch
      | thmInfo cv' v => exact nomatch hmatch
      | recInfo cv' mI rP rules => exact nomatch hmatch
      | projInfo e => exact nomatch hmatch

/-- **The member fold**: the non-recursor block members install, the
running valuation ends at the fold's, and the block invariant holds
of the result. -/
theorem indMembersS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (m : EnvS V env)
      {env₂ : Env} {cval₂ : TConstVal},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      (∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        EtaPins μ env cv.name cv.levelParams caps) →
      IndMembersR μ F blockNames caps env m.cval members env₂ cval₂ →
      BlockInstalledTT blockNames env m.cval →
      ∃ m₂ : EnvS V env₂,
        m₂.cval = cval₂ ∧ BlockInstalledTT blockNames env₂ cval₂ := by
  intro members
  induction members with
  | nil =>
    intro env m env₂ cval₂ hbn hp h hI
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, rfl, hI⟩
  | cons ci rest ih =>
    intro env m env₂ cval₂ hbn hp h hI
    obtain ⟨cvA, hmv, hmatch⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    have hfreshA : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci List.mem_cons_self
    cases ci with
    | indInfo cv caps' =>
      obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
        hI hbnA
        (fun caps₃ heq => by
          obtain ⟨-, -, -, rfl⟩ := ConstantInfo.indInfo.inj heq
          exact hp cv caps' List.mem_cons_self)
        rfl rfl (Or.inl ⟨caps, rfl⟩)
      exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => EtaPins.step
          (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)) hfreshA)
        (by rw [hm₁cval]; exact hmatch)
        (by rw [hm₁cval]; exact hI₁)
    | ctorInfo cv nP nF =>
      obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
        hI hbnA (fun caps₃ heq => ConstantInfo.noConfusion heq)
        rfl rfl (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
      exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => EtaPins.step
          (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)) hfreshA)
        (by rw [hm₁cval]; exact hmatch)
        (by rw [hm₁cval]; exact hI₁)
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- **The recursor provisioning fold**: the group's recursors install
rule-less, giving the *self* environment the rule checks are run
against, its valuation, and the checked list. -/
theorem provisionRecsS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} (m : EnvS V envAcc)
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsR μ F blockNames envAcc m.cval recs envSelf cvalSelf
        checked →
      BlockInstalledTT blockNames envAcc m.cval →
      ∃ mS : EnvS V envSelf,
        mS.cval = cvalSelf ∧
        BlockInstalledTT blockNames envSelf cvalSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc m envSelf cvalSelf checked hbn h hI
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨m, rfl, hI⟩
  | cons ci rest ih =>
    intro envAcc m envSelf cvalSelf checked hbn h hI
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hrec, -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
      hI (by rw [hnameA]; exact hbn ci List.mem_cons_self)
      (fun caps₃ heq => ConstantInfo.noConfusion heq)
      rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
    exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
      (by rw [hm₁cval]; exact hrec)
      (by rw [hm₁cval]; exact hI₁)

end Setlec.SetR
