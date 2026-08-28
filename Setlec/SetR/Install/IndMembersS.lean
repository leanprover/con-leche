import Setlec.SetR.Install.IndMemberS
import Setlec.Verify.Extend.Block

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

/-- **The unit-like head obligation at a member install.** -/
def MemberUnitS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cvA : ConstantVal}, c₀.name = cvA.name →
    ∀ cv caps, c₀ = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawV V ⟨c₀ :: env.consts⟩ (cvalModeled m.cval cvA.name)
        c₀.name cv caps

/-- **The member fold**: the non-recursor block members install, the
running valuation ends at the fold's, and the block invariant holds
of the result. -/
theorem indMembersS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    (hunit : MemberUnitS V) {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (m : EnvS V env)
      {env₂ : Env} {cval₂ : TConstVal},
      IndMembersR μ F blockNames caps env m.cval members env₂ cval₂ →
      BlockInstalledTT blockNames env m.cval →
      ∃ m₂ : EnvS V env₂,
        m₂.cval = cval₂ ∧ BlockInstalledTT blockNames env₂ cval₂ := by
  intro members
  induction members with
  | nil =>
    intro env m env₂ cval₂ h hI
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, rfl, hI⟩
  | cons ci rest ih =>
    intro env m env₂ cval₂ h hI
    obtain ⟨cvA, hmv, hmatch⟩ := h
    -- the member's checked data
    obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
      id hmv
    obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, -⟩ :=
      hcv
    obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
    have hnameA : cvA.name = ci.name := by rw [hcvA]; rfl
    have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by
      rw [hcvA]
    have htypeA : cvA.type = type' := by rw [hcvA]
    have hfreshA : env.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hfind
    have hnresA : reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]; exact hnres
    have hmsA : cvA.name.isModelSuffix = false := hms
    -- the shared install step, at either member kind
    have hstep : ∀ (c₀ : ConstantInfo), c₀.toConstantVal = cvA →
        c₀.name = cvA.name →
        ((∃ caps', c₀ = .indInfo cvA caps') ∨
          (∃ nP nF, c₀ = .ctorInfo cvA nP nF)) →
        ∃ m₁ : EnvS V ⟨c₀ :: env.consts⟩,
          m₁.cval = cvalModeled m.cval cvA.name ∧
          BlockInstalledTT blockNames ⟨c₀ :: env.consts⟩
            (cvalModeled m.cval cvA.name) := by
      intro c₀ hc₀cv hc₀name hkind
      have hwf : EnvWF ⟨c₀ :: env.consts⟩ := by
        refine EnvWF.cons m.wf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hc₀cv, htypeA]; exact htf'
        · rw [hc₀cv, htypeA, hlpsA]; exact htp
        · rw [hc₀cv, htypeA]; exact Expr.constsResolve_mono htr
        · rw [hc₀cv, htypeA]; exact hbt'
        · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ <;>
            intro cv2 v2 h2 heq <;> exact nomatch heq
        · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ <;>
            intro cv2 mI rP rules heq <;> exact nomatch heq
        · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ <;>
            intro cv2 v2 heq <;> exact nomatch heq
      obtain ⟨m₁, hm₁⟩ := indMemberS m hc₀name hkind hfreshA hwf hnresA
        hmE hmlps (hkey m hmv hI)
        (heta m hc₀name) (hunit m hc₀name)
      refine ⟨m₁, hm₁, ?_⟩
      refine BlockInstalledTT.step hI (by rw [hc₀name]; exact hmsA)
        (by rw [hc₀name]; exact hmE)
        (by rw [hc₀cv]; exact hmlps)
        (by rw [hc₀cv]; exact hren)
        (fun ψ => by
          rw [hc₀name]
          exact congrFun cvalWith_self ψ)
        (fun n ψ hn => by
          rw [hc₀name] at hn
          exact congrFun (cvalWith_ne hn) ψ)
    -- dispatch on the member's kind and recurse
    cases ci with
    | indInfo cv caps' =>
      obtain ⟨m₁, hm₁cval, hI₁⟩ := hstep (.indInfo cvA caps) rfl rfl
        (Or.inl ⟨caps, rfl⟩)
      have hrec : IndMembersR μ F blockNames caps
          ⟨ConstantInfo.indInfo cvA caps :: env.consts⟩ m₁.cval rest
          env₂ cval₂ := by
        rw [hm₁cval]; exact hmatch
      obtain ⟨m₂, hm₂, hI₂⟩ := ih m₁ hrec (by rw [hm₁cval]; exact hI₁)
      exact ⟨m₂, hm₂, hI₂⟩
    | ctorInfo cv nP nF =>
      obtain ⟨m₁, hm₁cval, hI₁⟩ := hstep (.ctorInfo cvA nP nF) rfl rfl
        (Or.inr ⟨nP, nF, rfl⟩)
      have hrec : IndMembersR μ F blockNames caps
          ⟨ConstantInfo.ctorInfo cvA nP nF :: env.consts⟩ m₁.cval rest
          env₂ cval₂ := by
        rw [hm₁cval]; exact hmatch
      obtain ⟨m₂, hm₂, hI₂⟩ := ih m₁ hrec (by rw [hm₁cval]; exact hI₁)
      exact ⟨m₂, hm₂, hI₂⟩
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

end Setlec.SetR
