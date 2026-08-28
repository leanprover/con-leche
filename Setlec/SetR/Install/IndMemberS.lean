import Setlec.SetR.Install.Step

/-!
# The block-member install (task #148, T5, `declIndS` stage 1)

`indMemberS` is `extendAxiomS`'s sibling for a **modeled block
member**: a checked non-recursor member (`.indInfo` / `.ctorInfo`)
extends the invariant, with its valuation taken from the model
artifact — `cval T ψ := cval (T._model) ψ`, which is exactly the
identification `etaLawKeyS`/`unitLawKeyS` consume as `hvT`/`hvC`.

The two capability head obligations stay **parameters**, as in the TT
lane (`checkIndMemberTT`): at a single member's install the family's
constructor and projections need not be stored yet, so the caller —
the block fold, which knows the whole block is in — is the only place
they can be discharged.  Everything else is vacuous by kind or refuted
by the member's non-reservedness.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **One block member, installed at the model's valuation.** -/
theorem indMemberS {env : Env} (m : EnvS V env) {c₀ : ConstantInfo}
    {cvA : ConstantVal}
    (hc₀name : c₀.name = cvA.name)
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF))
    (hfresh : env.find? cvA.name = none)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    (hnres : reservedBasisNames.contains cvA.name = false)
    -- the model artifact whose valuation the member takes
    {cvm : ConstantVal} {mval : Expr} {hint : ReducibilityHint}
    (hmE : env.find? (cvA.name.str "_model")
      = some (.defnInfo cvm mval hint))
    (hmlps : cvm.levelParams = cvA.levelParams)
    -- the member's type front door, at that valuation
    (hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cvA.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.cval (cvA.name.str "_model") ψ) ∈ˢ interp V ρ t ∧
        AnnotOkV V ρ t)
    -- the capability head obligations (the block fold's to discharge)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawV V ⟨c₀ :: env.consts⟩
        (cvalWith m.cval cvA.name
          (fun ψ => m.cval (cvA.name.str "_model") ψ)) T cvT caps)
    (hheadUnit : ∀ cv caps, c₀ = .indInfo cv caps →
      caps.unitlike = true →
      reservedBasisNames.contains c₀.name = false →
      UnitLawV V ⟨c₀ :: env.consts⟩
        (cvalWith m.cval cvA.name
          (fun ψ => m.cval (cvA.name.str "_model") ψ)) c₀.name cv caps) :
    Nonempty (EnvS V ⟨c₀ :: env.consts⟩) := by
  have hfresh' : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfresh
  have hnres' : reservedBasisNames.contains c₀.name = false := by
    rw [hc₀name]; exact hnres
  have hnrec : ∀ cv2 mI rP rules, c₀ ≠ .recInfo cv2 mI rP rules := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;>
      intro cv2 mI rP rules heq <;> exact nomatch heq
  have hnproj : ∀ entry, c₀ ≠ .projInfo entry := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;>
      intro entry heq <;> exact nomatch heq
  have hndefn : ∀ cv2 v2 h2, c₀ ≠ .defnInfo cv2 v2 h2 := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;>
      intro cv2 v2 h2 heq <;> exact nomatch heq
  have hnthm : ∀ cv2 v2, c₀ ≠ .thmInfo cv2 v2 := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;>
      intro cv2 v2 heq <;> exact nomatch heq
  have hnax : ∀ cv2, c₀ ≠ .axiomInfo cv2 := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;>
      intro cv2 heq <;> exact nomatch heq
  have hlpsA : c₀.toConstantVal.levelParams = cvA.levelParams := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;> rfl
  have hi : Installs env m.cval
      (cvalWith m.cval cvA.name
        (fun ψ => m.cval (cvA.name.str "_model") ψ)) c₀ :=
    Installs.of_fresh hfresh' (fun n hn => by
      rw [hc₀name] at hn
      exact (cvalWith_ne hn).symm)
  refine ⟨EnvS.cons m hi hwf ?_ ?_ ?_ ?_
    (fun cv2 v2 h2 heq => absurd heq (hndefn cv2 v2 h2))
    (fun cv2 v2 heq => absurd heq (hnthm cv2 v2))
    ?_
    (fun cv2 mI rP rules heq => absurd heq (hnrec cv2 mI rP rules))
    (fun cv2 mI rP rules heq => absurd heq (hnrec cv2 mI rP rules))
    hheadEta hheadUnit
    (fun entry heq => absurd heq (hnproj entry))
    (fun _ entry heq => absurd heq (hnproj entry))
    ?_ ?_
    (fun cv2 v2 h2 heq => absurd heq (hndefn cv2 v2 h2))
    (fun cv2 v2 h2 heq => absurd heq (hndefn cv2 v2 h2))
    (fun cv2 heq => absurd heq (hnax cv2))⟩
  · -- the model's valuation is closed
    intro ψ
    show VExpr.Closed (cvalWith m.cval cvA.name _ c₀.name ψ)
    rw [hc₀name, cvalWith_self]
    exact m.cval_closed _ _
  · -- it reads only the member's declared level parameters
    intro φ₁ φ₂ hp
    show cvalWith m.cval cvA.name _ c₀.name φ₁
      = cvalWith m.cval cvA.name _ c₀.name φ₂
    rw [hc₀name, cvalWith_self]
    refine m.val_params _ _ hmE φ₁ φ₂ ?_
    intro p hpm
    exact hp p (by rw [hlpsA, ← hmlps]; exact hpm)
  · -- and is truthful
    intro ψ ρ
    show AnnotOkV V ρ (cvalWith m.cval cvA.name _ c₀.name ψ)
    rw [hc₀name, cvalWith_self]
    exact m.annot_okV _ _ _
  · -- the type front door, transported up
    intro φ
    obtain ⟨t, ht, hd⟩ := hkey φ
    refine ⟨t, ?_, ?_⟩
    · have h := hi.denoteUp (φ := φ) (e := cvA.type) ht
      rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ <;> exact h
    · show ∀ ρ : Nat → V,
        interp V ρ (cvalWith m.cval cvA.name _ c₀.name φ)
          ∈ˢ interp V ρ t ∧ AnnotOkV V ρ t
      rw [hc₀name, cvalWith_self]
      exact hd
  · -- `Empty` is reserved
    intro hE
    have h : reservedBasisNames.contains emptyName = false := by
      rw [show emptyName = c₀.name from hE.symm]
      exact hnres'
    exact nomatch h
  · -- so is `Eq`
    intro hE
    rw [hE] at hnres'
    exact nomatch hnres'
  · -- and the member is not reserved at all
    intro hres
    rw [hres] at hnres'
    exact nomatch hnres'

end Setlec.SetR
