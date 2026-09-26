module

public import ConLeche.Model.Inductives.FixKit
import ConLeche.Kernel.Inductives.BlockInstall
public section

/-!
# A block member's capability laws

`blockCapsAt p₁ mi isRec` is the record every member's former carries,
and it claims a capability only at a member with EXACTLY ONE
constructor: η at no index, unit-likeness at no index and no field.
The P tier owes the laws from the member's cons on, and reads exactly
two things of the member's leaf — its FOLD at the fieldless shape, and
(for η) the constructor's — so `fibreUnitLaw`/`fibreEtaLaw0`
(`FixKit.lean`, leaf-abstract) discharge them at the member's hole
leaf (`blockTyG`), given its fold.

Off the structure-like arm the record claims nothing that is not
vacuous: a member with a field is never unit-like, and its η claim is
premised on the projection-function family being stored
(`blockCapsLawsAt_vacuous`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape)

universe w'

variable {V : Type w'} [SetTheory V] {env : Env}

/-! ## Reading the record -/

/-- The record a member carries, by its constructor list: the
capability slots are filled only at EXACTLY ONE constructor. -/
theorem blockCapsAt_cases (p₁ : BlockShape) (mi : Nat) (isRec : Bool) :
    (∃ c : ConstantVal × Nat, (p₁.members.getD mi default).ctors = [c] ∧
      ConLeche.blockCapsAt p₁ mi isRec =
        { eta := (p₁.members.getD mi default).nIdx == 0 && !p₁.isProp && !isRec
          etaCtor := c.1.name
          etaParams := p₁.nP
          etaFields := c.2
          unitlike := (p₁.members.getD mi default).nIdx == 0 && c.2 == 0 && !isRec
          unitParams := p₁.nP
          ruleK := p₁.k == 1 && c.2 == 0 && p₁.isProp
          sortZ := Level.zeronessOf p₁.resSort
          all := p₁.memberNames
          nparams := p₁.nP }) ∨
    ConLeche.blockCapsAt p₁ mi isRec = { all := p₁.memberNames, nparams := p₁.nP } := by
  unfold ConLeche.blockCapsAt
  split
  · next a b hc => exact Or.inl ⟨b, hc, rfl⟩
  · exact Or.inr rfl

/-- A unit-like member has no field and the block's parameter count in
both arithmetic slots. -/
theorem blockCapsAt_unitlike {p₁ : BlockShape} {mi : Nat} {isRec : Bool}
    (hu : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = true) :
    (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0 ∧
    (ConLeche.blockCapsAt p₁ mi isRec).etaParams = p₁.nP ∧
    (ConLeche.blockCapsAt p₁ mi isRec).unitParams = p₁.nP := by
  rcases blockCapsAt_cases p₁ mi isRec with ⟨c, -, h⟩ | h
  · rw [h] at hu ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at hu
    exact ⟨hu.1.2, rfl, rfl⟩
  · rw [h] at hu; exact nomatch hu

/-- A member claiming η but not unit-likeness has a field. -/
theorem blockCapsAt_etaFields_pos {p₁ : BlockShape} {mi : Nat} {isRec : Bool}
    (hU : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = false)
    (he : (ConLeche.blockCapsAt p₁ mi isRec).eta = true) :
    0 < (ConLeche.blockCapsAt p₁ mi isRec).etaFields := by
  rcases blockCapsAt_cases p₁ mi isRec with ⟨c, -, h⟩ | h
  · rw [h] at hU he ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hU
    show 0 < c.2
    rcases hU with (hU | hU) | hU
    · exact absurd he.1.1 hU
    · omega
    · exact nomatch he.2.symm.trans hU
  · rw [h] at he; exact nomatch he

/-! ## The laws -/

/-- **A member with a field owes nothing** while its projection-function
family is free (`capsLawsAt_vacuous` at a block member). -/
theorem blockCapsLawsAt_vacuous {env' : Env} (m' : EnvModel V env') {p₁ : BlockShape}
    {mi : Nat} {isRec : Bool} {T : Name} {cvTa : ConstantVal}
    (hU : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = false)
    (hfr : (ConLeche.blockCapsAt p₁ mi isRec).eta = true →
      env'.find? (projFnName T 0) = none) :
    CapsLawsAt m' T cvTa (ConLeche.blockCapsAt p₁ mi isRec) :=
  capsLawsAt_vacuous m' hU fun he => ⟨blockCapsAt_etaFields_pos hU he, hfr he⟩

/-- **A block member's capability laws**, both arms — `blockCtorsLoop`'s
`hTlawsOf` at a member of a block.  On the structure-like arm the
member's leaf enters only through its FOLD at the fieldless shape
(`hfoldZ`); off it the record is
vacuous. -/
theorem blockCapsLawsAt {env' : Env} (m' : EnvModel V env')
    {p₁ : BlockShape} {mi : Nat} {isRec : Bool} {T : Name} {cvTa : ConstantVal}
    {w : (Name → Nat) → Nat} {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {L : (Name → Nat) → AnnotTerm}
    (hfr : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = false →
      (ConLeche.blockCapsAt p₁ mi isRec).eta = true →
      env'.find? (projFnName T 0) = none)
    (hpar : ∀ ψ, p₁.nP = (pps ψ).length)
    (hleaf : ∀ ψ, m'.acval T ψ = L ψ)
    (hread : ∀ ψ, denoteMeta m'.acval env' ψ 0 cvTa.type
      = some (mkPisAV (pps ψ) (.sort (w ψ))))
    (hokTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (mkPisAV (pps ψ) (.sort (w ψ))))
    (hfoldZ : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = true →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((pps ψ).map (·.2.2)) ts →
        ts.foldl SetTheory.app (interp V ρ (L ψ))
          = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hleafC : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = true →
      ∀ ψ, m'.acval (ConLeche.blockCapsAt p₁ mi isRec).etaCtor ψ
        = sumMkAV (w ψ) 0 (ds ψ) [] (uChains [[]]))
    (hfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((pps ψ).map (·.2.2)) as → SpineFit ρ ((ds ψ).map (·.2.2)) as) :
    CapsLawsAt m' T cvTa (ConLeche.blockCapsAt p₁ mi isRec) := by
  by_cases hu : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = true
  · obtain ⟨hz, hpE, hpU⟩ := blockCapsAt_unitlike hu
    exact ⟨fun _ _ _ => fibreEtaLaw0 hz hleaf (hfoldZ hu) (hleafC hu) hread hokTy hfit
        (fun ψ => by rw [hpE]; exact hpar ψ),
      fun _ _ => fibreUnitLaw hleaf (hfoldZ hu) hread hokTy
        (fun ψ => by rw [hpU]; exact hpar ψ)⟩
  · have hU : (ConLeche.blockCapsAt p₁ mi isRec).unitlike = false := by simpa using hu
    exact blockCapsLawsAt_vacuous m' hU (hfr hU)

end ConLeche.Model
