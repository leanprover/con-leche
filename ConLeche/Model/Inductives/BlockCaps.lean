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

Off the fieldless structure-like arm the record claims nothing that is
not vacuous: both laws are premised on having no field
(`capsLawsAt_vacuous`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape)

universe w'

variable {V : Type w'} [SetTheory V] {env : Env}

/-! ## Reading the record -/

/-- A member's capability record counts its telescope. -/
theorem blockCapsAt_telescope (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (blockCapsAt p mi isRec).nparams + (blockCapsAt p mi isRec).nIdx
      = p.nP + (p.members.getD mi default).nIdx := by
  unfold blockCapsAt
  split <;> rfl

/-- The record a member carries, by its constructor list: the
capability slots are filled only at EXACTLY ONE constructor. -/
theorem blockCapsAt_cases (p₁ : BlockShape) (mi : Nat) (isRec : Bool) :
    (∃ c : ConstantVal × Nat, (p₁.members.getD mi default).ctors = [c] ∧
      ConLeche.blockCapsAt p₁ mi isRec =
        { eta := (p₁.members.getD mi default).nIdx == 0 && !isRec
          etaCtor := c.1.name
          etaParams := p₁.nP
          etaFields := c.2
          all := p₁.memberNames
          nparams := p₁.nP
          nIdx := (p₁.members.getD mi default).nIdx
          ctors := [c.1.name] }) ∨
    ConLeche.blockCapsAt p₁ mi isRec =
      {
        all := p₁.memberNames
        nparams := p₁.nP
        nIdx := (p₁.members.getD mi default).nIdx
        ctors := (p₁.members.getD mi default).ctors.map fun c => c.1.name } := by
  unfold ConLeche.blockCapsAt
  split
  · next a b hc => exact Or.inl ⟨b, hc, rfl⟩
  · exact Or.inr rfl

/-- A fieldless η member: its constructor has no field, and the record
carries the block's parameter count. -/
theorem blockCapsAt_fieldless {p₁ : BlockShape} {mi : Nat} {isRec : Bool}
    (hu : (ConLeche.blockCapsAt p₁ mi isRec).eta = true ∧
      (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0) :
    (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0 ∧
    (ConLeche.blockCapsAt p₁ mi isRec).etaParams = p₁.nP := by
  rcases blockCapsAt_cases p₁ mi isRec with ⟨c, -, h⟩ | h
  · refine ⟨hu.2, ?_⟩
    rw [h]
  · rw [h] at hu; exact nomatch hu.1

/-! ## The laws -/

/-- **A block member's capability laws**, both arms — `blockCtorsLoop`'s
`hTlawsOf` at a member of a block.  On the structure-like arm the
member's leaf enters only through its FOLD at the fieldless shape
(`hfoldZ`); off it the record is
vacuous. -/
theorem blockCapsLawsAt {env' : Env} (m' : EnvModel V env')
    {p₁ : BlockShape} {mi : Nat} {isRec : Bool} {T : Name} {cvTa : ConstantVal}
    {w : (Name → Nat) → Nat} {pps ds : (Name → Nat) → List Term}
    {L : (Name → Nat) → Term}
    (hpar : ∀ ψ, p₁.nP = (pps ψ).length)
    (hleaf : ∀ ψ, m'.acval T ψ = L ψ)
    (hlam : ∀ ψ, ∃ B, L ψ = mkLamsAV (pps ψ) B)
    (hfoldZ : (ConLeche.blockCapsAt p₁ mi isRec).eta = true ∧
      (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0 →
      ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
        SpineFit ρ ((pps ψ)) ts →
        ts.foldl SetTheory.app (interp V ρ (L ψ))
          = sumSet (w ψ) (sumFibre (w ψ) (consList ts ρ) [[] ++ [idxEqAV []]]))
    (hleafC : (ConLeche.blockCapsAt p₁ mi isRec).eta = true ∧
      (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0 →
      ∀ ψ, m'.acval (ConLeche.blockCapsAt p₁ mi isRec).etaCtor ψ
        = sumMkAV (w ψ) 0 (ds ψ) [] (uChains [[]]))
    (hfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as : List V),
      SpineFit ρ ((pps ψ)) as → SpineFit ρ ((ds ψ)) as)
    (hreadC : (ConLeche.blockCapsAt p₁ mi isRec).eta = true ∧
      (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0 →
      ∀ (cvC : ConstantVal) (nPc nFc : Nat),
        env'.find? (ConLeche.blockCapsAt p₁ mi isRec).etaCtor
          = some (.ctorInfo cvC nPc nFc) →
        cvC.levelParams = cvTa.levelParams ∧ ∃ B : (Name → Nat) → Term,
          ∀ ψ, denote m'.acval env' ψ 0 cvC.type = some (mkPisAV (ds ψ) (B ψ))) :
    CapsLawsAt m' T cvTa (ConLeche.blockCapsAt p₁ mi isRec) := by
  by_cases hu : (ConLeche.blockCapsAt p₁ mi isRec).eta = true ∧
      (ConLeche.blockCapsAt p₁ mi isRec).etaFields = 0
  · have hpE := (blockCapsAt_fieldless hu).2
    exact ⟨fun _ _ _ => fibreEtaLaw0 hleaf (hfoldZ hu) (hleafC hu) hlam hfit
        (fun ψ => by rw [hpE]; exact hpar ψ) (hreadC hu),
      fun _ _ _ => fibreUnitLaw hleaf (hfoldZ hu) hlam
        (fun ψ => by rw [hpE]; exact hpar ψ)⟩
  · exact capsLawsAt_vacuous m' fun he => Nat.pos_of_ne_zero fun hz => hu ⟨he, hz⟩

end ConLeche.Model
