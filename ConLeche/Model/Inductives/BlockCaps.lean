module

public import ConLeche.Model.Inductives.FixKit
import ConLeche.Kernel.Inductives.BlockInstall
public section

/-!
# A block member's capability record, read

`blockCapsAt p₁ mi isRec` is the record every member's former carries;
it claims η only at a member with EXACTLY ONE constructor and no index
(`blockCapsAt_cases`), and counts the member's telescope
(`blockCapsAt_telescope`).  The η law itself is the member's projection
table's (`TowerTableLaw`), established at the table's install.
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

/-- The record a member carries, by its constructor list: η is claimable
only at EXACTLY ONE constructor. -/
theorem blockCapsAt_cases (p₁ : BlockShape) (mi : Nat) (isRec : Bool) :
    (∃ c : ConstantVal × Nat, (p₁.members.getD mi default).ctors = [c] ∧
      ConLeche.blockCapsAt p₁ mi isRec =
        { eta := (p₁.members.getD mi default).nIdx == 0 && !isRec
          all := p₁.memberNames
          nparams := p₁.nP
          nIdx := (p₁.members.getD mi default).nIdx
          ctors := [c.1.name]
          neverZero := (formerZ (p₁.members.getD mi default).declared).isNever }) ∨
    ConLeche.blockCapsAt p₁ mi isRec =
      {
        all := p₁.memberNames
        nparams := p₁.nP
        nIdx := (p₁.members.getD mi default).nIdx
        ctors := (p₁.members.getD mi default).ctors.map fun c => c.1.name
        neverZero := (formerZ (p₁.members.getD mi default).declared).isNever } := by
  unfold ConLeche.blockCapsAt
  split
  · next a b hc => exact Or.inl ⟨b, hc, rfl⟩
  · exact Or.inr rfl

end ConLeche.Model
