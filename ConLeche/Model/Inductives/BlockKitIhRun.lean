module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreHpre
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The counting guard at the run

The counting guard's reading at `w = 0` (`blockCountingGuard_run`),
consumed by the graph kit's step (`BlockRecGraph.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Pin

variable (pp : ConLeche.BlockParts)
  (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
  (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ψ : Name → Nat)

end Pin

section Key

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

end Key

section CountingGuard

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **The counting guard at `ℓ ≠ 0 ∧ w = 0`, from the run**: one
recursor, its member the block's first, at most one constructor, large
elimination — `blockRecCounting_run` at the checked level.  The graph
kit's `huniq` reads it at a `Prop` block with a large motive. -/
theorem blockCountingGuard_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hmr : BlockMembersRun mpC.base2 (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf)
      p.toBlockShape cvTas)
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).w ψ = 0) :
    rs.length = 1 ∧ p.toBlockShape.recTgtAt 0 = 0 ∧
      ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt 0)).length ≤ 1 ∧
      (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).large = true := by
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  obtain ⟨hpos, hklen⟩ := blockRecLen_run h
  obtain ⟨-, -, hlarge, hk1, hnc⟩ :=
    blockRecCounting_run h hruns ψ hℓ hw
  have hmemk := (blockRecMajor_run (hm := trivial) (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hpos) ψ).2.1
  have hk1d : (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).k = 1 := hk1
  rw [hk1d] at hmemk
  exact ⟨by rw [hklen, hk1], by omega,
    Nat.le_trans (blockRecNCt_seam (V := V) (pk := pk) (uOfD := uOfD)
      (ppsOf := ppsOf) h 0 hpos).2 hnc, hlarge⟩

end CountingGuard

end ConLeche.Model
