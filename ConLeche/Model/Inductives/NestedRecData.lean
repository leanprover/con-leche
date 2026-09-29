module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.CheckerF
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Verify.Level
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.InstSpine
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndOpenRev
import ConLeche.Model.Inductives.NestedRecPins
public import ConLeche.Model.Rules.RedSoundKit

public section

/-!
# The nested recursors' rule contract at every fired pair

`tgtRecDataB`: `BlockRuleDataB` at the target rule data
at every `(recursor, constructor)` pair whose stored rule fires.  The
contract's five conjuncts split as the `eqB` rows did:

* the FIRST three (the frame's fit, the index readings, the fired
  spine) are about the rule's DATA — at a member major the block's
  (`blockRuleData3_run`, through `tgt…_eq_block`), at an outside major
  the instantiated container constructor's (`tgtDataRows_out`);
* the last two (the residue at the `ih` values, the λ-tower's fit) are
  about the rule's RIGHT-HAND SIDE and hold at ANY major from the
  target rule run (`tgtRuleResidueCore`, `tgtRuleTowerFitG` below), given
  the first conjunct, the field readings (`hdF`) and the frame's
  grading (`hokPF`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Value-level fits along a peel -/

section Fits

open ConLeche.Model.Rules (PiChain piChain_succ_inv PiChain.inst)

/-- **The fit re-instantiates, under the ∀-chain guard** (the converse
of `teleFit_of_inst`). -/
theorem teleFit_inst_of {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      TeleFit V ρ (E.inst aa k) L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    rw [teleFit_nil_inv h, ← interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi]
    cases h with
    | cons hmem hfit =>
      refine .cons (by rw [interp_inst]; exact hmem) ?_
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      exact ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit

/-- `teleFit_inst_of` at the head binder. -/
theorem teleFit_inst0_of {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V (cons (interp V ρ aa) ρ) E L rest) :
    TeleFit V ρ (E.inst aa) L rest := by
  refine teleFit_inst_of (k := 0) hpc ?_
  rwa [shiftE_zero_zero, instE_zero]

/-- **A fit continues past a peel**: fitting a ∀-chain at a spine's
values followed by more values, the peel's residual fits the rest. -/
theorem teleFit_peel :
    ∀ (ws : List AnnotTerm) {T C : AnnotTerm} {σ : Nat → V} {fs : List V} {X : V},
      ConLeche.Model.AnnotTerm.peelPis T ws = some C →
      PiChain (ws.length + fs.length) T →
      TeleFit V σ T (ws.map (interp V σ) ++ fs) X → TeleFit V σ C fs X
  | [], T, C, σ, fs, X, hp, _, h => by
    obtain rfl : T = C := Option.some.inj hp
    simpa using h
  | w :: ws, T, C, σ, fs, X, hp, hpc, h => by
    have hpc' : PiChain ((ws.length + fs.length) + 1) T := by
      simpa [Nat.add_right_comm] using hpc
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc'
    simp only [ConLeche.Model.AnnotTerm.peelPis] at hp
    rw [List.map_cons, List.cons_append] at h
    cases h with
    | cons _ hfit =>
      exact teleFit_peel ws hp (PiChain.inst w 0 hB)
        (teleFit_inst0_of (by simpa using hB) hfit)

/-- **A fit moves between frames agreeing below the term's bound.** -/
theorem teleFit_congr_frame :
    ∀ (vals : List V) {T : AnnotTerm} {n : Nat} {ρ ρ' : Nat → V} {X : V},
      Term.bvarsBelow n T.erase → (∀ k, k < n → ρ k = ρ' k) →
      TeleFit V ρ T vals X → ∃ X', TeleFit V ρ' T vals X'
  | [], T, _, _, ρ', _, _, _, _ => ⟨_, .nil⟩
  | a :: as, _, n, ρ, ρ', X, hb, hag, h => by
    cases h with
    | cons hmem hfit =>
      simp only [AnnotTerm.erase_pi] at hb
      obtain ⟨hA, hB⟩ := hb
      obtain ⟨X', hX'⟩ := teleFit_congr_frame as (n := n + 1) (ρ := cons a ρ)
        (ρ' := cons a ρ') hB (fun k hk => by
          cases k with
          | zero => rfl
          | succ k => exact hag k (by omega)) hfit
      exact ⟨X', .cons (by rw [← interp_congr_below V _ n ρ ρ' hA hag]; exact hmem) hX'⟩

end Fits

section AnyMajor

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

/-! ## The λ-tower's fit, at any major -/

/-! ## The contract from its three DATA conjuncts, at any major -/

/-! ## The DATA rows at a MEMBER major -/

omit [SetTheory V] in
/-- **The counting guard at ANY majors** (`blockRecCounting_run` without
the family-size facts): at a `Prop` result and a non-zero elimination
level the recorded guard (`RecFamFacts.small`, the block's own bit) says
the declared shape is large and there is at most one constructor. -/
theorem blockRecCountG {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) {uOf : Nat → Level}
    (hruns : ∀ c, c < (tgtRs out).length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (pp.toBlockShape.majorIdxAt c + 1)
          ((tgtRs out).getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (pp.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (pp.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0)
    (hw : Level.eval ψ pp.toBlockShape.resSort = 0) {c : Nat} (hc : c < (tgtRs out).length) :
    pp.toBlockShape.large = true ∧ pp.toBlockShape.numCtors ≤ 1 := by
  obtain ⟨R'⟩ := id h
  have humem := blockRecUOf_run R' hruns hc
  have hu0 : Level.eval ψ (uOf c) ≠ 0 := by
    rw [blockRecElimPin_run h hruns ψ hc]; exact hℓ
  have hallow : ConLeche.blockLargeElimAllowed pp.toBlockShape false = true := by
    rcases R'.fam.small with hg | hzero
    · exact hg
    · exact absurd (ConLeche.Level.isEquiv_sound (hzero _ humem) ψ) hu0
  obtain ⟨hl, -, -, hcn⟩ := blockLargeElim_counting hallow hw
  exact ⟨hl, hcn⟩

/-! ## The `.nested` firing at an outside major: its levels and its pins' values -/

/-! ## The DATA rows at an OUTSIDE major -/

section Member

variable {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}

end Member

end AnyMajor

end ConLeche.Model
