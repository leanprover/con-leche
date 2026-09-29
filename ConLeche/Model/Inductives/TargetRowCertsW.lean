module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetRowCertsRun
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Capstone
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The certificates at the target data, at one rule

`BlockRuleCerts.of_segments` at the target check's `(c, j)`-th rule:
the prefix and field openings are the member rows' (both open the same
stored types), the `ih` openers are the target run's `ih`
variables, opened off a generated tower over their types
(`ihTeleOf`), the residue and the conclusion are the target run's
(`TargetRuleRun.hty`/`hdeq` at `bodyO`/`concl`).  The frame's grading
is the member rows' on the prefix and the fields (`blockRuleHokPF_run`) and, on
the `ih` block, each `ih` type's own inference at the frame
(`targetCall_ihTy_graded`), lifted past the earlier slots; the
conclusion is the recursor type's peel (`blockRuleCaAt_run`) at the
target width, graded as the member rows' (`blockRuleConclFitW_run`,
`blockRuleConclArgsW_run`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

omit [SetTheory V] in
theorem ihDomsLifted_length (Ts : List AnnotTerm) : (ihDomsLifted Ts).length = Ts.length := by
  simp [ihDomsLifted]

omit [SetTheory V] in
theorem ihDomsLifted_getD {Ts : List AnnotTerm} {q : Nat} (hq : q < Ts.length) :
    (ihDomsLifted Ts).getD q default = (Ts.getD q default).liftN q 0 := by
  rw [ihDomsLifted, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq]
  rfl

/-- An `ih` variable is a free variable at one of the `ih` types. -/
theorem mem_ihFvarsAt {B : Nat} {tys : List Expr} {x : Expr} (hx : x ∈ ihFvarsAt B tys) :
    ∃ i ty, x = Expr.fvar i ty ∧ ty ∈ tys := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hr' : r < tys.length := List.mem_range.mp hr
  refine ⟨B + r, tys.getD r default, rfl, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
  exact List.getElem_mem hr'

/-- **`hokA` from two segments**: the first graded as a whole, the
second under the first's values. -/
theorem hokA_of_two {PF I : List AnnotTerm}
    (hPF : ∀ l, l < PF.length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (PF.take l) ys → WellDenotedV V (consList ys σ) (PF.getD l default))
    (hI : ∀ q, q < I.length → ∀ (σ : Nat → V) (zs ys : List V),
      SpineFit σ PF zs → SpineFit (consList zs σ) (I.take q) ys →
      WellDenotedV V (consList ys (consList zs σ)) (I.getD q default)) :
    ∀ l, l < PF.length + I.length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((PF ++ I).take l) ys →
      WellDenotedV V (consList ys σ) ((PF ++ I).getD l default) := by
  intro l hl σ ys hys
  rcases Nat.lt_or_ge l PF.length with hlP | hlP
  · rw [List.take_append_of_le_length (by omega)] at hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlP, ← List.getD_eq_getElem?_getD]
    exact hPF l hlP σ ys hys
  · rw [List.take_append, List.take_of_length_le (by omega)] at hys
    obtain ⟨zs, ws, rfl, hzs, hws⟩ := spineFit_append_inv hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hlP, ← List.getD_eq_getElem?_getD,
      consList_append]
    exact hI (l - PF.length) (by omega) σ zs ws hzs hws

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

end Rows

end ConLeche.Model
