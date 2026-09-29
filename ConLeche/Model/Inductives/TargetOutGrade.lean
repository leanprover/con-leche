module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.IndDomGrade
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Semantics.Tower.SumTower

public section

/-!
# The instantiated constructor is GRADED at an outside class

An outside class's rule certificates (`BlockRuleCerts`) grade the rule's
frame: the prefix, then the fields of the container's constructor at the
major's instantiation `C.{us} ds`.  No recorded clause fact grades a
constructor's fields; the grading comes from the constructor's STORED
type, whose reading is graded (`type_wellDenotedV`), peeled along the
parameters' readings — which fit the constructor's own parameter binders
by `LfpCtorReads` (the constructor's parameters are the block's) at the
key frame the major's parameters satisfy (`tgtOutSat`).

* `wdV_mkPisAV_dom`/`wdV_mkPisAV_body` — a graded tower's domains and
  body are graded along fitting spines;
* **`tgtOutCrestWd`** — the instantiated constructor's reading at the
  rule prefix is graded at every prefix spine fitting the rule's prefix
  domains.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Towers -/

/-- A graded Π-tower's domains are graded along fitting spines. -/
theorem wdV_mkPisAV_dom :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {σ : Nat → V},
      WellDenotedV V σ (mkPisAV ds b) → ∀ l, l < ds.length → ∀ ys : List V,
      SpineFit σ ((ds.map (·.2.2)).take l) ys →
      WellDenotedV V (consList ys σ) ((ds.map (·.2.2)).getD l default)
  | [], _, _, _, l, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | d :: ds, b, σ, h, 0, _, ys, hys => by
    have hy : ys = [] := by
      have := hys.length_eq; simpa using this
    subst hy
    exact WellDenotedV_pi_dom h
  | d :: ds, b, σ, h, l + 1, hl, ys, hys => by
    match ys, hys with
    | y :: ys', hys =>
      simp only [List.map_cons, List.take_succ_cons] at hys
      obtain ⟨hy, hys'⟩ := hys
      have hb := WellDenotedV_pi_body h hy
      have := wdV_mkPisAV_dom hb l (by simpa using hl) ys' hys'
      simpa [consList_cons] using this

/-- A graded Π-tower's body is graded along fitting spines. -/
theorem wdV_mkPisAV_body :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm} {σ : Nat → V},
      WellDenotedV V σ (mkPisAV ds b) → ∀ ys : List V,
      SpineFit σ (ds.map (·.2.2)) ys → WellDenotedV V (consList ys σ) b
  | [], _, _, h, ys, hys => by
    have hy : ys = [] := by
      have := hys.length_eq; simpa using this
    subst hy
    exact h
  | d :: ds, b, σ, h, ys, hys => by
    match ys, hys with
    | y :: ys', hys =>
      simp only [List.map_cons] at hys
      obtain ⟨hy, hys'⟩ := hys
      have := wdV_mkPisAV_body (WellDenotedV_pi_body h hy) ys' hys'
      simpa [consList_cons] using this

/-! ## The instantiated constructor, graded -/

section Crest

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

end Crest

end ConLeche.Model
