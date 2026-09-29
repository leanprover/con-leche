module

public import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Verify.EnvBound
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# The rule rows at an OUTSIDE class, at the base frame

`tgtOutDec_core` (`TargetOutRow.lean`) is the decoding row at an outside
class under the class's reading premises; `tgtOutSat`
(`TargetOutSat.lean`) discharges them from the run.  This file fixes the
class's parameter readings as a FUNCTION of the level valuation
(`tgtOutDsa`, the unique reading of the major's parameters at the rule
prefix), factors the rule's opening of the instantiated constructor
(`tgtOutOpen`), and states the rows the graph producer reads at an
outside class, at the base frame and at a prefix spine fitting the
rule's prefix domains (the class's index set is guarded by that fit,
as a member class's is, `blockRecIs`):

* `tgtOutSpF` — `hspF`: a hole fit of the recorded constructor at the
  carrier of the key frame fits the rule's field domains;
* `tgtOutDec` — `hdec`: a spine fitting the rule's prefix and field
  domains hole-fits the constructor at the tuple of the class's index
  expressions, and the fired spine reads to the injection.
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

/-- **An outside major's parameters, read at the rule prefix** — a
function of the level valuation (the reading is unique,
`denoteMetaSpine_eq_map`). -/
@[expose] def tgtOutDsa (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (j : Nat) :
    List AnnotTerm :=
  (tgtMajor out j).ds.map fun x => (denoteMeta acval envC ψ (tgtRP p j) x).getD default

/-- A read spine is the list of its arguments' readings. -/
theorem denoteMetaSpine_eq_map {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      vs = as.map fun x => (denoteMeta acval env φ d x).getD default
  | [], _, .nil => rfl
  | _ :: _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, ← denoteMetaSpine_eq_map hs]

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {p : BlockShape}
  {nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **`targetOutsideInst`, inverted**: the major's inductive is stored,
its type instantiated at the levels and parameters is a telescope ending
in a sort, and the index count is that telescope's. -/
theorem targetOutsideInst_inv {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {r : Nat × Level}
    (h : ConLeche.targetOutsideInst (m := ConLeche.CheckM) fe I us ds = .ok r) :
    ∃ cvI caps ty s, fe.find? I = some (.indInfo cvI caps) ∧
      ConLeche.instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us) = some ty ∧
      ty.piBinders.2 = .sort s ∧ r = (ty.piBinders.1.length, s) := by
  unfold ConLeche.targetOutsideInst at h
  split at h
  · next cvI caps hf =>
    split at h
    · next ty hty =>
      simp only [pure, Except.pure] at h
      split at h
      · next s hs =>
        refine ⟨cvI, caps, ty, s, hf, hty, ?_, ?_⟩
        · rw [← hs]
        · exact (Except.ok.inj h).symm
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

end Rows

end ConLeche.Model
