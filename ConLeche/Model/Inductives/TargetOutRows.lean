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

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-- **An outside major's parameters, read at the rule prefix** — a
function of the level valuation (the reading is unique,
`denoteSpine_eq_map`). -/
@[expose] def tgtOutDsa (acval : Name → (Name → Nat) → Term) (envC : Env) (p : BlockShape)
    (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (j : Nat) :
    List Term :=
  (tgtMajor out j).ds.map fun x => (denote acval envC ψ (tgtRP p j) x).getD default

/-- A read spine is the list of its arguments' readings. -/
theorem denoteSpine_eq_map {acval : Name → (Name → Nat) → Term} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List Term}, DenoteSpine acval env φ d as vs →
      vs = as.map fun x => (denote acval env φ d x).getD default
  | [], _, .nil => rfl
  | _ :: _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, ← denoteSpine_eq_map hs]

section Rows

variable {envC : Env} {mpC : EnvModelM V envC} {F : Nat} {p : BlockShape}
  {nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

/-- **`targetOutsideInst`, inverted**: the major's inductive is stored,
its telescope instantiated at the levels and parameters ends in a sort,
and the index count is that telescope's. -/
theorem targetOutsideInst_inv {ops : ConLeche.CheckerOps ConLeche.CheckM} {fe : FEnv} {I : Name}
    {us : List Level} {ds : List Expr} {r : Nat × Level}
    (h : ConLeche.targetOutsideInst ops fe I us ds = .ok r) :
    ∃ cvI caps tyI ty s, fe.find? I = some (.indInfo cvI caps) ∧
      ConLeche.familyTelescope ops fe.env cvI caps = .ok tyI ∧
      ConLeche.instPisWith ds (tyI.instantiateLevelParams cvI.levelParams us) = some ty ∧
      ty.piBinders.2 = .sort s ∧ r = (ty.piBinders.1.length, s) := by
  unfold ConLeche.targetOutsideInst at h
  split at h
  · next cvI caps hf =>
    simp only [Bind.bind, Except.bind] at h
    split at h
    · simp at h
    rename_i tyI hfam
    split at h
    · next ty hty =>
      simp only [pure, Except.pure] at h
      split at h
      · next s hs =>
        exact ⟨cvI, caps, tyI, ty, s, hf, hfam, hty, by rw [← hs], (Except.ok.inj h).symm⟩
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- **`targetOutsideInst` at a recorded class**, at the telescope the class's block read. -/
theorem TgtOutCls.outsideInst {env : Env} {mp : EnvModelM V env} {M : TargetMajor} {D : LfpDatum V}
    {mm : Nat} {cvI : ConstantVal} (hcl : TgtOutCls mp M D mm cvI) {F : Nat} {us : List Level}
    {ds : List Expr} {r : Nat × Level}
    (h : ConLeche.targetOutsideInst (ConLeche.fueledOps .verified F) (mkFEnv env) M.ind us ds = .ok r) :
    ∃ ty s, ConLeche.instPisWith ds ((D.formerAt mm cvI).type.instantiateLevelParams cvI.levelParams us)
        = some ty ∧ ty.piBinders.2 = .sort s ∧ r = (ty.piBinders.1.length, s) := by
  obtain ⟨cvI', caps', tyI, ty, s, hf', hfam, hty, hs, hr⟩ := targetOutsideInst_inv h
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [mkFEnv_find?, hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
  rw [hcl.family_eq hfI hfam] at hty
  exact ⟨ty, s, hty, hs, hr⟩

end Rows

end ConLeche.Model
