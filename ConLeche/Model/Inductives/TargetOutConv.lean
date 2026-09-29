module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockHoleValid
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Semantics.Tower.BlockTower
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.EnvBound
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# The index clause's CONVERSE at an outside major

At an outside major `I.{us} D⃗ ı⃗` the target check compares the
recursor's index binder domains, binder by binder (`TargetTyEntry.hidx`),
with `targetIdxDoms`' outside arm: the container's type instantiated at
the levels and the parameters, opened at the rule prefix
(`openPisAtFvars M.nIdx ty rP`).  This file is that comparison's model
side, the twin of `blockRecIdxConv_run` (`BlockRecIdxConv.lean`) at a
container:

* `instFormer_read` (`ContN2.lean`) reads the instantiated former as the
  recorded index telescope `D.ids` substituted at the parameters'
  readings, so a spine fits the opened domains at the prefix exactly
  when it fits `D.ids` at the key frame;
* the opened domains are graded at the fitting spines — the stored
  former's reading is graded (`type_wellDenotedV`), the parameters'
  readings are (`tgtOutSatW`), and grading crosses the substitution
  (`WellDenoted_substAV`, `AnnotValid_substAV`);
* **`tgtOutIdxConv`** — at a prefix fitting the rule's prefix domains,
  index values fitting the container's index telescope at the key frame
  fit the recursor's index binders: `defeqDom_agree_at` position by
  position, at the context "recursor prefix ++ opened container
  indices" (the container side's list IS the context, so only the
  recursor side is walked);
* **`tgtOutConclTy`** — the graph kit's `hconclTy` at an outside class.
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

/-- A term with at least `n` leading syntactic binders strips `n`. -/
theorem stripPis_isSome_of_piCount : ∀ (n : Nat) (e : Expr), n ≤ piCount e →
    (e.stripPis n).isSome = true
  | 0, _, _ => rfl
  | n + 1, .forallE t b mb, h => by
    simp only [piCount] at h
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_of_piCount n b (by omega)
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h | _ + 1, .const _ _, h
  | _ + 1, .lit _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h | _ + 1, .letE _ _ _, h
  | _ + 1, .proj _ _ _, h => by simp [piCount] at h

omit [SetTheory V] in
/-- A substituted telescope's entries are the entries substituted at
their own depth. -/
theorem substTele_getD (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k q : Nat), q < ab.length →
      ((AnnotTerm.substTele τ k ab).map (·.2.2)).getD q default
        = AnnotTerm.substAV τ ((ab.map (·.2.2)).getD q default) (k + q)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, k, 0, _ => by simp [AnnotTerm.substTele]
  | _ :: ab, k, q + 1, h => by
    simp only [AnnotTerm.substTele, List.map_cons, List.getD_cons_succ]
    rw [substTele_getD τ ab (k + 1) q (by simpa using h)]
    rw [show k + 1 + q = k + (q + 1) by omega]

omit [SetTheory V] in
/-- A substituted telescope's prefix is the prefix's substitution. -/
theorem substTele_take (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k q : Nat),
      (AnnotTerm.substTele τ k ab).take q = AnnotTerm.substTele τ k (ab.take q)
  | [], _, q => by simp [AnnotTerm.substTele]
  | _ :: _, _, 0 => by simp [AnnotTerm.substTele]
  | _ :: ab, k, q + 1 => by
    simp only [AnnotTerm.substTele, List.take_succ_cons]
    rw [substTele_take τ ab (k + 1) q]

section Conv

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

end Conv

end ConLeche.Model
