module

import ConLeche.Verify.Leaves
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.BridgeWfImp

public section

/-!
# An outside class's reading at the rule prefix

At a recursor whose major is an outside container `I.{us} D⃗`, the rule
rows of the class (`tgtOutDec_core`, `TargetOutRow.lean`) read the
container's parameters `D⃗` at the rule prefix and need them to SATISFY
the container's parameter telescope at the key frame.  Both come from
the check's own run:

* the scoping of `D⃗` — the major type's first `nPc` arguments, whose
  free variables are the recursor type's first `nP` openers
  (`TargetTyEntry.outside_of`);
* the typing (`TargetTyEntry.pinTys_of`): the
  instantiation `I.{us} D⃗` INFERS at the rule prefix `rP`, whose
  context is the recursor type's first `rP` binder readings
  (`blockRulePdomsAV`).  `infer_sound` grades its reading under that
  context, and a graded instance of a recorded member reads its
  parameters in the member's parameter telescope (`keyParamsFit`).

`tgtOutSat` packages the class reading premises of `tgtOutDec_core`
(`hul`, `hds`, `hdsa`, `hlenP`) and its satisfaction premise `hsat` at
every prefix spine fitting the rule's prefix domains — the only spines
the graph producer's rule rows quantify over.
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

omit [SetTheory V] in
/-- An application's argument is scoped wherever the application is. -/
theorem wscoped_of_getAppArgs : ∀ {e : Expr} {d : Nat}, Expr.WScoped d e →
    ∀ x ∈ e.getAppArgs, Expr.WScoped d x
  | .app f a, d, h, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.WScoped] at h
    rcases hx with hx | rfl
    · exact wscoped_of_getAppArgs h.1 x hx
    · exact h.2
  | .bvar _, _, _, _, hx | .fvar _ _, _, _, _, hx | .sort _, _, _, _, hx
  | .const _ _, _, _, _, hx | .lam _ _ _, _, _, _, hx | .forallE _ _ _, _, _, _, hx
  | .letE _ _ _, _, _, _, hx | .lit _, _, _, _, hx | .proj _ _ _, _, _, _, hx => by
    simp [Expr.getAppArgs] at hx

end ConLeche.Model
