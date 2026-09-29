module

import ConLeche.Model.Inductives.TargetClassFrame
import ConLeche.Model.Inductives.TargetClasses
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetIhData
public import ConLeche.Model.Inductives.TargetFrame
public import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Subst
import ConLeche.Verify.BridgeWfImp

public section

/-!
# A target call's target is a MAJOR of its callee's class

The graph kit's two `ih` rows (`hihF`, `hchain`) read, per `ih` key, the
call's target as a major of the CALLEE's recursor: the callee spine
`x⃗ ++ e⃗ ++ [f a⃗]` (the caller's prefix, the key's index readings and
the applied field) fits the callee's recursor binder data.  At a member
callee this is the member rows' argument (`tgtCall_carrierG` +
`blockRecSpineFit_of_parts`), at any caller.  At an OUTSIDE callee (a
container's auxiliary recursor): the call's typing puts the applied
field in the callee's major domain `I.{us} D⃗ ı⃗` read at the members' own
values (`targetCall_genW`, `targetAbs_read`), the container's recorded
leaf (`keyLeaf`) reads that domain as the container's carrier at the
callee's KEY frame at the index tuple, with the index values fitting the
container's index telescope there — the call's parameters `D⃗` are the
callee major's own, read at the caller's prefix openers, which the
reading does not distinguish from the callee's (`replF_erasedEq`) —
and the index converse (`tgtOutIdxConv`) and the major's reading
(`tgtOutMajor`) turn that into the callee spine's fit.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Two syntactic facts -/

/-- **Replacing free variables by free variables at the same index is
invisible to the reading**: `replF` at such a map is erasure-equal to
the identity. -/
theorem replF_erasedEq {g : Nat → Option Expr} :
    ∀ e : Expr, (∀ l ∈ e.fvarLeaves, ∀ x, g l.1 = some x → ∃ ty, x = .fvar l.1 ty) →
      Expr.ErasedEq (replF g e) e := by
  intro e
  induction e with
  | bvar j => intro _; exact Expr.ErasedEq.rfl _
  | fvar i ty =>
    intro h
    simp only [replF]
    cases hgi : g i with
    | none => exact Expr.ErasedEq.rfl _
    | some x =>
      obtain ⟨ty', rfl⟩ := h (i, ty) (by simp [Expr.fvarLeaves]) x hgi
      show Expr.ErasedEq (.fvar i ty') (.fvar i ty)
      simp [Expr.ErasedEq]
  | sort u => intro _; exact Expr.ErasedEq.rfl _
  | const n us => intro _; exact Expr.ErasedEq.rfl _
  | lit l => intro _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro h
    refine ⟨ihf fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      iha fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | lam t b m iht ihb =>
    intro h
    refine ⟨rfl, iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | forallE t b m iht ihb =>
    intro h
    refine ⟨rfl, iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | letE t v b iht ihv ihb =>
    intro h
    refine ⟨iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihv fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | proj s i e ih =>
    intro h
    exact ⟨rfl, rfl, ih fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩

/-- Erasure equality through an application spine. -/
theorem erasedEq_mkAppN :
    ∀ {as as' : List Expr} {f f' : Expr}, Expr.ErasedEq f f' → as.length = as'.length →
      (∀ (i : Nat) (h : i < as.length) (h' : i < as'.length), Expr.ErasedEq as[i] as'[i]) →
      Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN f' as')
  | [], [], _, _, hf, _, _ => hf
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | a :: as, a' :: as', f, f', hf, hl, h => by
    show Expr.ErasedEq (Expr.mkAppN (.app f a) as) (Expr.mkAppN (.app f' a') as')
    exact erasedEq_mkAppN ⟨hf, h 0 (by simp) (by simp)⟩ (by simpa using hl)
      (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

section MajDom

end MajDom

/-! ## The call's typing at the members' own values, at any callee -/

section MemVal

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}

end MemVal

/-! ## One `ih` key at every class -/

section Key

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

end Key

end ConLeche.Model
