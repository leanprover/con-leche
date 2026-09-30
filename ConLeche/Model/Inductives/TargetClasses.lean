module

import ConLeche.Model.Inductives.TargetOutRows
public import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetGraph
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRecMem

public section

/-!
# The recursor's CLASSES at a nested block, and the graph producer over them

The graph producer `graphRecPre_core` (`BlockRecGraph.lean`) is stated
over classes: recursor `c`'s index sets `Is`, carriers `Cr`, injections,
tuple sorts, index counts, tuple function and decoding fit are
parameters.  Here they are DEFINED, once, for a target check at ANY
majors:

* every class is ONE recorded lfp clause read at a level assignment, a
  parameter frame and a component (charter item 5: "the model uses
  nothing from an inductive but its lfp clause") — `tgtClsD`/`tgtClsψ`/
  `tgtClsFr`/`tgtClsM`:
  - a MEMBER major's class is the block's own datum `d.toLfp` at `ψ`, the
    prefix's first `nP` values and the member `recTgtAt c`;
  - an OUTSIDE major's class is the container's recorded datum `Dc c`
    (a `TgtOutCls` record, `TargetClass.lean`) at the major's level
    substitution, the KEY frame (the major's parameters read at the
    prefix, `tgtOutDsa`) and the container's member `mc c`;
* the index set is guarded by the prefix fit (and, at a member, the
  parameters' fit — `blockRecIs`'s guard);
* the fit is the clause's HOLE fit at the carrier.

At a member class the definitions unfold to the member rows' own data
(`blockRecIs`, `blockRecCr`, `blockHoleFitRel`, `d.tup`), at an outside
class to the outside rows' (`TargetOut*.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The class data -/

section Data

variable (d : BlockData V) (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
  (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (p : BlockShape)
  (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat) (ρ : Nat → V)

/-- Class `c`'s recorded clause: the block's own at a member major, the
container's at an outside one. -/
@[expose] def tgtClsD (c : Nat) : LfpDatum V :=
  if (tgtMajor out c).member.isSome then d.toLfp else Dc c

/-- Class `c`'s level assignment. -/
@[expose] def tgtClsψ (c : Nat) : Name → Nat :=
  if (tgtMajor out c).member.isSome then ψ
  else Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls

/-- Class `c`'s component. -/
@[expose] def tgtClsM (c : Nat) : Nat :=
  if (tgtMajor out c).member.isSome then p.recTgtAt c else mc c

/-- Class `c`'s parameter frame at the prefix spine `xs`. -/
@[expose] noncomputable def tgtClsFr (xs : List V) (c : Nat) : Nat → V :=
  if (tgtMajor out c).member.isSome then consList (xs.take d.nP) ρ
  else keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ)

/-- Class `c`'s guard at the prefix spine `xs`. -/
@[expose] def tgtClsG (xs : List V) (c : Nat) : Prop :=
  if (tgtMajor out c).member.isSome then
    SpineFit ρ (d.params ψ) (xs.take d.nP) ∧
      SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs
  else SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs

/-- **Class `c`'s index set** at the prefix spine `xs`: the clause's, at
the class's frame, under the guard. -/
@[expose] noncomputable def tgtClsIs (xs : List V) (c : Nat) : V :=
  open Classical in
  if tgtClsG d acval envC p out ψ ρ xs c then
    (tgtClsD d Dc out c).idx (tgtClsψ cvc out ψ c) (tgtClsFr d acval envC p out ψ ρ xs c)
      (tgtClsM mc p out c)
  else empty

/-- **Class `c`'s carrier** at the prefix spine `xs`. -/
@[expose] noncomputable def tgtClsCr (xs : List V) (c : Nat) : V :=
  (tgtClsD d Dc out c).carrier (tgtClsψ cvc out ψ c) (tgtClsFr d acval envC p out ψ ρ xs c)
    (tgtClsM mc p out c)

/-- Class `c`'s injection. -/
@[expose] noncomputable def tgtClsInj (c : Nat) : Nat → List V → V :=
  (tgtClsD d Dc out c).inj (tgtClsψ cvc out ψ c) (tgtClsM mc p out c)

/-- Class `c`'s index-tuple sort. -/
@[expose] def tgtClsU (c : Nat) : Nat :=
  (tgtClsD d Dc out c).u (tgtClsM mc p out c) (tgtClsψ cvc out ψ c)

/-- Class `c`'s index count. -/
@[expose] def tgtClsNIdx (c : Nat) : Nat :=
  if (tgtMajor out c).member.isSome then d.nIdxAt (p.recTgtAt c) else (tgtMajor out c).nIdx

/-- Class `c`'s tuple of an index spine. -/
@[expose] noncomputable def tgtClsTup (c : Nat) (is : List V) : V :=
  tupW (tgtClsU d Dc mc cvc p out ψ c) is

/-- **The decoding fit at class `c`**: the clause's hole fit at the
class's frame and carrier. -/
@[expose] def tgtClsFit (xs : List V) (c : Nat) (i : V) (j : Nat) (fs : List V) : Prop :=
  (tgtClsD d Dc out c).HFits (tgtClsψ cvc out ψ c) (tgtClsFr d acval envC p out ψ ρ xs c)
    ((tgtClsD d Dc out c).carrier (tgtClsψ cvc out ψ c) (tgtClsFr d acval envC p out ψ ρ xs c))
    i (tgtClsM mc p out c) j fs

end Data

/-! ## 2. The two cases -/

section Cases

variable {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
  {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env} {p : BlockShape}
  {out : List (ConstantVal × TargetMajor × List Expr)} {ψ : Name → Nat} {ρ : Nat → V}
  {c : Nat}

theorem tgtClsIs_mem (hm : (tgtMajor out c).member.isSome = true) (xs : List V) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c
      = blockRecIs d ψ ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ) p.recTgtAt xs c := by
  classical
  simp only [tgtClsIs, tgtClsG, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hm, if_true, blockRecIs]
  rfl

theorem tgtClsCr_mem (hm : (tgtMajor out c).member.isSome = true) (xs : List V) :
    tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c = blockRecCr d ψ ρ p.recTgtAt xs c := by
  simp only [tgtClsCr, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hm, if_true]
  rfl

omit [SetTheory V] in
theorem tgtClsInj_mem (hm : (tgtMajor out c).member.isSome = true) :
    tgtClsInj d Dc mc cvc p out ψ c = d.inj ψ (p.recTgtAt c) := by
  simp only [tgtClsInj, tgtClsD, tgtClsψ, tgtClsM, hm, if_true]
  rfl

omit [SetTheory V] in
theorem tgtClsU_mem (hm : (tgtMajor out c).member.isSome = true) :
    tgtClsU d Dc mc cvc p out ψ c = d.uM (p.recTgtAt c) ψ := by
  simp only [tgtClsU, tgtClsD, tgtClsψ, tgtClsM, hm, if_true]
  rfl

omit [SetTheory V] in
theorem tgtClsNIdx_mem (hm : (tgtMajor out c).member.isSome = true) :
    tgtClsNIdx d p out c = d.nIdxAt (p.recTgtAt c) := by
  simp only [tgtClsNIdx, hm, if_true]

theorem tgtClsTup_mem (hm : (tgtMajor out c).member.isSome = true) (is : List V) :
    tgtClsTup d Dc mc cvc p out ψ c is = d.tup ψ (p.recTgtAt c) is := by
  rw [tgtClsTup, tgtClsU_mem hm]; rfl

theorem tgtClsFit_mem (hm : (tgtMajor out c).member.isSome = true) (xs : List V) (i : V)
    (j : Nat) (fs : List V) :
    tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs c i j fs
      ↔ blockHoleFitRel d ψ ρ p.recTgtAt xs c i j fs := by
  simp only [tgtClsFit, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hm, if_true]
  rfl

omit [SetTheory V] in
theorem tgtClsNIdx_out (hMo : (tgtMajor out c).member = none) :
    tgtClsNIdx d p out c = (tgtMajor out c).nIdx := by
  simp only [tgtClsNIdx, hMo, Option.isSome_none]
  rfl

end Cases

/-! ## 3. The rows at every class -/

/-- The stored rule at `(c, j)`, below the constructor count. -/
theorem tgtRule_exists {envC : Env} {F : Nat} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR) {c : Nat} (hc : c < rs.length)
    {j : Nat} (hj : j < blockRecNCt rs c) :
    ∃ cA rhs, rs[c].2.2.2[j]? = some cA ∧ rs[c].2.1[j]? = some rhs := by
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  exact ⟨_, _, List.getElem?_eq_getElem hjr,
    List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩

end ConLeche.Model
