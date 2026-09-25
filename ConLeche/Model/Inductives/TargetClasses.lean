module

import ConLeche.Model.Inductives.TargetOutRows
public import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetRowCerts
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetGraph
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRecMem

public section

/-!
# The recursor's CLASSES at a nested block, and the graph producer over them (lane NESTIND, session 8)

The graph producer `graphRecPre_core` (`BlockRecGraph.lean`) is stated
over classes: recursor `c`'s index sets `Is`, carriers `Cr`, injections,
tuple sorts, index counts, tuple function and decoding fit are
parameters.  Here they are DEFINED, once, for a target check at ANY
majors (`outside = true` at a nested block):

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

theorem tgtClsIs_out (hMo : (tgtMajor out c).member = none) (xs : List V) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c
      = (open Classical in
        if SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs then
          (Dc c).idx (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)
            (keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ)) (mc c)
        else empty) := by
  classical
  simp only [tgtClsIs, tgtClsG, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hMo, Option.isSome_none]
  rfl

theorem tgtClsIs_out_pos (hMo : (tgtMajor out c).member = none) {xs : List V}
    (hp : SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs) :
    tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c
      = (Dc c).idx (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)
          (keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ)) (mc c) := by
  classical
  rw [tgtClsIs_out hMo, if_pos hp]

theorem tgtClsIs_out_fits (hMo : (tgtMajor out c).member = none) {xs : List V} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs := by
  classical
  rw [tgtClsIs_out hMo] at hi
  by_cases hp : SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs
  · exact hp
  · rw [if_neg hp] at hi; exact absurd hi (not_mem_empty _)

theorem tgtClsCr_out (hMo : (tgtMajor out c).member = none) (xs : List V) :
    tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs c
      = (Dc c).carrier (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)
          (keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ)) (mc c) := by
  simp only [tgtClsCr, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hMo, Option.isSome_none]
  rfl

omit [SetTheory V] in
theorem tgtClsInj_out (hMo : (tgtMajor out c).member = none) :
    tgtClsInj d Dc mc cvc p out ψ c
      = (Dc c).inj (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls) (mc c) := by
  simp only [tgtClsInj, tgtClsD, tgtClsψ, tgtClsM, hMo, Option.isSome_none]
  rfl

omit [SetTheory V] in
theorem tgtClsU_out (hMo : (tgtMajor out c).member = none) :
    tgtClsU d Dc mc cvc p out ψ c
      = (Dc c).u (mc c) (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls) := by
  simp only [tgtClsU, tgtClsD, tgtClsψ, tgtClsM, hMo, Option.isSome_none]
  rfl

omit [SetTheory V] in
theorem tgtClsNIdx_out (hMo : (tgtMajor out c).member = none) :
    tgtClsNIdx d p out c = (tgtMajor out c).nIdx := by
  simp only [tgtClsNIdx, hMo, Option.isSome_none]
  rfl

theorem tgtClsFit_out (hMo : (tgtMajor out c).member = none) (xs : List V) (i : V)
    (j : Nat) (fs : List V) :
    tgtClsFit d Dc mc cvc acval envC p out ψ ρ xs c i j fs
      ↔ (Dc c).HFits (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)
          (keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ))
          ((Dc c).carrier (Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls)
            (keyFrame (tgtOutDsa acval envC p out ψ c) (tgtRP p c) (consList xs ρ)))
          i (mc c) j fs := by
  simp only [tgtClsFit, tgtClsD, tgtClsψ, tgtClsFr, tgtClsM, hMo, Option.isSome_none]
  rfl

end Cases

/-! ## 3. The rows at every class -/

omit [SetTheory V] in
/-- A member major's position is a member of the stage record's. -/
theorem tgtMemAt_of_member {out : List (ConstantVal × TargetMajor × List Expr)} {c : Nat}
    (hc : c < (tgtRs out).length) (hm : (tgtMajor out c).member.isSome = true) :
    ConLeche.tgtMemAt out c := by
  have hc' : c < out.length := by simpa [ConLeche.tgtRs] using hc
  have hg : out.getD c default = out[c] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc', Option.getD_some]
  rw [tgtMajor, hg] at hm
  show (out[c]?).all _ = true
  rw [List.getElem?_eq_getElem hc']
  exact hm

omit [SetTheory V] in
/-- The target check's rule prefix is the shape's. -/
theorem tgtRP_eq (p : BlockShape) (c : Nat) : tgtRP p c = p.rulePrefixAt c := rfl

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

/-- **At a member class the target field domains' chain lift is the
member rows'** (`tgtFdomsAV_eq_block`). -/
theorem tgtFdomsK_eq_block {F : Nat} {fe : FEnv} {p : BlockShape} {outside nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun μ F fe p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hm : (tgtMajor out j).member.isSome = true)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) (K : Nat) :
    tgtFdomsK K acval env p out ψ j i = blockRecFdomsK K acval env p (tgtRs out) ψ j i := by
  rw [tgtFdomsK, blockRecFdomsK, tgtFdomsAV_eq_block R hr hcA hrhs hm]

/-- **At a member class the target index expressions, lifted, are the
member rows'** (`tgtEsAV_eq_block`). -/
theorem tgtEsK_eq_block {F : Nat} {fe : FEnv} {p : BlockShape} {outside nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun μ F fe p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hm : (tgtMajor out j).member.isSome = true)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) (K : Nat) :
    liftEsK K ((blockRulePdomsAV acval env p (tgtRs out) ψ j).length
        + (tgtFdomsAV p out acval env ψ j i).length) (tgtEsAV p out acval env ψ j i)
      = blockRecEsK K acval env p (tgtRs out) ψ j i := by
  rw [liftEsK, blockRecEsK, tgtEsAV_eq_block R hr hcA hrhs hm,
    tgtFdomsAV_eq_block R hr hcA hrhs hm]

/-- **At a member class the target fired spine, lifted, is the member
rows'** (`tgtMkAV_eq_block`). -/
theorem tgtMkK_eq_block {F : Nat} {fe : FEnv} {p : BlockShape} {outside nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun μ F fe p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hm : (tgtMajor out j).member.isSome = true)
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) (K : Nat) :
    tgtMkK K acval env p out ψ j i = blockRecMkK K acval env p (tgtRs out) ψ j i := by
  rw [tgtMkK, blockRecMkK, tgtMkAV_eq_block R hr hcA hrhs hm,
    tgtFdomsAV_eq_block R hr hcA hrhs hm]

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {outside nested : Bool}
  {block : List ConstantInfo} {names : List Name} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- **Row `hsplit` at every class.** -/
theorem tgtCls_hsplit (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      (prefOf (pp.toBlockShape.rulePrefixAt c) ys).length = pp.toBlockShape.rulePrefixAt c ∧
      ys = prefOf (pp.toBlockShape.rulePrefixAt c) ys
        ++ (idxOf (pp.toBlockShape.rulePrefixAt c) ys ++ [majOf ys]) ∧
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c (idxOf (pp.toBlockShape.rulePrefixAt c) ys)
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c ∧
      majOf ys ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c)
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          (idxOf (pp.toBlockShape.rulePrefixAt c) ys)) := by
  intro c hc ys hfit
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hmemk := (blockRecMajor_run (hm := hmR) (V := V) hμ mpC h hmr hr ψ).2.1
    have hs := blockRec_hsplit_at (V := V) (ψ := ψ) (ρ := ρ) (c := c)
      (rP := pp.toBlockShape.rulePrefixAt) (mem := pp.toBlockShape.recTgtAt)
      (rds := blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (pdoms := blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ) hM
      (by rw [blockRulePdomsAV, List.map_take]) hmemk
      (blockRecSplitOne_of_shape (blockRecTyShape_at hμ mpC h hmr ψ ρ hmR hc)) ys hfit
    rw [tgtClsTup_mem hm, tgtClsIs_mem hm, tgtClsCr_mem hm]
    exact hs
  | none =>
    obtain ⟨hlen, hdec, hpref, -, hIs, hmaj⟩ :=
      tgtOutSplit hμ hcov h R hr hmb (hcls c hc hmb) ψ ρ ys hfit
    simp only [tgtRP_eq] at hlen hdec hpref hIs hmaj
    rw [tgtClsTup, tgtClsU_out hmb, tgtClsIs_out_pos hmb hpref, tgtClsCr_out hmb]
    exact ⟨hlen, hdec, hIs, hmaj⟩

/-- **Row `hconcl` at every class.** -/
theorem tgtCls_hconcl (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval envC pp.toBlockShape
          (tgtRs out) ψ) (tgtClsU d Dc mc cvc pp.toBlockShape out ψ)
          (tgtClsNIdx d pp.toBlockShape out) ρ (prefOf (pp.toBlockShape.rulePrefixAt c) ys)
          (tagged c (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            (idxOf (pp.toBlockShape.rulePrefixAt c) ys)) (majOf ys))
        = interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) := by
  intro c hc ys hfit
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hmemk := (blockRecMajor_run (hm := hmR) (V := V) hμ mpC h hmr hr ψ).2.1
    rw [tgtClsTup_mem hm]
    exact blockRec_hconcl_at (V := V) hM hc (tgtClsU_mem hm) (tgtClsNIdx_mem hm)
      (Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)) (blockMembers_IdsM_length hmr hmemk ψ)
      (blockRecSplitOne_of_shape (blockRecTyShape_at hμ mpC h hmr ψ ρ hmR hc)) ys hfit
  | none =>
    rw [tgtClsTup, tgtClsU_out hmb]
    exact tgtOutConcl hμ hcov h R hr hmb (hcls c hc hmb) ψ ρ hc (tgtClsU_out hmb)
      (tgtClsNIdx_out hmb) ys hfit

/-- **Row `hconclTy` at every class**: the conclusion at any class
element reads to a set of the checked elimination level. -/
theorem tgtCls_hconclTy (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length →
      ∀ i, i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) i →
      interp V (consList (xs ++ (isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c)
          (tgtClsNIdx d pp.toBlockShape out c) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) : V) := by
  intro xs c hc i hi x hx
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
    rw [tgtClsIs_mem hm] at hi
    rw [tgtClsCr_mem hm] at hx
    rw [tgtClsU_mem hm, tgtClsNIdx_mem hm]
    exact blockRecConclTy_at hμ mpC h hmr hM hruns ψ ρ xs hmR hc i hi x hx
  | none =>
    have hpref := tgtClsIs_out_fits hmb hi
    rw [tgtClsIs_out_pos hmb hpref] at hi
    rw [tgtClsCr_out hmb] at hx
    rw [tgtClsU_out hmb, tgtClsNIdx_out hmb]
    exact tgtOutConclTy hμ hcov h R hr hmb (hcls c hc hmb) ψ ρ xs hpref i hi x hx

/-- **Row `hcerts` at every class**, at the target data. -/
theorem tgtCls_hcerts (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      BlockRuleCerts V mpC F ψ (pp.toBlockShape.rulePrefixAt c)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
        (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
        (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j)
        (tgtRbAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j)
        (tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ c j) := by
  intro c hc j hj
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    rw [tgtFdomsK_eq_block R hr hcA hrhs hm]
    exact tgtRuleCerts_at (fe := mkFEnv envC) hμ h R hdR hN hS hcore hmr hM ψ c hc hmR hm j hj
  | none =>
    have hformer : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
      intro t ht
      obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
      exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
    rw [tgtOutFdomsK_eq hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ]
    exact tgtOutCertsW hμ hcov h R hr hmb (hcls c hc hmb) hformer ψ hj

/-- The member rows' constructor lists, from the stage record. -/
theorem tgtCls_hctM
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) :
    ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      ConLeche.tgtMemAt out c → (tgtRs out)[c]? = some r →
      d.ctorsM (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  intro c r hmc hr
  obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt (hm := hmc) h hr
  show ctorsAs.getD _ [] = _
  rw [List.getD_eq_getElem?_getD, hctA]; rfl

/-- **Row `hspF` at every class**: a decoding's fields fit the rule's
field domains after the prefix. -/
theorem tgtCls_hspF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (ρ : Nat → V) (K : Nat) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) := by
  intro xs c hc j hj i fs hi hf
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hdnP : d.nP = pp.nP := by obtain ⟨_, _, _, rfl⟩ := hdR; rfl
    have hctM := tgtCls_hctM h hdR
    rw [tgtClsIs_mem hm] at hi
    rw [tgtClsFit_mem hm] at hf
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
    rw [blockRecIs_pos hpar hpref] at hi
    have hmemk := (blockRecMajor_run (hm := hmR) (V := V) hμ mpC h hmr hr ψ).2.1
    have hmN : pp.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
    have hfS := (blockHoleFitRel_iff hM hpar hmN hi).mp hf
    rw [tgtFdomsK_eq_block R hr hcA hrhs hm]
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
    exact blockKitSpF_at hμ h hcore hmr hdnP hctM ψ
      (fun j' r' hm' hr' => blockRuleDoms_bounded_one hμ h hcore ψ j' r' hm' hr')
      ρ K xs c hc hmR hpar hpref j hj i fs hi hfS
  | none =>
    have hpref := tgtClsIs_out_fits hmb hi
    rw [tgtClsFit_out hmb] at hf
    rw [tgtOutFdomsK_eq hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ]
    exact tgtOutSpF hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ ρ hpref hf

/-- **Row `hCaB` at every class**: the rule's conclusion at the rule's
frame is the bound at the constructed element (at any `ih` values: the
conclusion is read past them). -/
theorem tgtCls_hCaB (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (ρ : Nat → V)
    (tup : Nat → List V → V) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs → ∀ g : V,
      interp V (consList (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
          mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) tup ρ xs c j fs g) (consList (xs ++ fs) ρ))
          (tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ c j)
        = blockRecMot (tgtRs out).length
            (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs
            (tagged c i (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs)) := by
  intro xs c hc j hj i fs hi hf g
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hdnP : d.nP = pp.nP := by obtain ⟨_, _, _, rfl⟩ := hdR; rfl
    have hctM := tgtCls_hctM h hdR
    rw [tgtClsIs_mem hm] at hi
    rw [tgtClsFit_mem hm] at hf
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
    rw [blockRecIs_pos hpar hpref] at hi
    rw [tgtClsInj_mem hm]
    exact tgtKitCaB_at (fe := mkFEnv envC) (uX := tgtClsU d Dc mc cvc pp.toBlockShape out ψ) hμ h R hcore hmr hM hdnP hctM ψ ρ xs tup c hc hmR hm
      (tgtClsU_mem hm) (tgtClsNIdx_mem hm) hpar hpref j hj i fs hi hf g
  | none =>
    have hpref := tgtClsIs_out_fits hmb hi
    rw [tgtClsIs_out_pos hmb hpref] at hi
    rw [tgtClsFit_out hmb] at hf
    rw [tgtClsInj_out hmb]
    exact tgtOutCaB hμ hcov h R hr hmb (hcls c hc hmb) ψ ρ hc (tgtClsU_out hmb)
      (tgtClsNIdx_out hmb) _ tup hpref hj hi hf g

/-- **Row `hrule` at every class**, at any chain valuation: the rule's
own spine fits the recursor's binder data. -/
theorem tgtCls_hrule (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame K a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2))
        (xs ++ ((liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
              ψ c).length + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K a ρ))
            (tgtMkK K mpC.base2.acval envC pp.toBlockShape out ψ c j)])) := by
  intro c hc j hj xs fs hxl hsp
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hdnP : d.nP = pp.nP := by obtain ⟨_, _, _, rfl⟩ := hdR; rfl
    have hctM := tgtCls_hctM h hdR
    rw [tgtFdomsK_eq_block R hr hcA hrhs hm] at hsp
    rw [tgtEsK_eq_block R hr hcA hrhs hm, tgtMkK_eq_block R hr hcA hrhs hm]
    exact blockKitRule_at hμ h hcore hmr hM hdnP hctM ψ K a ρ c hc hmR j hj xs fs hxl hsp
  | none =>
    rw [tgtEsAV_outside hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ]
    exact tgtOutRuleK hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ K a ρ hxl hsp

/-- **Row `hdec` at every class**, at any chain valuation: the rule's
fields fit its constructor at the tuple of its index readings, and the
fired spine reads to the injection. -/
theorem tgtCls_hdec (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame K a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK K mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((liftEsK K ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
                ψ c).length + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame K a ρ))
            (tgtMkK K mpC.base2.acval envC pp.toBlockShape out ψ c j)
          = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs := by
  intro c hc j hj xs fs hxl hsp
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  cases hmb : (tgtMajor out c).member with
  | some t =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    have hdnP : d.nP = pp.nP := by obtain ⟨_, _, _, rfl⟩ := hdR; rfl
    have hctM := tgtCls_hctM h hdR
    -- the rule's spine is a major of the class: the tuple is in the index set
    have hfit := tgtCls_hrule hμ hcov h R hcls hdR hcore hmr hM ψ K a ρ c hc j hj xs fs hxl hsp
    have hxr : xs.length = pp.toBlockShape.rulePrefixAt c := by
      rw [hxl, blockRulePdomsAV_length hμ mpC h hr ψ]
    obtain ⟨-, -, hi, -⟩ := tgtCls_hsplit (Dc := Dc) (mc := mc) (cvc := cvc) hμ hcov h R hcls hmr
      hM ψ ρ c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    rw [tgtClsIs_mem hm, tgtClsTup_mem hm] at hi
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
    rw [blockRecIs_pos hpar hpref] at hi
    have hmemk := (blockRecMajor_run (hm := hmR) (V := V) hμ mpC h hmr hr ψ).2.1
    have hmN : pp.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
    rw [tgtFdomsK_eq_block R hr hcA hrhs hm] at hsp
    rw [tgtEsK_eq_block R hr hcA hrhs hm] at hi ⊢
    rw [tgtMkK_eq_block R hr hcA hrhs hm, tgtClsFit_mem hm, tgtClsTup_mem hm, tgtClsInj_mem hm]
    obtain ⟨hS, hmk⟩ := blockRuleDecoding_at hμ h hcore hmr hM hdnP hctM ψ K a ρ c hc hmR j hj
      xs fs hxl hsp
    exact ⟨(blockHoleFitRel_iff hM hpar hmN hi).mpr hS, hmk⟩
  | none =>
    rw [tgtEsAV_outside hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ]
    obtain ⟨hHF, hmk, -⟩ := tgtOutDecK hμ hcov h R hr hcA hrhs hmb (hcls c hc hmb) ψ K a ρ hxl hsp
    rw [tgtClsFit_out hmb, tgtClsTup, tgtClsU_out hmb, tgtClsInj_out hmb]
    exact ⟨hHF, hmk⟩

/-- **F4, read**: with an OUTSIDE major and a large eliminator, the
block's sort is never `Prop` — the target check's counting guard runs at
the container bit or'ed with its outside majors (`TargetRecRun.small`),
and the elimination-level pin excludes the all-`Prop` arm. -/
theorem tgt_neverZero_of_outside
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) (hMo : (tgtMajor out c).member = none)
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0) :
    pp.toBlockShape.resSort.isNeverZero = true := by
  have hfst := ConLeche.targetRecRun_out_fst R
  have hc' : c < out.length := by simpa [ConLeche.tgtRs] using hc
  have hcT : c < R.tys.length := by
    have := congrArg List.length hfst; simp at this; omega
  have hmaj : (R.tys[c]).2.1 = tgtMajor out c := by
    have h1 := congrArg (fun L => L[c]?) hfst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hc', List.getElem?_eq_getElem hcT,
      Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    rw [tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc', Option.getD_some]
    exact h1.2.symm
  have hany : R.tys.any (fun t => t.2.1.member.isNone) = true := by
    rw [List.any_eq_true]
    exact ⟨R.tys[c], List.getElem_mem hcT, by rw [hmaj, hMo]; rfl⟩
  obtain ⟨-, hsm⟩ := R.small
  rcases hsm with hA | hZ
  · simpa [ConLeche.blockLargeElimAllowed, hany] using hA
  · exfalso
    have hu : R.tys[c].2.2 ∈ R.tys.map (·.2.2) := List.mem_map.mpr ⟨_, List.getElem_mem hcT, rfl⟩
    have h0 := ConLeche.Level.isEquiv_sound (hZ _ hu) ψ
    have hp := ConLeche.Level.isEquiv_sound (R.pin _ hu) ψ
    apply hℓ
    rw [← hp, h0]; rfl

/-- **Row `huniq` at every class** (charter item 5: exactly the
kernel's elimination guard): at `ℓ = 0` the bound is a truth value; at
`ℓ ≠ 0` either some major is outside — then the block's sort is never
`Prop` (F4), every class's clause (the block's, or the container's at
the block's sort, `tgtOutCls_w`) has an injective injection (`mkInj`) —
or every major is a member, the member rows' argument
(`blockGraphUniq_run`: `mkInj`, or the counting guard and the
subsingleton criterion). -/
theorem tgtCls_huniq (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs) →
      ∀ e e',
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          xs u e →
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs u →
        v' ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs u →
        v = v' := by
  intro xs
  by_cases hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
      pp.toBlockShape.large) = 0
  · -- the bound is a truth value
    refine huniq_of_prop fun u hu => ?_
    have hmem := blockRecMot_mem_univ (K := (tgtRs out).length)
      (tgtCls_hconclTy hμ hcov h R hcls hmr hM ψ ρ xs) u hu
    rwa [hℓ] at hmem
  by_cases hall : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member.isSome = true
  · -- every major a member: the member rows' argument
    have hOk : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs (tgtRs out) := by
      obtain ⟨S⟩ := h
      refine ⟨S.mono fun i _ => ?_⟩
      by_cases hi : i < (tgtRs out).length
      · exact tgtMemAt_of_member hi (hall i hi)
      · have hi' : out.length ≤ i := by simp [ConLeche.tgtRs] at hi; omega
        show (out[i]?).all _ = true
        rw [List.getElem?_eq_none hi']; rfl
    intro u hu e e' he he'
    obtain ⟨c, j, fs⟩ := e
    obtain ⟨c', j', fs'⟩ := e'
    obtain ⟨hc, hj, i, hi, hf, rfl⟩ := he
    obtain ⟨hc', hj', i', hi', hf', heq⟩ := he'
    obtain ⟨rfl, rfl, hinj⟩ := tagged_inj heq
    have hm := hall c hc
    rw [tgtClsIs_mem hm] at hi hi'
    rw [tgtClsFit_mem hm] at hf hf'
    rw [tgtClsInj_mem hm] at hinj ⊢
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
    have hiD := hi
    rw [blockRecIs_pos hpar hpref] at hiD
    have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
    have hmemk := (blockRecMajor_run (hm := trivial) (V := V) hμ mpC hOk hmr hr ψ).2.1
    have hmN : pp.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
    have hsf := (blockHoleFitRel_iff hM hpar hmN hiD).mp hf
    have hsf' := (blockHoleFitRel_iff hM hpar hmN hiD).mp hf'
    -- the injection lies in the member's carrier: `u` is a major of the member class
    have hu' : tagged c i (d.inj ψ (pp.toBlockShape.recTgtAt c) j fs)
        ∈ˢ unionSet (tgtRs out).length
          (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            pp.toBlockShape.recTgtAt xs)
          (blockRecCr d ψ ρ pp.toBlockShape.recTgtAt xs) := by
      obtain ⟨c₁, hc₁, i₁, hi₁, x₁, hx₁, hu₁⟩ := mem_unionSet.mp hu
      rw [tgtClsInj_mem hm] at hu₁
      obtain ⟨h1, h2, h3⟩ := tagged_inj hu₁
      subst h1 h2 h3
      rw [tgtClsIs_mem hm] at hi₁
      rw [tgtClsCr_mem hm] at hx₁
      exact mem_unionSet.mpr ⟨_, hc₁, _, hi₁, _, hx₁, rfl⟩
    have hconclTyM : ∀ c₂, c₂ < (tgtRs out).length →
        ∀ i₂, i₂ ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
            (tgtRs out) ψ) pp.toBlockShape.recTgtAt xs c₂ →
        ∀ x, x ∈ˢ app (blockRecCr d ψ ρ pp.toBlockShape.recTgtAt xs c₂) i₂ →
        interp V
            (consList (xs ++ (isOfW (d.uM (pp.toBlockShape.recTgtAt c₂) ψ)
              (d.nIdxAt (pp.toBlockShape.recTgtAt c₂)) i₂ ++ [x])) ρ)
            (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c₂)
          ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) : V) := by
      obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
      intro c₂ hc₂
      exact blockRecConclTy_at hμ mpC h hmr hM hruns ψ ρ xs
        (tgtMemAt_of_member hc₂ (hall c₂ hc₂)) hc₂
    have key := blockGraphUniq_run hμ hOk hdR hN hS hcore hmr hM ψ ρ xs hconclTyM _ hu'
      (c, j, fs) (c, j', fs') ⟨hc, hj, i, hi, hsf, rfl⟩ ⟨hc, hj', i, hi, hsf', by rw [hinj]⟩
    rcases key with he | hsub
    · exact Or.inl he
    · refine Or.inr fun v v' hv hv' => hsub v v' ?_ ?_
      · rw [blockRecMot_tagged hc] at hv ⊢
        rwa [tgtClsU_mem hm, tgtClsNIdx_mem hm] at hv
      · rw [blockRecMot_tagged hc] at hv' ⊢
        rwa [tgtClsU_mem hm, tgtClsNIdx_mem hm] at hv'
  · -- some major outside: the block's sort is never `Prop`
    obtain ⟨c0, hc0, hc0m⟩ : ∃ c0, c0 < (tgtRs out).length ∧ (tgtMajor out c0).member = none := by
      refine Classical.byContradiction fun hno => hall fun c hc => ?_
      cases hmb : (tgtMajor out c).member with
      | some _ => rfl
      | none => exact absurd ⟨c, hc, hmb⟩ hno
    have hnz := tgt_neverZero_of_outside R hc0 hc0m ψ hℓ
    have hwB : Level.eval ψ pp.toBlockShape.resSort ≠ 0 :=
      ConLeche.Level.isNeverZero_sound ψ _ hnz
    refine huniq_of_dec fun u _ e e' he he' => ?_
    obtain ⟨c, j, fs⟩ := e
    obtain ⟨c', j', fs'⟩ := e'
    obtain ⟨hc, -, i, -, hf, rfl⟩ := he
    obtain ⟨-, -, i', -, hf', heq⟩ := he'
    obtain ⟨rfl, rfl, hinj⟩ := tagged_inj heq
    -- class `c`'s clause, at a nonzero sort
    have hcl : LfpClause mpC.base2.acval (tgtClsD d Dc out c) ∧
        (tgtClsD d Dc out c).w (tgtClsψ cvc out ψ c) ≠ 0 ∧
        tgtClsM mc pp.toBlockShape out c < (tgtClsD d Dc out c).N := by
      cases hmb : (tgtMajor out c).member with
      | some t =>
        have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
        have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
        have hmemk := (blockRecMajor_run (hm := tgtMemAt_of_member hc hm) (V := V) hμ mpC h
          hmr hr ψ).2.1
        simp only [tgtClsD, tgtClsψ, tgtClsM, hm, if_true]
        refine ⟨(mpC.lfp_ok _ hlfp).1, ?_, Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)⟩
        obtain ⟨_, _, _, rfl⟩ := hdR
        exact hwB
      | none =>
        have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
        have hclc := hcls c hc hmb
        have hC := (mpC.lfp_ok _ hclc.hD).1
        simp only [tgtClsD, tgtClsψ, tgtClsM, hmb, Option.isSome_none, Bool.false_eq_true,
          ↓reduceIte]
        refine ⟨hC, ?_, Nat.lt_of_lt_of_le hclc.hmm hC.kN⟩
        rw [tgtOutCls_w R hr hmb hclc ψ]
        exact hwB
    obtain ⟨hC, hw, hmN⟩ := hcl
    obtain ⟨hj1, hsp, -⟩ := hf
    obtain ⟨hj1', hsp', -⟩ := hf'
    obtain ⟨rfl, rfl⟩ := hC.mkInj _ hw _ hmN j fs j' fs' hj1 hj1' hsp.length_eq hsp'.length_eq hinj
    rfl

/-! ## 4. The graph producer over the classes -/

/-- **THE RECURSOR MODEL OVER THE CLASSES** — `graphRecPre_core` at the
class data (§1) and the target check's rule data, every row the kit
reads produced at every class (§3) except the four the classes' rows do
not carry: the `ih` openers' fit `hihF` and the `ih` chain `hchain`
(both read a CALLEE's class) and the induction `hind` (the classes'
clauses, `NestKit`).  `huniq` is the elimination guard's
(`tgtCls_huniq`). -/
theorem tgtRecPre_cls (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (ψ : Name → Nat) (ρ : Nat → V)
    -- the `ih` openers' fit, at every class
    (hihF : ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length
          (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ)
        (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j)
        (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
          ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs g))
    -- the induction over the classes
    (hind : ∀ xs : List V, ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs) →
        (∃ e, graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
            (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
            (tgtRs out).length
            (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) xs u e ∧
          ∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtRs out).length
              (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
                mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs e →
            P v) → P u) →
      ∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs) → P u)
    -- the `ih` chain
    (hchain : ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
        xs.length = pp.toBlockShape.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').map
          (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c' is) x)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
        SpineFit (chainFrame (tgtRs out).length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
          (xs ++ fs) →
        tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
            (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
            (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtRs out).length
              (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
                mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs
              (c, j, fs)))
          = (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
              envC ψ c j).map (interp V (consList (xs ++ fs)
                (chainFrame (tgtRs out).length a ρ)))) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
          (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
          (fun c j => liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
          (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
          (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ)
          (fun c j => (tgtRbAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j).liftN (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
                j).length
              + (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
                mpC.base2.acval envC ψ c j).length)),
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e := by
  obtain ⟨uOf, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  -- `have` then destructure, every datum named, and the rows whose
  -- hypotheses mention the `ih` data η-expanded: elaborating them against the
  -- producer's binder types directly unfolds the target data (`tgtIhsAV`,
  -- `tgtFrame`, …) past the heartbeat limit, although the types agree
  have H := graphRecPre_core (ℓ := Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
      pp.toBlockShape.large)) (K := (tgtRs out).length) (ψ := ψ) (ρ := ρ)
    (nCt := blockRecNCt (tgtRs out)) (rP := pp.toBlockShape.rulePrefixAt)
    (rds := blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (concl := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (RecTy := blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (es := fun c j => liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (ihs := tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ)
    (mk := tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (Rb0 := tgtRbAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ)
    (ihv := tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
          ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
    (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
    (ihdoms := tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) out mpC.base2.acval envC ψ)
    (Ca := tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ)
    (mp := mpC) (F := F) hμ
    (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ)
    (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out)
    (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
    (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (fun c hc =>
      (recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1)
    (blockRecOneElimLevel ψ (fun c hc => blockRecElimPin_run h hruns ψ hc) (hbitsE ψ))
    (fun c hc => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ)
    (tgtCls_hsplit hμ hcov h R hcls hmr hM ψ ρ)
    (tgtCls_hconcl hμ hcov h R hcls hmr hM ψ ρ)
    (tgtCls_hconclTy hμ hcov h R hcls hmr hM ψ ρ)
    (fun c hc j hj => by
      have := tgtCls_hcerts hμ hcov h R hcls hdR hN hS hcore hmr hM ψ c hc j hj
      exact this)
    (tgtCls_hspF hμ hcov h R hcls hdR hcore hmr hM ψ ρ _)
    (fun xs c hc j hj i fs hi hf g hg => by
      have := hihF xs c hc j hj i fs hi hf g hg
      exact this)
    (fun xs c hc j hj i fs hi hf g => by
      have := tgtCls_hCaB hμ hcov h R hcls hdR hcore hmr hM ψ ρ
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) xs c hc j hj i fs hi hf g
      exact this)
    (fun xs u hu e e' he he' => by
      have := tgtCls_huniq hμ hcov h R hcls hdR hN hS hcore hmr hM hlfp ψ ρ xs u hu e e' he he'
      exact this)
    (fun xs P hP u hu => by
      have := hind xs P hP u hu
      exact this)
    (fun a => tgtCls_hrule hμ hcov h R hcls hdR hcore hmr hM ψ _ a ρ)
    (fun a => tgtCls_hdec hμ hcov h R hcls hdR hcore hmr hM ψ _ a ρ)
    (fun a xs r hr c hc j hj fs hxl hsp => by
      have := hchain a xs r hr c hc j hj fs hxl hsp
      exact this)
  obtain ⟨a, ha, hb⟩ := H
  exact ⟨a, ha, fun e he => hb e he⟩
end Rows

end ConLeche.Model
