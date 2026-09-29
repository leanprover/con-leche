module

public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Verify.Inductives.RecCheckRun

public section

/-!
# The target check's rule data, as functions of the run

The model's rule data (`ihs`, `Rb0`, …) are functions of the level
valuation and of the (recursor, constructor) position alone.  This file
RECOMPUTES every intermediate value of `targetRule` from the stored
data and pins them: at a `targetRecCheck` run, the `(j, i)`-th rule's run
record (`TargetRuleRun`) has exactly these witnesses.

The stored family, in the model's format, is `tgtRs out`: the checked
recursor, its annotated rules, the major's index count and its
constructors — the stage record's `rs`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape TargetMajor)

section Defs

variable (mode : ConLeche.CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
  (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr))

/-- The `j`-th stored recursor's type. -/
@[expose] def tgtRecTy (j : Nat) : Expr := (out.getD j default).1.type
/-- The `j`-th recursor's major (a member, or an outside container at its
instantiation). -/
@[expose] def tgtMajor (j : Nat) : TargetMajor := (out.getD j default).2.1
/-- The `j`-th recursor's rule prefix and major index (its record's). -/
@[expose] def tgtRP (j : Nat) : Nat := (p.recs.getD j default).rP
/-- The `i`-th constructor of the `j`-th recursor's major. -/
@[expose] def tgtCtorOf (j i : Nat) : ConstantVal × Nat := (tgtMajor out j).ctors.getD i default
/-- The `(j, i)`-th stored rule. -/
@[expose] def tgtRhsOf (j i : Nat) : Expr := ((out.getD j default).2.2).getD i default
/-- The rule's width `rP + nF`. -/
@[expose] def tgtB (j i : Nat) : Nat := tgtRP p j + (tgtCtorOf out j i).2

/-- The rule's prefix openers. -/
@[expose] def tgtPrefFvs (j : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (tgtRP p j) (tgtRecTy out j) 0).map (·.1)).getD []
/-- The constructor at the major's instantiation (`targetCtorAt`: a
member's stored at the block's levels, an outside container's
instantiated at the major's) and parameters (a member's: the recursor
type's first `nP` openers). -/
@[expose] def tgtCrest (j i : Nat) : Expr :=
  (ConLeche.instPisWith (tgtMajor out j).ds
    (ConLeche.targetCtorAt (tgtMajor out j) (tgtCtorOf out j i).1)).getD default
/-- The rule's field openers. -/
@[expose] def tgtFieldFvs (j i : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (tgtCtorOf out j i).2 (tgtCrest out j i) (tgtRP p j)).map (·.1)).getD []
/-- The constructor's conclusion at the rule's field openers (its index
expressions are `getAppArgs.drop nPc`, the major's parameter count). -/
@[expose] def tgtCbody (j i : Nat) : Expr :=
  ((ConLeche.openPisAtFvars (tgtCtorOf out j i).2 (tgtCrest out j i) (tgtRP p j)).map (·.2)).getD
    default
/-- **The recursor's conclusion at the constructor, AT THE MAJOR** (the
target check's `concl`, `targetRule`): the recursor type at the prefix,
the constructor's index expressions and the fired constructor
`C.{M.lvls} M.ds f⃗`. -/
@[expose] def tgtConclExpr (j i : Nat) : Expr :=
  (ConLeche.Expr.instPisAtLift
    (tgtPrefFvs p out j ++ (tgtCbody p out j i).getAppArgs.drop (tgtMajor out j).nPc
      ++ [Expr.mkAppN (.const (tgtCtorOf out j i).1.name (tgtMajor out j).lvls)
          ((tgtMajor out j).ds ++ tgtFieldFvs p out j i)])
    (tgtRecTy out j)).getD default
/-- The rule's body (below its `rP + nF` λ-binders). -/
@[expose] def tgtBody (j i : Nat) : Expr :=
  (((tgtRhsOf out j i).stripLams (tgtB p out j i)).map (·.2)).getD default
/-- The member abstraction at the rule's holes. -/
@[expose] def tgtAbsM (j i : Nat) : Expr → Expr :=
  ConLeche.targetAbs p.memberNames (p.lps.map .param)
    (ConLeche.targetHoles formerTys (tgtB p out j i))
variable (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)

end Defs

end ConLeche.Model

namespace ConLeche.Model

open ConLeche (FEnv BlockShape TargetMajor RecShape CheckMode)

/-! ## The pinning -/

section Pin

variable {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape} {nested : Bool}
  {block : List ConstantInfo} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

/-- The recomputed constructor at a stored rule is the stored one. -/
theorem tgtCtorOf_at {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) : tgtCtorOf out j i = cA := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtCtorOf, tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some]
    simp only at hcA
    rw [hcA, Option.getD_some]

end Pin

end ConLeche.Model
