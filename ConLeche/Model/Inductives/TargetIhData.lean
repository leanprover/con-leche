module

public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The target check's `ih` data for the graph kit

The recursor model's graph kit (`graphFamG`, `BlockRecGraph.lean`)
takes, per rule, the `ih` openers' domains, the graph-built `ih` values
(`ihv`), the calls' targets (`call`), the rule's conclusion `Ca` and a
FIT relation for its decodings.  This file defines the TARGET check's,
from the run alone (`TargetRuleData.lean`'s recomputed frame and
abstraction) and the lfp clause's HOLE fit:

* the keys are the rule's `ih` VARIABLES (one per distinct call), key
  `r` naming its callee (`tgtKeys`);
* per key, the call's telescope (`tgtTlA`: the field's whnf-telescope
  read at the frame, at the family's elimination bit), its index
  arguments (`tgtEisA`) and the applied field (`tgtFapA`), each read at
  the frame and the telescope's canonical openers (`locOpen`);
* the `ih` variables' domains are their `ih` types' readings, lifted
  past the earlier variables (`tgtIhdomsAV`, `walkCtx_targetRule`'s);
* `Ca` is the recursor's conclusion at the constructor (at the major,
  `tgtConclExpr`) read past the `ih` variables (`tgtCaAV`);
* a decoding's fit is the lfp clause's hole fit at the carrier
  (`blockHoleFitRel`) — no slot datum.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape TargetMajor)

universe w

section Defs

variable (mode : ConLeche.CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
  (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr))

variable (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)

/-- **`fdoms0` at the MAJOR**: the rule's field
openers' domains (the constructor at the major's instantiation), read at
the rule's frame. -/
@[expose] def tgtFdomsAV (ψ : Name → Nat) (j i : Nat) : List AnnotTerm :=
  readOpenedDoms acval env ψ (tgtRP p j) (tgtFieldFvs p out j i)

/-- **`es0` at the MAJOR**: the constructor's index expressions (past the
major's parameter count), read at the rule's frame. -/
@[expose] def tgtEsAV (ψ : Name → Nat) (j i : Nat) : List AnnotTerm :=
  ((tgtCbody p out j i).getAppArgs.drop (tgtMajor out j).nPc).map fun e =>
    (denoteMeta acval env ψ (tgtB p out j i) e).getD default

/-- **`mk0` at the MAJOR**: the fired spine `C.{M.lvls} M.ds f⃗` (the
target check's), read at the rule's frame. -/
@[expose] def tgtMkAV (ψ : Name → Nat) (j i : Nat) : AnnotTerm :=
  (denoteMeta acval env ψ (tgtB p out j i)
    (ConLeche.Expr.mkAppN (.const (tgtCtorOf out j i).1.name (tgtMajor out j).lvls)
      ((tgtMajor out j).ds ++ tgtFieldFvs p out j i))).getD default

variable {V : Type w} [SetTheory V]

end Defs

/-- **A decoding's fit, in HOLE form**: the fields fit class `c`'s
constructor `j` at the index tuple `i` in the lfp clause's hole
reading (`LfpDatum.HFits`) at the carrier — no slot datum. -/
@[expose] def blockHoleFitRel {V : Type w} [SetTheory V] (d : BlockData V) (ψ : Name → Nat)
    (ρ : Nat → V) (mem : Nat → Nat) (xs : List V) (c : Nat) (i : V) (j : Nat) (fs : List V) :
    Prop :=
  d.toLfp.HFits ψ (consList (xs.take d.nP) ρ) (d.toLfp.carrier ψ (consList (xs.take d.nP) ρ))
    i (mem c) j fs

end ConLeche.Model
