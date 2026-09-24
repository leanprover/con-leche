module

public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The target check's `ih` data for the graph kit (lane RECLIB, B3 (e))

The recursor model's graph kit (`graphFamG`, `BlockRecGraph.lean`)
takes, per rule, the `ih` openers' domains, the graph-built `ih` values
(`ihv`), the calls' targets (`call`), the rule's conclusion `Ca` and a
FIT relation for its decodings.  Today's are read off the classifier's
per-key data (`blockKitTlA`/`EisA`/`FapA`, `blockRuleFrameAt.ihKeys`) and
the slot fit (`ChainFit`).  This file defines the TARGET check's, from
the run alone (`TargetRuleData.lean`'s recomputed frame and
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
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo FEnv BlockShape TargetMajor
  TargetIh TargetFamily TargetFrame)

universe w

section Defs

variable (mode : ConLeche.CheckMode) (F : Nat) (fe : FEnv) (p : BlockShape)
  (formerTys : List Expr)
  (out : List (ConstantVal × TargetMajor × List Expr))

/-- The `(c, j)`-th rule's `ih` variables, in the order the abstraction
allocated them. -/
@[expose] def tgtIhL (c j : Nat) : List TargetIh :=
  (tgtAbs mode F fe p formerTys out c j).2.toList

/-- Entry `r`'s call telescope (the field's whnf-telescope binder
types). -/
@[expose] def tgtTeleTys (c j r : Nat) : List Expr :=
  ((tgtFrame mode F fe p formerTys out c j).teles.getD
    ((tgtIhL mode F fe p formerTys out c j).getD r default).field []).map (·.1)

/-- **The keys**: entry `r` and its callee. -/
@[expose] def tgtKeys (c j : Nat) : List (Nat × Nat) :=
  (List.range (tgtIhL mode F fe p formerTys out c j).length).map fun r =>
    (r, ((tgtIhL mode F fe p formerTys out c j).getD r default).callee)

variable (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)

/-- **Entry `r`'s telescope, read** at the frame, at the family's
elimination bit (the `ih` type's and the call λ's binders, K2). -/
@[expose] def tgtTlA (ψ : Name → Nat) (c j r : Nat) : List (Nat × Nat × AnnotTerm) :=
  ((teleDoms acval env ψ (tgtB p out c j) [] (tgtTeleTys mode F fe p formerTys out c j r)).getD
    []).map fun t => (0, pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)), t)

/-- **Entry `r`'s index arguments, read** at the frame and the
telescope's canonical openers. -/
@[expose] def tgtEisA (ψ : Name → Nat) (c j r : Nat) : List AnnotTerm :=
  ((tgtIhL mode F fe p formerTys out c j).getD r default).idx.map fun x =>
    (denoteMeta acval env ψ (tgtB p out c j + (tgtTeleTys mode F fe p formerTys out c j r).length)
      (x.instantiateList (locOpen (tgtB p out c j)
        (tgtTeleTys mode F fe p formerTys out c j r).length) 0)).getD default

/-- **Entry `r`'s applied field, read**: the field applied to the
telescope's variables, at the frame and the canonical openers. -/
@[expose] def tgtFapA (ψ : Name → Nat) (c j r : Nat) : AnnotTerm :=
  (denoteMeta acval env ψ (tgtB p out c j + (tgtTeleTys mode F fe p formerTys out c j r).length)
    ((Expr.mkAppN ((tgtFrame mode F fe p formerTys out c j).fields.getD
        ((tgtIhL mode F fe p formerTys out c j).getD r default).field default)
      (ConLeche.structTeleVars (tgtTeleTys mode F fe p formerTys out c j r).length)).instantiateList
      (locOpen (tgtB p out c j) (tgtTeleTys mode F fe p formerTys out c j r).length) 0)).getD
    default

/-- **The `ih` variables' domains**: their `ih` types read at the frame,
lifted past the earlier variables (the residue context's `ih` block). -/
@[expose] def tgtIhdomsAV (ψ : Name → Nat) (c j : Nat) : List AnnotTerm :=
  ihDomsLifted (ihTyReads acval env ψ (tgtB p out c j) (tgtIhL mode F fe p formerTys out c j))

/-- **`Ca` at the target data**: the recursor's conclusion at the
constructor (today's expression, `blockRuleConclExpr`), read past the
`ih` variables. -/
@[expose] def tgtCaAV (pp : ConLeche.BlockParts) (ψ : Name → Nat) (c j : Nat) : AnnotTerm :=
  (denoteMeta acval env ψ
    (tgtB pp.toBlockShape out c j + (tgtIhL mode F fe pp.toBlockShape formerTys out c j).length)
    (tgtConclExpr pp.toBlockShape out c j)).getD default

/-- **`fdoms0` at the MAJOR** (lane NESTIND, item 1): the rule's field
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

/-- **The graph-built `ih` values** at the target keys, at the classes'
tuple function `tup` (recursor `c'`'s index tuple of an index spine; a
member class's is `d.tup ψ (p.recTgtAt c')`, an outside class's the
container's `tupW`). -/
@[expose] noncomputable def tgtIhv (ψ : Name → Nat) (ℓ : Nat) (tup : Nat → List V → V)
    (ρ : Nat → V) : List V → Nat → Nat → List V → V → List V := fun xs c j fs g =>
  blockRecIhvAt ℓ tup (consList (xs ++ fs) ρ)
    (tgtKeys mode F fe p formerTys out c j) (tgtTlA mode F fe p formerTys out acval env ψ c j)
    (tgtEisA mode F fe p formerTys out acval env ψ c j)
    (tgtFapA mode F fe p formerTys out acval env ψ c j) g

/-- **The calls' targets** at the target keys, at the classes' tuple
function `tup`. -/
@[expose] def tgtCall (ψ : Name → Nat) (tup : Nat → List V → V) (ρ : Nat → V) (xs : List V)
    (c j : Nat) (fs : List V) (v : V) : Prop :=
  blockGraphCallAt tup
    (tgtKeys mode F fe p formerTys out c j) (tgtTlA mode F fe p formerTys out acval env ψ c j)
    (tgtEisA mode F fe p formerTys out acval env ψ c j)
    (tgtFapA mode F fe p formerTys out acval env ψ c j) (consList (xs ++ fs) ρ) v

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
