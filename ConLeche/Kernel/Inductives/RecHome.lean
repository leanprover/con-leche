module

public import ConLeche.Kernel.Inductives.FieldNf
public import ConLeche.Kernel.Inductives.BlockInstall

@[expose] public section

/-!
# The home closure of a family's member classes (PRIMREC / NESTHOME)

A recursor family whose call graph has a cycle through the installing
block's members is a NESTED HOME (`_tmp/primrec/PLAN.md`, stage S3): the
cycle runs through the members and the container instances the
positivity walk reaches from them.  The recursor check reads nothing from
the walk; it recomputes the walk's record itself (`nestMemberCtorNf`,
`nestFrameCtorNf`, `FieldNf.lean`) along the CLOSURE of the member
classes: a class is reached when a hole-carrying field of a reached
class names it (`homeLeafKey`) — a member hole names a member class, the
frame's own hole the frame's class, a container instance the class of
that instance — and it is then recomputed at the walk-layout key the leaf
gives (never reconstructed from the class's own major).  Only shallow
classes (`NestClassCtorNf.shallow`) of singleton container groups are
expanded: the walk derives their frames at the EMPTY stack, where the
recomputation is the record (`ClassNf.lean`).

The check that reads the closure (`targetHomeCovers`) asks every class
of a cyclic layer of the family's call graph to be reached, shallow, and
— at an outside major — to name a member and no member at other
parameters; the layer's calls are then checked against the recomputed
normal forms (K.53).  Nothing here rejects: a family whose layers the
closure does not cover is checked as before.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- A recursor class as the home closure reads it: its major's
inductive, levels, parameters, parameter count, constructors and member
index (`none`: an outside major). -/
structure HomeClass where
  ind : Name
  lvls : List Level
  ds : List Expr
  nPc : Nat
  ctors : List (ConstantVal × Nat)
  member : Option Nat
  deriving Inhabited

/-- A reached class: its walk-layout key (`none`: the members' layout)
and its constructors recomputed there. -/
structure HomeReach where
  key : Option (List Expr)
  nfs : List NestClassCtorNf
  deriving Inhabited

/-- A term with every free variable's annotation erased (the comparison
the class keys match up to). -/
def homeErase (e : Expr) : Expr :=
  e.replaceFVars fun i => some (.fvar i (.sort .zero))

/-- The members' holes back to their constants, erased. -/
def homeRb (ctx : NestCtx) (e : Expr) : Expr :=
  homeErase (e.replaceFVars (nestHoleConst ctx []))

/-- **A class's constructors, recomputed at a walk-layout key**: the
members' layout at `none`, a frame at the EMPTY stack at `some dsW`. -/
def homeClassNfs (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (C : HomeClass) : Option (List Expr) → m (List NestClassCtorNf)
  | none => C.ctors.mapM fun c => nestMemberCtorNf ops env ctx holes c.1 c.2
  | some dsW => do
    let grp ← nestClassGroup ctx C.ind C.lvls dsW
    C.ctors.mapM fun c => nestFrameCtorNf ops env ctx C.lvls dsW grp c.1 c.2

/-- **Does a walk-layout leaf name class `C`**, at a parent `P` reached at
`pkey` — and at which walk-layout key: a member hole names the member
class; the frame's own hole (`hiAt 0`, a singleton group) names the
parent's class, at the parent's key; a container instance names its
class, at the instance's parameters (below every frame hole). -/
def homeLeafKey (ctx : NestCtx) (P : HomeClass) (pkey : Option (List Expr)) (C : HomeClass)
    (leaf : Expr) : Option (Option (List Expr)) :=
  match leaf.getAppFn with
  | .fvar i _ =>
    if ctx.nP ≤ i ∧ i < ctx.hiAt 0 then
      if C.member == some (i - ctx.nP) then some none else none
    else
      match pkey with
      | some dsW =>
        if i == ctx.hiAt 0 && C.member.isNone && C.ind == P.ind && C.lvls == P.lvls &&
            C.ds.map homeErase == dsW.map (homeRb ctx) then some (some dsW)
        else none
      | none => none
  | .const I us =>
    let a := leaf.getAppArgs.take C.nPc
    if C.member.isNone && C.ind == I && C.lvls == us && a.length == C.nPc &&
        a.all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt 0) &&
        C.ds.map homeErase == a.map (homeRb ctx) then some (some a)
    else none
  | _ => none

/-- A reached class is EXPANDED (its leaves followed) when shallow. -/
def HomeReach.expands (r : HomeReach) : Bool := r.nfs.all (·.shallow)

/-- The first walk-layout key at which a leaf of a reached, expanded
class names `C`. -/
def homeFind (ctx : NestCtx) (Cs : List HomeClass) (R : List (Option HomeReach))
    (C : HomeClass) : Option (Option (List Expr)) :=
  (List.range Cs.length).findSome? fun a =>
    match R.getD a none with
    | some r =>
      if r.expands then
        r.nfs.findSome? fun e => e.leaves.findSome? fun l? =>
          l?.bind (homeLeafKey ctx (Cs.getD a default) r.key C)
      else none
    | none => none

/-- An outside class the closure may reach: its container's recorded
block a singleton (its frame's hole numbering is the recomputation's),
naming a member, no member itself. -/
def homeReachable (ctx : NestCtx) (C : HomeClass) : Bool :=
  C.member.isSome ||
    ((nestFrameMates ctx C.ind).isEmpty && !ctx.names.contains C.ind &&
      C.ds.any (·.nestOcc ctx.names 0 0))

/-- One round of the closure: every unreached reachable class a leaf of
a reached expanded class names, recomputed at the leaf's key. -/
def homeStep (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (Cs : List HomeClass) (R : List (Option HomeReach)) : m (List (Option HomeReach)) :=
  (List.range Cs.length).mapM fun c =>
    match R.getD c none with
    | some r => pure (some r)
    | none =>
      if homeReachable ctx (Cs.getD c default) then
        match homeFind ctx Cs R (Cs.getD c default) with
        | some key => do
          let nfs ← homeClassNfs ops env ctx holes (Cs.getD c default) key
          pure (some ⟨key, nfs⟩)
        | none => pure none
      else pure none

/-- The closure, `fuel` rounds from `R`. -/
def homeIter (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (Cs : List HomeClass) : Nat → List (Option HomeReach) → m (List (Option HomeReach))
  | 0, R => pure R
  | fuel + 1, R => do
    let R' ← homeStep ops env ctx holes Cs R
    homeIter ops env ctx holes Cs fuel R'

/-- **The home closure of the member classes**: the member classes
reached in the members' layout, then as many rounds as there are
classes. -/
def homeClosure (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (Cs : List HomeClass) : m (List (Option HomeReach)) := do
  let R0 ← (List.range Cs.length).mapM fun c =>
    match (Cs.getD c default).member with
    | some _ => do
      let nfs ← homeClassNfs ops env ctx holes (Cs.getD c default) none
      pure (some ⟨none, nfs⟩)
    | none => pure none
  homeIter ops env ctx holes Cs Cs.length R0

/-- **The closure is consistent at the classes `inS`**: every leaf of a
reached, expanded class that names a class of `inS` gives exactly that
class's own key — a call landing on the leaf lands where the class was
recomputed.  (The walk's keys are canonical, so this never fails on an
accepted walk; the proof reads it instead of the canonicity of the
walk's terms.) -/
def homeConsistent (ctx : NestCtx) (Cs : List HomeClass) (R : List (Option HomeReach))
    (inS : Nat → Bool) : Bool :=
  (List.range Cs.length).all fun a =>
    match R.getD a none with
    | some r =>
      !r.expands ||
      r.nfs.all fun e => e.leaves.all fun l? =>
        match l? with
        | some l => (List.range Cs.length).all fun c =>
          !inS c ||
            match homeLeafKey ctx (Cs.getD a default) r.key (Cs.getD c default) l with
            | some k =>
              match R.getD c none with
              | some rc => rc.key == k
              | none => false
            | none => true
        | none => true
    | none => true

/-- **A layer the closure covers**: every class of rank `n` reached,
expanded, and reachable (`homeReachable`). -/
def homeCovers (ctx : NestCtx) (Cs : List HomeClass) (R : List (Option HomeReach))
    (rank : List Nat) (n : Nat) : Bool :=
  (List.range Cs.length).all fun c =>
    rank.getD c 0 != n ||
      (homeReachable ctx (Cs.getD c default) &&
        match R.getD c none with
        | some r => r.expands
        | none => false)

end ConLeche
