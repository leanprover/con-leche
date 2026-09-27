module

public import ConLeche.Kernel.Inductives.FieldNf

@[expose] public section

/-!
# The home table of a nested block (PRIMREC / NESTHOME)

A recursor family whose call graph has a cycle through a nested block's
members is a NESTED HOME (`_tmp/primrec/PLAN.md`, stage S3): the cycle
runs through the members and the container instances the positivity walk
reaches from them.  The recursor check reads no walk DERIVATION for such
a cycle; what it reads is the HOME TABLE, which the positivity stage
computes right after the walk, at the walk's own context, environment
and operations (`homeTable`): the member classes in the walk's member
layout (`nestMemberCtorNf`), then — along the hole-carrying field leaves
of every SHALLOW entry (`NestClassCtorNf.shallow`: its containers'
parameters mention no frame hole, so the walk derives their frames at
the EMPTY stack again) — every container instance of a singleton
container block, each recomputed at the walk-layout key the leaf gives
(`nestFrameCtorNf`).  Each entry is the walk's own record at a node the
walk derived (`Verify/Inductives/ClassNf.lean`); the table itself is
data, and nothing here rejects.

The recursor check matches its classes against the table
(`homeMatch`: a member class its member's entry, an outside class the
first entry at its container, levels and read-back parameters) and asks
of every class of a cyclic layer it switches off the walk
(`homeCovers`) to be matched, expanded and to name a member; the
matched entries must name each other consistently (`homeConsistent`,
`homePairConsistent` — the walk's keys are canonical, so these hold on
every accepted walk; the proof reads the checks instead of the
canonicity).  The layer's calls are then checked against the matched
normal forms (K.53, `targetCallOk`).
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## The table, at the walk -/

/-- **One class of the home table**: its inductive, levels, member index
(`some`: a member class, in the walk's member layout) or walk-layout key
(`some ds`: a container instance, recomputed at a frame at the empty
stack), the container's parameter count and constructors (as the walk's
context reads them, `nestContainer`), and the recomputed constructors. -/
structure HomeEntry where
  ind : Name
  lvls : List Level
  mem : Option Nat
  key : Option (List Expr)
  nPc : Nat
  ctors : List (ConstantVal × Nat)
  nfs : List NestClassCtorNf
  deriving Inhabited

/-- **What the recursor stage reads off the positivity walk** (K.53′):
the classes of every node (official's
auxiliary types, the outside majors the stage admits), every node's
constructors' normal forms (a call's callee), and the home table
(`homeTable`, empty at a block without containers). -/
structure NestNodes where
  keys : List NestKey := []
  ctors : List NestCtorNf := []
  homes : List HomeEntry := []
  deriving Inhabited

/-- An entry is EXPANDED (its leaves followed) when shallow. -/
def HomeEntry.expands (e : HomeEntry) : Bool := e.nfs.all (·.shallow)

/-- **A class's constructors, recomputed at a walk-layout key**: the
members' layout at `none`, a frame at the EMPTY stack at `some ds`. -/
def homeEntryNfs (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (I : Name) (us : List Level) (ctors : List (ConstantVal × Nat)) :
    Option (List Expr) → m (List NestClassCtorNf)
  | none => ctors.mapM fun c => nestMemberCtorNf ops env ctx holes c.1 c.2
  | some ds => do
    let grp ← nestClassGroup ctx I us ds
    ctors.mapM fun c => nestFrameCtorNf ops env ctx us ds grp c.1 c.2

/-- The member classes, in the walk's member layout. -/
def homeMembers (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) : m (List HomeEntry) :=
  (List.range ctx.names.length).mapM fun t => do
    let nfs ← homeEntryNfs ops env ctx holes (ctx.names.getD t .anonymous) (ctx.lps.map .param)
      (ctorsAs.getD t []) none
    pure { ind := ctx.names.getD t .anonymous, lvls := ctx.lps.map .param, mem := some t,
           key := none, nPc := ctx.nP, ctors := ctorsAs.getD t [], nfs := nfs }

/-- **The container instance a leaf names**, if the table follows it: a
constant-headed leaf of a stored inductive that is no member, whose
recorded block is a singleton (its frame's hole numbering is the
recomputation's), at parameters below every frame hole. -/
def homeLeafNew (ctx : NestCtx) (l : Expr) :
    Option (Name × List Level × List Expr × Nat × List (ConstantVal × Nat)) :=
  match l.getAppFn with
  | .const I us =>
    if ctx.names.contains I || !(nestFrameMates ctx I).isEmpty then none else
    match nestContainer ctx I with
    | some (nPc, ctors) =>
      let a := l.getAppArgs.take nPc
      if a.length == nPc && a.all (fun x => x.bvarB == 0 && x.fvarB ≤ ctx.hiAt 0) then
        some (I, us, a, nPc, ctors)
      else none
    | none => none
  | _ => none

/-- Every container instance the leaves of the expanded entries name. -/
def homeNews (ctx : NestCtx) (T : List HomeEntry) :
    List (Name × List Level × List Expr × Nat × List (ConstantVal × Nat)) :=
  T.flatMap fun e =>
    if e.expands then e.nfs.flatMap fun n => n.leaves.filterMap fun l? => l?.bind (homeLeafNew ctx)
    else []

/-- The instances not yet in the table, recomputed and appended. -/
def homeAdd (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    List HomeEntry → List (Name × List Level × List Expr × Nat × List (ConstantVal × Nat)) →
      m (List HomeEntry)
  | T, [] => pure T
  | T, (I, us, a, nPc, ctors) :: rest => do
    if T.any (fun e => e.ind == I && e.lvls == us && e.key == some a) then
      homeAdd ops env ctx holes T rest
    else
      let nfs ← homeEntryNfs ops env ctx holes I us ctors (some a)
      homeAdd ops env ctx holes
        (T ++ [{ ind := I, lvls := us, mem := none, key := some a, nPc := nPc, ctors := ctors,
                 nfs := nfs }]) rest

/-- The table, `fuel` rounds from `T` (stopping at a round adding
nothing). -/
def homeIter (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    Nat → List HomeEntry → m (List HomeEntry)
  | 0, T => pure T
  | fuel + 1, T => do
    let T' ← homeAdd ops env ctx holes T (homeNews ctx T)
    if T'.length == T.length then pure T' else homeIter ops env ctx holes fuel T'

/-- **The home table** (see the module docstring): the member classes,
then `fuel` rounds along the expanded entries' leaves. -/
def homeTable (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (fuel : Nat) : m (List HomeEntry) := do
  let T0 ← homeMembers ops env ctx holes ctorsAs
  homeIter ops env ctx holes fuel T0

/-- **The home table at a walk of `n` nodes**: none at a block without
containers (`n = 0`: no nested home), else `n + 1` rounds (each round adds
an entry or ends it; the entries' keys are the walk's). -/
def homeTableAt (ops : CheckerOps m) (env : Env) (ctx : NestCtx) (holes : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (n : Nat) : m (List HomeEntry) :=
  if n == 0 then pure [] else homeTable ops env ctx holes ctorsAs (n + 1)

/-! ## The recursor check's reading -/

/-- A recursor class as the home table is matched against: its major's
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

/-- A matched class: its entry's walk-layout key (`none`: the members'
layout) and recomputed constructors. -/
structure HomeReach where
  key : Option (List Expr)
  nfs : List NestClassCtorNf
  deriving Inhabited

/-- A term with every free variable's annotation erased (the comparison
the class keys match up to). -/
def homeErase (e : Expr) : Expr := e.eraseFVarTys

/-- The members' holes back to their constants, erased. -/
def homeRb (ctx : NestCtx) (e : Expr) : Expr :=
  homeErase (e.replaceFVars (nestHoleConst ctx []))

/-- A matched class is EXPANDED when shallow. -/
def HomeReach.expands (r : HomeReach) : Bool := r.nfs.all (·.shallow)

/-- **A class's entry**: a member class its member's (with the member's
constructors), an outside class the first entry of its container at its
levels whose key reads back to its parameters (with the class's
parameter count and constructors). -/
def homeMatch (ctx : NestCtx) (T : List HomeEntry) (C : HomeClass) : Option HomeReach :=
  T.findSome? fun e =>
    match C.member, e.key with
    | some t, none =>
      if e.mem == some t && e.ctors == C.ctors then some ⟨none, e.nfs⟩ else none
    | none, some a =>
      if e.ind == C.ind && e.lvls == C.lvls && e.nPc == C.nPc && e.ctors == C.ctors &&
          C.ds.map homeErase == a.map (homeRb ctx) then some ⟨some a, e.nfs⟩
      else none
    | _, _ => none

/-- **Does a walk-layout leaf name class `C`**, at a parent `P` matched at
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

/-- An outside class the table may stand for: its container's recorded
block a singleton, naming a member, no member itself. -/
def homeReachable (ctx : NestCtx) (C : HomeClass) : Bool :=
  C.member.isSome ||
    ((nestFrameMates ctx C.ind).isEmpty && !ctx.names.contains C.ind &&
      C.ds.any (·.nestOcc ctx.names 0 0))

/-- **The matching is consistent at the classes `inS`**: every leaf of a
matched, expanded class that names a class of `inS` gives exactly that
class's own key — a call landing on the leaf lands where the class was
recomputed. -/
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

/-- **Classes of one key share their key** at the classes `inS`: two
matched outside classes of one container, at one level instantiation,
whose parameters agree up to annotations were matched at one walk-layout
key. -/
def homePairConsistent (Cs : List HomeClass) (R : List (Option HomeReach)) (inS : Nat → Bool) :
    Bool :=
  (List.range Cs.length).all fun a => (List.range Cs.length).all fun c =>
    !(inS a && inS c) || (Cs.getD a default).member.isSome ||
      !((Cs.getD a default).ind == (Cs.getD c default).ind &&
        (Cs.getD a default).lvls == (Cs.getD c default).lvls &&
        (Cs.getD a default).ds.map homeErase == (Cs.getD c default).ds.map homeErase) ||
      match R.getD a none, R.getD c none with
      | some ra, some rc => ra.key == rc.key
      | _, _ => false

/-- **A class the table covers**: reachable, matched and expanded. -/
def homeCovered (ctx : NestCtx) (Cs : List HomeClass) (R : List (Option HomeReach)) (c : Nat) :
    Bool :=
  homeReachable ctx (Cs.getD c default) &&
    match R.getD c none with
    | some r => r.expands
    | none => false

end ConLeche
