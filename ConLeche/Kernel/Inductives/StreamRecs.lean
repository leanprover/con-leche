module

public import ConLeche.Kernel.Inductives.RecCheck
public import ConLeche.Kernel.DeclCheck

@[expose] public section

/-!
# The stream's recursors, against the generated ones

The block's check GENERATES every recursor of an inductive block
(`genRecCheck`, `GenRec.lean`) and compares the stream's records with
them up to definitional equality.  What is installed is the record, read
off the block (`blockRecs`, `Kernel/Install.lean`); these checks say that
it is the generated recursor.

`streamRecsCheck`, per recursor, the stream's record against the
generated recursor at the same position:

* **shape**: as many rules as generated ones, each for the generated
  rule's constructor with its field count; at an auxiliary recursor (an
  outside major) the type's major domain is the container at the firing
  data (`streamNestedOk`, the reading the installed rules fire at);
* **the type**, unless it is the generated one: inferred (a sort) and
  compared with the generated one BINDER BY BINDER up to the major —
  both opened at their own locals, each domain `isDefEq` to the generated
  one at its depth (`recDomsAt`) — and then the residues (`recTyCheck`);
* **each rule**: a function of the recursor's rule prefix and the
  constructor's fields, syntactically (`ruleBinds`: what the ι step
  peels), and, unless its right-hand side is the generated one:
  closed, at the record's level parameters, resolving, inferred, its
  type `isDefEq` to the generated rule's, and `isDefEq` to the generated
  right-hand side (`ruleAgree`).

The records' K flags are checked against the block (`streamKCheck`).  The
comparisons run at the environment holding the constructors and the
generated recursors, with their rules and no tables.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **A record's type's domains against the generated one's**, binder
by binder from binder `j` on (`k` of them): each stored domain
`isDefEq` to the generated one at its depth, both telescopes opened at
their own locals (`openPisAtFvars`; a local's reading ignores its
annotation, so the two openings are one context). -/
def recDomsAt (ops : CheckerOps m) (env : Env) (rec : Name) (sfvs gfvs : List Expr) :
    Nat → Nat → m Unit
  | _, 0 => pure ()
  | j, k + 1 => do
    let a ← unwrapOr sfvs[j]? (.internal "stored recursor: domain index")
    let b ← unwrapOr gfvs[j]? (.internal "stored recursor: domain index")
    unless ← ops.isDefEq env j a.fvarTypeD b.fvarTypeD do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: the \
        domain of binder {j} differs")
    recDomsAt ops env rec sfvs gfvs (j + 1) k

/-- The record's and the generated type, opened `n` binders deep: the
domains, then the residues. -/
def recTyOpened (ops : CheckerOps m) (env : Env) (rec : Name) (n : Nat) :
    Option (List Expr × Expr) → Option (List Expr × Expr) → m Unit
  | some (sfvs, srest), some (gfvs, grest) => do
    recDomsAt ops env rec sfvs gfvs 0 n
    unless ← ops.isDefEq env n srest grest do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: its body \
        after the major differs")
  | none, _ =>
    throw (.invalid s!"the type of the recursor {rec} is not the generated one: it has fewer \
      than {n} binders")
  | some _, none =>
    throw (.internal s!"the generated type of the recursor {rec} has fewer than {n} binders")

/-- **A record's type's check**: closed, at the record's
level parameters `lps`, resolving at `fe`, a type (`inferType`, a sort),
and the generated one (closed: `classRecTyOk`'s check) binder by binder
up to the major (`n` binders) — the domains, then the residues. -/
def recTyCheck (ops : CheckerOps m) (fe : FEnv) (rec : Name)
    (lps : List Name) (n : Nat) (s g : Expr) : m Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the type of the recursor {rec} is not closed")
  unless s.allLevelParamsDefined lps do
    throw (.invalid s!"undeclared universe parameter in the type of the recursor {rec}")
  unless s.constsResolveF fe do
    throw (unresolvedConstsError s!"the type of the recursor {rec}" s)
  let st ← ops.inferType fe.env 0 s
  let _ ← ops.ensureSort fe.env 0 st
  recTyOpened ops fe.env rec n (openPisAtFvars n s 0) (openPisAtFvars n g 0)

/-- **One rule's check**: the record's right-hand side
`s` is closed, at the record's level parameters `lps`, resolving at
`fe`; it and the generated `g` are inferred, their types are
definitionally equal, and so are they. -/
def ruleAgree (ops : CheckerOps m) (fe : FEnv) (rec ctor : Name)
    (lps : List Name) (s g : Expr) : m Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not closed")
  unless s.allLevelParamsDefined lps do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has an undeclared universe \
      parameter")
  unless s.constsResolveF fe do
    throw (unresolvedConstsError s!"the recursor {rec}'s rule for {ctor}" s)
  let ts ← ops.inferType fe.env 0 s
  let tg ← ops.inferType fe.env 0 g
  unless ← ops.isDefEq fe.env 0 ts tg do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side whose \
      type is not the generated one's")
  unless ← ops.isDefEq fe.env 0 s g do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not definitionally equal to the generated one")

/-- **An auxiliary recursor's type fires where the generated one
does**: its major's domain (binder `mI`) is the container at the
firing data's levels, applied to the pins lifted past the index binders
and the index variables — what `NestedRead` states of the generated
type.  `true` at a member major (its rules fire `.plain`). -/
def streamNestedOk (ty : Expr) (mI rP : Nat) : RecRuleFire → Bool
  | .plain => true
  | .levels _ => true
  | .nested lvls pins =>
    match ty.stripPis mI with
    | some (_, .forallE dom _) =>
      (match dom.getAppFn with
       | .const _ us => us == lvls
       | _ => false) &&
      dom.getAppArgs ==
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))
    | _ => false

/-- The firing mode the generated recursor's rules carry at its major
(`generatedRules`): `.nested` at an outside major, `.plain` at a member. -/
def generatedFire (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => .plain

/-- The record's rules' shape against the generated recursor's class: one
rule per constructor of the class, in order, each with its field
count. -/
def streamRulesShape (rec : Name) : List RecRule → List (ConstantVal × Nat) → m Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      throw (.invalid s!"the recursor {rec}'s rule for {r.ctor} is not the generated one's \
        (constructor {c.1.name}, {c.2} fields)")
    streamRulesShape rec rs cs
  | rs, cs =>
    throw (.invalid s!"the recursor {rec} carries {rs.length} more or fewer rules than the \
      generated one ({cs.length} unmatched)")

/-- The record's rules' checks: each binds its arguments (`ruleBinds`) and agrees with the
generated right-hand side at its position (a rule equal to the generated one needs no
comparison). -/
def streamRulesCheck (ops : CheckerOps m) (fe : FEnv) (rec : Name)
    (lps : List Name) (rP : Nat) : List RecRule → List Expr → m Unit
  | r :: rs, g :: gs => do
    ruleBinds rec rP r
    unless r.rhs == g do
      ruleAgree ops fe rec r.ctor lps r.rhs g
    streamRulesCheck ops fe rec lps rP rs gs
  | [], [] => pure ()
  | _, _ => throw (.internal s!"the recursor {rec}: the generated rules are not one per stored rule")

/-- **The comparison of one recursor**: its type unless it is the generated one, and its rules. -/
def streamRecCompare (ops : CheckerOps m) (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) : m Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck ops fe g.1.name g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  streamRulesCheck ops fe g.1.name g.1.levelParams rc.rP rc.rules g.2.2

/-- **One recursor, the stream's against the generated one** (see the module
docstring): the stream's record `rc` against the generated recursor
`(cvG, M, rhssG)` at its position. -/
def streamRecCheck (ops : CheckerOps m) (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) : m Unit := do
  streamRulesShape rc.cvR.name rc.rules g.2.1.ctors
  unless streamNestedOk rc.cvR.type rc.mI rc.rP (generatedFire g.2.1 rc.rP) do
    throw (.invalid s!"the recursor {rc.cvR.name}'s stored type does not apply its \
      major's container at the generated firing data")
  streamRecCompare ops fe rc g

/-- **The block's recursors against the generated ones**, record
by record (the generated family is in the records' order). -/
def streamRecsCheck (ops : CheckerOps m) (fe : FEnv) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → m Unit
  | rc :: rcs, g :: gs => do
    streamRecCheck ops fe rc g
    streamRecsCheck ops fe rcs gs
  | [], [] => pure ()
  | _, _ => throw (.internal "stored recursors: the generated family is not the records'")

/-- **The records' K flags against the block**: each record's flag is the
one the generated recursor has (`recKExpected`).  What the flag says is
then a fact about the block, so nothing of the model reads the record for
it; a difference is a real disagreement of the stream, exit 1.  At a block
whose recursors carry no rules (`BlockShape.noRules`), a record with rules is
rejected here, with its reason. -/
def streamKCheck (p : BlockShape) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → m Unit
  | rc :: rcs, g :: gs => do
    if p.noRules && !rc.rules.isEmpty then
      throw (.invalid s!"the recursor {rc.cvR.name} carries reduction rules, but its block \
        has no large eliminator (hasLargeElim is false), so its recursors have none")
    unless rc.isK == recKExpected p g.2.1 do
      throw (.invalid s!"recursor {rc.cvR.name} declares k := {rc.isK}; the generated recursor \
        of this block is{if recKExpected p g.2.1 then "" else " not"} K-like")
    streamKCheck p rcs gs
  | _, _ => pure ()

/-! ## The declared feature flags -/

/-- The block's name in a message: its first type's. -/
def BlockShape.headName (p : BlockShape) : Name :=
  (p.members.head?.map (·.cvT.name)).getD .anonymous

/-- **One member's flags** (official's checks of lean4 PR #16595): `isK` only at the first
member of a block of one, a proposition with one constructor without fields; `hasProjections`
only at one constructor, no index, not impredicative; `hasEta` only with `hasProjections`, at a
block that is not recursive. -/
def memberFlagsCheck (p : BlockShape) (isRec : Bool) (i : Nat) (ms : MemberShape)
    (f : IndFlags) : Except CheckError Unit := do
  if f.isK && !(i == 0 && p.k == 1 && p.isProp &&
      (match ms.ctors with | [c] => c.2 == 0 | _ => false)) then
    throw (.invalid s!"inductive type {ms.cvT.name} is declared with K-like reduction (isK), \
      but it is not a proposition alone in its block with one constructor without fields")
  if f.hasProjections && !(ms.ctors.length == 1 && ms.nIdx == 0 && !f.isImpredicative) then
    throw (.invalid s!"inductive type {ms.cvT.name} is declared with projections \
      (hasProjections), but it does not have exactly one constructor and no indices, or it is \
      impredicative")
  if f.hasEta && !(f.hasProjections && !isRec) then
    throw (.invalid s!"inductive type {ms.cvT.name} is declared with eta (hasEta), but it has \
      no projections or is recursive")

/-- The members' flags, from position `i` on. -/
def membersFlagsCheck (p : BlockShape) (isRec : Bool) :
    Nat → List MemberShape → List IndFlags → Except CheckError Unit
  | i, ms :: rest, f :: fs => do
    memberFlagsCheck p isRec i ms f
    membersFlagsCheck p isRec (i + 1) rest fs
  | _, _, _ => pure ()

/-- **The block's declared feature flags, validated** (lean4 PR #16595; nothing at a block
without them).  The flags are the stream's, never recomputed; each must be allowed:
`isImpredicative` and `hasLargeElim` agree across the block; `isImpredicative` only at a
proposition; `hasLargeElim` is what the recursor records eliminate at, and is allowed only at a
block that is not impredicative and whose sort is never zero, or of one type with no
constructor, or with one constructor and `hasEta` or `isK`; the members' own flags
(`memberFlagsCheck`).  A nested occurrence of a proposition with one constructor without fields
is rejected: official's auxiliary type would copy its `isK` without being the block's first
type.  An impredicative block nested through a type with projections is rejected: the
auxiliary type would be impredicative (the block's first type's flag) and have projections (the
container's).  `isRec` is official's `is_rec` (`blockIsRec`), `Ms` the classes the recursors
eliminate, `hasProj` whether a stored type has projections (its projection table: a flagged
type's `hasProjections`, an unflagged one's structure-likeness). -/
def blockFlagsCheck (p : BlockShape) (isRec : Bool) (Ms : List TargetMajor)
    (hasProj : Name → Bool) : Except CheckError Unit :=
  match p.flags with
  | none => pure ()
  | some fl => do
    let f0 := fl.headD default
    unless fl.length == p.k do
      throw (.internal s!"inductive block {p.headName}: flags for {fl.length} of {p.k} types")
    unless fl.all fun f => f.isImpredicative == f0.isImpredicative &&
        f.hasLargeElim == f0.hasLargeElim do
      throw (.invalid s!"inductive block {p.headName}: its types disagree on isImpredicative \
        or hasLargeElim")
    if f0.isImpredicative && !p.isProp then
      throw (.invalid s!"inductive block {p.headName} is declared impredicative \
        (isImpredicative), but its type is not a proposition")
    unless f0.hasLargeElim == p.large do
      throw (.invalid s!"inductive block {p.headName}: hasLargeElim is {f0.hasLargeElim}, but \
        its recursors eliminate {if p.large then "into every universe" else "into Prop only"}")
    if f0.hasLargeElim && !(!f0.isImpredicative && (p.resSort.isNeverZero ||
        (p.k == 1 && (p.numCtors == 0 || (p.numCtors == 1 && (f0.hasEta || f0.isK)))))) then
      throw (.invalid s!"inductive block {p.headName} is declared with a large eliminator \
        (hasLargeElim), but it may be a proposition and is not a single type with no \
        constructor, or with one constructor that has eta or K-like reduction")
    membersFlagsCheck p isRec 0 p.members fl
    for M in Ms do
      if M.member.isNone && p.isProp && (match M.ctors with | [c] => c.2 == 0 | _ => false) then
        throw (.invalid s!"inductive block {p.headName} nests {M.ind}, a proposition with one \
          constructor without fields; its K-like reduction cannot be kept inside the block")
      if M.member.isNone && f0.isImpredicative && hasProj M.ind then
        throw (.invalid s!"inductive block {p.headName} is impredicative (isImpredicative) and \
          nests {M.ind}, which has projections; an impredicative type cannot have projections")

end ConLeche
