module

public import ConLeche.Kernel.Inductives.RecCheck

@[expose] public section

/-!
# The stored recursors, against the generated ones (task #431)

The installer GENERATES every recursor of an inductive block
(`genRecCheck`, `GenRec.lean`) and installs the STORED one — the
record's type and its rules' right-hand sides — once the two agree up
to definitional equality.  Everything else of the installed recursor
(its major index and rule prefix, each rule's constructor, field count,
constructor parameter count, firing mode and rescue bits) is the
generator's.

`storedRecsCheck`, per recursor, the stream's record against the
generated recursor at the same position:

* **shape**, decided before anything is installed: as many stored rules as generated ones, each for the
  generated rule's constructor with its field count; at an auxiliary
  recursor (an outside major) the stored type's major domain is the
  container at the firing data (`storedNestedOk`, the reading the
  installed rules fire at);
* **the type**, unless it is the generated one: inferred (a sort) and
  compared with the generated one BINDER BY BINDER up to the major —
  both opened at their own locals, each stored domain `isDefEq` to the
  generated one at its depth (`recDomsAt`) — and then the residues
  (`recTyCheck`);
* **each rule**, unless its right-hand side is the generated one:
  closed, at the record's level parameters, resolving, inferred, its
  type `isDefEq` to the generated rule's, and `isDefEq` to the
  generated right-hand side (`ruleAgree`).

The type and rule comparisons are checks (their only output a
verdict).  They run at the GENERATED install `fe` (the constructors' environment with the
generated recursors and their rules, no tables).
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The stored type's domains against the generated one's**, binder
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

/-- The stored and the generated type, opened `n` binders deep: the
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

/-- **The stored type's check** (task #431): closed, at the record's
level parameters `lps`, resolving at `fe`, a type (`inferType`, a sort),
and the generated one (closed: `classRecTyOk`'s check) binder by binder
up to the major (`n` binders) — the domains, then the residues. -/
def recTyCheck (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (rec : Name)
    (lps : List Name) (n : Nat) (s g : Expr) : m Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the type of the recursor {rec} is not closed")
  unless s.allLevelParamsDefined lps do
    throw (.invalid s!"undeclared universe parameter in the type of the recursor {rec}")
  unless w.resolve fe s do
    throw (unresolvedConstsError s!"the type of the recursor {rec}" s)
  let st ← ops.inferType fe.env 0 s
  let _ ← ops.ensureSort fe.env 0 st
  recTyOpened ops fe.env rec n (openPisAtFvars n s 0) (openPisAtFvars n g 0)

/-- **One stored rule's check** (task #431): the stored right-hand side
`s` is closed, at the record's level parameters `lps`, resolving at
`fe`; it and the generated `g` are inferred, their types are
definitionally equal, and so are they. -/
def ruleAgree (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (rec ctor : Name)
    (lps : List Name) (s g : Expr) : m Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not closed")
  unless s.allLevelParamsDefined lps do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has an undeclared universe \
      parameter")
  unless w.resolve fe s do
    throw (unresolvedConstsError s!"the recursor {rec}'s rule for {ctor}" s)
  let ts ← ops.inferType fe.env 0 s
  let tg ← ops.inferType fe.env 0 g
  unless ← ops.isDefEq fe.env 0 ts tg do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side whose \
      type is not the generated one's")
  unless ← ops.isDefEq fe.env 0 s g do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not definitionally equal to the generated one")

/-- **An auxiliary recursor's stored type fires where the generated one
does**: its major's domain (binder `mI`) is the container at the
firing data's levels, applied to the pins lifted past the index binders
and the index variables — what `NestedRead` states of the generated
type.  `true` at a member major (its rules fire `.plain`). -/
def storedNestedOk (ty : Expr) (mI rP : Nat) : RecRuleFire → Bool
  | .plain => true
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
(`tgtStoredRules`): `.nested` at an outside major, `.plain` at a member. -/
def storedFireOf (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  match M.member with
  | none => auxRuleFire M rP
  | some _ => .plain

/-- The stored rules' shape against the generated recursor's class: one
rule per constructor of the class, in order, each with its field
count. -/
def storedRulesShape (rec : Name) : List RecRule → List (ConstantVal × Nat) → m Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      throw (.invalid s!"the recursor {rec}'s rule for {r.ctor} is not the generated one's \
        (constructor {c.1.name}, {c.2} fields)")
    storedRulesShape rec rs cs
  | rs, cs =>
    throw (.invalid s!"the recursor {rec} carries {rs.length} more or fewer rules than the \
      generated one ({cs.length} unmatched)")

/-- The stored rules' checks, each against the generated right-hand side
at its position (a rule equal to the generated one needs none). -/
def storedRulesCheck (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (rec : Name)
    (lps : List Name) : List RecRule → List Expr → m Unit
  | r :: rs, g :: gs => do
    unless r.rhs == g do
      ruleAgree ops w fe rec r.ctor lps r.rhs g
    storedRulesCheck ops w fe rec lps rs gs
  | [], [] => pure ()
  | _, _ => throw (.internal s!"the recursor {rec}: the generated rules are not one per stored rule")

/-- **The comparison of one recursor** (a check, task #410's runner
runs it): its stored type unless it is the generated one, and its
stored rules. -/
def storedRecCompare (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) : m Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheck ops w fe g.1.name g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  storedRulesCheck ops w fe g.1.name g.1.levelParams rc.rules g.2.2

/-- **One recursor, stored against generated** (see the module
docstring): the stream's record `rc` against the generated recursor
`(cvG, M, rhssG)` at its position. -/
def storedRecCheck (ops : CheckerOps m) (w : StructWalkers)
    (fe : FEnv) (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) : m Unit := do
  storedRulesShape rc.cvR.name rc.rules g.2.1.ctors
  unless storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) do
    throw (.invalid s!"the recursor {rc.cvR.name}'s stored type does not apply its \
      major's container at the generated firing data")
  storedRecCompare ops w fe rc g

/-- **The block's stored recursors against the generated ones**, record
by record (the generated family is in the records' order). -/
def storedRecsCheck (ops : CheckerOps m) (w : StructWalkers)
    (fe : FEnv) : List RecShape → List (ConstantVal × TargetMajor × List Expr) → m Unit
  | rc :: rcs, g :: gs => do
    storedRecCheck ops w fe rc g
    storedRecsCheck ops w fe rcs gs
  | [], [] => pure ()
  | _, _ => throw (.internal "stored recursors: the generated family is not the records'")

/-- **The records' K flags against the block**: each record's flag is the
one the generated recursor has (`recKExpected`).  What the flag says is
then a fact about the block, so nothing of the model reads the record for
it; a difference is a real disagreement of the stream, exit 1. -/
def storedKCheck (p : BlockShape) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → m Unit
  | rc :: rcs, g :: gs => do
    unless rc.isK == recKExpected p g.2.1 do
      throw (.invalid s!"recursor {rc.cvR.name} declares k := {rc.isK}; the generated recursor \
        of this block is{if recKExpected p g.2.1 then "" else " not"} K-like")
    storedKCheck p rcs gs
  | _, _ => pure ()

/-- **What is installed**: each generated recursor with the stored type
and the stored right-hand sides, at the generated recursor's name, level
parameters and major (the generated constant is the record's with the
generated type, `classRecTyOk`, so this is the record's constant). -/
def storedOut (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    List (ConstantVal × TargetMajor × List Expr) :=
  List.zipWith (fun rc g => ({ g.1 with type := rc.cvR.type }, g.2.1, rc.rules.map (·.rhs)))
    recs out

end ConLeche
