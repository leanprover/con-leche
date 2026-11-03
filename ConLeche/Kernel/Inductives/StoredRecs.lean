module

public import ConLeche.Kernel.Inductives.GenRec

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

* **shape**, decided before anything is installed (never through the
  checks' runner): as many stored rules as generated ones, each for the
  generated rule's constructor with its field count; at an auxiliary
  recursor (an outside major) the stored type's major domain is the
  container at the firing data (`storedNestedOk`, the reading the
  installed rules fire at);
* **the type**, unless it is the generated one: inferred (a sort) and
  compared with the generated one BINDER BY BINDER up to the major —
  each stored domain `isDefEq` to the generated one, the telescope
  opened at locals of the GENERATED domains — and then the residues
  (`recTyAgree`);
* **each rule**, unless its right-hand side is the generated one:
  closed, at the record's level parameters, resolving, inferred, its
  type `isDefEq` to the generated rule's, and `isDefEq` to the
  generated right-hand side (`ruleAgree`).

The type and rule comparisons are checks (their only output a
verdict), run through the checks' runner `ck` (task #410).  They run at
the GENERATED install `fe` (the constructors' environment with the
generated recursors and their rules, no tables).
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The stored type against the generated one, binder by binder**: `n`
binders of each, from local `d` on, each stored domain `isDefEq` to the
generated one at its depth, both telescopes opened at a local of the
GENERATED domain; then the two residues.  A stored type that runs out
of binders first is not the generated type. -/
def recTyAgree (ops : CheckerOps m) (env : Env) (rec : Name) :
    Nat → Nat → Expr → Expr → m Unit
  | 0, d, s, g => do
    unless ← ops.isDefEq env d s g do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: its \
        body after binder {d} differs")
  | n + 1, d, .forallE ds bs, .forallE dg bg => do
    unless ← ops.isDefEq env d ds dg do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: the \
        domain of binder {d} differs")
    recTyAgree ops env rec n (d + 1) (bs.instantiate1 (.fvar d dg))
      (bg.instantiate1 (.fvar d dg))
  | _ + 1, d, _, _ =>
    throw (.invalid s!"the type of the recursor {rec} is not the generated one: it has no \
      binder {d}")

/-- **The stored type's check** (task #431): closed, at the record's
level parameters `lps`, resolving at `fe`, a type (`inferType`, a sort),
and the generated one (closed: `classRecTyOk`'s check) binder by binder
up to the major (`n` binders). -/
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
  recTyAgree ops fe.env rec n 0 s g

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
def storedRecCheck (ck : m Unit → m Unit) (ops : CheckerOps m) (w : StructWalkers)
    (fe : FEnv) (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) : m Unit := do
  storedRulesShape rc.cvR.name rc.rules g.2.1.ctors
  unless storedNestedOk rc.cvR.type rc.mI rc.rP (storedFireOf g.2.1 rc.rP) do
    throw (.internal s!"the recursor {rc.cvR.name}'s stored type does not apply its \
      major's container at the generated firing data")
  ck (storedRecCompare ops w fe rc g)

/-- **The block's stored recursors against the generated ones**, record
by record (the generated family is in the records' order). -/
def storedRecsCheck (ck : m Unit → m Unit) (ops : CheckerOps m) (w : StructWalkers)
    (fe : FEnv) : List RecShape → List (ConstantVal × TargetMajor × List Expr) → m Unit
  | rc :: rcs, g :: gs => do
    storedRecCheck ck ops w fe rc g
    storedRecsCheck ck ops w fe rcs gs
  | [], [] => pure ()
  | _, _ => throw (.internal "stored recursors: the generated family is not the records'")

/-- **What is installed**: each generated recursor with the stored type
and the stored right-hand sides, at the generated recursor's name, level
parameters and major (the generated constant is the record's with the
generated type, `classRecTyOk`, so this is the record's constant). -/
def storedOut (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr)) :
    List (ConstantVal × TargetMajor × List Expr) :=
  List.zipWith (fun rc g => ({ g.1 with type := rc.cvR.type }, g.2.1, rc.rules.map (·.rhs)))
    recs out

end ConLeche
