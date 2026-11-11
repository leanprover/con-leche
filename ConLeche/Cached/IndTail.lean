module

public import ConLeche.Cached.IndPass
public import ConLeche.Kernel.Inductives.RecCheck

@[expose] public section

/-!
# The cached twin of the inductive check: the stages after the recursors (task #498)

The production twins of the block check's tail (`checkBlockTail`,
`ConLeche/Kernel/Inductives/BlockTail.lean`) that the cached driver
(`checkBlockTailS`, `ConLeche/Cached/CheckerC.lean`) runs after the
recursor stage: the generated recursors' records
(`blockRecInfosTF`), the stream's recursors against the generated ones
(`streamRecsCheck`, `ConLeche/Kernel/Inductives/StreamRecs.lean`) and the
projection tables' checks (`checkBlockTables`).  Monomorphic `CheckCM`
definitions at a mode and an environment index, calling the cached core
(`inferI`, `defeqI` at `checkFuel`) directly and the cached walks of
`ConLeche/Cached/ExprOpsC.lean` where the specification runs the plain
ones.  Each is the specification at the shared operations
(`ConLeche/Verify/Cached/IndTailC.lean`; the tables' checks, which read
the environment, at the index `mkFEnv env` of the specification's `env`).
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-! ## The generated recursors' records -/

/-- The cached `auxRuleFire`: the class's parameters closed by
`abstractPrefixC` (one pass each). -/
def auxRuleFireC (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  .nested M.lvls (M.ds.map (Expr.abstractPrefixC rP 0))

/-- The cached `generatedRules`. -/
def generatedRulesC (rP : Nat) (M : TargetMajor) (rhss : List Expr) : List RecRule :=
  let rules := sumRules M.ctors rhss
  match M.member with
  | none =>
    let fire := auxRuleFireC M rP
    rules.map fun rl => { rl with fire := fire }
  | some _ => rules

/-- The cached `blockRecInfosTF`: the checked family's records, at their
majors, in push order. -/
def blockRecInfosTC
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → List ConstantInfo
  | _, [] => []
  | m, (cv, M, rhss) :: rest =>
    .recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (recKExpected p M) (generatedRulesC (p.rulePrefixAt m) M rhss)
      :: blockRecInfosTC p (m + 1) rest

/-- The cached `generatedFire`. -/
def generatedFireC (M : TargetMajor) (rP : Nat) : RecRuleFire :=
  match M.member with
  | none => auxRuleFireC M rP
  | some _ => .plain

/-! ## The stream's recursors against the generated ones -/

/-- The cached `streamNestedOk`: the pins lifted by `liftLooseBVarsC`, the
major domain's spine read by `getAppArgsC`. -/
def streamNestedOkC (ty : Expr) (mI rP : Nat) : RecRuleFire → Bool
  | .plain => true
  | .levels _ => true
  | .nested lvls pins =>
    match ty.stripPis mI with
    | some (_, .forallE dom _) =>
      (match dom.getAppFn with
       | .const _ us => us == lvls
       | _ => false) &&
      Expr.getAppArgsC dom ==
        pins.map (fun e => Expr.liftLooseBVarsC (mI - rP) e 0) ++
          (List.range (mI - rP)).map (fun i => Expr.bvar (mI - rP - 1 - i))
    | _ => false

/-- The cached `recDomsAt`. -/
def recDomsAtC (fe : FEnv) (rec : Name) (sfvs gfvs : List Expr) :
    Nat → Nat → CheckCM Unit
  | _, 0 => pure ()
  | j, k + 1 => do
    let a ← unwrapOr sfvs[j]? (.internal "stored recursor: domain index")
    let b ← unwrapOr gfvs[j]? (.internal "stored recursor: domain index")
    unless ← defeqI mode fe false checkFuel j a.fvarTypeD b.fvarTypeD do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: the \
        domain of binder {j} differs")
    recDomsAtC fe rec sfvs gfvs (j + 1) k

/-- The cached `recTyOpened`. -/
def recTyOpenedC (fe : FEnv) (rec : Name) (n : Nat) :
    Option (List Expr × Expr) → Option (List Expr × Expr) → CheckCM Unit
  | some (sfvs, srest), some (gfvs, grest) => do
    recDomsAtC mode fe rec sfvs gfvs 0 n
    unless ← defeqI mode fe false checkFuel n srest grest do
      throw (.invalid s!"the type of the recursor {rec} is not the generated one: its body \
        after the major differs")
  | none, _ =>
    throw (.invalid s!"the type of the recursor {rec} is not the generated one: it has fewer \
      than {n} binders")
  | some _, none =>
    throw (.internal s!"the generated type of the recursor {rec} has fewer than {n} binders")

/-- The cached `recTyCheck`: the guards by the memoised walks, the two
types opened by `openPisAtFvarsC`. -/
def recTyCheckC (fe : FEnv) (rec : Name) (lps : List Name) (n : Nat) (s g : Expr) :
    CheckCM Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the type of the recursor {rec} is not closed")
  unless Expr.allLevelParamsDefinedC lps s do
    throw (.invalid s!"undeclared universe parameter in the type of the recursor {rec}")
  unless constsResolveFC fe s do
    throw (unresolvedConstsErrorLC true s!"the type of the recursor {rec}" s)
  let st ← inferI mode fe false checkFuel false 0 s
  let _ ← ensureSortI mode fe false checkFuel 0 st
  recTyOpenedC mode fe rec n (openPisAtFvarsC n s 0) (openPisAtFvarsC n g 0)

/-- The cached `ruleAgree`. -/
def ruleAgreeC (fe : FEnv) (rec ctor : Name) (lps : List Name) (s g : Expr) :
    CheckCM Unit := do
  unless s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not closed")
  unless Expr.allLevelParamsDefinedC lps s do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has an undeclared universe \
      parameter")
  unless constsResolveFC fe s do
    throw (unresolvedConstsErrorLC true s!"the recursor {rec}'s rule for {ctor}" s)
  let ts ← inferI mode fe false checkFuel false 0 s
  let tg ← inferI mode fe false checkFuel false 0 g
  unless ← defeqI mode fe false checkFuel 0 ts tg do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side whose \
      type is not the generated one's")
  unless ← defeqI mode fe false checkFuel 0 s g do
    throw (.invalid s!"the recursor {rec}'s rule for {ctor} has a right-hand side that is \
      not definitionally equal to the generated one")

/-- The cached `streamRulesShape`. -/
def streamRulesShapeC (rec : Name) : List RecRule → List (ConstantVal × Nat) → CheckCM Unit
  | [], [] => pure ()
  | r :: rs, c :: cs => do
    unless r.ctor == c.1.name && r.nfields == c.2 do
      throw (.invalid s!"the recursor {rec}'s rule for {r.ctor} is not the generated one's \
        (constructor {c.1.name}, {c.2} fields)")
    streamRulesShapeC rec rs cs
  | rs, cs =>
    throw (.invalid s!"the recursor {rec} carries {rs.length} more or fewer rules than the \
      generated one ({cs.length} unmatched)")

/-- The cached `streamRulesCheck`. -/
def streamRulesCheckC (fe : FEnv) (rec : Name) (lps : List Name) :
    List RecRule → List Expr → CheckCM Unit
  | r :: rs, g :: gs => do
    unless r.rhs == g do
      ruleAgreeC mode fe rec r.ctor lps r.rhs g
    streamRulesCheckC fe rec lps rs gs
  | [], [] => pure ()
  | _, _ =>
    throw (.internal s!"the recursor {rec}: the generated rules are not one per stored rule")

/-- The cached `streamRecCompare`. -/
def streamRecCompareC (fe : FEnv) (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) :
    CheckCM Unit := do
  unless rc.cvR.type == g.1.type do
    recTyCheckC mode fe g.1.name g.1.levelParams (rc.mI + 1) rc.cvR.type g.1.type
  streamRulesCheckC mode fe g.1.name g.1.levelParams rc.rules g.2.2

/-- The cached `streamRecCheck`. -/
def streamRecCheckC (fe : FEnv) (rc : RecShape) (g : ConstantVal × TargetMajor × List Expr) :
    CheckCM Unit := do
  streamRulesShapeC rc.cvR.name rc.rules g.2.1.ctors
  unless streamNestedOkC rc.cvR.type rc.mI rc.rP (generatedFireC g.2.1 rc.rP) do
    throw (.invalid s!"the recursor {rc.cvR.name}'s stored type does not apply its \
      major's container at the generated firing data")
  streamRecCompareC mode fe rc g

/-- The cached `streamRecsCheck`. -/
def streamRecsCheckC (fe : FEnv) :
    List RecShape → List (ConstantVal × TargetMajor × List Expr) → CheckCM Unit
  | rc :: rcs, g :: gs => do
    streamRecCheckC mode fe rc g
    streamRecsCheckC fe rcs gs
  | [], [] => pure ()
  | _, _ => throw (.internal "stored recursors: the generated family is not the records'")

/-! ## The projection tables -/

/-- The cached `checkStructProjTable`: the bodies' guards by the memoised
walks. -/
def checkStructProjTableC (t : ProjTable) (fe : FEnv) : CheckCM Unit := do
  unless t.bodies.size = t.numFields ∧ t.bodies.all (fun b => !b.hasFvar &&
      Expr.allLevelParamsDefinedC t.levelParams b && constsResolveFC fe b &&
      b.looseBVarsBounded (t.numParams + 1)) do
    throw (.internal "direct structure: projection body scoping")
  unless (fe.find? t.structName).isSome do
    throw (.internal "direct structure: projection table before its structure")
  unless (fe.findTable? t.structName).isNone do
    throw (.invalid "projection table taken")

/-- The cached `checkBlockTables`. -/
def checkBlockTablesC (fe : FEnv) : List ProjTable → CheckCM Unit
  | [] => pure ()
  | t :: rest => do
    checkStructProjTableC t fe
    checkBlockTablesC fe rest

end ConLeche.Cached
