module

import ConLeche.Kernel.StdAxioms
public import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.NatOpPins
public import ConLeche.Kernel.Inductives.StructParts
public import Std.Data.HashSet

@[expose] public section

/-!
# The declaration checker's common ground

The core entry-point record (`CheckerOps`) with its pure and memoized
instantiations, the common per-declaration constant check
(`checkConstantVal`), and the small strategy-independent helpers the
install paths share (`openPisAtFvars`, `unwrapOr`).
Everything else is in `ConLeche/Kernel/Checker.lean`.
-/

namespace ConLeche

/-- The core entry points the declaration checker runs on: the checker
is written once against this record, monad-polymorphically, and
instantiated with the pure knot (`fueledOps`/`pureOps`, the
verification's subject) and, in `ConLeche/Cached/CheckerC.lean`, with the
memoized cached knot the binary executes. -/
structure CheckerOps (m : Type → Type) where
  inferType : Env → Nat → Expr → m Expr
  isDefEq : Env → Nat → Expr → Expr → m Bool
  ensureSort : Env → Nat → Expr → m Level
  whnf : Env → Nat → Expr → m Expr

variable (mode : CheckMode)

/-- The pure instantiation, at an arbitrary fuel. -/
def fueledOps (F : Nat) : CheckerOps CheckM where
  inferType env d e := inferTypeCore mode false env F d e
  isDefEq env d a b := isDefEqCore mode false env F d a b
  ensureSort env d e := ensureSortCore mode false env F d e
  whnf env d e := ConLeche.whnf mode false env F d e

/-- The pure instantiation, at the standard fuel. -/
def pureOps : CheckerOps CheckM := fueledOps mode checkFuel

/-- **The verdict at a term whose constants do not all resolve.**

Every front door for stream-supplied data — a declaration's type, a
value, a recursor rule's right-hand side — guards it with
`Expr.constsResolve` (or its indexed / cached twin) and throws here on
a `false`.  A term that mentions `sorryAx` DECLINES: that axiom is
tolerated as a declaration and installs nothing, so a use of it is a
positively detected unsupported feature, never a malformed stream.
Anything else is an unknown constant, and rejects with the message
unchanged.  `where_` names the slot, e.g. `"type of Foo"`.

`Expr.mentionsAnyConst` at the one name is the same walk `constsResolve`
just ran (the `.proj` struct name included); the cached driver runs its
memoized twin (`unresolvedConstsErrorLC`, `ConLeche/Cached/CheckerC.lean`).  The companion `unknownConstError`
(`ConLeche/Kernel/Core.lean`) decides the same question inside
inference, which runs after this guard. -/
def unresolvedConstsError (where_ : String) (e : Expr) : CheckError :=
  if e.mentionsAnyConst [sorryAxName] then
    .notImplemented s!"use of the sorryAx axiom in {where_}"
  else .invalid s!"unknown constant in {where_}"

/-- Task #342 S0: does the term contain a string literal?  (Error path
only; a memoized walk.) -/
partial def Expr.hasStrLitGo (memo : Std.HashSet Expr) : Expr → Bool × Std.HashSet Expr
  | .lit (.strVal _) => (true, memo)
  | .bvar _ | .sort _ | .const .. | .lit _ => (false, memo)
  | e =>
    if memo.contains e then (false, memo) else
    let memo := memo.insert e
    match e with
    | .fvar _ ty => Expr.hasStrLitGo memo ty
    | .app f a =>
      let (r, memo) := Expr.hasStrLitGo memo f
      if r then (true, memo) else Expr.hasStrLitGo memo a
    | .lam t b | .forallE t b =>
      let (r, memo) := Expr.hasStrLitGo memo t
      if r then (true, memo) else Expr.hasStrLitGo memo b
    | .letE t v b =>
      let (r, memo) := Expr.hasStrLitGo memo t
      if r then (true, memo) else
      let (r, memo) := Expr.hasStrLitGo memo v
      if r then (true, memo) else Expr.hasStrLitGo memo b
    | .proj _ _ x => Expr.hasStrLitGo memo x
    | _ => (false, memo)

/-- `unresolvedConstsError` with a string-literal guard ahead of it: a
string literal is declined here, before resolution, when the String
support declarations are not yet present. -/
def unresolvedConstsErrorL (strOk : Bool) (where_ : String) (e : Expr) : CheckError :=
  if !strOk && (Expr.hasStrLitGo {} e).1 then
    .notImplemented "string literals before the String support declarations"
  else unresolvedConstsError where_ e

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared
parameters.  `allowOp` is a definition's: only it may take a certified operation's name. -/
def checkConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (allowOp : Bool := false) : m Unit := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless cv.type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless cv.type.constsResolve env do
    throw (unresolvedConstsErrorL (strLitStored env) s!"type of {cv.name}" cv.type)
  let stype ← ops.inferType env 0 cv.type
  let _u ← ops.ensureSort env 0 stype

/-- Unwrap an optional value or fail with the given error (the
`Option`-shaped checks below stay bind-shaped for the verification
batteries). -/
def unwrapOr {α : Type} (o : Option α) (err : CheckError) : m α :=
  match o with
  | some a => pure a
  | none => throw err

end ConLeche
