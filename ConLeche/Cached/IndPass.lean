module

public import ConLeche.Cached.IndPositivity
public import ConLeche.Kernel.CheckerBase

@[expose] public section

/-!
# The cached twin of the inductive check: the constant guard (task #498)

`checkConstantValC`, the cached `checkConstantValF` (task #497,
`checkConstantValC_eq`, `ConLeche/Verify/Cached/WalkersC.lean`), with its
error and its sort entry point: the twins of the inductive check run it
on the block's formers and constructors and on the stream's recursors.
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- The cached `unresolvedConstsErrorL`: the `sorryAx` test by the
memoized `mentionsAnyConstC` (`unresolvedConstsErrorLC_eq`). -/
def unresolvedConstsErrorLC (strOk : Bool) (where_ : String) (e : Expr) : CheckError :=
  if !strOk && (Expr.hasStrLitGo {} e).1 then
    .notImplemented "string literals before the String support declarations"
  else if Expr.mentionsAnyConstC [sorryAxName] e then
    .notImplemented s!"use of the sorryAx axiom in {where_}"
  else .invalid s!"unknown constant in {where_}"

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode false fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorLC (strLitStoredF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

end ConLeche.Cached
