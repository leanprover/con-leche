import Setlec.Kernel.Expr

/-!
# Declarations and the global environment

Input declarations mirror `Lean.Declaration` (only the kinds the checker
supports so far are present; more are added feature by feature).

The environment is, for now, a simple association list of checked constants.
This is the *verified* reference representation; a faster indexed structure
can replace it later, with a proof that it refines this one.
-/

namespace Setlec

/-- Data common to all constants: name, universe parameters, type. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
  deriving DecidableEq, Repr, Inhabited

/-- One iota rule of a recursor: applying the recursor (with its
parameters, motives and minors) to a `ctor`-headed major premise reduces
to `rhs` applied to the parameters, motives, minors and the constructor's
`nfields` fields. -/
structure RecRule where
  ctor : Name
  nfields : Nat
  rhs : Expr
  deriving DecidableEq, Repr, Inhabited

/-- The trusted basis inductives (hand-written set models; everything
else is reduced to these by the lean-inductive-models preprocessor). -/
inductive BasisKind where
  | eqK | natK | psigmaK | punitK
  deriving DecidableEq, Repr, Inhabited

/-- A declaration presented to the checker. -/
inductive Declaration where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : Expr)
  | thmDecl (val : ConstantVal) (value : Expr)
  | basisDecl (kind : BasisKind)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

/-- The name of a non-basis declaration (basis blocks install several). -/
def name : Declaration → Name
  | .axiomDecl v | .defnDecl v _ | .thmDecl v _ => v.name
  | .basisDecl _ => .anonymous

end Declaration

/-- Information stored about an accepted constant. -/
inductive ConstantInfo where
  | axiomInfo (val : ConstantVal)
  | defnInfo (val : ConstantVal) (value : Expr)
  | thmInfo (val : ConstantVal) (value : Expr)
  /-- A basis inductive type former (whnf-stuck). -/
  | indInfo (val : ConstantVal)
  /-- A basis constructor (whnf-stuck; the iota target). -/
  | ctorInfo (val : ConstantVal) (numParams numFields : Nat)
  /-- A basis recursor with its iota rules. -/
  | recInfo (val : ConstantVal) (numParams numMotives numMinors numIndices : Nat)
      (rules : List RecRule)
  deriving DecidableEq, Repr, Inhabited

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ | .thmInfo v _ => v
  | .indInfo v | .ctorInfo v _ _ | .recInfo v _ _ _ _ _ => v

def name (c : ConstantInfo) : Name := c.toConstantVal.name

def type (c : ConstantInfo) : Expr := c.toConstantVal.type

end ConstantInfo

/-- The global environment: the list of constants accepted so far, newest
first.  Names are unique (the checker rejects duplicates), so the order is
irrelevant for lookup. -/
structure Env where
  consts : List ConstantInfo
  deriving Repr, Inhabited

namespace Env

/-- The empty environment; the starting point of every checker run. -/
def empty : Env := ⟨[]⟩

def find? (env : Env) (n : Name) : Option ConstantInfo :=
  env.consts.find? (·.name == n)

end Env

/-- Do all constants referenced in `e` (including inside `fvar` type
annotations) resolve in `env`?  Checked once per declaration; keeps the
environment well-formedness invariant syntactic. -/
def Expr.constsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ | .lit _ => true
  | .const n _ => (env.find? n).isSome
  | .fvar _ _ ty => ty.constsResolve env
  | .app f a => f.constsResolve env && a.constsResolve env
  | .lam _ ty body _ | .forallE _ ty body _ =>
    ty.constsResolve env && body.constsResolve env
  | .letE _ ty val body =>
    ty.constsResolve env && val.constsResolve env && body.constsResolve env
  | .proj _ _ e => e.constsResolve env

end Setlec
