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

/-- A declaration presented to the checker. -/
inductive Declaration where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : Expr)
  | thmDecl (val : ConstantVal) (value : Expr)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

/-- The underlying constant data. -/
def toConstantVal : Declaration → ConstantVal
  | .axiomDecl v | .defnDecl v _ | .thmDecl v _ => v

def name (d : Declaration) : Name := d.toConstantVal.name

end Declaration

/-- Information stored about an accepted constant. -/
inductive ConstantInfo where
  | axiomInfo (val : ConstantVal)
  | defnInfo (val : ConstantVal) (value : Expr)
  | thmInfo (val : ConstantVal) (value : Expr)
  deriving DecidableEq, Repr, Inhabited

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ | .thmInfo v _ => v

def name (c : ConstantInfo) : Name := c.toConstantVal.name

def type (c : ConstantInfo) : Expr := c.toConstantVal.type

end ConstantInfo

/-- The global environment: the list of constants accepted so far, in
declaration order (newest last). -/
structure Env where
  consts : List ConstantInfo
  deriving Repr, Inhabited

namespace Env

/-- The empty environment; the starting point of every checker run. -/
def empty : Env := ⟨[]⟩

def find? (env : Env) (n : Name) : Option ConstantInfo :=
  env.consts.find? (·.name == n)

end Env

end Setlec
