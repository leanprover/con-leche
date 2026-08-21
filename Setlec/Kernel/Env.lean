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
  | eqK | natK | psigmaK | punitK | emptyK | quotK
  deriving DecidableEq, Repr, Inhabited


/-- Definitional capabilities of a stored inductive type, recorded at
install: structural eta for its (single-constructor) values, unit-like
collapse (all inhabitants definitionally equal), and rule K for its
recursor.  The pinned basis blocks carry pinned capabilities; modeled
blocks earn them from checked `_model` theorems. -/
structure IndCaps where
  eta : Bool := false
  /-- The single constructor the eta law reconstructs through
  (meaningful only when `eta`). -/
  etaCtor : Name := .anonymous
  /-- Its parameter count (meaningful only when `eta`). -/
  etaParams : Nat := 0
  /-- Its field count (meaningful only when `eta`). -/
  etaFields : Nat := 0
  unitlike : Bool := false
  /-- The parameter count of the unit-like family (meaningful only
  when `unitlike`). -/
  unitParams : Nat := 0
  ruleK : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Information stored about an accepted constant. -/
inductive ConstantInfo where
  | axiomInfo (val : ConstantVal)
  | defnInfo (val : ConstantVal) (value : Expr)
  | thmInfo (val : ConstantVal) (value : Expr)
  /-- An inductive type former (whnf-stuck) with its capabilities. -/
  | indInfo (val : ConstantVal) (caps : IndCaps)
  /-- A basis constructor (whnf-stuck; the iota target). -/
  | ctorInfo (val : ConstantVal) (numParams numFields : Nat)
  /-- A basis recursor with its iota rules. -/
  | recInfo (val : ConstantVal) (numParams numMotives numMinors numIndices : Nat)
      (rules : List RecRule)
  deriving DecidableEq, Repr, Inhabited

/-- A declaration presented to the checker. -/
inductive Declaration where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : Expr)
  | thmDecl (val : ConstantVal) (value : Expr)
  | basisDecl (kind : BasisKind)
  /-- A preprocessed (modeled) inductive block: type formers,
  constructors and recursors, installed opaquely after checking each
  member against its `_model` counterpart. -/
  | indDecl (block : List ConstantInfo)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

/-- The name of a non-basis declaration (basis blocks install several). -/
def name : Declaration → Name
  | .axiomDecl v | .defnDecl v _ | .thmDecl v _ => v.name
  | .basisDecl _ | .indDecl _ => .anonymous

end Declaration

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ | .thmInfo v _ => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ _ _ => v

def name (c : ConstantInfo) : Name := c.toConstantVal.name

/-- The index count of a recursor (junk elsewhere). -/
def recNi : ConstantInfo → Nat
  | .recInfo _ _ _ _ ni _ => ni
  | _ => 0

/-- The iota rules of a recursor (junk elsewhere). -/
def recRules : ConstantInfo → List RecRule
  | .recInfo _ _ _ _ _ rs => rs
  | _ => []

/-- The parameter count of a constructor (junk elsewhere). -/
def ctorNP : ConstantInfo → Nat
  | .ctorInfo _ nP _ => nP
  | _ => 0

/-- The field count of a constructor (junk elsewhere). -/
def ctorNF : ConstantInfo → Nat
  | .ctorInfo _ _ nF => nF
  | _ => 0

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

end Setlec
