module

public import Fragment.Syntax

@[expose] public section

/-!
# Scope

Three syntactic predicates the declaration checks read: a term is
**closed** below a depth, it **mentions** some constants, and it
**uses** some level parameters.  The checker checks them once per
declaration (con-leche's `looseBVarsBounded`, `constsResolve`,
`allLevelParamsDefined`); the model reads a term only through the
variables below its depth, the constants it mentions and the
parameters it uses (`Hygiene.lean`).
-/

namespace Fragment

namespace Level

/-- Every parameter of the level is one of `ps`. -/
def paramsIn (ps : List Name) : Level → Bool
  | zero => true
  | succ l => paramsIn ps l
  | max a b => paramsIn ps a && paramsIn ps b
  | imax a b => paramsIn ps a && paramsIn ps b
  | param n => ps.contains n

end Level

namespace PropWhen

/-- Every parameter the datum mentions is one of `ps`. -/
def paramsIn (ps : List Name) : PropWhen → Bool
  | never => true
  | whenZero qs => qs.list.all ps.contains

end PropWhen

namespace Expr

/-- Every bound variable is below `k`: the term lives under `k`
binders. -/
def closedAt (k : Nat) : Expr → Bool
  | bvar i => decide (i < k)
  | sort _ => true
  | const _ _ => true
  | app f a => closedAt k f && closedAt k a
  | lam A _ b => closedAt k A && closedAt (k + 1) b
  | pi A _ B => closedAt k A && closedAt (k + 1) B

/-- The constants a term mentions. -/
def consts : Expr → List Name
  | bvar _ => []
  | sort _ => []
  | const c _ => [c]
  | app f a => consts f ++ consts a
  | lam A _ b => consts A ++ consts b
  | pi A _ B => consts A ++ consts B

/-- Every level parameter the term uses — in sorts, constant
instantiations and annotations — is one of `ps`. -/
def lparamsIn (ps : List Name) : Expr → Bool
  | bvar _ => true
  | sort u => u.paramsIn ps
  | const _ ls => ls.all (·.paramsIn ps)
  | app f a => lparamsIn ps f && lparamsIn ps a
  | lam A pw b => lparamsIn ps A && pw.paramsIn ps && lparamsIn ps b
  | pi A pw B => lparamsIn ps A && pw.paramsIn ps && lparamsIn ps B

end Expr

end Fragment
