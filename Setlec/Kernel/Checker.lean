import Setlec.Kernel.Env

/-!
# The checker

`checkDecl` checks one declaration against the current environment and, on
success, returns the extended environment.  `checkDecls` folds it over a list
of declarations, starting from the empty environment.

Current state: every declaration is rejected as "not implemented yet".
Features are added one at a time, each with its verification
(see `Setlec.Model.Consistency`).
-/

namespace Setlec

/-- Errors produced by the checker. -/
inductive CheckError where
  | notImplemented (d : Declaration)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented d => s!"not implemented yet: {d.name}"

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (_env : Env) (d : Declaration) : Except CheckError Env :=
  .error (.notImplemented d)

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ds : List Declaration) : Except CheckError Env :=
  ds.foldlM checkDecl Env.empty

end Setlec
