import Setlec.Kernel.Checker
import Setlec.Kernel.Basis

open Setlec

/-- Annotate each basis constant's type (and nothing else) in install
order, printing the annotated `ConstantInfo`s as `Repr`. -/
def main : IO Unit := do
  let blocks := [BasisKind.eqK, .natK, .psigmaK, .punitK, .emptyK]
  let mut env : Env := Env.empty
  for k in blocks do
    for ci in k.decls do
      let cv := ci.toConstantVal
      match annotate env 0 cv.type with
      | .error e =>
        IO.println s!"ERROR annotating {cv.name}: {e}"
        return
      | .ok ty' =>
        let cv' : ConstantVal := { cv with type := ty' }
        -- annotate iota-rule right-hand sides against the environment
        -- extended with the (annotated) block members so far, plus the
        -- recursor itself (rule rhs may mention it)
        let annotateRules (rules : List RecRule) (self : ConstantInfo) :
            Except String (List RecRule) := Id.run do
          let env' : Env := ⟨self :: env.consts⟩
          let mut out : List RecRule := []
          for r in rules do
            match annotate env' 0 r.rhs with
            | .error e => return .error s!"{e}"
            | .ok rhs' => out := out ++ [{ r with rhs := rhs' }]
          return .ok out
        let ci' : ConstantInfo ←
          match ci with
          | .indInfo _ caps => pure (.indInfo cv' caps)
          | .ctorInfo _ nP nF => pure (.ctorInfo cv' nP nF)
          | .recInfo _ nP nM nm ni rules =>
            match annotateRules rules (.recInfo cv' nP nM nm ni rules) with
            | .error e =>
              IO.println s!"ERROR annotating rules of {cv.name}: {e}"
              return
            | .ok rules' => pure (.recInfo cv' nP nM nm ni rules')
          | .axiomInfo _ => pure (.axiomInfo cv')
          | .defnInfo _ v => pure (.defnInfo cv' v)
          | .thmInfo _ v => pure (.thmInfo cv' v)
        IO.println (repr ci')
        IO.println "---8<---"
        env := ⟨ci' :: env.consts⟩
