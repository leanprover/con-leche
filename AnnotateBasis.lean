import Setlec.Kernel.Checker
import Setlec.Kernel.Basis

open Setlec

/-- Annotate each basis constant's type (and nothing else) in install
order, printing the annotated `ConstantInfo`s as `Repr`. -/
def main : IO Unit := do
  let blocks := [BasisKind.eqK, .natK, .psigmaK, .punitK]
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
        let ci' : ConstantInfo :=
          match ci with
          | .indInfo _ => .indInfo cv'
          | .ctorInfo _ nP nF => .ctorInfo cv' nP nF
          | .recInfo _ nP nM nm ni rules => .recInfo cv' nP nM nm ni rules
          | .axiomInfo _ => .axiomInfo cv'
          | .defnInfo _ v => .defnInfo cv' v
          | .thmInfo _ v => .thmInfo cv' v
        IO.println (repr ci')
        IO.println "---8<---"
        env := ⟨ci' :: env.consts⟩
