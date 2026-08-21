import Setlec.Kernel.Checker
import Setlec.Kernel.Basis
import Setlec.Kernel.StdAxioms

open Setlec

/-- Annotate each basis constant's type (and nothing else) in install
order, printing the annotated `ConstantInfo`s as `Repr`. -/
def main : IO Unit := do
  let blocks := [BasisKind.eqK, .natK, .psigmaK, .punitK, .emptyK, .quotK]
  let mut env : Env := Env.empty
  for k in blocks do
    for ci in k.decls do
      let cv := ci.toConstantVal
      match annotateCore env checkFuel 0 cv.type with
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
            match annotateCore env' checkFuel 0 r.rhs with
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
          | .defnInfo _ v h => pure (.defnInfo cv' v h)
          | .thmInfo _ v => pure (.thmInfo cv' v)
        IO.println (repr ci')
        IO.println "---8<---"
        env := ⟨ci' :: env.consts⟩
  -- standard-axiom prerequisite shapes: annotate the Iff/Nonempty
  -- families and the two axioms in dependency order, over the pinned
  -- Eq basis
  IO.println "===STD==="
  let mut envS : Env := ⟨[eqA]⟩
  for ci in iffFamily ++ nonemptyFamily do
    let cv := ci.toConstantVal
    match annotateCore envS checkFuel 0 cv.type with
    | .error e =>
      IO.println s!"ERROR annotating {cv.name}: {e}"
      return
    | .ok ty' =>
      let cv' : ConstantVal := { cv with type := ty' }
      let ci' : ConstantInfo :=
        match ci with
        | .indInfo _ caps => .indInfo cv' caps
        | .ctorInfo _ nP nF => .ctorInfo cv' nP nF
        | .recInfo _ nP nM nm ni rules => .recInfo cv' nP nM nm ni rules
        | .axiomInfo _ => .axiomInfo cv'
        | .defnInfo _ v h => .defnInfo cv' v h
        | .thmInfo _ v => .thmInfo cv' v
      IO.println (repr ci')
      IO.println "---8<---"
      envS := ⟨ci' :: envS.consts⟩
  for cv in [propextRaw, choiceRaw] do
    match annotateCore envS checkFuel 0 cv.type with
    | .error e =>
      IO.println s!"ERROR annotating {cv.name}: {e}"
      return
    | .ok ty' =>
      IO.println (repr ({ cv with type := ty' } : ConstantVal))
      IO.println "---8<---"
