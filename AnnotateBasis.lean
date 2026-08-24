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
          | .recInfo _ mI rP rules =>
            -- fill the install-computed rule fields (constructor
            -- parameter count and the canonical flag) exactly as
            -- `checkIotaRule` does, from the block members annotated
            -- so far, then annotate the right-hand sides
            let rules := rules.map fun r =>
              let cnP := match env.find? r.ctor with
                | some (.ctorInfo _ nP _) => nP
                | _ => 0
              { r with ctorParams := cnP
                       fire := if Expr.recRulePlain ty' mI rP cnP
                         then .plain else .inert }
            match annotateRules rules (.recInfo cv' mI rP rules) with
            | .error e =>
              IO.println s!"ERROR annotating rules of {cv.name}: {e}"
              return
            | .ok rules' => pure (.recInfo cv' mI rP rules')
          | .axiomInfo _ => pure (.axiomInfo cv')
          | .defnInfo _ v h => pure (.defnInfo cv' v h)
          | .thmInfo _ v => pure (.thmInfo cv' v)
          | .projInfo e => pure (.projInfo e)
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
        | .recInfo _ mI rP rules => .recInfo cv' mI rP rules
        | .axiomInfo _ => .axiomInfo cv'
        | .defnInfo _ v h => .defnInfo cv' v h
        | .thmInfo _ v => .thmInfo cv' v
        | .projInfo e => .projInfo e
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
  -- compiler-trust pins (task #95): annotate the reduce-operation and
  -- `ofReduce*` types over the pinned prerequisites (`Eq`/`Nat` basis,
  -- pinned `True` family, installed `trustCompiler`, pinned `Bool`)
  IO.println "===TRUST==="
  let mut envT : Env := ⟨[.indInfo boolCvA {},
    .axiomInfo trustCompilerA,
    .ctorInfo trueIntroCvA 0 0, .indInfo trueCvA {}, natA, eqA]⟩
  for cv in [reduceOpRaw reduceNatName, reduceOpRaw reduceBoolName] do
    match annotateCore envT checkFuel 0 cv.type with
    | .error e =>
      IO.println s!"ERROR annotating {cv.name}: {e}"
      return
    | .ok ty' =>
      IO.println (repr ({ cv with type := ty' } : ConstantVal))
      IO.println "---8<---"
      envT := ⟨.axiomInfo { cv with type := ty' } :: envT.consts⟩
  for cv in [ofReduceRaw ofReduceNatName, ofReduceRaw ofReduceBoolName] do
    match annotateCore envT checkFuel 0 cv.type with
    | .error e =>
      IO.println s!"ERROR annotating {cv.name}: {e}"
      return
    | .ok ty' =>
      IO.println (repr ({ cv with type := ty' } : ConstantVal))
      IO.println "---8<---"
