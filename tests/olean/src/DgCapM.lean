module
-- Guards task #399 (capture): by Lean's import rule M proves False with no
-- axiom: bar.eq_1 is rebound to DgCapQ2.foo.
import DgCapH
import DgCapQ2
public meta import Lean

open Lean in
elab "leaked" : term => do
  -- H's exported `bar.eq_1`, under H's private prefix (which carries the
  -- module name H was compiled as)
  let some (n, _) := (← getEnv).constants.toList.find? fun (n, _) =>
      isPrivateName n && n.toString.endsWith "DgCapH.0.bar.eq_1"
    | throwError "no exported bar.eq_1 of DgCapH"
  return mkConst n []

theorem bar_one : bar = 1 := leaked
theorem boom : False := absurd (bar_zero.symm.trans bar_one) (by decide)
#print axioms boom
