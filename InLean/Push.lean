module

public import InLean.FEnv
/- `Lean.Kernel.Environment.add` and `markQuotInit` are private to
`Lean.Environment`: inside core, the kernel calls them directly; here
`import all` stands in for being part of that module.  The bodies that use
them are therefore not exposed (`public section`, not `@[expose]`). -/
import all Lean.Environment

/-!
# InLean: adding a constant

The one place InLean writes a kernel environment: core's private
`Kernel.Environment.add` (`addConst`), and the twin of `FEnv.push`.
-/

public section

namespace InLean

open Lean

/-- Add a constant to a kernel environment, unchecked (core's private
`Kernel.Environment.add`). -/
def addConst (env : Kernel.Environment) (ci : ConstantInfo) : Kernel.Environment :=
  env.add ci

/-- Mark the quotient package as declared (core's private `markQuotInit`). -/
def markQuot (env : Kernel.Environment) : Kernel.Environment :=
  env.markQuotInit

/-- Twin of `FEnv.push`. -/
def FEnv.push (fe : FEnv) (ci : ConstantInfo) : FEnv := { fe with env := addConst fe.env ci }

/-- Twin of `FEnv.pushAll`. -/
def FEnv.pushAll : List ConstantInfo → FEnv → FEnv
  | [], fe => fe
  | ci :: rest, fe => FEnv.pushAll rest (fe.push ci)

end InLean
