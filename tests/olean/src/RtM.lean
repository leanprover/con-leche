module
prelude

public import RtA

/- Task #448: reads RtA's theorem at the compiler-trust name `Lean.reduceBool`: rejected by
   the reach (`stmtRecord`); Lean accepts the module. -/

public theorem rtUse : RtT := Lean.reduceBool
