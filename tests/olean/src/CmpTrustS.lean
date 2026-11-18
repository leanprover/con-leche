-- Task #607: CmpTrustC's hole at a compiler-trust name filled by a definition: declined (its
-- statement would not present the record; the target verdict is a reject, as the solution's
-- own check rejects a definition at that name).
prelude
import Init.Prelude
def Lean.reduceBool (b : Bool) : Bool := b
