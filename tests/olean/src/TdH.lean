module
-- Guards task #506: TdB loaded privately, so the `td` its exported `tdn.eq_1` reads is
-- dangling in TdH's export.  The gate makes TdH's exported theorem `ty` read it too (`ty`'s
-- type patched to `(fun _ => True) td`).
import TdB
public def tdn : Nat := (fun (_ : id True) => 0) td
public theorem tdn_zero : tdn = 0 := by rw [tdn]
public theorem ty : True := trivial
