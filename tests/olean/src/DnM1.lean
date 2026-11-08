module
-- Guards task #501 (exports completed on demand): M1 privately imports DgCapQ, so the foo
-- its exported bar1.eq_1 reads is dangling in M1's export.  The gate makes M1's exported
-- theorem `y` read it too (y's type patched to `foo = foo`).
import DgCapQ
public def bar1 : Nat := foo
public theorem bar1_zero : bar1 = 0 := by rw [bar1]; rfl
public theorem y : True := trivial
