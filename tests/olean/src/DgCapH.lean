module
-- Guards task #399 (capture): H privately imports DgCapQ; bar.eq_1 : bar = foo
-- is exported under a private name.
import DgCapQ
public def bar : Nat := foo
public theorem bar_zero : bar = 0 := by
  rw [bar]; rfl
