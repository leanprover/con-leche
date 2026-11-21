module
-- Guards task #501: as DnM1, over DgCapQ2's foo.
import DgCapQ2
public def bar2 : Nat := foo
public theorem bar2_one : bar2 = 1 := by rw [bar2]; rfl
public theorem y : True := trivial
