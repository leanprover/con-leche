module
-- Guards task #501: H loads DnM1's and DnM2's y, merged as two theorems of one statement.
import DnM1
import DnM2
public theorem z : True := by have := y; trivial
