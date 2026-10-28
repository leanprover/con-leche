module
prelude

public import CmpBase

public section

-- not a hole: the solution's opaque constant must have this value
opaque k : Nat := 0

-- a definition hole and an opaque hole
def answer : Nat := sorry

opaque secret : Nat := sorry

end
