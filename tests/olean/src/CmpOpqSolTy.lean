module
prelude

public import CmpBase

public section

-- tests/olean.sh points `answer`'s value at `flag`'s (a `Bool`): a
-- solution whose value has the wrong type
def flag : Bool := Bool.true

opaque k : Nat := 0

def answer : Nat := 42

opaque secret : Nat := 7

end
