module
prelude
public import Init.Prelude

-- task #618: a stand-in for CxZ that re-exports CxX1, which CxA is compiled against, so that
-- CxA's exported cn may read CxX1's cc (see CxM)
public import CxX1

public section

def cz : Nat := 0

end
