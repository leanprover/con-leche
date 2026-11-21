module
prelude
public import Init.Prelude

-- task #618: CxM loads CxA's cn (exported as an axiom of the statement cc, CxA's definition
-- with the value True, cc being CxX1's type Prop) and CxB's cn (a theorem of the statement cc,
-- CxX2's proposition True); Lean's merge keeps one, the two statements being one expression.
-- CxM reads neither, nor CxX1's cc, which it does not load.  Lean accepts the module (CxA was
-- compiled against a stand-in CxZ that re-exported CxX1); so does every worker of its closure.
-- No model family makes CxM's value of cn agree with both modules' (CxA's is ⟦True⟧ = {pt},
-- CxB's is the proof pt).
public import CxA
public import CxB

public section

def cm : Nat := 0

end
