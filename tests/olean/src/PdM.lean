module
prelude

public import Init.Prelude
public import PdA
import all PdB

public section

-- both `pd`s meet here: PdA's definition at its exported level (the
-- assumption of its statement), PdB's theorem at its private level.
-- Lean merges them (a theorem stands for an assumption of its
-- statement, without a test that the statement is a proposition), and
-- so must the modular check: PdA's definition is a proof (its type is
-- inferred to be a proposition), so both copies have one key
theorem pd_use : id True := pd

end
