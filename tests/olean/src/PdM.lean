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
-- so does the modular check: one copy is a theorem, so both are proofs
-- of one proposition, with no inference (task #506)
theorem pd_use : id True := pd

end
