module
-- Guards task #506: TdA's definition `td` (exported as the assumption of its statement) is
-- the context's copy; TdH's exported `ty`, its type patched by the gate to read `td`, is read
-- by `td_use`, and TdH's view locates `td` as TdB's theorem.  The two copies are proofs of
-- one statement, `id True`, and one of them is a theorem: they agree with no inference.  The
-- statement is a proposition only by more than `isPropCheap`'s shape.  Lean, importing the
-- patched files, compares nothing here (it never loads TdB's `td`); its import refuses a
-- theorem and a definition of one name loaded together (PdN), as the modular check does.
public import TdA
import TdH
public section
theorem td_use : True := by have := ty; trivial
end
