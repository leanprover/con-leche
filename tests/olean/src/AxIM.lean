module
prelude
-- Guards task #444: AxI's axiom (an axiom at its home) and AxIT's theorem (at its private
-- level) meet.  Lean merges them (`subsumesInfo`'s theorem/axiom arm, with no test that the
-- statement is a proposition), and so must the modular check: the axiom's type is inferred
-- to be a proposition, beyond what `isPropCheap` sees.
public import Init.Prelude
public import AxI
import all AxIT
public section
theorem axi_use : id True := axi
end
