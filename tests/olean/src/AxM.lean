module
prelude
-- Guards task #444: AxA's and AxB's axioms meet, both axioms at their homes.  Lean merges
-- them (`subsumesInfo`'s axiom/axiom arm: the statement is a proposition by `isPropCheap`),
-- and so must the modular check: an axiom whose type is inferred to be a proposition is a
-- proof, so both copies have one key.
public import Init.Prelude
public import AxA
public import AxB
public section
theorem ax_use : True := Lean.trustCompiler
end
