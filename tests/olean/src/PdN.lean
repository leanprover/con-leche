module
prelude

public import Init.Prelude
import all PdA
public import PdB

public section

-- task #506: PdA's definition of `id True` at its private level (a definition, not the
-- assumption of its statement) and PdB's theorem, loaded together.  Lean refuses this import
-- ("environment already contains 'pd'": its merge has no theorem/definition arm), and so does
-- the modular check's clash rule, which is Lean's: the one-theorem rule of task #506 applies
-- to copies the clash rule merges and to copies that meet through a home's view (TdM), and
-- does not widen the clash rule.  Lean cannot compile the file, so tests/olean/build.sh
-- compiles it against a stand-in PdA without `pd`.
theorem pd_use_n : id True := pd

end
