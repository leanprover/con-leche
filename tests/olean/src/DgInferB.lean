module
-- Guards task #399: importer needs the private def's value for rfl.
-- Expected: Lean rejects (inferV is not unfoldable to 7 for the importer, or
-- pv is not visible) -- see the case notes; must-reject candidate.
public import DgInferA
public theorem inferB : inferV = 7 := rfl
