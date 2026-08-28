import Setlec.TTVerify.OfReduceKey
import Setlec.Verify.Denote.SubstConst

/-!
# Substituting the operation for its own constant — relocated

`shallowE` and `denote_substConst0` moved to
`Setlec/Verify/Denote/SubstConst.lean` (task #148, T5), generalized
over a bare valuation exactly as the original docstring here
predicted; this module keeps the import edge for the TT-lane call
sites.
-/
