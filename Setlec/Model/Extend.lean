import Setlec.Model.Extend.Inversions
import Setlec.Model.Extend.Sibs
import Setlec.Model.Extend.Model
import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Iota
import Setlec.Model.Extend.Modeled
import Setlec.Model.Extend.ProjFn
import Setlec.Model.Extend.Ind
import Setlec.Model.Extend.Proj
import Setlec.Model.Extend.Decl

/-!
# Model extension steps (umbrella)

One lemma per way the checker extends the environment: plain constants
(`extend_model`), pinned basis constants (`extend_basis_one`), opaque
modeled inductive-kind members (`extend_modeled_one`) and modeled
recursors with their checked iota rules (`extend_modeled_rec`,
consuming the `RuleChecked` bundles that `checkIotaRules_inv`
extracts).  `Setlec.Model.Consistency` assembles these into
`checkDecl_sound`.

The content lives in `Setlec/Model/Extend/`; this module only
re-exports it so downstream imports stay unchanged.
-/
