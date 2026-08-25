import Setlec.Model.Basis.PUnit.Iota
import Setlec.Model.Basis.Eq.Iota
import Setlec.Model.Basis.Eq.RuleOk
import Setlec.Model.Basis.Nat.Iota
import Setlec.Model.Basis.Nat.RuleOk
import Setlec.Model.Basis.PSigma.Iota
import Setlec.Model.Basis.PSigma.RuleOk
import Setlec.Model.Basis.Glue

/-!
# Iota-rule semantics for the pinned basis recursors

For each iota rule, three facts feed the `whnf` soundness of the
reduction step: the interpretation of the (annotated) rule rhs, the
truthfulness of its annotations, and the *fold equation* — the
recursor's value applied through the rule's telescope equals the rhs's
value applied to the non-index prefix and fields.  One module per basis
type and topic under `Setlec/Model/Basis/`.
-/
