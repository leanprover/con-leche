import Setlec.Model.Basis.PUnit.Claims
import Setlec.Model.Basis.Eq.Claims
import Setlec.Model.Basis.Nat.Claims
import Setlec.Model.Basis.PSigma.Claims

/-!
# Iota-rule semantics for the pinned basis recursors

For each iota rule, three facts feed the `whnf` soundness of the
reduction step: the interpretation of the (annotated) rule rhs, the
truthfulness of its annotations, and the *fold equation* — the
recursor's value applied through the rule's telescope equals the rhs's
value applied to the non-index prefix and fields.  One module per basis
type and topic under `Setlec/Model/Basis/`.
-/
