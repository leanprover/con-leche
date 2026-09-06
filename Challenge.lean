import Setlec.Cached.ParsedC
import Setlec.SetTheory.Core

/-!
# Comparator challenge

The checker's headline claim, for `leanprover/comparator` (config in
`comparator.json`, proof in `Solution.lean`).  Trusted here: the shipped
checker up to its driver `checkDeclsSPCachedD`, and the `SetTheory`
interface.
-/

universe w

namespace Setlec

set_option warn.sorry false in
/-- The checker at `cfgP` (what `setlec --verified`, the default, runs)
never accepts a stream storing a constant of type `Empty`, in every model
`V` of `SetTheory`. -/
theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    {ds : List Cached.DeclC} {env' : Env}
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∀ c ∈ env'.consts, c.toConstantVal.type = .const emptyName [] → False :=
  sorry

end Setlec
