import Setlec.Verify.Cached.MainC

/-!
# Comparator solution

`Challenge.lean`'s theorem, proved from the capstone
`no_proof_of_Empty_SPCD_P` (`cfgOf .verified = cfgP` by `rfl`).  Must not
import `Challenge`.
-/

universe w

namespace Setlec

theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∀ c ∈ env'.consts, c.toConstantVal.type = .const (.str .anonymous "Empty") [] → False :=
  Cached.no_proof_of_Empty_SPCD_P V (μ := .verified) rfl h

end Setlec
