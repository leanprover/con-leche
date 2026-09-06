import Setlec.Verify.Cached.MainC

/-!
# The comparator solution

The theorem of `Challenge.lean`, restated verbatim and proved from the
shipped capstone `Setlec.Cached.no_proof_of_Empty_SPCD_P`
(`Setlec/Verify/Cached/MainC.lean`) at the verified mode: `cfgP` is
`cfgOf .verified` by `rfl` (`cfgOf_verified_eq_cfgP`).

This module deliberately does **not** import `Challenge`: the comparator
builds the two modules separately and compares the two environments'
copies of the statement, constant by constant.
-/

universe w

namespace Setlec

theorem no_proof_of_Empty (V : Type w) [SetTheory V]
    {ds : List Cached.DeclC} {env' : Env}
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∀ c ∈ env'.consts, c.toConstantVal.type = .const emptyName [] → False :=
  Cached.no_proof_of_Empty_SPCD_P V (μ := .verified) rfl h

end Setlec
