import Setlec.SetP.Direct.DeclDirectP
import Setlec.Semantics.Direct.DeclDirectSum

/-!
# The direct sum's install, assembled (task #175 sum-types) — WIP STUB

`declDirectSumP`: the P carrier survives the direct sum install's run
(`DeclDirectSumRun`).  The stage proofs follow; this stub holds the
statement so the fold's dispatch builds.
-/

namespace Setlec.SetP
open Setlec.Semantics

open Setlec (Env ConstantInfo DirectSumParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The P carrier survives a direct sum install.** -/
theorem declDirectSumP (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p : DirectSumParts} (mp : EnvS2PM V μ env)
    (hE : Setlec.EtaFamiliesClosed env) (hdp : Setlec.directSumParts? env block = some p)
    (h : Setlec.Semantics.DeclDirectSumRun μ F env p env₂) : Nonempty (EnvS2PM V μ env₂) := by
  sorry

end Setlec.SetP
