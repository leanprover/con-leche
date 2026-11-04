module

public import ConLeche.Kernel.Core

public section

/-!
# The mode function (task #185)

`CheckMode.verifiedChecks` (`ConLeche/Kernel/Env.lean`) is what the
cores read of the mode, a `match` on the enum; under
`hμ : μ.verifiedChecks = true` the mode is `.verified` itself
(`CheckMode.eq_verified`).

The module imports `Kernel.Core` and nothing else: it is base-tier.
-/

namespace ConLeche

variable {mode : CheckMode}

/-- **The `--verified` mode is `.verified`** — the model tier's way
through a cached body's certificate switches: after
`obtain rfl := CheckMode.eq_verified hμ` every `certAtI` read is at the
literal `.verified` and reduces by `rfl`. -/
theorem CheckMode.eq_verified (h : mode.verifiedChecks = true) :
    mode = .verified := by
  cases mode <;> simp_all [CheckMode.verifiedChecks]

end ConLeche
