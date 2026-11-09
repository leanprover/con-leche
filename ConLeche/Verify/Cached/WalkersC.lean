module

public import ConLeche.Verify.Cached.GuardsC

public section

/-!
# The cached driver's walker is the plain one (task #214)

`structWalkersC` — the memoised constant-resolution gate the cached
driver hands the direct installers (`StructWalkers`,
`ConLeche/Kernel/Inductives/StructInstallF.lean`) — is equal to the
specification record `StructWalkers.plain`, by `constsResolveFC_spec`
(task #171).  Every bridge lemma about the driver rewrites by
`structWalkersC_eq_plain` once and then reads the plain installer.
-/

namespace ConLeche.Cached

open ConLeche

/-- **The driver's walker is the plain one.** -/
theorem structWalkersC_eq_plain : structWalkersC = StructWalkers.plain := by
  unfold structWalkersC StructWalkers.plain
  congr 1
  funext fe e; exact constsResolveFC_spec

end ConLeche.Cached
