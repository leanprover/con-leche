module

public import ConLeche.Frontend.Olean.Snapshot

@[expose] public section

/-!
# A compared run's request

The data `--olean --compare` and the modular comparison run on (`ConLeche/Driver/Compare.lean`),
on their own so that a statement can name a request without the driver.
-/

namespace ConLeche.Driver

open ConLeche Frontend.Olean

/-- **A compared run's request**: the challenge and solution modules, the trusted directories
(none given: the search path is trusted), the search path, and the `--constant` names. -/
structure CmpReq where
  challenge : Name
  solution : Name
  trusted : SearchPath
  path : SearchPath
  constants : Option (Array Name)

end ConLeche.Driver
