import Setlec.Verify.Cached.Erase
import Setlec.Verify.Cached.GuardsC
import Setlec.Verify.Cached.OpsC
import Setlec.Verify.Cached.SimC
import Setlec.Verify.Cached.SimCEff
import Setlec.Verify.Cached.DiscC1
import Setlec.Verify.Cached.DiscC2
import Setlec.Verify.Cached.DiscC3
import Setlec.Verify.Cached.BinderLoopC

/-!
# The cached checker variant's verification (task #163)

Umbrella for `Setlec/Verify/Cached/*` — the simulation relating the
cached core (`Setlec/Cached/*`, the `--core=cached-parsed` variant) to
the pure fueled checker, landing on the consistency corollaries.  See
DESIGN.md, "Task #163 CACHED-LIVE P1" for the frozen statement
inventory; files are added here as their batches seal.
-/
