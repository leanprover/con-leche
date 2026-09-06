import Lech.Verify.Cached.Erase
import Lech.Verify.Cached.GuardsC
import Lech.Verify.Cached.OpsC
import Lech.Verify.Cached.SimC
import Lech.Verify.Cached.SimCEff
import Lech.Verify.Cached.DiscC1
import Lech.Verify.Cached.DiscC2
import Lech.Verify.Cached.DiscC3
import Lech.Verify.Cached.BinderLoopC
import Lech.Verify.Cached.DiscC4
import Lech.Verify.Cached.DiscC5
import Lech.Verify.Cached.DiscC6
import Lech.Verify.Cached.KnotC
import Lech.Verify.Cached.SimCS
import Lech.Verify.Cached.BridgeCS1
import Lech.Verify.Cached.BridgeCS2
import Lech.Verify.Cached.BridgeCS3
import Lech.Verify.Cached.BridgeCS4
import Lech.Verify.Cached.BridgeCSDecl
import Lech.Verify.Cached.BridgeCP
import Lech.Verify.Cached.MainC
import Lech.Verify.Cached.AgreeFloor
import Lech.Verify.Cached.AgreeAnnot

/-!
# The cached checker variant's verification (task #163)

Umbrella for `Lech/Verify/Cached/*` — the simulation relating the
cached core (`Lech/Cached/*`, the `--core=cached-parsed` variant) to
the pure fueled checker, landing on the consistency corollaries.  See
DESIGN.md, "Task #163 CACHED-LIVE P1" for the frozen statement
inventory; files are added here as their batches seal.
-/
