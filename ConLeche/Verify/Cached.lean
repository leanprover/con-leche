import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Cached.GuardsC
import ConLeche.Verify.Cached.OpsC
import ConLeche.Verify.Cached.SimC
import ConLeche.Verify.Cached.SimCEff
import ConLeche.Verify.Cached.DiscC1
import ConLeche.Verify.Cached.DiscC2
import ConLeche.Verify.Cached.DiscC3
import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.Cached.DiscC4
import ConLeche.Verify.Cached.DiscC5
import ConLeche.Verify.Cached.DiscC6
import ConLeche.Verify.Cached.KnotC
import ConLeche.Verify.Cached.SimCS
import ConLeche.Verify.Cached.BridgeCS1
import ConLeche.Verify.Cached.BridgeCS2
import ConLeche.Verify.Cached.BridgeCS3
import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Verify.Cached.BridgeCP
import ConLeche.Verify.Cached.MainC
import ConLeche.Verify.Cached.AgreeFloor
import ConLeche.Verify.Cached.AgreeAnnot

/-!
# The cached checker variant's verification (task #163)

Umbrella for `ConLeche/Verify/Cached/*` — the simulation relating the
cached core (`ConLeche/Cached/*`, the `--core=cached-parsed` variant) to
the pure fueled checker, landing on the consistency corollaries.  See
DESIGN.md, "Task #163 CACHED-LIVE P1" for the frozen statement
inventory; files are added here as their batches seal.
-/
