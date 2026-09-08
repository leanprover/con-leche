module

public import ConLeche.Verify.Cached.Erase
public import ConLeche.Verify.Cached.GuardsC
public import ConLeche.Verify.Cached.OpsC
public import ConLeche.Verify.Cached.SimC
public import ConLeche.Verify.Cached.SimCEff
public import ConLeche.Verify.Cached.DiscC1
public import ConLeche.Verify.Cached.DiscC2
public import ConLeche.Verify.Cached.DiscC3
public import ConLeche.Verify.Cached.BinderLoopC
public import ConLeche.Verify.Cached.DiscC4
public import ConLeche.Verify.Cached.DiscC5
public import ConLeche.Verify.Cached.DiscC6
public import ConLeche.Verify.Cached.KnotC
public import ConLeche.Verify.Cached.SimCS
public import ConLeche.Verify.Cached.BridgeCS1
public import ConLeche.Verify.Cached.BridgeCS2
public import ConLeche.Verify.Cached.BridgeCS3
public import ConLeche.Verify.Cached.BridgeCS4
public import ConLeche.Verify.Cached.BridgeCSDecl
public import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Verify.Cached.MainC
public import ConLeche.Verify.Cached.AgreeFloor

@[expose] public section

/-!
# The cached checker variant's verification (task #163)

Umbrella for `ConLeche/Verify/Cached/*` — the simulation relating the
cached core (`ConLeche/Cached/*`, the `--core=cached-parsed` variant) to
the pure fueled checker, landing on the consistency corollaries.  See
DESIGN.md, "Task #163 CACHED-LIVE P1" for the frozen statement
inventory; files are added here as their batches seal.
-/
