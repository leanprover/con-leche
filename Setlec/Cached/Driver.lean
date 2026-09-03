import Setlec.Cached.ParsedC
import Setlec.Kernel.WFStore

/-!
# The pilot's driver seam

Three declaration folds with the *same* signature as the production
`checkDeclsSP`, so the binary selects one and nothing else changes:

* `checkDeclsSP` (production, unchanged) — parsed indices all the way
  down: the parse arena seeds the run's single `IState`, declarations
  stay as `DeclP`, and the tier-two snapshot bracket applies;
* `checkDeclsSharedI` — the interned core under the **`Expr`-typed**
  shared-state driver (`Setlec.checkDeclsShared`, already in the
  kernel): declarations are read back from the parse arena first;
* `checkDeclsSharedC` — the cached-clone core under the same
  `Expr`-typed shared-state driver;
* `checkDeclsSPCached` (`Setlec/Cached/ParsedC.lean`) — the
  cached-clone core under its own parsed-declaration driver, the
  clone's counterpart of `checkDeclsSP`.

The last two are the pilot's controlled pair: identical declaration
checker, identical `FEnv` indexing, identical per-declaration state
lifetime and flush discipline, identical input objects — the *only*
difference is what the core computes on.  `checkDeclsSP` is reported
alongside as the production reference; it additionally carries
parse-time interning and the snapshot bracket, which are arena
mechanisms with no clone counterpart, so a `SP`-vs-clone gap mixes
representation with driver.
-/

namespace Setlec.Cached

open Setlec

/-- Read the parsed declarations back as `Expr`-level `Declaration`s
(the input both `Expr`-typed drivers consume). -/
def declsOfP (st : EStore) : List DeclP → CheckM (List Declaration)
  | [] => pure []
  | pd :: rest =>
    match st.readbackDecl pd with
    | some d => do
      let ds ← declsOfP st rest
      pure (d :: ds)
    | none => throw (.internal "parse-arena declaration readback failed")

/-- The cached-clone fold. -/
def checkDeclsSharedC (mode : CheckMode) (st : WFStore)
    (pds : List DeclP) : CheckM Env := do
  let ds ← declsOfP st.raw pds
  checkDeclsShared mode ds

/-- The interned-core fold under the same `Expr`-typed driver. -/
def checkDeclsSharedI (mode : CheckMode) (st : WFStore)
    (pds : List DeclP) : CheckM Env := do
  let ds ← declsOfP st.raw pds
  Setlec.checkDeclsShared mode ds

/-- Which core/driver pair the binary runs (`--core=…`).

The default for the certified mode (`--set-model`) is `cachedParsed`
(task #163 flip, user-granted 2026-09-03): its acceptance is covered
by the same consistency corollaries as production's
(`Setlec/Verify/Cached/MainC.lean`: `checkDeclsSPCached_sound_R` and
the `no_proof_of_Empty_SPC_*` family, all three carriers), and it is
ahead of the interned core on every measured real workload in that
mode (DESIGN.md, "DE-GATING BASELINE (post-capstone)").  The default
is MODE-AWARE: `--no-model` keeps the production front door
(`CheckerNC`) unless a core is requested explicitly — the
cert-skipping lane's design (task #147) was never cloned, and the
measured no-model split goes the other way on decl-heavy streams (the
interned core wins init-prelude/init-full/grind there by 1.6-1.7x;
cached wins term-heavy — see the DESIGN flip record). -/
inductive CoreVariant where
  /-- `checkDeclsSP`: the production parsed-index driver (verified). -/
  | production
  /-- `checkDeclsSharedI`: interned core, `Expr`-typed shared driver
  (pilot measurement instrument, unverified). -/
  | internedShared
  /-- `checkDeclsSharedC`: cached core, same driver (pilot measurement
  instrument, unverified). -/
  | cached
  /-- `checkDeclsSPCached`: the cached core under its own
  parsed-declaration driver (the arena converted once, guards as
  memoized `ExprC` walks).  **Supported and verified** (task #163):
  acceptance is covered by the same consistency corollaries as
  production's (`Setlec/Verify/Cached/MainC.lean`). -/
  | cachedParsed
  deriving DecidableEq, Repr, Inhabited

/-- The certified mode's default core (see `CoreVariant`'s docstring;
task #163 flip). -/
def defaultCore : CoreVariant := .cachedParsed

end Setlec.Cached
