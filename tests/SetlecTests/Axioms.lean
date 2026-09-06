import Setlec.MainTheorem
import Setlec.Verify.Cached.MainC
import Setlec.SetP.FoldP
import Setlec.SetP.CapstoneP

/-!
# THE AXIOM PIN (2026-09-06, external review §2/§5.1)

**Why this module exists.**  The headline of this project is that the
consistency theorems stand on nothing but Lean's three standard axioms:

    [propext, Classical.choice, Quot.sound]

Until now that was a *claim in the design journal* — the tree had exactly
one `#guard_msgs in #print axioms`, on `SetTheory.ofAczelChain`
(`Setlec/SetTheory/Aczel.lean`), and none on any capstone.  An external
reviewer could not confirm the headline without a full rebuild and a
scratch file of their own.  The guards below are that scratch file,
in-tree and run by `lake test`: if a `sorry`, a new axiom, or a stray
`Classical`-adjacent import ever enters a capstone's proof term, the
message changes and the build fails.

**What it does NOT catch**, and why `tests/trust-surface.sh` is its
companion: `#print axioms` is blind to compiler escapes.  A theorem can
sit at exactly these three axioms and still be about a function whose
compiled behaviour was replaced by `@[implemented_by]` or read off a
`@[computed_field]` word.  Two gates, two blindnesses:

  * this module     — what the PROOF TERM assumes (the logical TCB);
  * trust-surface.sh — what the COMPILED CODE assumes (the runtime TCB);
  * proofdeps.sh    — which MODULES the proof term reaches.

**Layering.**  This module *imports* the capstones; nothing imports it.
It is under the `SetlecTests` library (`lake test`), so it can never
enter a capstone's own dependency closure — `tests/proofdeps.sh` would
report the door if it ever did.

**The ten pinned theorems.**  The two main theorems first — those are
the statements a reader comes for — then the letters they are
corollaries of, then the assembly under those.  Six of them are also
`tests/proofdeps.sh`'s roots — `no_proof_of_Empty`,
`no_proof_of_Empty_IO`, `no_proof_of_Empty_SPCD_P`,
`checkDeclsSPCachedD_sound_P`, `foldSPC_PM`, `no_proof_of_Empty_P` —
which pin the MODULES their proof terms reach.  The other four are
pinned here only.  The two gates measure different things and neither
implies the other.

| theorem | what it says |
|---|---|
| `Setlec.no_proof_of_Empty` | **THE MAIN THEOREM**: an accepted stream yields no constant of type `Empty` |
| `Setlec.no_proof_of_Empty_IO` | the same, for the callback-carrying `IO` loop the binary runs |
| `no_proof_of_Empty_SPCD_P` | the shipped driver's letter, at every validating mode |
| `no_proof_of_Empty_SPCD_IO` | its `IO`-loop sibling |
| `no_proof_of_Empty_P` | the pure fueled checker's letter |
| `no_proof_of_Empty_P_of` | its install-tier-conditional milestone shape |
| `checkDeclsSPCachedD_sound_P` | the acceptance corollary under the driver's letter |
| `foldSPC_PM` | the fold that threads the model invariant |
| `checkDeclsSPCachedM_eq` | the `IO` loop's result IS the pure driver's (the bridge the `IO` letters stand on) |
| `no_constant_of_Empty_P` | the business end at the invariant |

`checkDeclsSPCachedM_eq` is not a consistency statement but a
*computational* one, and it is pinned for exactly that reason: it is
what makes the `IO` letters mean something about the loop the binary
runs rather than about a twin, so its footprint has to be as clean as
theirs.
-/

namespace SetlecTests.Axioms

/-! ## The main theorems (`Setlec/MainTheorem.lean`)

The statements the project exists to make — `False` first (task #181:
the pinned `False` block), then `Empty`.  Everything below them is what
they are corollaries of. -/

/--
info: 'Setlec.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.no_proof_of_False

/--
info: 'Setlec.no_proof_of_Empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.no_proof_of_Empty

/--
info: 'Setlec.no_proof_of_Empty_IO' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.no_proof_of_Empty_IO

/-! ## The shipped driver (`Setlec/Verify/Cached/MainC.lean`) -/

/--
info: 'Setlec.Cached.no_proof_of_False_SPCD_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.no_proof_of_False_SPCD_P

/--
info: 'Setlec.Cached.no_proof_of_Empty_SPCD_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.no_proof_of_Empty_SPCD_P

/--
info: 'Setlec.Cached.checkDeclsSPCachedD_sound_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.checkDeclsSPCachedD_sound_P

/--
info: 'Setlec.Cached.foldSPC_PM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.foldSPC_PM

/--
info: 'Setlec.Cached.no_proof_of_Empty_SPCD_IO' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.no_proof_of_Empty_SPCD_IO

/-! ## The `IO` loop's bridge (`Setlec/Cached/ParsedC.lean`)

Not a consistency statement — a computational one: the callback-carrying
loop's result *is* the pure driver's.  It is pinned because it is what
makes the two `IO` letters above statements about the loop the binary
actually runs. -/

/--
info: 'Setlec.Cached.checkDeclsSPCachedM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.Cached.checkDeclsSPCachedM_eq

/-! ## The pure fueled checker (`Setlec/SetP/FoldP.lean`) -/

/--
info: 'Setlec.SetP.no_proof_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_proof_of_False_P

/--
info: 'Setlec.SetP.no_proof_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_proof_of_Empty_P

/--
info: 'Setlec.SetP.no_proof_of_Empty_P_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_proof_of_Empty_P_of

/-! ## The business end (`Setlec/SetP/CapstoneP.lean`) -/

/--
info: 'Setlec.SetP.no_constant_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_constant_of_False_P

/--
info: 'Setlec.SetP.no_constant_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_constant_of_Empty_P

/--
info: 'Setlec.SetP.no_constant_of_emptyPin_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_constant_of_emptyPin_P

end SetlecTests.Axioms
