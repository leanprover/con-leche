import ConLeche.MainTheorem
import ConLeche.Verify.Cached.MainC
import ConLeche.SetP.FoldP
import ConLeche.SetP.CapstoneP

/-!
# THE AXIOM PIN (2026-09-06, external review §2/§5.1)

**Why this module exists.**  The headline of this project is that the
consistency theorems stand on nothing but Lean's three standard axioms:

    [propext, Classical.choice, Quot.sound]

Until now that was a *claim in the design journal* — the tree had exactly
one `#guard_msgs in #print axioms`, on `SetTheory.ofAczelChain`
(`ConLeche/SetTheory/Aczel.lean`), and none on any capstone.  An external
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
It is under the `ConLecheTests` library (`lake test`), so it can never
enter a capstone's own dependency closure — `tests/proofdeps.sh` would
report the door if it ever did.

**The eleven pinned theorems.**  The main theorem first — that is the
statement a reader comes for — then the letters it is a corollary of,
then the assembly under those, then the same letters about the pinned
`Empty`.  Seven of them are also `tests/proofdeps.sh`'s roots —
`no_proof_of_False`, `no_proof_of_False_SPCD_P`, `no_proof_of_False_P`,
`no_proof_of_Empty_SPCD_P`, `checkDeclsSPCachedD_sound_P`,
`foldSPC_PM`, `no_proof_of_Empty_P` — which pin the MODULES their proof
terms reach.  The other four are pinned here only.  The two gates
measure different things and neither implies the other.

| theorem | what it says |
|---|---|
| `ConLeche.no_proof_of_False` | **THE MAIN THEOREM**: an accepted stream yields no constant of type `False` |
| `no_proof_of_False_SPCD_P` | the shipped driver's letter, at every validating mode |
| `no_proof_of_Empty_SPCD_P` | the same about the pinned `Empty` |
| `checkDeclsSPCachedD_sound_P` | the acceptance corollary under the driver's letters |
| `foldSPC_PM` | the fold that threads the model invariant |
| `no_proof_of_False_P` | the pure fueled checker's letter |
| `no_proof_of_Empty_P` | the same about `Empty` |
| `no_proof_of_Empty_P_of` | its install-tier-conditional milestone shape |
| `no_constant_of_False_P` | the business end at the invariant |
| `no_constant_of_Empty_P` | the same about `Empty` |
| `no_constant_of_emptyPin_P` | the pin under it |

**What is deliberately NOT pinned here** (2026-09-07, the user's
two-loop ruling): anything about the `CON_LECHE_PROGRESS` lane.  That lane
runs a *separate, openly unverified* fold in `Main.lean`
(`checkDeclsProgressIO`) — the same steps as the verified one with a
line printed before each declaration — and the default run calls
`checkDeclsSPCachedD`, which is what the theorems above are about.  An
earlier round of that task carried a monad-generic loop with callbacks,
a bridge at every lawful monad and a hand-proved `LawfulMonad IO`, all
pinned here; the ruling replaced them with two trivial folds and a
sentence saying which one is verified.
-/

namespace ConLecheTests.Axioms

/-! ## The main theorem (`ConLeche/MainTheorem.lean`)

The statement the project exists to make (task #181: the pinned `False`
block).  Everything below it is what it is a corollary of. -/

/--
info: 'ConLeche.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.no_proof_of_False

/-! ## The shipped driver (`ConLeche/Verify/Cached/MainC.lean`) -/

/--
info: 'ConLeche.Cached.no_proof_of_False_SPCD_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_False_SPCD_P

/--
info: 'ConLeche.Cached.no_proof_of_Empty_SPCD_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_Empty_SPCD_P

/--
info: 'ConLeche.Cached.checkDeclsSPCachedD_sound_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDeclsSPCachedD_sound_P

/--
info: 'ConLeche.Cached.foldSPC_PM' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.foldSPC_PM

/-! ## The pure fueled checker (`ConLeche/SetP/FoldP.lean`) -/

/--
info: 'ConLeche.SetP.no_proof_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_proof_of_False_P

/--
info: 'ConLeche.SetP.no_proof_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_proof_of_Empty_P

/--
info: 'ConLeche.SetP.no_proof_of_Empty_P_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_proof_of_Empty_P_of

/-! ## The business end (`ConLeche/SetP/CapstoneP.lean`) -/

/--
info: 'ConLeche.SetP.no_constant_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_constant_of_False_P

/--
info: 'ConLeche.SetP.no_constant_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_constant_of_Empty_P

/--
info: 'ConLeche.SetP.no_constant_of_emptyPin_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.SetP.no_constant_of_emptyPin_P

end ConLecheTests.Axioms
