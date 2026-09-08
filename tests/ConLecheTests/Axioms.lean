import ConLeche.MainTheorem
import ConLeche.Verify.Cached.MainC
import ConLeche.Model.Fold
import ConLeche.Model.Capstone

/-!
# THE AXIOM PIN (2026-09-06, external review §2/§5.1)

**Why this module exists.**  The headline of this project is that the
consistency theorems stand on nothing but Lean's three standard axioms:

    [propext, Classical.choice, Quot.sound]

Until now that was a *claim in the design journal* — the tree had exactly
one `#guard_msgs in #print axioms`, on the Aczel realizability leaf
(`SetTheory/Aczel.lean`, deleted at task #212 in favour of the Mathlib
bridge `bridge/lean4lean-model`), and none on any capstone.  An external
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
`no_proof_of_False`, `no_proof_of_False_cached`, `no_proof_of_False_pure`,
`no_proof_of_Empty_cached`, `checkDecls_sound`,
`fold_preserves`, `no_proof_of_Empty_pure` — which pin the MODULES their proof
terms reach.  The other four are pinned here only.  The two gates
measure different things and neither implies the other.

| theorem | what it says |
|---|---|
| `ConLeche.no_proof_of_False` | **THE MAIN THEOREM**: an accepted stream yields no constant of type `False` |
| `no_proof_of_False_cached` | the shipped driver's letter, at every validating mode |
| `no_proof_of_Empty_cached` | the same about the pinned `Empty` |
| `checkDecls_sound` | the acceptance corollary under the driver's letters |
| `fold_preserves` | the fold that threads the model invariant |
| `no_proof_of_False_pure` | the pure fueled checker's letter |
| `no_proof_of_Empty_pure` | the same about `Empty` |
| `no_proof_of_Empty_P_of` | its install-tier-conditional milestone shape |
| `no_constant_of_False` | the business end at the invariant |
| `no_constant_of_Empty` | the same about `Empty` |
| `no_constant_of_emptyPin` | the pin under it |

**What is deliberately NOT pinned here** (2026-09-07, the user's
two-loop ruling): anything about the `CON_LECHE_PROGRESS` lane.  That lane
runs a *separate, openly unverified* fold in `Main.lean`
(`checkDeclsProgressIO`) — the same steps as the verified one with a
line printed before each declaration — and the default run calls
`checkDecls`, which is what the theorems above are about.  An
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
info: 'ConLeche.Cached.no_proof_of_False_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_False_cached

/--
info: 'ConLeche.Cached.no_proof_of_Empty_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_Empty_cached

/--
info: 'ConLeche.Cached.checkDecls_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_sound

/--
info: 'ConLeche.Cached.fold_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fold_preserves

/-! ## The pure fueled checker (`ConLeche/Model/Fold.lean`) -/

/--
info: 'ConLeche.Model.no_proof_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_False_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_P_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_P_of

/-! ## The business end (`ConLeche/Model/Capstone.lean`) -/

/--
info: 'ConLeche.Model.no_constant_of_False_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_False

/--
info: 'ConLeche.Model.no_constant_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_Empty

/--
info: 'ConLeche.Model.no_constant_of_emptyPin_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_emptyPin

end ConLecheTests.Axioms
