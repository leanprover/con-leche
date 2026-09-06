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

**The six pinned theorems** — the four capstone roots
`tests/proofdeps.sh` pins module-wise, plus the two further letters of
the graded tier:

| theorem | what it says |
|---|---|
| `no_proof_of_Empty_SPCD_P` | the shipped driver's letter |
| `checkDeclsSPCachedD_sound_P` | the acceptance corollary under it |
| `foldSPC_PM` | the fold that threads the model invariant |
| `no_proof_of_Empty_P` | the pure fueled checker's letter |
| `no_proof_of_Empty_P_of` | its install-tier-conditional milestone shape |
| `no_constant_of_Empty_P` | the business end at the invariant |
-/

namespace SetlecTests.Axioms

/-! ## The shipped driver (`Setlec/Verify/Cached/MainC.lean`) -/

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

/-! ## The pure fueled checker (`Setlec/SetP/FoldP.lean`) -/

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
info: 'Setlec.SetP.no_constant_of_Empty_P' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Setlec.SetP.no_constant_of_Empty_P

end SetlecTests.Axioms
