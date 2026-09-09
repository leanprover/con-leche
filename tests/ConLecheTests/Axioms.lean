module

public import ConLeche.MainTheorem
public import ConLeche.Verify.Cached.MainC
public import ConLeche.Model.Fold
public import ConLeche.Model.Capstone
public section

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

**The twenty-one pinned theorems.**  The main theorem first — that is
the statement a reader comes for — then the letter on the driver's
type it wraps and the assembly under it (task #253: the model a fully
checked environment carries, the bridge to the specification, the
specification's letter), then the ordinary fold's letters, the
assembly under those, the same letters about the pinned `Empty`, and
the one `@[csimp]` equation the compiled equality rests on.  Fourteen
of them are also `tests/proofdeps.sh`'s roots (`tests/ProofDeps.lean`
names them), which pin the MODULES their proof terms reach.  The two
gates measure different things and neither implies the other.

| theorem | what it says |
|---|---|
| `ConLeche.no_proof_of_False` | **THE MAIN THEOREM**: a fully checked environment — the driver's type — holds no constant of type `False` |
| `no_proof_of_False_checked` / `no_proof_of_Empty_checked` | the same on the driver's type at every validating mode |
| `fullyChecked_sound` | the model a fully checked environment carries |
| `fullyChecked_spec` | the bridge: the driver's fully checked environment is one in the specification's sense |
| `no_proof_of_False_spec` / `no_proof_of_Empty_spec` | the specification's letters |
| `fullyCheckedSpec_sound` | the model the specification carries |
| `checkDecls_spec` | the ordinary fold's route into the specification |
| `ConLeche.no_proof_of_False_fold` | the ordinary fold's letter (the main theorem's statement until task #253) |
| `no_proof_of_False_cached` | the shipped fold's own letter, at every validating mode |
| `no_proof_of_Empty_cached` | the same about the pinned `Empty` |
| `checkDecls_sound` | the acceptance corollary under the driver's letters |
| `fold_preserves` | the fold that threads the model invariant |
| `no_proof_of_False_pure` | the pure fueled checker's letter |
| `no_proof_of_Empty_pure` | the same about `Empty` |
| `no_proof_of_Empty_pure_of` | its install-tier-conditional milestone shape |
| `no_constant_of_False` | the business end at the invariant |
| `no_constant_of_Empty` | the same about `Empty` |
| `no_constant_of_emptyPin` | the pin under it |
| `Expr.beq_eq_beqMemo` | the compiled expression equality IS `decide (a = b)` — the `@[csimp]` licence, so the trust-surface gate's "no escape" reading of `Expr.lean` is a theorem at these axioms (`Quot.sound` is the memo's quotient) |

**What is deliberately NOT pinned here** (2026-09-07, the user's
two-loop ruling): anything about the `--progress` lane.  That lane
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

/-! ## The driver's type and its assembly (`ConLeche/Verify/Cached/InstalledC.lean`,
`ConLeche/Model/Installed.lean`, task #253) -/

/--
info: 'ConLeche.Cached.no_proof_of_False_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_False_checked

/--
info: 'ConLeche.Cached.no_proof_of_Empty_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_Empty_checked

/--
info: 'ConLeche.Cached.fullyChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fullyChecked_sound

/--
info: 'ConLeche.Cached.fullyChecked_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fullyChecked_spec

/--
info: 'ConLeche.Model.no_proof_of_False_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_False_spec

/--
info: 'ConLeche.Model.no_proof_of_Empty_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_spec

/--
info: 'ConLeche.Model.fullyCheckedSpec_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.fullyCheckedSpec_sound

/--
info: 'ConLeche.Cached.checkDecls_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_spec

/--
info: 'ConLeche.no_proof_of_False_fold' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.no_proof_of_False_fold

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
info: 'ConLeche.Model.no_proof_of_False_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_False_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_pure_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_pure_of

/-! ## The business end (`ConLeche/Model/Capstone.lean`) -/

/--
info: 'ConLeche.Model.no_constant_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_False

/--
info: 'ConLeche.Model.no_constant_of_Empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_Empty

/--
info: 'ConLeche.Model.no_constant_of_emptyPin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_emptyPin

/-! ## The compiled equality (`ConLeche/Kernel/Expr.lean`)

Not a capstone: the licence under which the compiler runs `beqMemo`
for `Expr.beq`.  It is pinned because it is the theorem that turned a
census row into a `@[csimp]` equation, and because its proof is the
one place the tree quotients a runtime state (`Squash`, hence
`Quot.sound`). -/

/--
info: 'ConLeche.Expr.beq_eq_beqMemo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Expr.beq_eq_beqMemo

end ConLecheTests.Axioms
