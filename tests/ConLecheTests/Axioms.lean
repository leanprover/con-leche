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

**The eighteen pinned theorems.**  The main theorem first — that is
the statement a reader comes for — with the functionality of the
relation it is stated over and the main corollary derived from it,
then the letters on the fold it is stated about, the two transfer theorems between an accept of the fold
and the driver's fully checked environment, the letters on that
environment and the model it carries, the pure fueled checker's
letters, the business end at the invariant, and the one `@[csimp]`
equation the compiled equality rests on.  Eleven of them are also
`tests/proofdeps.sh`'s roots (`tests/ProofDeps.lean` names them), which
pin the MODULES their proof terms reach.  The two gates measure
different things and neither implies the other.

| theorem | what it says |
|---|---|
| `ConLeche.model_exists` | **THE MAIN THEOREM**: what `checkDecls` accepts in the verified mode has a model in every `SetTheory V` (`Nonempty (Model V env)`) |
| `ConLeche.Denotes_functional` | a term has at most one denotation under `Denotes` |
| `ConLeche.no_proof_of_False` | **THE MAIN COROLLARY**: hence it holds no constant of type `False` |
| `no_proof_of_False_cached` / `no_proof_of_Empty_cached` | the fold's letters at every validating mode |
| `checkDecls_sound` | the model an accept of the fold carries |
| `fullyChecked_checkDecls` / `checkDecls_fullyChecked` | the driver's fully checked environment is an accept of the fold, and conversely |
| `no_proof_of_False_checked` / `no_proof_of_Empty_checked` | the letters on the driver's fully checked environment |
| `fullyChecked_sound` | the model a fully checked environment carries |
| `no_proof_of_False_pure` | the pure fueled checker's letter |
| `no_proof_of_Empty_pure` | the same about `Empty` |
| `no_proof_of_Empty_pure_of` | its install-tier-conditional milestone shape |
| `no_constant_of_False` | the business end at the invariant |
| `no_constant_of_Empty` | the same about `Empty` |
| `no_constant_of_emptyPin` | the pin under it |
| `Expr.beq_eq_beqMemo` | the compiled expression equality IS `decide (a = b)` — the `@[csimp]` licence, so the trust-surface gate's "no escape" reading of `Expr.lean` is a theorem at these axioms (`Quot.sound` is the memo's quotient) |

**What is deliberately NOT pinned here**: anything about the
`--progress` lane.  The heartbeat is printed between the steps of the
one driver (`Main.lean`), whose return value carries the proof that
`checkDecls` returns its environment; the theorems above are about
`checkDecls`, and a run with the flag is covered exactly as a run
without it.
-/

namespace ConLecheTests.Axioms

/-! ## The main theorem and the main corollary (`ConLeche/MainTheorem.lean`)

The statements the project exists to make (task #277): every accepted
environment has a model (`model_exists`, over the relation `Denotes`
of `ConLeche/Denotes.lean`, whose functionality is pinned beside it),
and hence — the main corollary, derived from it in three lines —
holds no constant of type `False`.  Everything below them is what
they are corollaries of. -/

/--
info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.model_exists

/--
info: 'ConLeche.Denotes_functional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Denotes_functional

/--
info: 'ConLeche.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.no_proof_of_False

/-! ## The fold's letters (`ConLeche/Verify/Cached/MainC.lean`) -/

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

/-! ## The fold and the driver's fully checked environment
(`ConLeche/Cached/Installed.lean`, `ConLeche/Verify/Cached/InstalledC.lean`) -/

/--
info: 'ConLeche.Cached.fullyChecked_checkDecls' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fullyChecked_checkDecls

/--
info: 'ConLeche.Cached.checkDecls_fullyChecked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_fullyChecked

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
