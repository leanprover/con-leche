module

public import ConLeche.MainTheorem
public import ConLecheTests.CompareAttack
public import ConLeche.Verify.Frontend.Olean.Files
public import ConLeche.Verify.Frontend.Olean.Local
public import ConLeche.Verify.Frontend.Olean.View
public import ConLeche.Verify.Frontend.Olean.Emit
public import ConLeche.Verify.Frontend.Olean.Group
public import ConLeche.Verify.Frontend.Olean.Present
public import ConLeche.Verify.Driver.Reach
public import ConLeche.Verify.Driver.Graph
public import ConLeche.Verify.Driver.Main
public import ConLeche.Verify.Driver.Oleans
public import ConLeche.Verify.Driver.Routes
public import ConLeche.Verify.Driver.Worker
public import ConLeche.Verify.Driver.Groups
public import ConLeche.Verify.Driver.Modular
public import ConLeche.Verify.Driver.Main
public import ConLeche.Verify.Cached.MainC
public import ConLeche.Model.StreamConsts
public import ConLeche.Verify.Cached.StreamThm
public import ConLeche.Model.Fold
public import ConLeche.Model.Capstone
public import ConLeche.Semantics.DeclWF
public section

/-!
# THE AXIOM PIN

**Why this module exists.**  The headline of this project is that the
consistency theorems stand on nothing but Lean's three standard axioms:

    [propext, Classical.choice, Quot.sound]

The guards below pin that claim in-tree, run by `lake test`: if a `sorry`, a new axiom, or a stray
`Classical`-adjacent import ever enters a capstone's proof term, the
message changes and the build fails.

**What it does NOT catch**, and why `tests/trust-surface.sh` is its
companion: `#print axioms` is blind to compiler escapes.  A theorem can
sit at exactly these three axioms and still be about a function whose
compiled behaviour was replaced by `@[implemented_by]` or read off a
`@[computed_field]` word.  Two gates, two blindnesses:

  * this module     — what the PROOF TERM assumes (the logical TCB);
  * trust-surface.sh — what the COMPILED CODE assumes (the runtime TCB).

**Layering.**  This module *imports* the capstones; nothing imports it.
It is under the `ConLecheTests` library (`lake test`), so it can never
enter a capstone's own dependency closure.

**The twenty-one pinned theorems.**  The main theorem first — that is
the statement a reader comes for — with the functionality of the
relation it is stated over and the main corollary derived from it,
the main corollary lifted to the driver in the IO model,
then the letters on the fold it is stated about, the two transfer theorems between an accept of the fold
and the driver's fully checked environment, the letters on that
environment and the model it carries, the pure fueled checker's
letters, the business end at the invariant, and the one `@[csimp]`
equation the compiled equality rests on.

| theorem | what it says |
|---|---|
| `ConLeche.model_exists` | **THE MAIN THEOREM**: every stream `checkDecls` accepts in the verified mode has a model in every `SetTheory V` (`IsModel`, over the input) |
| `ConLeche.solution_model_exists` | **THE MAIN THEOREM, WITH A SOLUTION**: a stream `checkDecls` accepts with the environment of another accepted stream as its solution (its own axioms justified by it) has a model in every `SetTheory V`, and declares `False` and `Eq`, where it declares them at all, as the prelude's |
| `ConLeche.main_compare_json_model` | an exit 0 of `--compare -- <c> <s>` parsed `c`, and the challenge's records prepared with the prelude have such a model |
| `ConLeche.main_compare_model` | an exit 0 of `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`: on every snapshot that agrees under `T`, the constants of the closure of `C` through `T` have such a model (`main_compare_no_False`: where that closure holds a theorem of type `False`, no exit 0) |
| `ConLeche.Denotes_functional` | a term has at most one denotation under `Denotes` (`ConLeche/Denotes.lean`, with the relation) |
| `ConLeche.no_False_declaration` | **THE MAIN COROLLARY**: chunks that are a `jsonWithTheoremFalse` file — a name entry `False`, a constant expression of it, a name entry, and a theorem record of that name and type, in that order — make the binary's chain (the prelude parses, the chunks parse, the fold accepts the prepared records) return an error |
| `ConLeche.modular_model_exists` | **THE MODULAR THEOREM**: a development every module of which passes the local checks has a compatible family of models of the own environments |
| `ConLeche.modular_no_False` | its corollary: no module's own environment stores a constant of type `False` |
| `ConLeche.main_modular` | **THE MODULAR THEOREM, OVER THE FILES**: where `--check-graph -- <root>` and `--olean --module` at every module of the headers' closure exit 0 (`main_modular_one`: `--olean --modular -- <root>`), every module of the closure of `root` has a model of its constants, and a name it sees as another module's has that module's value |
| `ConLeche.main_modular_no_False` | **THE MODULAR COROLLARY, RUN BY RUN**, from `main_modular` alone: where a module of a root's closure holds a theorem of type `False` in its private view, declares the prelude's `False` or sees `False` as a module that does, and every module of the headers' closure has an exit 0 of `--olean --module` on the snapshot, no outcome of `--check-graph -- <root>` is an exit 0 (`main_modular_one_no_False`: nor of `--olean --modular -- <root>`) |
| `ConLeche.main_no_False` | **THE MAIN COROLLARY, LIFTED TO THE DRIVER**: on a snapshot where the file's bytes are a `jsonWithTheoremFalse` file, no outcome of `runArgs` at the arguments `-- <file>` is an exit 0 |
| `ConLeche.no_False_theorem_accepted` | the step it rests on, at the STREAM: records one of which declares a theorem of type `False` are never accepted by `checkDecls` (`ConLeche/Verify/Cached/StreamThm.lean`) |
| `no_proof_of_False_cached` / `no_proof_of_Empty_cached` | the fold's letters at every validating mode |
| `checkDecls_sound` | the model an accept of the fold carries |
| `checkDecls_envWF` / `checkDeclsPure_envWF` | what the fold (resp. the pure fueled fold) accepts is syntactically well formed (`EnvWF`), model-free: no `SetTheory` argument |
| `checkDecls_of_jobs` | every record's job at the frozen index passing is an accept of the fold |
| `no_proof_of_False_pure` | the pure fueled checker's letter |
| `no_proof_of_Empty_pure` | the same about `Empty` |
| `no_proof_of_Empty_pure_of` | its install-tier-conditional milestone shape |
| `no_constant_of_False` | the business end at the invariant |
| `no_constant_of_Empty` | the same about `Empty` |
| `no_constant_of_emptyPin` | the pin under it |
| `Expr.beq_eq_beqMemo` | the compiled expression equality IS `decide (a = b)` — the `@[csimp]` justification, so the trust-surface gate's "no escape" reading of `Expr.lean` is a theorem at these axioms (`Quot.sound` is the memo's quotient) |
| `Expr.decEq_eq_decEqPtr` | the compiled `DecidableEq Expr` IS the structural decision — its `@[csimp]` justification |

**What is deliberately NOT pinned here**: anything about the
`--progress` lane.  The heartbeat is printed between the steps of the
one driver (`Main.lean`), whose return value carries the proof that
`checkDecls` returns its environment; the theorems above are about
`checkDecls`, and a run with the flag is covered exactly as a run
without it.
-/

namespace ConLecheTests.Axioms

/-! ## The main theorem and the main corollary (`ConLeche/MainTheorem.lean`),
and the relation they are stated over (`ConLeche/Denotes.lean`)

The statements the project exists to make (task #277): every accepted
stream has a model (`model_exists`, over `IsModel` and the total reading
`Expr.eval`, task #617),
and hence every FILE — the chunks the binary reads — that the checker
accepts declares no theorem of type `False` (`no_False_declaration`,
tasks #290/#294/#296), which is THE MAIN COROLLARY: the statement a reader
can check without knowing what an `Env`, or even a declaration record,
is.  The step it rests on at the stream — no list of declarations one
of whose records declares a theorem of type `False` is accepted
(`no_False_theorem_accepted`, tasks #286/#288/#291, now in
`ConLeche/Verify/Cached/StreamThm.lean`) — is pinned beside it.
`Denotes_functional`, which says the relation is a partial function,
is proved with the relation itself (task #284) and is pinned here too.
Everything below them is what they are corollaries of. -/

/--
info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.model_exists

/--
info: 'ConLeche.solution_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.solution_model_exists

/--
info: 'ConLeche.main_compare_json_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_compare_json_model

/--
info: 'ConLeche.main_compare_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_compare_model

/--
info: 'ConLeche.main_compare_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_compare_no_False

/--
info: 'ConLeche.modular_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.modular_model_exists

/--
info: 'ConLeche.modular_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.modular_no_False

/--
info: 'ConLeche.Denotes_functional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Denotes_functional

/--
info: 'ConLeche.no_False_theorem_accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.no_False_theorem_accepted

/--
info: 'ConLeche.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.no_False_declaration

/--
info: 'ConLeche.main_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_no_False

/-! ## What the fold stores of what it reads
(`ConLeche/Model/StreamConsts.lean`)

The other direction of the same relation between input and output:
every record of the stream that declares a constant leaves that
constant, under its own name, with its own level parameters and its
own declared type, in the environment the fold returns. -/

/--
info: 'ConLeche.main_oleans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_oleans

/--
info: 'ConLeche.main_oleans_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_oleans_no_False

/--
info: 'ConLeche.main_compare_json_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_compare_json_no_False

/--
info: 'ConLeche.main_modular_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_compare

/--
info: 'ConLeche.main_modular_compare_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_compare_one

/--
info: 'ConLeche.main_modular_compare_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_compare_no_False

/--
info: 'ConLeche.main_modular_compare_one_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_compare_one_no_False

/--
info: 'ConLeche.main_modular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular

/--
info: 'ConLeche.main_modular_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_one

/--
info: 'ConLeche.main_modular_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_no_False

/--
info: 'ConLeche.main_modular_one_no_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.main_modular_one_no_False

/--
info: 'ConLeche.Driver.Compose.Run.localOk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.Compose.Run.localOk

/--
info: 'ConLeche.Frontend.Olean.readOleansAt_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readOleansAt_ok

/--
info: 'ConLeche.Frontend.Olean.emitAll_covers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.emitAll_covers

/--
info: 'ConLeche.Frontend.Olean.declsOf_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.declsOf_thm

/--
info: 'ConLeche.Frontend.Olean.declsOf_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.declsOf_from

/--
info: 'ConLeche.Frontend.Olean.readOleansAt_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readOleansAt_thm

/--
info: 'ConLeche.Frontend.Olean.readOleansAt_filled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readOleansAt_filled

/--
info: 'ConLeche.Driver.checkMainG_oleans_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.checkMainG_oleans_accept

/--
info: 'ConLeche.Frontend.Olean.closureOrder_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.closureOrder_ok

/--
info: 'ConLeche.Frontend.Olean.mergeAll_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.mergeAll_ok

/--
info: 'ConLeche.Frontend.Olean.readEntries_of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readEntries_of_view

/--
info: 'ConLeche.Frontend.Olean.readEntries_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readEntries_eq

/--
info: 'ConLeche.Frontend.Olean.groupRecord_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.groupRecord_from

/--
info: 'ConLeche.Frontend.Olean.groupRecord_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.groupRecord_valid

/--
info: 'ConLeche.Cached.checkDecls_of_jobs_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_of_jobs_from

/--
info: 'ConLeche.Driver.checkModuleG_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.checkModuleG_accept

/--
info: 'ConLeche.Driver.runArgs_module_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.runArgs_module_accept

/--
info: 'ConLeche.Driver.worker_ctx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_ctx

/--
info: 'ConLeche.Driver.worker_one_record' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_one_record

/--
info: 'ConLeche.Driver.worker_thm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_thm

/--
info: 'ConLeche.Driver.worker_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_local

/--
info: 'ConLeche.Driver.reach_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.reach_ok

/--
info: 'ConLeche.Driver.reachGo_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.reachGo_closed

/--
info: 'ConLeche.Driver.reachGo_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.reachGo_roots

/--
info: 'ConLeche.Driver.worker_ground' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_ground

/--
info: 'ConLeche.Driver.reach_from' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.reach_from

/--
info: 'ConLeche.Driver.copy_behind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.copy_behind

/--
info: 'ConLeche.Driver.group_presents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.group_presents

/--
info: 'ConLeche.Driver.recordFrom_presents' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.recordFrom_presents

/--
info: 'ConLeche.Driver.worker_presented' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.worker_presented

/--
info: 'ConLeche.Driver.interfaceOk_of_workers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.interfaceOk_of_workers

/--
info: 'ConLeche.Driver.presented_of_worker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.presented_of_worker

/--
info: 'ConLeche.Driver.ctx_envWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.ctx_envWF

/--
info: 'ConLeche.Driver.Graph.checkGraphG_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.Graph.checkGraphG_ok

/--
info: 'ConLeche.Driver.Graph.checkGraphG_closure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.Graph.checkGraphG_closure

/--
info: 'ConLeche.Driver.runArgs_graph_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.runArgs_graph_accept

/--
info: 'ConLeche.Driver.Graph.graphOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.Graph.graphOf_ok

/--
info: 'ConLeche.Driver.reach_within' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.reach_within

/--
info: 'ConLeche.Driver.modTables_within' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.modTables_within

/--
info: 'ConLeche.Driver.checkModularG_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.checkModularG_accept

/--
info: 'ConLeche.Driver.runArgs_modular_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.runArgs_modular_accept

/--
info: 'ConLeche.Driver.recordReads_scoped' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Driver.recordReads_scoped

/--
info: 'ConLeche.Frontend.Olean.entryWith_of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.entryWith_of_view

/--
info: 'ConLeche.Frontend.Olean.stmtWith_of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.stmtWith_of_view

/--
info: 'ConLeche.Frontend.Olean.parseAllViews_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.parseAllViews_eq

/--
info: 'ConLeche.Frontend.Olean.readView_of_all' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.readView_of_all

/--
info: 'ConLeche.Frontend.Olean.moduleImports_of_view' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Frontend.Olean.moduleImports_of_view

/--
info: 'ConLeche.Cached.checkDecls_consts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_consts

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

/-! ## The fold's well-formedness, model-free (`ConLeche/Semantics/DeclWF.lean`)

What the fold accepts is syntactically well formed, with no set theory in the statement or the
proof: the `example` below states it at no `SetTheory` instance. -/

/--
info: 'ConLeche.Semantics.checkDecls_envWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Semantics.checkDecls_envWF

/--
info: 'ConLeche.Semantics.checkDeclsPure_envWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Semantics.checkDeclsPure_envWF

example {pins : List ConLeche.NatOpPinSet} {maxNatSize : Nat} {ds : Array ConLeche.Declaration}
    {env' : ConLeche.Env} (h : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok env') :
    ConLeche.EnvWF env' :=
  ConLeche.Semantics.checkDecls_envWF h

/-! ## The driver's jobs and the fold (`ConLeche/Verify/Cached/StreamIndex.lean`) -/

/--
info: 'ConLeche.Cached.checkDecls_of_jobs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_of_jobs

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

Not a capstone: the justification under which the compiler runs `beqMemo`
for `Expr.beq`.  It is pinned because it is the theorem that turned a
census row into a `@[csimp]` equation, and because its proof is the
one place the tree quotients a runtime state (`Squash`, hence
`Quot.sound`). -/

/--
info: 'ConLeche.Expr.beq_eq_beqMemo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Expr.beq_eq_beqMemo

/--
info: 'ConLeche.Expr.decEq_eq_decEqPtr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Expr.decEq_eq_decEqPtr

/--
info: 'ConLeche.CompareAttackTest.no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.CompareAttackTest.no_model

end ConLecheTests.Axioms
