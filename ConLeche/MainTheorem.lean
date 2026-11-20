module

import ConLeche.Verify.Cached.MainC
import ConLeche.Denotes
import ConLeche.Frontend.Prelude
import ConLeche.Cached.Decls
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Driver.Cli
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Driver.Main
import ConLeche.Modular
import ConLeche.Model.Modular.Main
import ConLeche.Model.Capstone
import ConLeche.Verify.Driver.CompareJsonRun
import ConLeche.Model.Copies
import ConLeche.Verify.Frontend.Olean.Local
import ConLeche.Verify.Driver.Graph
public import ConLeche.Model.Modular.SeesCompare
import ConLeche.Semantics.DeclWF
import ConLeche.Semantics.IsModelBasis
import ConLeche.Model.IsModelBridge
import ConLeche.Model.Solution
import ConLeche.Model.Modular.SeesMain
import ConLeche.Model.Modular.SeesFalse
import ConLeche.Model.IsModelOlean
import ConLeche.Model.IsModelCompare
import ConLeche.Semantics.NoFalse
import ConLeche.Verify.FalseRuns
import ConLeche.Model.Modular.IsModel
import ConLeche.OleanInput

public section

/-!
# The main theorems and their corollaries

What the checker accepts has a model (`model_exists`); hence an accepted stream holds no constant
of type `False` (`no_False_declaration`).  The corollary follows from the theorem and one fact
about the stream, model-free: a constant of type `False` is stored with its type, so its type's
`False` is stored, and the checker stores at that name only the prelude's `False`, so the stream
declares it (`checkDecls_declaresFalse_of_constant`); in a model of such a stream `⟦False⟧` is
empty (`IsModel.no_False_constant`).  Each run of the binary has its main theorem below and its
corollary in the same shape: the run's acceptance hypotheses and a constant of type `False` of
its input — a theorem, an axiom, an opaque constant, a definition, or a hole read as the axiom of
its statement — give `False`.  The statements, with a plain-words account of every name in them,
are in `ConLeche/Challenge.lean`; the reading of terms and the notion of model in
`ConLeche/IsModel.lean`.

* `checkDecls` (`ConLeche/Cached/Decls.lean`) is the declaration
  fold: it checks every parsed declaration in order, each against the
  environment of the declarations before it, and pushes what the
  declaration says.  The binary's driver (`ConLeche/Driver/Cli.lean`)
  runs the same checks independently, against views of an index built
  from the records, and returns the proof that `checkDecls` accepts
  (`Cached.checkDecls_of_jobs`), so the success line is printed
  from an accept of `checkDecls` and from nothing else.
* `Frontend.parseChunks` is the streaming parse of a file's chunks (the
  driver's parse returns its result with the proof that it is this); a
  run checks the parsed records prepared with the built-in prelude
  (`Frontend.preparePrelude`), which keeps every one of them.
* `Declaration` is a parsed declaration, and the records travel as an
  `Array` of them — what the parse returns and what the fold folds;
  `Env` is the environment the checker builds; `env.consts` are the
  constants it accepted; `.verified` is the default mode.
* `False` and `Eq` are pinned: a stream that declares them other than
  as the prelude's is rejected, so where a stream declares them it
  declares the prelude's (`DeclaresFalse`, `DeclaresEq`), whose own
  clauses make `False` empty and `Eq` equality in every model.
* `pins` is the list of `Nat.div`/`Nat.mod` pin variants the fold's
  install gate tries (task #304).  Both statements are for EVERY list:
  consistency does not depend on it — under the empty list every
  stream that declares `Nat.div` simply declines, and under any other
  what an accept establishes is the certificates' verdict in the
  accepted environment, which is all the model tier reads.  The
  shipped `con-leche` binary runs the fold at `natOpPinSets`, the
  variants this toolchain committed.
* `maxNatSize` is the maximum `Nat` size: the largest `Nat` numeral, in bytes,
  the fold takes in or computes.  A larger one only ever makes the fold
  reject, so both statements hold at every `maxNatSize`; the binary runs at
  128 MiB unless `--max-nat-size` sets another.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls checkChallenge)

universe w

/-- **The main theorem.**  Every stream the checker accepts has a
model in every set theory (`IsModel`, `ConLeche/IsModel.lean`) — at
every `Nat.div`/`Nat.mod` pin list, so consistency does not depend on
which variants the install gate is handed (the empty list included:
under it every stream that declares `Nat.div` declines).  The shipped
binary runs the fold at `natOpPinSets`. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) := by
  cases h : checkDecls .verified pins maxNatSize ds with
  | error e => rw [h] at accepted; cases accepted
  | ok env =>
    obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) h
    exact ⟨_, isModel_of_envModelM m (Cached.checkDecls_recordsStored h)⟩

/-- **The main theorem, with a solution.**  A challenge stream the checker
accepts with its axioms justified by a solution stream (`checkChallenge`),
the solution itself accepted, has a model in every set theory. -/
theorem solution_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dsS ds : Array Declaration)
    (solution : (checkDecls .verified pins maxNatSize dsS).isOk)
    (challenge : (checkChallenge .verified pins maxNatSize dsS ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  Model.Solution.challenge_isModel solution challenge

/-- **The main corollary.**  An accepted stream holds no constant of type `False` — no theorem,
axiom, opaque constant or definition, and no hole read as the axiom of its statement: a model of
the stream (`model_exists`) makes `False` empty, because the stream declares the prelude's `False`
(`checkDecls_declaresFalse_of_constant`: the constant's type reads `False`, and the checker
stores at that name only the pinned block). -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) {c : ConstantInfo}
    (hc : c ∈ constantsOf ds.toList) (hty : c.type = .const falseName []) : False :=
  IsModel.no_False_constant (model_exists V pins maxNatSize ds accepted)
    (checkDecls_declaresFalse_of_constant accepted hc hty) hc hty

/-! ## `runArgs`, all of `main` but its plumbing, in the IO model (tasks #424, #450)

`main` (`Main.lean`) is `enableAbortOnNonlinear`, then `Driver.runArgs`
at `IO`, then the flush and the exit with the code `runArgs` returned;
those few lines are read, not proved.  `runArgs` is generic in the IO
class `CheckerIO`, the code computed outside its `liftIO` escape.  The
theorem below is about every outcome of `runArgs` in the model
`ModelIO`, at the fixed arguments `-- <file>`: the default mode, which
is `.verified`, the default worker count; nothing is said about
`--help` or the other flags.  It is a statement about the binary's
exit code under the assumption `ConLeche/Frontend/CheckerIO.lean`
states and argues for: the binary's file operations give the model's
answers on one snapshot, the actions passed to `CheckerIO.liftIO` do
not change what those see and do not end the process with exit code 0,
and Lean's compiler and runtime run the code as written — so that a run
of the binary that exits 0 is one of the model's outcomes. -/

open Frontend in
/-- **The main corollary, lifted to the driver.**  No exit 0 of `runArgs` at the arguments
`-- <file>` (`ModelIO.CanGive`: from whatever files the run finds open) has a file whose parsed
records hold a constant of type `False`.  The run accepted the parsed records prepared with the
built-in prelude (`Driver.runArgs_stream`), a stream holding every one of them
(`no_False_declaration`). -/
theorem main_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    {r : ParseResultD} {c : ConstantInfo}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hp : parseChunks [b] = .ok r) (hc : c ∈ constantsOf r.decls.toList)
    (hty : c.type = .const falseName []) : False := by
  obtain ⟨ds, ha, hsub⟩ := Driver.runArgs_stream h hb hp
  exact no_False_declaration V _ _ ds ha (hsub c hc) hty

open Frontend in
/-- **The main theorem, on `.olean` files.**  Every exit 0 of `runArgs` at the arguments
`--olean --search-path=<dirs> -- <root>` has a model of its input (`Olean.closureConstants`,
`ConLeche/OleanInput.lean`): every constant of the private views of the modules of the closure
of `root`. -/
theorem main_oleans (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model, IsModel V model (Olean.closureConstants (Driver.searchPathOf dirs) fs #[r]) :=
  oleans_isModel V hr h

open Frontend in
/-- **The main corollary, on `.olean` files.**  No exit 0 of `runArgs` at the arguments
`--olean --search-path=<dirs> -- <root>` has a constant of type `False` in the private part of a
module of the closure of `root`.  The run accepted the reader's records prepared with the built-in
prelude, which store every constant of the closure by one of the same statement
(`Driver.runArgs_olean_stream`, `no_False_declaration`).  Not from `main_oleans`: its model is of
the closure's constants alone, and a crafted closure may read `False` from the prelude. -/
theorem main_oleans_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m : Name} {fs : FS}
    {c : ConstantInfo} (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0)
    (hm : Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m)
    (hc : Olean.InModulePart (Driver.searchPathOf dirs) fs m .private c)
    (hty : c.type = .const falseName []) : False := by
  obtain ⟨ds, ha, c', hc', hcv⟩ := Driver.runArgs_olean_stream hr h hm hc
  exact no_False_declaration V _ _ ds ha hc' (by show c'.toConstantVal.type = _; rw [hcv]; exact hty)

/-! ## Modular checking (task #463)

A development of modules (`ConLeche/Modular.lean`) every module of which passes the local checks
has, for every module, a model of its own constants (`IsModel`, over the input), and every module
gives each name of its context the value the module it reads it from gives it.  Each module's
model is built from its sources' models alone (`ConLeche/Modular/Generic.lean`'s
`Development.modular`, at con-leche's models: `ConLeche/Model/Modular/Instance.lean`), and read
positionally (`ConLeche/Model/Modular/IsModel.lean`). -/

open Modular in
/-- **The modular theorem.** -/
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j ≤ i, IsModel V (model j) (· ∈ constantsOf (dev j).decls)) ∧
      ∀ j ≤ i, ∀ n, ((dev j).context.find? n).isSome = true →
        (dev j).src n ≤ i ∧ model j n = model ((dev j).src n) n :=
  Model.Modular.modular_isModel V pins maxNatSize dev i hok

open Frontend in
/-- **The modular theorem, run by run.**  On a snapshot where `--check-graph
--search-path=<dirs> -- <root>` exits 0 and every module of the headers' import closure of `root`
has an exit 0 of `--olean --module`, there is a model for every module of the closure of `root`
(`Olean.InClosure`): a model of the module's constants (`Olean.moduleConstants`, its private
part's), and a name the module sees as another module's (`Olean.Sees`: its header loads a part
of that module holding a constant of that name) has the value that module's model gives it. -/
theorem main_modular (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root])
      fs 0)
    (hwork : ∀ m', Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [r] m' → ∃ root',
      Olean.parseModName root' = some m' ∧ ModelIO.CanGive
        (Driver.runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  Driver.Compose.modular_sees_graph V hr h hwork

open Frontend in
/-- **The modular theorem, in one process.**  Every exit 0 of `--olean --modular
--search-path=<dirs> -- <root>` has the family of models of `main_modular`. -/
theorem main_modular_one (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive
      (Driver.runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  Driver.Compose.modular_sees_one V hr h

open Frontend in
/-- **The modular corollary, run by run.**  On a snapshot where the private view of a module `m`
of the closure of `root` (`Olean.InClosure`), by the specification, holds a theorem of type
`False`, where `m` declares the prelude's `False` or sees `False` as a module `m'` that does
(`Olean.Sees`, `DeclaresFalse`), and where every module of the headers' closure has an exit 0 of
`--olean --module`, no outcome of `--check-graph --search-path=<dirs> -- <root>` is an exit 0.
It follows from `main_modular` alone. -/
theorem main_modular_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m m' : Name}
    {fs : FS} {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m)
    (hF : m' = m ∨ Olean.Sees (Driver.searchPathOf dirs) fs m falseName m')
    (hD : DeclaresFalse (Olean.moduleConstants (Driver.searchPathOf dirs) fs m'))
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName [])
    (hwork : ∀ m', Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [r] m' → ∃ root',
      Olean.parseModName root' = some m' ∧ ModelIO.CanGive
        (Driver.runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root])
      fs 0 :=
  Driver.Compose.no_False_graph V hr hcl hF hD hv hmem hk hty hwork

open Frontend in
/-- **The modular corollary, in one process.**  On a snapshot as in `main_modular_no_False`, no
outcome of `--olean --modular --search-path=<dirs> -- <root>` is an exit 0.  It follows from
`main_modular_one` alone. -/
theorem main_modular_one_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m m' : Name}
    {fs : FS} {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m)
    (hF : m' = m ∨ Olean.Sees (Driver.searchPathOf dirs) fs m falseName m')
    (hD : DeclaresFalse (Olean.moduleConstants (Driver.searchPathOf dirs) fs m'))
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive
      (Driver.runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0 :=
  Driver.Compose.no_False_one V hr hcl hF hD hv hmem hk hty

/-! ## A challenge and its solution (tasks #607, #619)

`--olean --compare` reads a challenge module `C` through the trusted directories alone and a
solution module `S` through the trusted directories, then the search path; it checks the
solution's closure in full, then the challenge's closure in full with its axioms justified by the
solution's environment, as `--compare` does on two lean4export files.  The theorem is about the
challenge's closure through the trusted directories alone: what the solution's files hold, and the
search path's, is not in the statement. -/

open Frontend in
/-- **An accepted comparison: the challenge has a model** (`Olean.closureConstants`): every exit 0
of `runArgs` at `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`, where
`c` names the module `C` and `s` the module `S`, says of every snapshot `fs'` that agrees with the
run's on the paths the reader forms under `T` that the constants of the private views of the
modules of the closure of `C` through `T` have a model in every set theory. -/
theorem main_compare_model (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants
        (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs' #[C]) :=
  compare_isModel V hc hs h

open Frontend in
/-- **A challenge holding a constant of type `False` is never solved.**  No exit 0 of `runArgs`
at `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` has a constant of
type `False` — a hole, a theorem, an opaque constant or a definition — in the private part of a
module of the closure of `C` through `T`, whatever the solution's files hold.  Proved from the
run's environment, which stores the constant and has a model (`compare_no_False`): not from
`main_compare_model`, whose model is of the closure's constants alone (a crafted closure may read
`False` from the prelude). -/
theorem main_compare_no_False (V : Type w) [SetTheory V] {T D c s : String} {C S m : Name}
    {fs : FS} {ci : ConstantInfo}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0)
    (hm : Olean.InClosure (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs
      #[C] m)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D))
      fs m .private ci)
    (hty : ci.type = .const falseName []) : False :=
  compare_no_False V hc hs h hm hci hty

/-! ## A challenge and its solution, module by module (tasks #608, #619)

`--schedule-commands --compare -- <c> <s>` prints the commands of a modular comparison: the graph
check of the closures of the challenge `C` and its solution `S`, `S` added to `C`'s header with
`import all` (`--check-graph --compare`), a worker at every module of that graph but `C`, and the
compare worker at `C` (`--olean --module --compare`): `C`'s worker with the solution loaded whole,
each record of `C` some name of which a loaded module stores a copy of that constant (a hole, a
theorem, an opaque constant by its statement, a definition by its value too, an inductive block
as the same record, each up to the names of its level parameters), every other record of `C`
checked as any module's.  Every command reads through the trusted path, then the search path;
the challenge's closure is walked through the trusted path alone.  The theorem is about the
challenge's closure through its own directories (`Driver.trustedOr`: the trusted path, or the
search path where none is given): what the solution's files hold, and the search path's, is not
in the statement. -/

open Frontend in
/-- **An accepted modular comparison: the challenge's closure has a family of models**
(the shape of `main_modular`).  On a snapshot where every command `--schedule-commands --compare`
prints for the challenge `C` and its solution `S` exits 0 (the graph check, a worker at every
module of the headers' closure of `C` and `S` but `C`, the compare worker at `C`), on every
snapshot `fs'` that agrees with it under the challenge's directories, every module of the
closure of `C` through them has a model of its constants, and a name a module sees as another
module's has the value that module's model gives it. -/
theorem main_modular_compare (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Driver.Graph.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive (Driver.runArgs
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root']) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    let sp := Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)
    ∀ fs', FS.AgreeUnder sp fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, Olean.InClosure sp fs' #[C] m → IsModel V (model m) (Olean.moduleConstants sp fs' m)) ∧
        (∀ m n m', Olean.InClosure sp fs' #[C] m → Olean.Sees sp fs' m n m' →
          model m n = model m' n) :=
  Driver.Compose.modular_compare_graph V hc hs hgraph hwork hcmp

open Frontend in
/-- **An accepted modular comparison in one process** (`--olean --modular --compare`): the family
of `main_modular_compare`. -/
theorem main_modular_compare_one (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    let sp := Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)
    ∀ fs', FS.AgreeUnder sp fs fs' →
      ∃ model : Name → (Name → List Nat → V),
        (∀ m, Olean.InClosure sp fs' #[C] m → IsModel V (model m) (Olean.moduleConstants sp fs' m)) ∧
        (∀ m n m', Olean.InClosure sp fs' #[C] m → Olean.Sees sp fs' m n m' →
          model m n = model m' n) :=
  Driver.Compose.modular_compare_one V hc hs h

open Frontend in
/-- **A challenge holding a constant of type `False` is never solved, module by module.**  No
snapshot where every command of `main_modular_compare` exits 0 has a constant of type `False` in
the private part of a module of the closure of `C` through the challenge's directories.  Proved
from the run's own environments (`Driver.Compose.modular_compare_graph_no_False`): not from
`main_modular_compare`, whose family covers the challenge's closure only, while the compare
worker reads `C` with the solution loaded whole (a crafted `C` may see `False` through `S`
alone). -/
theorem main_modular_compare_no_False (V : Type w) [SetTheory V] {T D c s : String}
    {C S m : Name} {fs : FS} {ci : ConstantInfo}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Driver.Graph.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive (Driver.runArgs
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root']) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hm : Olean.InClosure (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs
      #[C] m)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D))
      fs m .private ci)
    (hty : ci.type = .const falseName []) : False :=
  Driver.Compose.modular_compare_graph_no_False V hc hs hgraph hwork hcmp hm hci hty

open Frontend in
/-- **A challenge holding a constant of type `False` is never solved in one process**
(`--olean --modular --compare`), as `main_modular_compare_no_False`. -/
theorem main_modular_compare_one_no_False (V : Type w) [SetTheory V] {T D c s : String}
    {C S m : Name} {fs : FS} {ci : ConstantInfo}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hm : Olean.InClosure (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs
      #[C] m)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D))
      fs m .private ci)
    (hty : ci.type = .const falseName []) : False :=
  Driver.Compose.modular_compare_one_no_False V hc hs h hm hci hty

/-! ## A challenge and its solution, as two lean4export files (task #619)

`--compare -- <c> <s>` checks the solution file `s` in full, then the challenge file `c` with the
solution's environment justifying its axioms: an axiom of the challenge other than the built-in ones, and
a definition, theorem or opaque constant whose value uses `sorryAx` (read as the axiom of its
statement), is accepted when the solution holds a constant of its name and statement, up to the
names of its level parameters, everything the statement reads being the same constant in both. -/

open Frontend in
/-- **The JSON comparison's accept has a model**: an exit 0 of `runArgs` at `--compare -- <c> <s>`
found the challenge file `c` parsing as one chunk, and the challenge's records have a model in
every set theory: its axioms are justified by the solution file's checked environment
(`solution_model_exists`). -/
theorem main_compare_json_model (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, bC, rC, bS, rS, env, -, hbC, hpC, -, -, hS, hC⟩ :=
    Driver.runArgs_compare_json_accept h
  obtain ⟨model, hm⟩ := solution_model_exists V _ _ _ _ (by rw [hS]; rfl) (by rw [hC]; rfl)
  refine ⟨bC, rC, hbC, hpC, model, hm.anti fun c hc => ?_⟩
  obtain ⟨d, hd, hc⟩ := mem_constantsOf.1 hc
  exact mem_constantsOf.2 ⟨d, Array.mem_toList_iff.2
    (Frontend.mem_preparePrelude (pre := pre) (Array.mem_toList_iff.1 hd)), hc⟩

open Frontend in
/-- **A challenge file holding a constant of type `False` is never solved.**  No exit 0 of
`runArgs` at `--compare -- <c> <s>` has a challenge file `c` whose parsed records hold a constant
of type `False` — a hole read as the axiom of its statement among them — whatever the file `s`
holds.  The run accepted the solution file's records and the challenge's, prepared with the
built-in prelude, with the solution (`Driver.runArgs_compare_json_stream`); a model of that
stream (`solution_model_exists`) makes `False` empty, as it declares the prelude's `False`. -/
theorem main_compare_json_no_False (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    {bC : ByteArray} {rC : ParseResultD} {ci : ConstantInfo}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0)
    (hbC : fs.file c = some bC) (hp : parseChunks [bC] = .ok rC)
    (hci : ci ∈ constantsOf rC.decls.toList) (hty : ci.type = .const falseName []) : False := by
  obtain ⟨dsS, ds, hS, hC, hsub⟩ := Driver.runArgs_compare_json_stream h hbC hp
  exact IsModel.no_False_constant (solution_model_exists V _ _ dsS ds hS hC)
    (checkDecls_declaresFalse_of_constant hC (hsub ci hci) hty) (hsub ci hci) hty

end ConLeche
