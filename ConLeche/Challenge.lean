module

public import ConLeche.IsModel
public import ConLeche.OleanInput
public import ConLeche.Accepts
public import ConLeche.Driver.CmpReq

public section

/-!
# The main theorems, stated

ConLeche is a proof checker for Lean: it reads the declarations of a Lean development, from the
JSON file `lean4export` writes or from Lean's `.olean` files, and re-checks every one of them.
This module states the theorems the project exists to prove, about runs of the `con-leche`
binary, with `sorry` for their proofs; the proofs are in `ConLeche/MainTheorem.lean`.  Nothing
imports this file.

> **Main theorem.**  Whatever input a run of the checker accepts has a model in every set
> theory `V`: one set per constant and list of universe levels, under which every constant of
> the input is a member of what its type denotes, every definition is what its value denotes,
> and every recursor computes by its rules.

Hence an accepted input is not a proof of a contradiction, and more: every statement it proves
is true in the model.  Where the input declares Lean's `False`, a constant of type `False` would
be a member of the empty set; the `…_no_False` theorems say so directly under `ModelExists` (the
consistency / non-vacuity assumption that a model of `SetTheory` exists: because `SetTheory` is
strictly first-order, model existence is essentially the consistency of `ZFC⁻` + an ω-chain of
Grothendieck universes, needed so both the `∀ V [SetTheory V]` model statements and the
`…_no_False` corollaries are non-vacuous).

## What is specification, and what is a hole

The statements read the INPUT through definitions that say what it means.  These are imported
here, in full:

* `IsModel V model C` (`ConLeche/IsModel.lean`): `model` is a model of the constants `C`, every
  term read by `Expr.eval`, a total function from a term to a set; `constantsOf ds` are the
  constants of the declarations `ds`.  `SetTheory V` is the set theory: the proofs work for every
  `V` implementing that interface.
* The `.olean` input (`ConLeche/OleanInput.lean`, `ConLeche/Frontend/Olean/Snapshot.lean`): the
  constants of a module's files on a snapshot of the file system (`moduleConstants`), of the
  closure of some modules under their imports (`InClosure`, `closureConstants`), and what one
  module sees of another (`Sees`).
* The file system (`ConLeche/Frontend/CheckerIO.lean`): a snapshot `FS`, the model `ModelIO` of
  the file operations, and `ModelIO.CanGive x fs v`: the action `x` can answer `v` on the
  snapshot `fs`.
* `jsonWithTheoremFalse` (`ConLeche/Accepts.lean`): one JSON file declaring a theorem of type
  `False`.
* The data types the holes take and return: `ParseResultD` (the parsed declarations), `CheckError`,
  `CmpReq`, the search paths.

The binary's own functions are HOLES below: `def … := sorry` at their exact types, under their
real names.  The statements constrain the implementation that fills them: the solution's,
`ConLeche/MainTheorem.lean`'s imports.  The theorems are about that implementation, and a user
who reads them as facts about the `con-leche` binary must trust that the binary is built from it.

* `Driver.runArgs args` is all of the binary's `main` but its plumbing, at the command line
  `args`.  A theorem speaks of the exit codes `ModelIO` allows; that the binary's real file
  operations give the model's answers, on one snapshot, is the assumption
  `ConLeche/Frontend/CheckerIO.lean` states.
* `Frontend.parseChunks` is the JSON parse; `Driver.searchPathOf`, `Driver.trustedOr` and
  `Driver.CmpReq.solRoots` turn the command line into the directories a run reads.

The runs are at the checker's default settings, and `--trusted` mode is outside every
statement.
-/

namespace ConLeche

open SetTheory

universe w

/-! ## The holes: the checker's functions the statements name -/

/-- **The JSON parse** (a hole): the theorems constrain the solution's implementation, and a
user must trust that the binary is built from it. -/
def Frontend.parseChunks (chunks : List ByteArray) :
    Except (CheckError × Nat) Frontend.ParseResultD :=
  sorry

/-- **The directories of a `--search-path=` value** (a hole): the theorems constrain the
solution's implementation, and a user must trust that the binary is built from it. -/
def Driver.searchPathOf (dirs : String) : List System.FilePath :=
  sorry

open Frontend.Olean in
/-- **The challenge's directories** (a hole): the theorems constrain the solution's
implementation, and a user must trust that the binary is built from it. -/
def Driver.trustedOr (trusted path : SearchPath) : SearchPath :=
  sorry

open Frontend.Olean in
/-- **The solution's lookup** (a hole): the theorems constrain the solution's implementation,
and a user must trust that the binary is built from it. -/
def Driver.CmpReq.solRoots (r : Driver.CmpReq) : Roots :=
  sorry

open Frontend in
/-- **The binary's run** at the command line `args`, generic in the IO class (a hole): the
theorems constrain the solution's implementation, and a user must trust that the binary is built
from it. -/
def Driver.runArgs {m : Type → Type} [CheckerIO m] (args : List String) : m UInt8 :=
  sorry

/-! ## A lean4export file

The binary on one file (`-- <file>`), and on a challenge file with its solution file
(`--compare -- <c> <s>`). -/

open Frontend in
/-- **An accepted file's records have a model**: an exit 0 of `-- <file>` read the file as
records that have a model in every set theory. -/
theorem main_json_model (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList) :=
  sorry

open Frontend in
/-- **No accepted file declares a theorem of type `False`**: assuming `ModelExists` — i.e., that
our first-order set theory (`ZFC⁻` + an ω-chain of Grothendieck universes) has a model, which is
essentially its consistency and is needed so the statement is non-vacuous — no exit 0 of
`-- <file>` reads a `jsonWithTheoremFalse` file. -/
theorem main_no_False (hM : ModelExists.{w}) {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False :=
  sorry

open Frontend in
/-- **An accepted comparison's challenge file has a model**: an exit 0 of `--compare -- <c> <s>`
read the file `c` as records that have a model in every set theory. -/
theorem main_compare_json_model (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) :=
  sorry

/-! ## `.olean` files, in one process

A module and everything it imports (`--olean -- <root>`); a challenge module with its solution
module (`--olean --compare -- <c> <s>`). -/

open Frontend in
/-- **An accepted module's closure has a model**: every exit 0 of `--olean --search-path=<dirs>
-- <root>` has a model of the constants of the modules `root` imports, itself included. -/
theorem main_oleans (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model, IsModel V model (Olean.closureConstants (Driver.searchPathOf dirs) fs #[r]) :=
  sorry

open Frontend in
/-- **An accepted comparison's challenge closure has a model**: every exit 0 of `--olean
--compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` has a model of the constants
of the challenge's closure, read through the challenge's directories, on every snapshot that
agrees with the run's there. -/
theorem main_compare_model (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants
        (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs' #[C]) :=
  sorry

/-! ## `.olean` files, module by module

The import graph checked once (`--check-graph`) and each module checked on its own (`--olean
--module`), or all of it in one process (`--olean --modular`); the same for a challenge with its
solution.  The conclusion is a family of models, one per module of the closure, that agree:
a name a module sees as another module's has the value that module's model gives it. -/

open Frontend in
/-- **An accepted modular check has a family of models**: on a snapshot where `--check-graph
--search-path=<dirs> -- <root>` exits 0 and every module of the headers' closure of `root` has
an exit 0 of `--olean --module`, every module of the closure has a model of its constants, and
the models agree on what the modules see of each other. -/
theorem main_modular (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root])
      fs 0)
    (hwork : ∀ m', Olean.HdrClosure (Driver.searchPathOf dirs) fs [r] m' → ∃ root',
      Olean.parseModName root' = some m' ∧ ModelIO.CanGive
        (Driver.runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  sorry

open Frontend in
/-- **The same, in one process**: every exit 0 of `--olean --modular --search-path=<dirs>
-- <root>` has the family of models of `main_modular`. -/
theorem main_modular_one (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive
      (Driver.runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n) :=
  sorry

open Frontend in
/-- **An accepted modular comparison's challenge closure has a family of models**: on a
snapshot where every command `--schedule-commands --compare` prints for the challenge `C` and
its solution `S` exits 0 (the graph check, a worker at every module of the headers' closure of
`C` and `S` but `C`, the compare worker at `C`), on every snapshot that agrees with it under the
challenge's directories, the family of `main_modular` for the closure of `C`. -/
theorem main_modular_compare (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Olean.HdrClosure
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
  sorry

open Frontend in
/-- **The same, in one process**: every exit 0 of `--olean --modular --compare` has the family
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
  sorry

open Frontend in
/-- **No accepted modular comparison's challenge module holds a constant of type `False`**:
assuming `ModelExists` (essentially the consistency / non-vacuity of our first-order set theory),
no snapshot where every command of `main_modular_compare` exits 0 has a constant of type `False`
in the challenge module `C`, read through the challenge's directories.  This covers what `C` sees
through its solution too, which the family of `main_modular_compare` does not. -/
theorem main_modular_compare_no_False (hM : ModelExists.{w}) {T D c s : String}
    {C S : Name} {fs : FS} {ci : ConstantInfo}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Olean.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive (Driver.runArgs
        ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
          root']) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hci : Olean.InModulePart (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D))
      fs C .private ci)
    (hty : ci.type = .const falseName []) : False :=
  sorry

end ConLeche
