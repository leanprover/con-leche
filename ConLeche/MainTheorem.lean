module

public import ConLeche.Accepts
public import ConLeche.Model.Modular.SeesCompare
import ConLeche.Model.IsModelJson
import ConLeche.Model.Solution
import ConLeche.Model.IsModelOlean
import ConLeche.Model.IsModelCompare
import ConLeche.Model.Modular.SeesMain

public section

/-!
# The main theorems

Whatever input the checker accepts has a model in every set theory: one set per constant and
list of universe levels, under which every constant of the input is a member of what its type
denotes, every definition is what its value denotes, and every recursor computes by its rules
(`IsModel`, `ConLeche/IsModel.lean`).  Each theorem below but the last two says this of one way
of running the `con-leche` binary, and some say the consequence: the input holds no constant of
type `False`.  The statements about the runs, with every name in them explained, are in
`ConLeche/Challenge.lean`.  The last two are about the checking function the runs call.

A theorem about a run speaks of `Driver.runArgs`, which is all of the binary's `main` but its
plumbing, in the file-system model `ModelIO`: an exit code `0` the model allows from a snapshot
`fs` of the files (`ModelIO.CanGive`).  `ConLeche/Frontend/CheckerIO.lean` states what this
assumes of the real files.  A comparison checks a challenge with its holes and axioms justified
by a solution; its theorems are about the challenge's input alone.

The proofs use the axioms `propext`, `Classical.choice` and `Quot.sound` and no other
(`tests/ConLecheTests/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls checkChallenge)

universe w

/-! ## A lean4export file

The binary on one file (`-- <file>`), and on a challenge file with its solution file
(`--compare -- <c> <s>`). -/

open Frontend in
/-- **An accepted file's records have a model**: an exit 0 of `-- <file>` read the file as
records that have a model in every set theory. -/
theorem main_json_model (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList) :=
  json_isModel V h hb

open Frontend in
/-- **No accepted file declares a theorem of type `False`**: no exit 0 of `-- <file>` reads a
`jsonWithTheoremFalse` file. -/
theorem main_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False :=
  json_no_False V h hb hF

open Frontend in
/-- **An accepted comparison's challenge file has a model**: an exit 0 of `--compare -- <c> <s>`
read the file `c` as records that have a model in every set theory. -/
theorem main_compare_json_model (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) :=
  compare_json_isModel V h

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
  oleans_isModel V hr h

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
  compare_isModel V hc hs h

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
  Driver.Compose.modular_sees_graph V hr h hwork

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
  Driver.Compose.modular_sees_one V hr h

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
  Driver.Compose.modular_compare_graph V hc hs hgraph hwork hcmp

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
  Driver.Compose.modular_compare_one V hc hs h

open Frontend in
/-- **No accepted modular comparison's challenge module holds a constant of type `False`**: no
snapshot where every command of `main_modular_compare` exits 0 has a constant of type `False` in
the challenge module `C`, read through the challenge's directories.  This covers what `C` sees
through its solution too, which the family of `main_modular_compare` does not. -/
theorem main_modular_compare_no_False (V : Type w) [SetTheory V] {T D c s : String}
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
  Driver.Compose.modular_compare_graph_no_False V hc hs hgraph hwork hcmp (.root (by simp)) hci hty

/-! ## The pure checker

The checking function on parsed declarations, which every run above calls: `checkDecls`, and
`checkChallenge` with a solution's declarations justifying a challenge's axioms. -/

/-- **Every stream the checker accepts has a model in every set theory.** -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  checkDecls_isModel V pins maxNatSize ds accepted

/-- **A challenge stream accepted with its axioms justified by an accepted solution stream has
a model in every set theory.** -/
theorem solution_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dsS ds : Array Declaration)
    (solution : (checkDecls .verified pins maxNatSize dsS).isOk)
    (challenge : (checkChallenge .verified pins maxNatSize dsS ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  Model.Solution.challenge_isModel solution challenge

end ConLeche
