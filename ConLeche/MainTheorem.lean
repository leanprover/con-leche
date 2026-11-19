module

import ConLeche.Verify.Cached.MainC
import ConLeche.Denotes
public import ConLeche.Accepts
import ConLeche.Frontend.Prelude
import ConLeche.Cached.Decls
import ConLeche.Model.Denotes
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Driver.Cli
import ConLeche.Verify.Frontend.Olean.Files
import ConLeche.Verify.Driver.Main
import ConLeche.Modular
import ConLeche.Model.Modular.Main
import ConLeche.Model.Capstone
import ConLeche.Model.Modular.Compare
public import ConLeche.Verify.Driver.CompareRun
public import ConLeche.Verify.Driver.CompareJsonRun
public import ConLeche.Model.Copies
import ConLeche.Model.Modular.CompareJson
public import ConLeche.Verify.Frontend.Olean.Local
import ConLeche.Verify.Driver.Routes
public import ConLeche.Verify.Driver.Graph
public import ConLeche.Verify.Driver.Worker
public section

/-!
# The main theorem and the main corollary

What the checker accepts has a model; hence a file that declares a
theorem of type `False` is rejected — the form a reader can check
without knowing what an `Env` is.  Those two theorems, and the main
corollary lifted to the driver (`main_no_False`, at the end), are all
this file holds.  The corollary's hypothesis is the file: the chunks the binary
read are the UTF-8 of `jsonWithTheoremFalse`'s template, ONE way of
writing a theorem of type `False` into a JSON export.  Its conclusion
is the binary's accept path itself, erroring: the three pure functions
the driver's phases compute, chained — the built-in prelude parses, the
chunks parse, the verified fold accepts the parsed records prepared
with the prelude — return an error.  The steps between are imported:
the parser reads such chunks into records holding a theorem record of
type `False` (`Frontend.parseChunks_jsonWithTheoremFalse`), the
preparation keeps every parsed record (`Frontend.mem_preparePrelude`),
and a stream holding such a record is never accepted
(`no_False_theorem_accepted`: the record is installed under its own
name with its declared type, and in the model of the main theorem that
type is the empty set).  The statements, with a plain-words account of
every name in them, are in `ConLeche/Challenge.lean`; the reading of
terms and the notion of model — and `Denotes_functional`, which says a
term has at most one denotation — in `ConLeche/Denotes.lean`.

* `checkDecls` (`ConLeche/Cached/Decls.lean`) is the declaration
  fold: it checks every parsed declaration in order, each against the
  environment of the declarations before it, and pushes what the
  declaration says.  The binary's driver (`ConLeche/Driver/Cli.lean`)
  runs the same checks independently, against views of an index built
  from the records, and returns the proof that `checkDecls` accepts
  (`Cached.checkDecls_of_jobs`), so the success line is printed
  from an accept of `checkDecls` and from nothing else.
* `Frontend.builtinPreludeE` is the parsed built-in prelude,
  `Frontend.parseChunks` the streaming parse of the file's chunks (the
  driver's parse returns its result with the proof that it is this), and
  `Frontend.preparePrelude` the preparation of the parsed records for
  the fold.  The three fail in ONE error type — the checker's own
  `CheckError` with the position of the failure (the input's line
  number for the first two, the fold position for the fold) — so the
  chain is a plain `Except` `do` block with no conversion in it, and
  the conclusion is simply that it errors, with no claim about which
  step erred or why.
* `Declaration` is a parsed declaration, and the records travel as an
  `Array` of them — what the parse returns and what the fold folds;
  `Env` is the environment the checker builds; `env.consts` are the
  constants it accepted; `.verified` is the default mode.
* `jsonWithTheoremFalse` (`ConLeche/Accepts.lean`) is one particular
  JSON file declaring a theorem of type `False`, as a whole-file
  template over the chunks' concatenation — not every proof of `False`,
  one shape of one.
* `False` and `Eq` are built in: the checker installs them from its own
  pins, and a stream that declares them differently is rejected.
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
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory — at every `Nat.div`/`Nat.mod` pin list, so
consistency does not depend on which variants the install gate is
handed (the empty list included: under it every stream that declares
`Nat.div` declines).  The shipped binary runs the fold at
`natOpPinSets`. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins maxNatSize ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

open Frontend in
/-- **The main corollary.**  A file declaring a theorem of type `False`
in the shape `jsonWithTheoremFalse` describes is rejected: the parse
reads the template's four lines into a theorem record of type `False`,
the preparation keeps the record, and a stream holding it is never
accepted.  At every pin list, as the main theorem: the shipped binary
runs the fold at `natOpPinSets`. -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified pins maxNatSize ds) = .error e := by
  refine Except.exists_error_of_not_ok fun env hacc => ?_
  obtain ⟨pre, -, hacc⟩ := exceptBind_ok hacc
  obtain ⟨r, hparse, hcheck⟩ := exceptBind_ok hacc
  obtain ⟨cv, vl, hty, hmem⟩ := Frontend.parseChunks_jsonWithTheoremFalse h hparse
  exact no_False_theorem_accepted V _ cv vl (Frontend.mem_preparePrelude hmem) hty env hcheck

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
/-- **The main corollary, lifted to the driver.**  On a snapshot where the
file's bytes are a `jsonWithTheoremFalse` file, no outcome of `runArgs` at
the arguments `-- <file>` is an exit 0 (`ModelIO.CanGive`: from whatever
files the run finds open). -/
theorem main_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (hb : fs.file file = some b) (hF : jsonWithTheoremFalse [b]) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0 := by
  rintro ⟨_, _, h⟩
  obtain ⟨pre, b', r, env, hp, hb', hr, hc⟩ := Driver.runArgs_accept h
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨e, he⟩ := no_False_declaration V natOpPinSets Cached.maxNatSizeDefault [b] hF
  simp [hp, hr, hc, bind, Except.bind] at he

open Frontend in
/-- **The main corollary, on `.olean` files.**  On a snapshot where the private view of a module
of the closure of `root`, by the specification, holds a theorem of type `False`, no outcome of
`runArgs` at the arguments `--olean --search-path=<dirs> -- <root>` is an exit 0.  At these
arguments every constant of the closure is checked. -/
theorem main_oleans_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m : Name} {fs : FS}
    {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m)
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--olean", "--search-path=" ++ dirs, "--", root]) fs 0 := by
  rintro ⟨_, _, h⟩
  obtain ⟨pre, rd, env, -, hrd, hchk⟩ := Driver.runArgs_olean_accept h
  have hroots : (#[root].filterMap Olean.parseModName) = #[r] := by simp [hr]
  rw [hroots] at hrd
  obtain ⟨_, _, hrd⟩ := hrd
  obtain ⟨v', hd⟩ := Olean.readOleansAt_thm rfl hrd hcl hv hmem hk
  exact no_False_theorem_accepted V _ _ _
    (Array.mem_map_of_mem (f := Cached.fillDecl _) (Frontend.mem_prepareD hd)) hty env hchk


/-! ## Modular checking (task #463)

A development of modules (`ConLeche/Modular.lean`) every module of which passes the local checks
has a compatible family of models of the modules' own environments: every module gives each name
of its context the value the module it reads it from gives it, and every theorem the point.  Each module's model is built from its
sources' models alone (`ConLeche/Modular/Generic.lean`'s `Development.modular`, at con-leche's
models: `ConLeche/Model/Modular/Instance.lean`). -/

open Modular in
/-- **The modular theorem.** -/
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∃ m : ∀ j ≤ i, Model V (dev j).own,
      (∀ j hj n, ((dev j).context.find? n).isSome = true →
        ∃ h : (dev j).src n ≤ i, (m j hj).cval n = (m ((dev j).src n) h).cval n) ∧
      ∀ j hj n cv, (dev j).own.find? n = some (.thmInfo cv) →
        (m j hj).cval n = fun _ => pt := by
  obtain ⟨mm, hc⟩ := Model.Modular.modularModels (V := V) (pins := pins) hok
  have hex : ∀ j (hj : j ≤ i), ∃ mp : Model.EnvModelM V (dev j).own,
      ∀ n, ((dev j).own.find? n).isSome = true → mp.base2.acval n = (mm j (by omega)).1 n :=
    fun j hj => (mm j (by omega)).2.2.2.2.elim fun mp h => ⟨mp, h.2.2⟩
  refine ⟨fun j hj => Model.Model.ofEnvModelM (Classical.choose (hex j hj)), ?_, ?_⟩
  · intro j hj n hn
    obtain ⟨hs, he, -⟩ := hc j (by omega) n ⟨hn, trivial⟩
    have hs' : (dev j).src n < i + 1 := hs
    have hsi : (dev j).src n ≤ i := by omega
    refine ⟨hsi, ?_⟩
    rw [Model.Model.ofEnvModelM_cval, Model.Model.ofEnvModelM_cval]
    apply Model.cvalOf_congr
    rw [Classical.choose_spec (hex j hj) n (Model.Modular.own_stored_of_context hok hj hn),
      Classical.choose_spec (hex _ hsi) n (Model.Modular.src_stored hok hj hn)]
    exact he
  · intro j hj n cv hn
    rw [Model.Model.ofEnvModelM_cval]
    apply Model.cvalOf_prf
    rw [Classical.choose_spec (hex j hj) n (by rw [hn]; rfl)]
    exact Model.Modular.ProofLeaves.thm (mm j (by omega)).2.2.2.1 hn

/-- **The modular corollary**: no module's own environment stores a constant of type `False`. -/
theorem modular_no_False (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∀ j ≤ i, ∀ c ∈ (dev j).own.consts, c.toConstantVal.type = .const falseName [] → False := by
  intro j hj c hc hty
  obtain ⟨mm, -⟩ := Model.Modular.modularModels (V := V) (pins := pins) hok
  obtain ⟨mp, -⟩ := (mm j (by omega)).2.2.2.2
  exact Model.no_constant_of_False mp c hc hty

open Frontend in
/-- **An accepted run over a closure holds no theorem of type `False`**: on a snapshot where every
module of a closure (`C`, each node's imports its header's, closed under imports, ranked one to one
and decreasing along every import) has an accepted worker, no module of `C` has a theorem of type
`False` in its private view.  The run is a development every module of which passes the local
checks (`Driver.Compose.Run.localOk`), and the theorem is a constant of its module's own
environment (`Driver.Compose.Run.thm_own`). -/
theorem run_no_False (V : Type w) [SetTheory V] {sp : Olean.SearchPath} {fs : FS}
    {maxNatSize : Nat}
    (C : List Driver.Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ C, ModelIO.CanGive (Olean.moduleImports sp e.1) fs (.ok e.2))
    (edges : ∀ e ∈ C, ∀ i ∈ e.2, i.module ∈ C.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (C.map fun e => rk e.1).Nodup)
    (acc : ∀ M ∈ C.map (·.1), ∃ jobs, Driver.WorkerAccepted .verified maxNatSize sp fs M jobs)
    {m : Name} (hm : m ∈ C.map (·.1)) {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr}
    {v : Expr} {all : List Name} (hv : Olean.ViewOf sp fs m d) (hmem : c ∈ d.constants)
    (hk : c.kind = .thm v all) (hty : c.type = .const falseName []) : False := by
  obtain ⟨_, w, -⟩ := acc m hm
  let R := Driver.Compose.Run.ofAccepted C rk good edges inj acc w
  have hmR : m ∈ R.names := by rw [Driver.Compose.Run.ofAccepted_names]; exact hm
  obtain ⟨ci, hci, hcty⟩ := R.thm_own hmR hv hmem hk
  exact modular_no_False V natOpPinSets maxNatSize R.dev (R.rk m) (fun j _ => R.localOk j) (R.rk m)
    (Nat.le_refl _) ci hci (by rw [hcty, hty])

open Frontend in
/-- **The modular corollary, run by run.**  On a snapshot where the private view of a module of
the headers' import closure of `root`, by the specification, holds a theorem of type `False`, and
where every module of that closure has an exit 0 of `--olean --module`, no outcome of
`--check-graph --search-path=<dirs> -- <root>` is an exit 0. -/
theorem main_modular_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m : Name}
    {fs : FS} {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [r] m)
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName [])
    (hwork : ∀ m', Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [r] m' → ∃ root',
      Olean.parseModName root' = some m' ∧ ModelIO.CanGive
        (Driver.runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--check-graph", "--search-path=" ++ dirs, "--", root])
      fs 0 := by
  rintro ⟨_, _, h⟩
  obtain ⟨jobs, _, _, hg⟩ := Driver.runArgs_graph_accept hr h
  obtain ⟨C, rk, good, hroots, edges, inj, hhdr⟩ := Driver.Graph.checkGraphG_ok hg
  refine run_no_False V (maxNatSize := Cached.maxNatSizeDefault) C rk good edges inj
    (fun M hM => ?_)
    (Driver.Compose.hdrClosure_mem good hroots (fun e he i hi => (edges e he i hi).1) hcl)
    hv hmem hk hty
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he)
  obtain ⟨m', jobs', hp', hacc⟩ := Driver.runArgs_module_accept hw
  obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
  exact ⟨jobs', hacc⟩

open Frontend in
/-- **The modular corollary, in one process.**  On a snapshot where the private view of a module
of the headers' import closure of `root`, by the specification, holds a theorem of type `False`,
no outcome of `--olean --modular --search-path=<dirs> -- <root>` is an exit 0. -/
theorem main_modular_one_no_False (V : Type w) [SetTheory V] {dirs root : String} {r m : Name}
    {fs : FS} {d : Olean.ModDecoded} {c : Olean.CEntryF Name Expr} {v : Expr} {all : List Name}
    (hr : Olean.parseModName root = some r)
    (hcl : Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [r] m)
    (hv : Olean.ViewOf (Driver.searchPathOf dirs) fs m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all) (hty : c.type = .const falseName []) :
    ¬ ModelIO.CanGive
      (Driver.runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0 := by
  rintro ⟨_, _, h⟩
  obtain ⟨m₀, hp, C, rk, good, hm₀, edges, inj, hacc⟩ := Driver.runArgs_modular_accept h
  obtain rfl : m₀ = r := Option.some.inj (hp.symm.trans hr)
  refine run_no_False V (maxNatSize := Cached.maxNatSizeDefault) C rk good edges inj
    (fun M hM => ?_)
    (Driver.Compose.hdrClosure_mem good (fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact hm₀)
      (fun e he i hi => (edges e he i hi).1) hcl) hv hmem hk hty
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  exact ⟨1, hacc e he⟩

/-! ## A challenge and its solution (task #607)

`--olean --compare` reads a challenge module `C` through the trusted directories alone and a
solution module `S` through the trusted directories, then the search path; it compares the
challenge's records with the solution's (`Driver.compareRecords`) and checks the solution's
closure.  An accept makes the two a development of two modules, the solution's and the
challenge's, both passing the local checks, and the modular theorem's construction gives the
challenge's environment a model read off the solution's (`Model.Compare.compare_models`). -/

open Frontend in
/-- **An accepted comparison: the challenge has a solution.**  Every exit 0 of `runArgs` at
`--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`, where `c` names the
module `C` and `s` the module `S`, read the challenge's closure through `T` alone and the
solution's through `T`, then `D`, and in every set theory `V` there are

* a model `mC` of the challenge's environment (`Driver.challengeEnv`: its records at their own
  level-parameter names, every hole of `C` the axiom of its statement) and a model `mS` of the
  solution's (`Driver.solutionEnv`), such that
* every constant of the challenge's environment is the solution's constant of that name, with as
  many level parameters, and `mC` gives it `mS`'s value read at the challenge's names;
* every hole of `C` is inhabited by the solution's constant: that constant's value in `mS` is a
  member of what the hole's type denotes in `mC`;
* every declaration `C` imports (its home, the first module of the challenge's closure storing
  it, is not `C`), but a theorem, which Lean keys by its statement, has the same home in the
  solution's closure: it is that module's constant, not one the solution declares itself. -/
theorem main_compare_solves (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    ∃ pre rdC rdS, builtinPreludeE = .ok pre ∧
      ModelIO.CanGive (Olean.readOleansAt r.chalRoots #[C] none (lenient := true)
        (homes := true)) fs (.ok rdC) ∧
      ModelIO.CanGive (Olean.readOleansAt r.solRoots #[S] none (lenient := true)
        (homes := true)) fs (.ok rdS) ∧
      ∃ (mC : Model V (Driver.challengeEnv pre C r.chalRoots rdC))
        (mS : Model V (Driver.solutionEnv pre r.solRoots fs rdS)),
        (∀ n cC, (Driver.challengeEnv pre C r.chalRoots rdC).find? n = some cC →
          ∃ cS, (Driver.solutionEnv pre r.solRoots fs rdS).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        (∀ d ∈ Driver.cmpRecs pre r.chalRoots rdC, rdC.homes[Driver.recKey d]? = some C →
          Driver.isHole (Driver.usedOf (some (r.chalRoots.path, rdC))) d = true →
          ∃ cv cS, Driver.recCv? d = some cv ∧
            (Driver.solutionEnv pre r.solRoots fs rdS).find? cv.name = some cS ∧
            ∀ φ ρ, ∃ Ty, Denotes mC.cval (Driver.challengeEnv pre C r.chalRoots rdC) φ ρ cv.type Ty ∧
              mS.cval cv.name (Level.substFn φ cS.toConstantVal.levelParams
                (cv.levelParams.map Level.param)) ∈ˢ Ty) ∧
        ∀ d ∈ Driver.cmpRecs pre r.chalRoots rdC, rdC.homes[Driver.recKey d]? ≠ some C →
          (∀ cv v, d ≠ .thmDecl cv v) →
          rdS.homes[Driver.recKey d]? = rdC.homes[Driver.recKey d]? := by
  intro r
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, rdC, rdS, ctx, filled, env, h1, h2, h3, h4, h5, h6⟩ :=
    Driver.runArgs_compare_accept hc hs h
  obtain ⟨mC, mS, h7, h8⟩ := Model.Compare.compare_solved V h4 h5 h6
  refine ⟨pre, rdC, rdS, h1, h2, h3, mC, mS, h7, h8, fun d hd hne hthm => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hd
  exact Model.Compare.compare_homes h4 k hk hne hthm

open Frontend in
/-- **An accepted comparison is a property of the trusted files alone** (T1 and T2).  Every exit
0 of `runArgs` at `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` on
a snapshot `fs` says of every snapshot `fs'` that agrees with `fs` on the paths the reader forms
under the challenge's directories (`T`, or `D` where `T` names none): the challenge's read on
`fs'` (`Olean.challengeView`) can give records whose environment, every hole of `C` the axiom of
its statement, has a model in every set theory `V`, in which every hole is inhabited.  What the
solution's files hold, and the search path's, is not in the statement. -/
theorem main_compare_trusted (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    ∀ fs', FS.AgreeUnder r.chalRoots.path fs fs' →
      ∃ pre rdC, builtinPreludeE = .ok pre ∧
        Olean.challengeView r.chalRoots.path C none fs' (.ok (.ok rdC)) ∧
        ∃ mC : Model V (Driver.challengeEnv pre C r.chalRoots rdC),
          ∀ d ∈ Driver.cmpRecs pre r.chalRoots rdC, rdC.homes[Driver.recKey d]? = some C →
            Driver.isHole (Driver.usedOf (some (r.chalRoots.path, rdC))) d = true →
            ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
              Denotes mC.cval (Driver.challengeEnv pre C r.chalRoots rdC) φ ρ cv.type Ty ∧
              ∃ v, v ∈ˢ Ty := by
  intro r fs' hag
  obtain ⟨pre, rdC, rdS, h1, h2, -, mC, mS, -, h5, -⟩ := main_compare_solves V hc hs h
  refine ⟨pre, rdC, h1, ?_, mC, fun d hd hown hh => ?_⟩
  · rw [← Olean.challenge_local hag]
    obtain ⟨hs₁, hs₂, h2⟩ := h2
    refine ⟨hs₁, hs₂, ?_⟩
    rw [← r.chalRoots_eta]
    exact h2
  · obtain ⟨cv, cS, hcv, -, hmem⟩ := h5 d hd hown hh
    exact ⟨cv, hcv, fun φ ρ => let ⟨Ty, hT, hm⟩ := hmem φ ρ; ⟨Ty, hT, _, hm⟩⟩

/-! ## A challenge and its solution, as two lean4export files (task #612)

`--compare -- <c> <s>` compares the challenge file `c` with the solution file `s`: every record of
the challenge file is the challenge's own (an export has no modules), its holes the axioms but
the standard ones and the declarations whose value uses `sorry` (`Driver.jsonHole`), every other
record the solution's by content, up to the names of its level parameters; and the solution's
file is checked in full.  The challenge's meaning is a function of its bytes alone: the theorem
is stated over them. -/

open Frontend in
/-- **An accepted comparison of two lean4export files: the challenge has a solution.**  On a
snapshot where the challenge file `c` has the bytes `bC` and the solution file `s` the bytes
`bS`, every exit 0 of `runArgs` at `--compare -- <c> <s>` means: `bC` and `bS` each parse as one
chunk; `checkDecls .verified` accepts the solution's records prepared with the built-in prelude;
the challenge's environment (`Driver.jsonChallengeEnv`: the challenge's records, each hole as
the axiom of its statement, at the challenge's own level-parameter names) embeds into the
solution's: every constant of it is a copy of the solution's constant of that name, up to the
names of its level parameters (`Model.ConstCopy`), or, for a hole, the axiom of such a copy of
that constant's statement; and in every set theory `V` there are

* a model `mC` of the challenge's environment and a model `mS` of the solution's, `mC` giving
  every constant `mS`'s value read at the challenge's level-parameter names;
* every hole of the challenge file is inhabited by the solution's constant: that constant's
  value in `mS` is a member of what the hole's type denotes in `mC`. -/
theorem main_compare_json_solves (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    {bC bS : ByteArray} (hbC : fs.file c = some bC) (hbS : fs.file s = some bS)
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ pre rC rS, builtinPreludeE = .ok pre ∧ parseChunks [bC] = .ok rC ∧
      parseChunks [bS] = .ok rS ∧
      (∃ env, checkDecls .verified natOpPinSets Cached.maxNatSizeDefault
        (preparePrelude pre rS.decls) = .ok env) ∧
      (∀ n cC, (Driver.jsonChallengeEnv pre rC.decls).find? n = some cC →
        ∃ cS, (streamEnv (preparePrelude pre rS.decls).toList).find? n = some cS ∧
          (Model.ConstCopy cS cC ∨ Model.ConstCopy (.axiomInfo cS.toConstantVal) cC)) ∧
      ∃ (mC : Model V (Driver.jsonChallengeEnv pre rC.decls))
        (mS : Model V (streamEnv (preparePrelude pre rS.decls).toList)),
        (∀ n cC, (Driver.jsonChallengeEnv pre rC.decls).find? n = some cC →
          ∃ cS, (streamEnv (preparePrelude pre rS.decls).toList).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ rC.decls, Driver.jsonHole d = true →
          ∃ cv cS, Driver.recCv? d = some cv ∧
            (streamEnv (preparePrelude pre rS.decls).toList).find? cv.name = some cS ∧
            ∀ φ ρ, ∃ Ty, Denotes mC.cval (Driver.jsonChallengeEnv pre rC.decls) φ ρ cv.type Ty ∧
              mS.cval cv.name (Level.substFn φ cS.toConstantVal.levelParams
                (cv.levelParams.map Level.param)) ∈ˢ Ty := by
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, bC', rC, bS', rS, ctx, filled, env, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    Driver.runArgs_compare_json_accept h
  obtain rfl : bC = bC' := Option.some.inj (hbC.symm.trans h2)
  obtain rfl : bS = bS' := Option.some.inj (hbS.symm.trans h4)
  obtain ⟨hemb, mC, mS, hm, hh⟩ := Model.Compare.compare_json_solved V h6 h7 h8
  exact ⟨pre, rC, rS, h1, h3, h5, ⟨env, h8⟩, hemb, mC, mS, hm, hh⟩

open Frontend in
/-- **A challenge file with a hole of type `False` has no solution.**  On a snapshot where the
challenge file `c`'s bytes parse to records one of which is a hole (`Driver.jsonHole`: an axiom
other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`, or a definition, theorem
or opaque constant whose value uses `sorryAx`) of type `False`, no outcome of `runArgs` at
`--compare -- <c> <s>` is an exit 0, whatever the file `s` holds: the hole would be inhabited
in a model, and `False` denotes the empty set. -/
theorem main_compare_json_no_False (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    {bC : ByteArray} {rC : ParseResultD} {d : Declaration} {cv : ConstantVal}
    (hbC : fs.file c = some bC) (hp : parseChunks [bC] = .ok rC) (hd : d ∈ rC.decls)
    (hh : Driver.jsonHole d = true) (hcv : Driver.recCv? d = some cv)
    (hty : cv.type = .const falseName []) :
    ¬ ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0 := by
  intro h
  have h0 := h
  obtain ⟨_, _, h'⟩ := h0
  obtain ⟨-, -, -, bS, -, -, -, -, -, -, -, hbS, -⟩ := Driver.runArgs_compare_json_accept h'
  obtain ⟨pre, rC', rS, -, hp', -, -, -, mC, mS, -, hholes⟩ :=
    main_compare_json_solves V hbC hbS h
  obtain rfl : rC = rC' := Except.ok.inj (hp.symm.trans hp')
  obtain ⟨cv', cS, hcv', -, hmem⟩ := hholes d hd hh
  obtain rfl : cv = cv' := Option.some.inj (hcv.symm.trans hcv')
  obtain ⟨Ty, hT, hin⟩ := hmem (fun _ => 0) (fun _ => SetTheory.empty)
  rw [hty] at hT
  rw [mC.false_empty _ _ _ hT] at hin
  exact SetTheory.not_mem_empty _ hin

end ConLeche
