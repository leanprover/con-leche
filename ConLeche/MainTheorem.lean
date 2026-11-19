module

import ConLeche.Verify.Cached.MainC
import ConLeche.Denotes
public import ConLeche.Accepts
import ConLeche.Frontend.Prelude
import ConLeche.Cached.Decls
import ConLeche.Model.OfEnvModelM
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
import ConLeche.Model.Copies
import ConLeche.Model.Modular.CompareJson
public import ConLeche.Verify.Frontend.Olean.Local
import ConLeche.Verify.Driver.Routes
import ConLeche.Verify.Driver.Graph
public import ConLeche.Model.Modular.CompareRun
import ConLeche.Verify.Driver.CompareLocal
import ConLeche.Semantics.DeclWF
import ConLeche.Semantics.IsModelBasis
import ConLeche.Model.IsModelBridge

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
and a stream holding such a record is never accepted: its type names
`False`, so the accepted stream declares the prelude's `False`
(`Cached.checkDecls_declaresFalse`), and no model of such a stream has
a theorem of type `False` (`IsModel.no_false_record`).  The statements,
with a plain-words account of every name in them, are in
`ConLeche/Challenge.lean`; the reading of terms and the notion of
model in `ConLeche/IsModel.lean`.

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
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every stream the checker accepts has a
model in every set theory (`IsModel`, `ConLeche/IsModel.lean`), and a
stream that declares `False` or `Eq` at all declares the prelude's —
at every `Nat.div`/`Nat.mod` pin list, so consistency does not depend
on which variants the install gate is handed (the empty list included:
under it every stream that declares `Nat.div` declines).  The shipped
binary runs the fold at `natOpPinSets`. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins maxNatSize ds = .ok env) :
    (∃ model, IsModel V model (recordsOf ds.toList)) ∧
      (DeclaresName (recordsOf ds.toList) falseName → DeclaresFalse (recordsOf ds.toList)) ∧
      (DeclaresName (recordsOf ds.toList) eqName → DeclaresEq (recordsOf ds.toList)) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) accepted
  have hrec := Cached.checkDecls_recordsStored accepted
  have hstored : ∀ n, DeclaresName (recordsOf ds.toList) n → (env.find? n).isSome = true := by
    rintro n ⟨c, hc, rfl⟩
    obtain ⟨ci, hf, -⟩ := hrec c hc
    rw [hf]; rfl
  exact ⟨⟨_, isModel_of_envModelM m hrec⟩,
    fun h => Cached.checkDecls_declaresFalse accepted (hstored _ h),
    fun h => Cached.checkDecls_declaresEq accepted (hstored _ h)⟩

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
  have hmem' := Array.mem_toList_iff.mpr (Frontend.mem_preparePrelude (pre := pre) hmem)
  obtain ⟨⟨model, hM⟩, -, -⟩ := model_exists V pins maxNatSize _ env hcheck
  -- the theorem is a record of type `False`
  have hrec : HasRecord (recordsOf (preparePrelude pre r.decls).toList) cv.name cv.levelParams
      (.const falseName []) := ⟨.thmInfo cv, ⟨_, hmem', List.mem_singleton_self _⟩, by
        rw [← hty]; rfl⟩
  -- its type reads `False`, so the accepted environment stores it, as the prelude's
  have hF : DeclaresFalse (recordsOf (preparePrelude pre r.decls).toList) := by
    refine Cached.checkDecls_declaresFalse hcheck ?_
    obtain ⟨ci, hf, hcv, -⟩ := Cached.checkDecls_recordsStored hcheck (.thmInfo cv)
      ⟨_, hmem', List.mem_singleton_self _⟩
    obtain ⟨-, -, hres, -⟩ := (Semantics.checkDecls_envWF hcheck).consts ci (Env.find?_mem hf)
    rw [hcv] at hres
    change Expr.constsResolve env cv.type = true at hres
    rw [hty] at hres
    exact hres
  exact IsModel.no_false_record hM hF hrec

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
  have hv' : Olean.ViewOf (R.look m) fs m d := by
    rw [Driver.Compose.Run.ofAccepted_look]; exact hv
  obtain ⟨ci, hci, hcty⟩ :=
    R.thm_own hmR (Driver.Compose.Run.ofAccepted_x C rk good edges inj acc w m) hv' hmem hk
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
  obtain ⟨C, rk, good, hroots, edges, inj, hhdr⟩ :=
    Driver.Graph.checkGraphG_ok rfl (fun _ h => h) (fun _ _ h => by simp at h) hg
  replace good := fun e he => (good e he).plain
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

* a model `mC` of the challenge's environment (`Driver.challengeEnv`: the records of `C` and
  what they read, closed under reads, at their own level-parameter names, every hole of `C` the
  axiom of its statement) and a model `mS` of the solution's (`Driver.solutionEnv`), such that
* every constant of the challenge's environment is the solution's constant of that name, with as
  many level parameters, and `mC` gives it `mS`'s value read at the challenge's names;
* every constant of the challenge's environment, every hole of `C` among them, is inhabited by
  the solution's constant: that constant's value in `mS` is a member of what the challenge's
  type denotes in `mC`.

The challenge's environment holds what `C`'s records read, with the bodies (the merged read), and
a model makes every definition denote its value and every recursor rule hold (`Model.defn_eq`,
`Model.rule_eqs`).  So a challenge that imports `def f : Nat := 3` and has a hole `t : f = 5` has
no accepted solution: `t` reads `f`, so in `mC` `f` is `3`, and `f = 5` denotes the empty set.
Which module a solution's constant comes from (the comparison's home rule) is the code's
business; the statement needs only the models. -/
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
        ∀ n cC, (Driver.challengeEnv pre C r.chalRoots rdC).find? n = some cC →
          ∃ cS, (Driver.solutionEnv pre r.solRoots fs rdS).find? n = some cS ∧
            ∀ φ ρ, ∃ Ty, Denotes mC.cval (Driver.challengeEnv pre C r.chalRoots rdC) φ ρ
              cC.toConstantVal.type Ty ∧
              mS.cval n (Level.substFn φ cS.toConstantVal.levelParams
                (cC.toConstantVal.levelParams.map Level.param)) ∈ˢ Ty := by
  intro r
  obtain ⟨_, _, h⟩ := h
  obtain ⟨pre, rdC, rdS, ctx, filled, env, h1, h2, h3, h4, h5, h6⟩ :=
    Driver.runArgs_compare_accept hc hs h
  obtain ⟨mC, mS, h7, -⟩ := Model.Compare.compare_solved V h4 h5 h6
  refine ⟨pre, rdC, rdS, h1, h2, h3, mC, mS, h7, fun n cC hf => ?_⟩
  obtain ⟨cS, hS, -, he⟩ := h7 n cC hf
  refine ⟨cS, hS, fun φ ρ => ?_⟩
  obtain ⟨Ty, hTy, hm⟩ := mC.mem cC (Env.find?_mem hf) φ ρ
  rw [Env.find?_name hf, he φ] at hm
  exact ⟨Ty, hTy, hm⟩

open Frontend in
/-- **An accepted comparison is a property of the trusted files alone** (T1 and T2).  Every exit
0 of `runArgs` at `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` on
a snapshot `fs` says of every snapshot `fs'` that agrees with `fs` on the paths the reader forms
under the challenge's directories (`T`, or `D` where `T` names none): the challenge's read on
`fs'` (`Olean.challengeView`) can give records whose environment, every hole of `C` the axiom of
its statement, has a model in every set theory `V`.  A model inhabits the type of every constant
of its environment, so every hole is inhabited, in a model where every definition the challenge
reads denotes its value.  What the solution's files hold, and the search path's, is not in the
statement. -/
theorem main_compare_trusted (V : Type w) [SetTheory V] {T D c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    ∀ fs', FS.AgreeUnder r.chalRoots.path fs fs' →
      ∃ pre rdC, builtinPreludeE = .ok pre ∧
        Olean.challengeView r.chalRoots.path C none fs' (.ok (.ok rdC)) ∧
        Nonempty (Model V (Driver.challengeEnv pre C r.chalRoots rdC)) := by
  intro r fs' hag
  obtain ⟨pre, rdC, rdS, h1, h2, -, mC, -⟩ := main_compare_solves V hc hs h
  refine ⟨pre, rdC, h1, ?_, ⟨mC⟩⟩
  · rw [← Olean.challenge_local hag]
    obtain ⟨hs₁, hs₂, h2⟩ := h2
    refine ⟨hs₁, hs₂, ?_⟩
    rw [← r.chalRoots_eta]
    exact h2

/-! ## A challenge and its solution, module by module (task #608)

`--check-graph --compare` checks the graph of the closures of a challenge `C` and its solution
`S`, with `C`'s header importing `S`; `--olean --module` checks every module of it but `C`; the
compare worker (`--olean --module --compare`) reads `C` as one more module: its context the
reach of its names, read from the module of `S`'s closure that declares each, compared record by
record with `C`'s.  On one snapshot, those runs together are a development every module of which
passes the local checks (`Driver.Compose.Run.ofCompare`), and the modular theorem's family gives
the challenge's environment a model (`Model.CompareRun.run_models`). -/

/-- **The core of the modular comparison theorems**: a closure of the challenge `C` and its
solution `S` (each node's imports its header's, `S` added to `C`'s), ranked, read module by module
through `look` (the solution's lookup `sp`, or it without its fallback; `sp` at `C`), with an
accepted worker at every module but `C` and an accepted compare worker at `C`. -/
theorem compare_closure_solves (V : Type w) [SetTheory V] {spC sp : Frontend.Olean.Roots} {fs : FS}
    {C S : Name} (look : Name → Frontend.Olean.Roots) (trims : ∀ M, (look M).Trims sp)
    (hlook : look C = sp) (Cg : List Driver.Graph.Node) (rk : Name → Nat)
    (good : ∀ e ∈ Cg, Driver.Graph.NodeOk sp fs (Driver.Graph.cmpExtra C S) e)
    (hC : C ∈ Cg.map (·.1))
    (edges : ∀ e ∈ Cg, ∀ i ∈ e.2, i.module ∈ Cg.map (·.1) ∧ rk i.module < rk e.1)
    (inj : (Cg.map fun e => rk e.1).Nodup)
    (hhdr : ∀ e ∈ Cg, Driver.Graph.HdrClosure sp fs [C, S] e.1)
    (acc : ∀ M ∈ Cg.map (·.1), M ≠ C → ∃ jobs,
      Driver.WorkerAccepted .verified Cached.maxNatSizeDefault (look M) fs M jobs)
    {cr : Driver.CmpModuleRead} {cj : Nat} (hcr : Driver.CmpFacts spC sp fs C S cj cr) :
    let InC := Driver.Graph.HdrClosure sp fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat),
      Driver.CmpFacts spC sp fs C S cj cr ∧ w C = cr.w ∧
      (∀ m, InC m → m ≠ C → Driver.WorkerFacts (look m) fs m (jobs m) (w m)) ∧
      ∃ (mM : ∀ m, InC m → Model V (Driver.ownEnvOf (look m) fs m (w m)))
        (mC : Model V (Driver.chalEnvOf cr)),
        (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
          ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
            (mM m hm).cval n = (mM _ hh).cval n) ∧
        (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
          ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
            ∃ cS, (Driver.ownEnvOf (look (Driver.Compose.ctxHome cr.w.reach n)) fs
              (Driver.Compose.ctxHome cr.w.reach n)
              (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
          ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
            Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty := by
  intro InC
  have plain := Driver.Compose.cmp_plain good hC edges hhdr
  have hnames : ∀ m, InC m → m ∈ Cg.map (·.1) := fun m hm =>
    (Driver.Compose.cmp_rank_le good hC edges hm).1
  have hInC : ∀ m ∈ Cg.map (·.1), InC m := fun m hm => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    exact hhdr e he
  let R := Driver.Compose.Run.ofCompare C S Cg rk look trims hlook good edges inj plain acc cj cr
    hcr cr.w
  have hw : R.w C = cr.w := Driver.Compose.Run.ofCompare_w C S Cg rk look trims hlook good edges
    inj plain acc cj cr hcr cr.w
  have hRn : R.names = Cg.map (·.1) := Driver.Compose.Run.ofCompare_names C S Cg rk look trims
    hlook good edges inj plain acc cj cr hcr cr.w
  have hRx : R.x = Driver.Graph.cmpExtra C S := Driver.Compose.Run.ofCompare_x C S Cg rk look
    trims hlook good edges inj plain acc cj cr hcr cr.w
  rw [← hRn] at hnames hInC hC
  obtain ⟨m, mC, h1, h2, h3⟩ := Model.CompareRun.run_models V R hC hw hcr
  have hx : ∀ h, R.x h = #[] → h ≠ C := fun h hx he => by
    subst he
    rw [hRx, Driver.Compose.cmpExtra_self] at hx
    simp at hx
  refine ⟨R.w, R.jobs, cr, cj, hcr, hw, fun M hM hne => R.facts₀ (hnames M hM)
    (by rw [hRx]; exact Driver.Compose.cmpExtra_other hne), fun M hM => m M (hnames M hM), mC,
    fun M hM n hn => ?_, fun n cC hfC => ?_, h3⟩
  · obtain ⟨hh, he⟩ := h1 M (hnames M hM) n hn
    exact ⟨hInC _ hh, he⟩
  · obtain ⟨hh, hxh, cS, hS, hl, he⟩ := h2 n cC hfC
    exact ⟨hInC _ hh, hx _ hxh, cS, hS, hl, he⟩

open Frontend in
/-- **An accepted modular comparison: the challenge has a solution, module by module.**  On a
snapshot where `--check-graph --compare --search-path=<dirs> -- <c> <s>`, `--olean --module` at
every module of the headers' closure of `C` and `S` but `C`, and the compare worker
`--olean --module --compare --search-path=<dirs> -- <c> <s>` exit 0 (`c` naming `C`, `s` naming
`S`), there are the workers' reads (`w`, the compare worker's `cr` at `C`) and, in every set
theory `V`,

* a model `mM m` of the own environment of every module `m` of the closure (its context with its
  own records installed), compatible: every name of a module's context is valued as the module
  that declares it (its home in the context) values it;
* a model `mC` of the challenge's environment (`Driver.chalEnvOf`: the compare worker's context,
  every record of one of `C`'s names at `C`'s level-parameter names), in which every name is
  valued as its home, a module of the closure other than `C`, values it, at `C`'s names;
* every hole of `C` (an axiom of `C`, or a declaration of `C` using `sorryAx`) inhabited in `mC`.

A model makes every definition of its environment denote its value and every recursor rule hold
(`Model.defn_eq`, `Model.rule_eqs`), and a module's own environment holds its definitions with
their bodies.  So where the challenge imports `def f : Nat := 3` from `A` and has a hole
`t : f = 5`, its `f` is `A`'s, `3` in `mM A`, hence `3` in `mC`, and `f = 5` denotes the empty
set: no implementation that proves this statement accepts any solution.  Which module the
compare worker's context reads a name from (the comparison's home rule) is the code's business;
the statement needs only the family of models. -/
theorem main_compare_modular_solves (V : Type w) [SetTheory V] {dirs c s : String} {C S : Name}
    {fs : FS} (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--search-path=" ++ dirs, "--", c, s]) fs 0)
    (hwork : ∀ m, Driver.Graph.HdrClosure (Driver.searchPathOf dirs) fs [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive
        (Driver.runArgs ["--olean", "--module", "--search-path=" ++ dirs, "--", root']) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--search-path=" ++ dirs, "--", c, s]) fs 0) :
    let sp := Driver.searchPathOf dirs
    let InC := Driver.Graph.HdrClosure sp fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat),
      Driver.CmpFacts sp sp fs C S cj cr ∧ w C = cr.w ∧
      (∀ m, InC m → m ≠ C → Driver.WorkerFacts sp fs m (jobs m) (w m)) ∧
      ∃ (mM : ∀ m, InC m → Model V (Driver.ownEnvOf sp fs m (w m)))
        (mC : Model V (Driver.chalEnvOf cr)),
        (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
          ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
            (mM m hm).cval n = (mM _ hh).cval n) ∧
        (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
          ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
            ∃ cS, (Driver.ownEnvOf sp fs
              (Driver.Compose.ctxHome cr.w.reach n)
              (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
          ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
            Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty := by
  intro sp InC
  obtain ⟨_, _, hg⟩ := hgraph
  obtain ⟨gj, _, _, hg⟩ := Driver.runArgs_graphCmp_accept hc hs hg
  obtain ⟨Cg, rk, good, hroots, edges, inj, hhdr⟩ :=
    Driver.Graph.checkGraphG_ok rfl (roots' := [C, S]) (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold Driver.Graph.cmpExtra at hi
        split at hi
        · simp [Driver.Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hg
  have hC : C ∈ Cg.map (·.1) := hroots C (by simp)
  obtain ⟨_, _, hcm⟩ := hcmp
  obtain ⟨C', S', cj, hc', hs', cr, hcr⟩ := Driver.runArgs_cmpModule_accept hcm
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  refine compare_closure_solves V (fun _ => sp) (fun _ => Frontend.Olean.Roots.Trims.refl _) rfl
    Cg rk good hC edges inj hhdr (fun M hM hne => ?_) hcr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he) hne
  obtain ⟨m', jobs', hp', hacc⟩ := Driver.runArgs_module_accept hw
  obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
  exact ⟨jobs', hacc⟩

open Frontend in
/-- **An accepted modular comparison in one process.**  On a snapshot where
`--olean --modular --compare --search-path=<dirs> -- <c> <s>` exits 0 (`c` naming `C`, `s`
naming `S`), the same as `main_compare_modular_solves` from its three kinds of commands. -/
theorem main_compare_modular_one_solves (V : Type w) [SetTheory V] {dirs c s : String}
    {C S : Name} {fs : FS} (hc : Olean.parseModName c = some C)
    (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--modular", "--compare",
      "--search-path=" ++ dirs, "--", c, s]) fs 0) :
    let sp := Driver.searchPathOf dirs
    let InC := Driver.Graph.HdrClosure sp fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat),
      Driver.CmpFacts sp sp fs C S cj cr ∧ w C = cr.w ∧
      (∀ m, InC m → m ≠ C → Driver.WorkerFacts sp fs m (jobs m) (w m)) ∧
      ∃ (mM : ∀ m, InC m → Model V (Driver.ownEnvOf sp fs m (w m)))
        (mC : Model V (Driver.chalEnvOf cr)),
        (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
          ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
            (mM m hm).cval n = (mM _ hh).cval n) ∧
        (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
          ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
            ∃ cS, (Driver.ownEnvOf sp fs
              (Driver.Compose.ctxHome cr.w.reach n)
              (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
          ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
            Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty := by
  intro sp InC
  obtain ⟨_, _, h⟩ := h
  obtain ⟨C', S', hc', hs', jobs, Cg, T, ⟨_, _, hg⟩, hall, cr, hcr⟩ :=
    Driver.runArgs_modularCmp_accept h
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  obtain ⟨rk, good, hroots, edges, inj, -⟩ := Driver.Graph.graphOf_ok rfl hg
  have hhdr := Driver.Graph.graphOf_closure rfl (roots' := [C', S'])
    (fun r hr => by simp at hr; simp [hr])
    (fun m i hi => by
      unfold Driver.Graph.cmpExtra at hi
      split at hi
      · simp [Driver.Graph.solutionImport] at hi; simp [hi]
      · simp at hi) hg
  refine compare_closure_solves V (fun _ => sp) (fun _ => Frontend.Olean.Roots.Trims.refl _) rfl
    Cg.toList rk good (hroots C' (by simp)) edges inj hhdr (fun M hM hne => ?_) hcr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  exact ⟨1, hall e he hne⟩

open Frontend Classical in
/-- **An accepted modular comparison with a trusted path** (`--trusted-search-path=<T>`, `T`
naming a directory): as `main_compare_modular_solves`, the challenge's closure read through `T`
alone and the rest through `T`, then `<D>`.  The commands: `--check-graph --compare`, a worker at
every module of the headers' closure of `C` and `S` but `C` (at a module of `C`'s closure through
`T`, `--search-path=<T>`, else with both paths), and the compare worker, all with both paths but
those workers of `C`'s closure.  Every worker's facts and every module's own environment are at
its lookup (`Driver.Compose.cmpLook`). -/
theorem main_compare_modular_trusted_solves (V : Type w) [SetTheory V] {T D c s : String}
    {C S : Name} {fs : FS} (hT : (Driver.searchPathOf T).isEmpty = false)
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Driver.Graph.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive (Driver.runArgs
        (if Driver.Graph.HdrClosure
            (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).chalRoots
            fs [C] m
          then ["--olean", "--module", "--search-path=" ++ T, "--", root']
          else ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
            root'])) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    let InC := Driver.Graph.HdrClosure r.solRoots fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat),
      Driver.CmpFacts r.chalRoots r.solRoots fs C S cj cr ∧ w C = cr.w ∧
      (∀ m, InC m → m ≠ C → Driver.WorkerFacts (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m) fs m (jobs m) (w m)) ∧
      ∃ (mM : ∀ m, InC m → Model V (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m) fs m (w m)))
        (mC : Model V (Driver.chalEnvOf cr)),
        (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
          ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
            (mM m hm).cval n = (mM _ hh).cval n) ∧
        (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
          ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
            ∃ cS, (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C (Driver.Compose.ctxHome cr.w.reach n)) fs
              (Driver.Compose.ctxHome cr.w.reach n)
              (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
          ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
            Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty := by
  intro r InC
  have hchal : r.chalRoots = (Driver.searchPathOf T : Olean.Roots) := by
    simp [r, Driver.CmpReq.chalRoots, hT]
  obtain ⟨_, _, hg⟩ := hgraph
  obtain ⟨gj, _, _, hg⟩ := Driver.runArgs_graphCmpT_accept hc hs hg
  obtain ⟨Cg, rk, good, hroots, edges, inj, hhdr⟩ :=
    Driver.Graph.checkGraphG_ok (Driver.CmpReq.solRoots_bare _) (roots' := [C, S])
      (fun r hr => by simp at hr; simp [hr])
      (fun m i hi => by
        unfold Driver.Graph.cmpExtra at hi
        split at hi
        · simp [Driver.Graph.solutionImport] at hi; simp [hi]
        · simp at hi) hg
  have hC : C ∈ Cg.map (·.1) := hroots C (by simp)
  obtain ⟨_, _, hcm⟩ := hcmp
  obtain ⟨C', S', cj, hc', hs', cr, hcr⟩ := Driver.runArgs_cmpModuleT_accept hcm
  obtain rfl : C = C' := Option.some.inj (hc.symm.trans hc')
  obtain rfl : S = S' := Option.some.inj (hs.symm.trans hs')
  refine compare_closure_solves V _ (Driver.Compose.cmpLook_trims r.chal_trims fs C)
    (Driver.Compose.cmpLook_self _ _ fs C) Cg rk good hC edges inj hhdr (fun M hM hne => ?_) hcr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨root', hp, _, _, hw⟩ := hwork e.1 (hhdr e he) hne
  split at hw
  · rename_i hcc
    obtain ⟨m', jobs', hp', hacc⟩ := Driver.runArgs_module_accept hw
    obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
    refine ⟨jobs', ?_⟩
    have hl : Driver.Compose.cmpLook r.chalRoots r.solRoots fs C e.1 = r.chalRoots := by
      unfold Driver.Compose.cmpLook
      split
      · rfl
      · rename_i hn; exact absurd ⟨hne, hcc⟩ hn
    rw [hl, hchal]
    exact hacc
  · rename_i hcc
    obtain ⟨m', jobs', hp', hacc⟩ := Driver.runArgs_moduleT_accept hw
    obtain rfl : m' = e.1 := Option.some.inj (hp'.symm.trans hp)
    refine ⟨jobs', ?_⟩
    have hl : Driver.Compose.cmpLook r.chalRoots r.solRoots fs C e.1 = r.solRoots := by
      unfold Driver.Compose.cmpLook
      split
      · rename_i hn; exact absurd hn.2 hcc
      · rfl
    rw [hl]
    exact hacc C S

open Frontend Classical in
/-- **An accepted modular comparison with a trusted path, in one process.**  On a snapshot where
`--olean --modular --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>` exits 0,
the same as `main_compare_modular_trusted_solves` from its commands. -/
theorem main_compare_modular_one_trusted_solves (V : Type w) [SetTheory V] {T D c s : String}
    {C S : Name} {fs : FS} (hc : Olean.parseModName c = some C)
    (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--modular", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    let InC := Driver.Graph.HdrClosure r.solRoots fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat),
      Driver.CmpFacts r.chalRoots r.solRoots fs C S cj cr ∧ w C = cr.w ∧
      (∀ m, InC m → m ≠ C → Driver.WorkerFacts (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m) fs m (jobs m) (w m)) ∧
      ∃ (mM : ∀ m, InC m → Model V (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m) fs m (w m)))
        (mC : Model V (Driver.chalEnvOf cr)),
        (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
          ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
            (mM m hm).cval n = (mM _ hh).cval n) ∧
        (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
          ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
            ∃ cS, (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C (Driver.Compose.ctxHome cr.w.reach n)) fs
              (Driver.Compose.ctxHome cr.w.reach n)
              (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
            cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
            ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
              (cC.toConstantVal.levelParams.map Level.param))) ∧
        ∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
          ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
            Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty := by
  intro r InC
  obtain ⟨_, _, h⟩ := h
  obtain ⟨C', S', hc', hs', jobs, Cg, Tg, ⟨_, _, hg⟩, CC, RC, ⟨_, _, hgC⟩, hall, cr, hcr⟩ :=
    Driver.runArgs_modularCmpT_accept h
  obtain rfl : C' = C := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : S' = S := Option.some.inj (hs'.symm.trans hs)
  obtain ⟨rk, good, hroots, edges, inj, -⟩ := Driver.Graph.graphOf_ok (Driver.CmpReq.solRoots_bare _) hg
  have hhdr := Driver.Graph.graphOf_closure (Driver.CmpReq.solRoots_bare _) (roots' := [C', S'])
    (fun r hr => by simp at hr; simp [hr])
    (fun m i hi => by
      unfold Driver.Graph.cmpExtra at hi
      split at hi
      · simp [Driver.Graph.solutionImport] at hi; simp [hi]
      · simp at hi) hg
  -- the challenge's closure: the walk's modules, through the challenge's lookup
  obtain ⟨rkC, goodC, hrootsC, edgesC, -, -, -⟩ := Driver.Graph.graphOf_ok (Driver.CmpReq.chalRoots_bare _) hgC
  have hhdrC := Driver.Graph.graphOf_closure (Driver.CmpReq.chalRoots_bare _) (roots' := [C'])
    (fun r hr => hr) (fun _ _ hi => by simp at hi) hgC
  have hCC : ∀ m, (Driver.Graph.namesOf CC.toList).contains m = true ↔
      Driver.Graph.HdrClosure r.chalRoots fs [C'] m := fun m => by
    constructor
    · intro hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 (Driver.Graph.namesOf_contains hm)
      exact hhdrC e he
    · intro hm
      exact Driver.Graph.namesOf_of_mem (Driver.Compose.hdrClosure_mem
        (fun e he => (goodC e he).plain) hrootsC (fun e he i hi => (edgesC e he i hi).1) hm)
  refine compare_closure_solves V _ (Driver.Compose.cmpLook_trims r.chal_trims fs C')
    (Driver.Compose.cmpLook_self _ _ fs C') Cg.toList rk good (hroots C' (by simp)) edges inj hhdr
    (fun M hM hne => ?_) hcr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  refine ⟨1, ?_⟩
  have := hall e he hne
  by_cases hcc : Driver.Graph.HdrClosure r.chalRoots fs [C'] e.1
  · simp only [(hCC e.1).2 hcc, ↓reduceIte] at this
    have hl : Driver.Compose.cmpLook r.chalRoots r.solRoots fs C' e.1 = r.chalRoots := by
      unfold Driver.Compose.cmpLook
      split
      · rfl
      · rename_i hn; exact absurd ⟨hne, hcc⟩ hn
    rw [hl]
    exact this
  · have hn : (Driver.Graph.namesOf CC.toList).contains e.1 = false := by
      cases hb : (Driver.Graph.namesOf CC.toList).contains e.1
      · rfl
      · exact absurd ((hCC e.1).1 hb) hcc
    simp only [hn, Bool.false_eq_true, ↓reduceIte] at this
    have hl : Driver.Compose.cmpLook r.chalRoots r.solRoots fs C' e.1 = r.solRoots := by
      unfold Driver.Compose.cmpLook
      split
      · rename_i hn; exact absurd hn.2 hcc
      · rfl
    rw [hl]
    exact this

open Frontend Classical in
/-- **An accepted modular comparison with a trusted path is a property of the trusted files**
(T1, with T2 of `main_compare_modular_trusted_solves`).  From the same commands' exits 0 on a
snapshot `fs`: in every set theory `V`, the modules of the closure have compatible models `mM`
and the challenge's environment a model `mC` that values every name as its home's model does and
in which every hole of `C` is inhabited; and on every snapshot `fs'` that agrees with `fs` on the paths
the reader forms under `T`, the challenge's files give the same records (`cr.w.home`, whose
emission are the holes), the challenge's own view (which fixes the homes of what it imports) is
the same, and every worker of a module of the challenge's closure reads and checks alike.  What
the solution's files hold, and the search path's, is not in the statement about `fs'`. -/
theorem main_compare_modular_trusted (V : Type w) [SetTheory V] {T D c s : String}
    {C S : Name} {fs : FS} (hT : (Driver.searchPathOf T).isEmpty = false)
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (hgraph : ModelIO.CanGive (Driver.runArgs ["--check-graph", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0)
    (hwork : ∀ m, Driver.Graph.HdrClosure
        (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).solRoots fs
        [C, S] m → m ≠ C →
      ∃ root', Olean.parseModName root' = some m ∧ ModelIO.CanGive (Driver.runArgs
        (if Driver.Graph.HdrClosure
            (⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩ : Driver.CmpReq).chalRoots
            fs [C] m
          then ["--olean", "--module", "--search-path=" ++ T, "--", root']
          else ["--olean", "--module", "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--",
            root'])) fs 0)
    (hcmp : ModelIO.CanGive (Driver.runArgs ["--olean", "--module", "--compare",
      "--trusted-search-path=" ++ T, "--search-path=" ++ D, "--", c, s]) fs 0) :
    let r : Driver.CmpReq := ⟨C, S, Driver.searchPathOf T, Driver.searchPathOf D, none⟩
    let InC := Driver.Graph.HdrClosure r.solRoots fs [C, S]
    ∃ (w : Name → Driver.WorkerRead) (jobs : Name → Nat) (cr : Driver.CmpModuleRead) (cj : Nat)
      (mM : ∀ m, InC m → Model V (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m) fs m (w m)))
      (mC : Model V (Driver.chalEnvOf cr)),
      (∀ m (hm : InC m) n, ((streamEnv (w m).reach.ctx.toList).find? n).isSome = true →
        ∃ hh : InC (Driver.Compose.ctxHome (w m).reach n),
          (mM m hm).cval n = (mM _ hh).cval n) ∧
      (∀ n cC, (Driver.chalEnvOf cr).find? n = some cC →
        ∃ hh : InC (Driver.Compose.ctxHome cr.w.reach n), Driver.Compose.ctxHome cr.w.reach n ≠ C ∧
          ∃ cS, (Driver.ownEnvOf (Driver.Compose.cmpLook r.chalRoots r.solRoots fs C (Driver.Compose.ctxHome cr.w.reach n)) fs
            (Driver.Compose.ctxHome cr.w.reach n)
            (w (Driver.Compose.ctxHome cr.w.reach n))).find? n = some cS ∧
          cS.toConstantVal.levelParams.length = cC.toConstantVal.levelParams.length ∧
          ∀ φ, mC.cval n φ = (mM _ hh).cval n (Level.substFn φ cS.toConstantVal.levelParams
            (cC.toConstantVal.levelParams.map Level.param))) ∧
      (∀ d ∈ cr.w.emitted, Driver.isHole (Driver.ownUses cr.w.home) d = true →
        ∃ cv, Driver.recCv? d = some cv ∧ ∀ φ ρ, ∃ Ty,
          Denotes mC.cval (Driver.chalEnvOf cr) φ ρ cv.type Ty ∧ mC.cval cv.name φ ∈ˢ Ty) ∧
      ∀ fs', FS.AgreeUnder (Driver.searchPathOf T) fs fs' →
        (∃ f, ModelIO.CanGive (Olean.readFiles r.chalRoots C .private) fs' (.ok f) ∧
          Olean.homeOf C f = .ok (cr.w.home, cr.w.expo)) ∧
        ModelIO.CanGive (Olean.workerReads (.ofPath r.chalRoots) C cj) fs' (.ok cr.view) ∧
        ∀ m, Driver.Graph.HdrClosure r.chalRoots fs [C] m → m ≠ C →
          Driver.WorkerFacts r.chalRoots fs' m (jobs m) (w m) := by
  intro r InC
  have hchal : r.chalRoots = (Driver.searchPathOf T : Olean.Roots) := by
    simp [r, Driver.CmpReq.chalRoots, hT]
  have hR : Olean.RootsIn (Driver.searchPathOf T) r.chalRoots := by
    rw [hchal]; exact ⟨fun _ h => h, fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  obtain ⟨w, jobs, cr, cj, hcr, -, hwf, mM, mC, h1, h2, h3⟩ :=
    main_compare_modular_trusted_solves V hT hc hs hgraph hwork hcmp
  refine ⟨w, jobs, cr, cj, mM, mC, h1, h2, h3, fun fs' hag => ?_⟩
  obtain ⟨h1, h2⟩ := hcr.chal_local hR hag
  refine ⟨h1, h2, fun m hm hne => ?_⟩
  have hin : Driver.Graph.HdrClosure r.solRoots fs [C, S] m := by
    have := Driver.Graph.HdrClosure.trims r.chal_trims hm
    clear hm hwork hne
    induction this with
    | root hr => exact .root (by simp at hr; simp [hr])
    | step _ hc' hi ih => exact .step ih hc' hi
  have hl : Driver.Compose.cmpLook r.chalRoots r.solRoots fs C m = r.chalRoots := by
    unfold Driver.Compose.cmpLook
    split
    · rfl
    · rename_i hn; exact absurd ⟨hne, hm⟩ hn
  have := hwf m hin hne
  rw [hl] at this
  exact Driver.WorkerFacts.local hR hag this

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
  value in `mS` is a member of what the hole's type denotes in `mC`.

A model makes every definition denote its value and every recursor rule hold (`Model.defn_eq`,
`Model.rule_eqs`), and the challenge's environment holds its definitions with their bodies: a
challenge file with `def f : Nat := 3` and a hole `t : f = 5` has no solution. -/
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
