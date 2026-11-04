module

import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
public import ConLeche.Accepts
import ConLeche.Frontend.Prelude
import ConLeche.Cached.Installed
import ConLeche.Model.Denotes
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Frontend.Prepare
import ConLeche.Verify.Frontend.FileFalse
public import ConLeche.Driver.Cli
import ConLeche.Verify.Driver.Main
public section

/-!
# The main theorem and the main corollary

What the checker accepts has a model; hence a file that declares a
theorem of type `False` is rejected — the form a reader can check
without knowing what an `Env` is.  Those two theorems, and their
statements over all of `main` in the IO model (`main_model`,
`main_no_False`, at the end),
are all this file holds.  The corollary's hypothesis is the file: the chunks the binary
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

* `checkDecls` (`ConLeche/Cached/Installed.lean`) is the declaration
  fold: it installs every parsed declaration — a definition, theorem
  or opaque guarded and pushed with its check recorded, everything
  else checked in full as it is installed — and then checks every
  recorded declaration against the prefix of the environment it was
  installed at.  The binary's driver (`Main.lean`) runs this fold with a
  heartbeat between the steps and returns its environment together
  with the proof that `checkDecls` returns it
  (`Cached.fullyChecked_checkDecls`), so the success line is printed
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
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

open Frontend in
/-- **The main corollary.**  A file declaring a theorem of type `False`
in the shape `jsonWithTheoremFalse` describes is rejected: the parse
reads the template's four lines into a theorem record of type `False`,
the preparation keeps the record, and a stream holding it is never
accepted.  At every pin list, as the main theorem: the shipped binary
runs the fold at `natOpPinSets`. -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified pins ds) = .error e := by
  refine Except.exists_error_of_not_ok fun env hacc => ?_
  obtain ⟨pre, -, hacc⟩ := exceptBind_ok hacc
  obtain ⟨r, hparse, hcheck⟩ := exceptBind_ok hacc
  obtain ⟨cv, vl, hty, hmem⟩ := Frontend.parseChunks_jsonWithTheoremFalse h hparse
  exact no_False_theorem_accepted V _ cv vl (Frontend.mem_preparePrelude hmem) hty env hcheck

/-! ## All of `main`, in the IO model (tasks #424, #450)

`main` (`Main.lean`) is `Driver.mainG` at `IO`, followed by the exit
with the code `mainG` returned; `mainG` is generic in the IO class
`CheckerIO`, the code computed outside its `liftIO` escape.  The two
theorems below are about every outcome of `mainG` in the model
`ModelIO`, at the fixed arguments `-- <file>`: the default mode, which
is `.verified`, the default worker count; nothing is said about
`--help` or the other flags.  They are statements about the binary's
exit code under the assumption `ConLeche/Frontend/CheckerIO.lean`
states and argues for: the binary's file operations give the model's
answers on one snapshot, the actions passed to `CheckerIO.liftIO` do
not change what those see and do not end the process, and Lean's
compiler and runtime run the code as written — so that the binary's run is one of the model's outcomes. -/

open Frontend in
/-- **An accepted file has a model.**  Every outcome of `main` at the
arguments `-- <file>` that is an exit 0 read the file's bytes `b` off
the snapshot; they parse as one chunk to records `r`, the fold accepts
`r`'s declarations prepared with the built-in prelude, and the
environment it returns has a model in `V`. -/
theorem main_model (V : Type w) [SetTheory V] {file : String} {fs : FS}
    (h : (Driver.mainG ["--", file] : ModelIO _) fs (.ok 0)) :
    ∃ pre b r env, builtinPreludeE = .ok pre ∧ fs.file file = some b ∧
      parseChunks [b] = .ok r ∧
      checkDecls .verified natOpPinSets (preparePrelude pre r.decls) = .ok env ∧
      Nonempty (Model V env) := by
  obtain ⟨pre, b, r, env, hp, hb, hr, hc⟩ := Driver.mainG_accept h
  exact ⟨pre, b, r, env, hp, hb, hr, hc, model_exists V _ _ env hc⟩

open Frontend in
/-- **The main corollary over all of `main`.**  On a snapshot where the
file's bytes are a `jsonWithTheoremFalse` file, no outcome of `main` at
the arguments `-- <file>` is an exit 0. -/
theorem main_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (hb : fs.file file = some b) (hF : jsonWithTheoremFalse [b]) :
    ¬ (Driver.mainG ["--", file] : ModelIO _) fs (.ok 0) := by
  intro h
  obtain ⟨pre, b', r, env, hp, hb', hr, hc⟩ := Driver.mainG_accept h
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨e, he⟩ := no_False_declaration V natOpPinSets [b] hF
  simp [hp, hr, hc, bind, Except.bind] at he

end ConLeche
