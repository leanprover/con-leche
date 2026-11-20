module

public import ConLeche.Cached.Decls
public import ConLeche.IsModel
public import ConLeche.Denotes
public import ConLeche.Accepts
public import ConLeche.Frontend.Prelude
public import ConLeche.Modular
public section

/-!
# The advertised statements

ConLeche is a proof checker for Lean's export format: hand it the stream
of declarations `lean4export` writes for a Lean development and it
re-checks every one of them from scratch.  This module states the
theorems the project exists to prove and leaves them `sorry`; the
proofs are in `ConLeche/MainTheorem.lean`.  Nothing imports this file.

> **Main theorem.**  If the checker accepts a stream of declarations,
> the stream has a model in every set theory `V`: one set per constant
> and list of universe levels, under which every declaration holds —
> every constant, every theorem included, is a member of what its type
> denotes, every definition is what its value denotes, and every
> recursor computes by its rules.
>
> **Main corollary.**  Hence a file — the chunks the binary reads —
> that declares a theorem of type `False` is rejected.

The corollary's conclusion is the binary's accept path, erroring: the
three pure functions the driver's phases compute, chained.  The
built-in prelude parses (`Frontend.builtinPreludeE`); the chunks parse
(`Frontend.parseChunks`); the verified fold accepts the parsed records
prepared with the prelude (`checkDecls .verified` over
`Frontend.preparePrelude`).  The chain returns an error, and the
theorem says nothing about which of the three produced it.  The driver
(`Main.lean`) runs the same three steps with IO between them — the
streaming read loop, the heartbeat, the parallel check pool — and
prints its success line only from an accept of the fold.

The corollary follows from the theorem in four steps, from the chunks
inwards.  Chunks that declare such a theorem are read by the parser
into declaration records holding a theorem record of that type — the parser resolves the file's index tables line by line, an
index bound once is never rebound, and the chunk boundaries are
invisible to it; the preparation the binary runs on the parsed records
before the fold (the built-in prelude in front, the ground of the
pinned `Nat` operations hoisted ahead of them) keeps every parsed
record; a record declaring such a theorem is installed under its own
name with its declared type and is never dropped, so it would leave a
constant of type `False` behind; its type names `False`, so the stream
declares `False`, as the prelude's; and in a model of such a stream
`False` denotes the empty set, which has no members.  An accepted file
is therefore not a proof of a contradiction, and more: every statement
it proves is true in the model.  Definitional equalities need no
clause of their own — a reader who cares that a definition unfolds as
declared states that as a theorem proved by `rfl`, and `Eq`, declared
as the prelude's, denotes equality, which turns that theorem into the
equation of the two sides' denotations.

* `checkDecls` is the shipped checking function — the one the
  `con-leche` binary runs on the parsed stream; `.verified` is its
  default `--verified` mode.
* `ds : Array Declaration` is the parsed stream; `(checkDecls … ds).isOk`
  says the checker accepted it.
* `pins : List NatOpPinSet` is the list of pin variants the fold's
  `Nat.div`/`Nat.mod` install gate tries — the one large constant the
  checker carries, and the statements quantify over it: consistency
  holds at EVERY list, the empty one included (under which a stream
  that declares `Nat.div` simply declines).  The shipped `con-leche`
  binary runs the fold at `ConLeche.natOpPinSets`, the variants this
  toolchain committed.
* `maxNatSize : Nat` is the largest `Nat` numeral, in bytes, the fold
  takes in or computes; a larger one makes it reject, as the official
  kernel does.  The statements hold at every `maxNatSize`.  The shipped
  binary runs the fold at the official default, 128 MiB, unless
  `--max-nat-size` sets another.
* `IsModel V model C` (`ConLeche/IsModel.lean`) says that `model` is
  a model of the constants `C` in `V` — here `constantsOf ds`, every
  constant of every declaration of `ds`, as a membership predicate — :
  every constant holds, its terms read by `Expr.eval`, a total function
  from a checker term to a set.  `model : Name → List Nat → V` is the
  set a constant denotes at the values of its universe levels, given
  positionally.  That file is the whole of what the main theorem's
  meaning rests on beyond the checker's own data types; it reads the
  INPUT, nothing of the environment the checker builds.  Nothing in
  it treats `False` or `Eq` specially; the checker accepts a stream
  declaring them only as the prelude does, whose own clauses make
  `False` empty and `Eq` equality in every model — which is what the
  corollary uses.
* `SetTheory V` is not a hypothesis about the input: the proof works
  for every `V` implementing that interface and never fixes one.
* `chunks : List ByteArray` are the pieces the binary's read loop is
  handed — any cut of the file, empty pieces included.
  `jsonWithTheoremFalse chunks` (`ConLeche/Accepts.lean`) says their
  concatenation is ONE particular JSON file declaring a theorem of type
  `False`: four lines in the exporter's own shapes — a name entry
  `False`, an expression entry for the constant `False`, a name entry
  for the theorem's own name, and the theorem record whose type is that
  expression — in that order, with anything at all before, between and
  after them.  The name says what it is not: it is one way of writing
  such a theorem into a JSON file, not every proof of `False` a file
  might hold, and a file that puts the same theorem there differently
  is outside it.  It is the hypothesis a reader can check without
  knowing what an `Env`, or even a declaration record, is: it speaks
  only of the bytes handed to the binary.  The five parts are
  `String`s, so the file is the UTF-8 of one interpolated Lean string;
  an export is UTF-8, so this narrows nothing a reader cares about.
* `Frontend.builtinPreludeE` is the parsed built-in prelude,
  `Frontend.parseChunks chunks` the parse of the chunks, and
  `Frontend.preparePrelude pre` the preparation of the parsed records
  for the fold.  All three fail in the same error type — the checker's
  `CheckError` paired with the position of the failure, which is the
  input's line number in the frontend's half and the fold position in
  the fold's — so the chain is one `Except` `do` block, and the
  corollary's conclusion, `∃ e, … = .error e`, says it returns one of
  those errors: the binary rejected the file.
* `False` is pinned: a stream that declares `False` or `False.rec`
  other than as the prelude's is rejected, so the conclusion needs no
  hypothesis about the input beyond its shape — not even that the file
  fits in memory: the parser refuses an input the machine word cannot
  address before reading it, which is an error like any other.
* The modular statements below are still over `Model V env`
  (`ConLeche/Denotes.lean`), a model of the environment a module's
  checks build, read by the relation `Denotes`.

Both statements are about the checking function and the parse, not
the process, and `--trusted` mode is outside both.  See README.md.

> **Modular theorem.**  A development of modules every one of which
> passes the local checks has a compatible family of models of the
> modules' own environments: two modules that store a name under one
> key give it one value, and every proof the point.  Hence no module's
> own environment stores a constant of type `False`.

* `dev : Nat → Modular.Module` is the development (`ConLeche/Modular.lean`):
  per module its context records, its own records, and for every name
  the module it is read from and its key (its home module, or for a
  proof its statement).  `LocalOk .verified pins maxNatSize dev j` are module `j`'s
  local checks: its interface presents its own records, and as an
  importer its context is made of presented records read as their
  homes read them, its own records are accepted from it by the fold's
  step, and its proof flags are proofs.

The statements about the binary's runs are in `ConLeche/MainTheorem.lean`, under the assumption
`ConLeche/Frontend/CheckerIO.lean` states: a run's file operations answer on one snapshot of the
files.  A statement about several runs (the import graph check, `--check-graph`, and the
per-module checks of the modules it numbers) assumes one snapshot for all of them: the files do
not change while the runs read them.
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every stream the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList) :=
  sorry

open Frontend in
/-- **The main corollary.**  A file declaring a theorem of type `False`
in the shape `jsonWithTheoremFalse` describes is rejected. -/
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified pins maxNatSize ds) = .error e :=
  sorry


open Modular in
/-- **The modular theorem.** -/
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j ≤ i, IsModel V (model j) (· ∈ constantsOf (dev j).decls)) ∧
      ∀ j ≤ i, ∀ n, ((dev j).context.find? n).isSome = true →
        (dev j).src n ≤ i ∧ model j n = model ((dev j).src n) n :=
  sorry

/-- **The modular corollary**: no module's own environment stores a constant of type `False`. -/
theorem modular_no_False (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∀ j ≤ i, ∀ c ∈ (dev j).own.consts, c.toConstantVal.type = .const falseName [] → False :=
  sorry

end ConLeche
