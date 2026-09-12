module

public import ConLeche.Cached.Installed
public import ConLeche.Denotes
public import ConLeche.Accepts
public import ConLeche.Frontend.Prelude
public section

/-!
# The advertised statements

ConLeche is a proof checker for Lean's export format: hand it the stream
of declarations `lean4export` writes for a Lean development and it
re-checks every one of them from scratch.  This module states the
theorems the project exists to prove and leaves them `sorry`; the
proofs are in `ConLeche/MainTheorem.lean`.  Nothing imports this file.

> **Main theorem.**  If the checker accepts a stream, the environment
> it built has a model in every set theory `V`: one set per constant
> under which every constant — every theorem included — is a member
> of its type, `False` is empty, and `Eq` is set equality.
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
constant of type `False` behind; and `False` denotes the empty set,
which has no members, so an accepted environment holds no such
constant.  An accepted file is therefore not a proof of a
contradiction, and more: every statement it proves is true in the
model.  Definitional equalities need no clause of their own — a reader
who cares that a definition unfolds as declared states that as a
theorem proved by `rfl`, and `Model`'s `eq_equality` field, which says
the built-in `Eq` denotes set equality, turns that theorem into the
equation of the two sides' denotations.

* `checkDecls` is the shipped checking function — the one the
  `con-leche` binary runs on the parsed stream; `.verified` is its
  default `--verified` mode.
* `ds : Array Declaration` is the parsed stream, `Env` the environment the
  checker builds, `env.consts` the constants it accepted; `.ok env`
  says the checker accepted `ds` and this is what it accepted.
* `Model V env` (`ConLeche/Denotes.lean`) is a model of `env` in `V`,
  built on `Denotes`, the reading of a checker term as a set; that
  file is the whole of what the main theorem's meaning rests on beyond
  the checker's own data types.  It also proves `Denotes_functional`:
  a term has at most one denotation, so where `Model` says a stored
  constant is a member of *some* denotation of its type, it is saying
  so of *the* denotation.
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
* `False` is built in: the checker installs it from its own pin, and a
  stream that declares `False` or `False.rec` differently is rejected,
  so the conclusion needs no hypothesis about the input beyond its
  shape — not even that the file fits in memory: the parser refuses an
  input the machine word cannot address before reading it, which is an
  error like any other.

Both statements are about the checking function and the parse, not
the process, and `--trusted` mode is outside both.  See README.md.
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory. -/
theorem model_exists (V : Type w) [SetTheory V]
    (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified ds = .ok env) :
    Nonempty (Model V env) :=
  sorry

open Frontend in
/-- **The main corollary.**  A file declaring a theorem of type `False`
in the shape `jsonWithTheoremFalse` describes is rejected. -/
theorem no_False_declaration (V : Type w) [SetTheory V] (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified ds) = .error e :=
  sorry

end ConLeche
