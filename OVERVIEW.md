# ConLeche: an overview of the proof

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to [`README.md`](./README.md), which is
> human-written and states the main theorem and its corollary in the
> maintainer's own words, with its own links into the source.
> This one is a guided tour of the verification, from the binary that
> runs to the set-theoretic assumption it rests on, with links into the
> source on `master`.

## 0. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format, or a
module with its import closure from its `.olean` files, and prints one
verdict line:

```
con-leche [--verified|--trusted] [--jobs=<n>] [--max-nat-size=<bytes>]
          [--progress[=<stride>]] [--] FILE.ndjson
con-leche [flags] --olean --search-path=DIR[:DIR...] [--constant=NAME]... [--] MODULE...
con-leche [--jobs=<n>] --check-graph --search-path=DIR[:DIR...] [--] MODULE...
con-leche [flags] --olean --module --search-path=DIR[:DIR...] [--] MODULE
con-leche [flags] --olean --modular --search-path=DIR[:DIR...] [--] MODULE
con-leche [flags] --olean --schedule[-OPT=V]... --search-path=DIR[:DIR...] [--] MODULE
con-leche --help
```

That is every flag the binary takes. `--verified` is the default and
the mode the theorem is about; `--trusted` runs the same checker bodies
with the certification-only work switched off, is faster, and is
outside the theorem; `--jobs=<n>` sets the check phase's worker count
(below); `--max-nat-size=<bytes>` sets the largest `Nat` numeral the
checker takes in or computes, as the official kernel's
`LEAN_NAT_MAX_SIZE` does (default 128 MiB; a larger numeral rejects the
declaration, §6);
`--progress[=<stride>]` turns on a heartbeat on stderr
(below); `--olean` takes module names (`Init`, `Mathlib`) in place of the
file, looked up in the directories `--search-path` lists, and checks every constant of their
import closure, or with `--constant` only the named constants and what they mention (§2, the
`.olean` reader); `--olean --module` checks one module's own declarations alone, against the
records of the modules it loads that they read (§2, one module alone); `--olean --modular` checks
every module of the root's closure so, in one process, and `--olean --schedule` by one
`--module` process per module (§2, every module of a closure; `--modular` is of limited use: every
module redoes its own reach, so on Mathlib it took 3.0 times the merged run's instructions at a
lower peak (2.4 against 3.1 GiB), and the merged run, or the scheduler for isolation and memory
limits, is the better choice); `--check-graph` reads only
the headers of those modules' import closure and checks that its import graph is acyclic and
every import is on the search path (§2, the import graph); `--` ends the options, every argument after it being a
file or a module, whatever it is called; `--help` before any `--` prints a summary of all this
and exits 0
([`helpText` in `ConLeche/Driver/Cli.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L130)).
Any other option is a usage error: the run reports it, points at
`--help` and exits 3 without reading its input, so a verdict's
provenance can be read off the invocation.

A name's component in `«»` is taken literally
(`Challenge.«12.34».«5»`); in a `--constant` name, an unescaped component of
digits is a number (`_private.M.0.foo`). A `--constant` the closure does not hold is
an error (exit 3). `--search-path` takes the directories as `LEAN_PATH` lists them
and may be repeated. A module is looked up as Lean does: in the directory
holding its root (the first component of its name) as a directory `Root/`
or a file `Root.olean`; each root is looked up once per run in every
directory, and a root in two directories is an error (exit 3), a directory
counted once however often it is listed or reached through a symbolic link.
There its files are `M.olean` and, for a module of the module system, exactly
`M.olean.server` and `M.olean.private` beside it; another directory is never
looked at for them. A root on no directory, a module missing in its root's
directory, and a missing or stray part are errors (exit 3).

The exit code follows the lean kernel arena convention
([the exit-code mapping in `ConLeche/Driver/CheckMain.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckMain.lean#L37)):

| exit | verdict | meaning |
|---|---|---|
| 0 | `accepted N declarations` | every declaration checked; `N` counts the stream's declaration records |
| 1 | `rejected` | a declaration is invalid: a type error, a bad inductive block, a proof of the wrong statement |
| 2 | `declined` | the checker positively detected a feature it does not support, and says which; nothing is claimed about the stream |
| 3 | error | bad usage, malformed input, or an internal failure of unclear cause |

The distinction between 1 and 2 is deliberate: a reject is a verdict
about the input, a decline is a statement about the checker. A decline
is never used for "something unexpectedly went wrong"; that is exit 3,
which verification is meant to make rare. Only exit 0 carries the
theorem's guarantee. The count `N` is a property of the input: a prelude
declaration counts only where the input has its own record of it. The official kernel's `Accepted N
declarations` counts an inductive record as its members, so it is larger;
`scripts/stream-census.py` derives both numbers from a stream. An internal panic is not a verdict either, and
does not end with one of these codes: the binary sets
`LEAN_ABORT_ON_PANIC` and `LEAN_ABORT_ON_NONLINEAR` for itself at
start-up, so every panic — the runtime's `INTERNAL PANIC: out of
memory`, a Lean-level `panic!` or out-of-bounds `get!`, and a copy of
one of the arrays the checker marks linear (the parse's tables, which
must be updated in place) — prints
its message on stderr and calls `abort()`: the process dies of
`SIGABRT`, which a shell reports as exit status 134. An abort also
writes a core dump where the shell's limit allows one, and at Mathlib
scale that is gigabytes, so `tests/arena.sh` and
`scripts/perf-tables.sh` run with `ulimit -c 0`, as should a large run
started by hand.

A run has two phases. The parse ends with the index of the whole
stream: what each record declares, read off the record (a single pass,
without threads). The check phase checks every record against the
index's view of the records before it (see §2), from a fresh memo state.
The flag `--jobs=<n>` runs the parse and the check phase on `n` worker
threads; without it there is one worker per hardware thread. At
`--jobs=1` the check phase runs on one worker thread.
The check phase always runs on worker threads, never on the main
thread: its per-record memo state is allocated out of the running
thread's heap, and the main thread's heap is the one the parse has just
fragmented, which at Mathlib scale costs the
single-worker run a factor of two in wall time at the same
instruction count. Each worker thread reserves about 1 GiB of address space (its stack
reservation; the resident set grows by about 25 MB per worker), so a
run under an address-space limit (`ulimit -v`) must lower the count
to what the limit affords — about ten workers under 16 GB. At every
worker count the records and the index are marked persistent once
before the check phase, which removes the atomic reference counting the
workers would otherwise pay on them and is worth 18–32 % of wall time on
the pool, growing with the worker count, and 3.5 % at one worker. The
verdict, and the declaration a rejection names, are the same at every
`n`: the results are walked in record order, so the first failing
record in fold order is the one reported. The flag
`--progress[=N|P%|Ss]` prints a heartbeat on stderr, a line every `N` declarations, per `P` percent
of a phase, or at the first declaration done once `S` seconds have passed (so a long single check,
or a step with no declarations, says nothing until it ends): `check <done> (<percent>%)` after a
completed check, with its name at `--progress=1`, each phase saying when it starts (`reading`,
`checking`), bracketed by `parse done`, `check done` and a `done:` summary with the two phase
durations and the worker count (bare, every declaration); on more than one worker, each `check`
line ends with the number of busy workers and the oldest record one of them is on, with its age,
only at `--progress=1` or once it has run for 10 s. With `--olean` the parse is preceded by
`read:` lines, each with the time and the resident set: the import closure traced, the modules
loading, at the pace asked for (a count of declarations counts their constants), then the merge, the blocks and the emission, so that a run
that does not get through the read says how far it got and at what size.
With or without the flag, every run closes its stderr with a few
`stats:` lines: the phase times (the index's within the parse's); for the
check phase the wall time,
the worker count, the workers' busy time and utilisation (busy ÷
(workers × wall)) and, on more than one worker, the tail (from the
last record's start to the end of the phase, how many workers were
still busy then and their busy time inside it); the five slowest
checks with their fold positions; and the peak resident
set. They cost two clock reads per record, kept per worker and merged
when the pool ends, and change neither stdout nor the exit code. The heartbeat
is printed between the steps of the one driver, which returns the
proof that `checkDecls` — the function
the theorem is about — accepts (see §2), so a run with the flag is
covered exactly as a run without it, and so is a run on the pool.

Every name and raw string these messages print comes from the input,
so it is printed through one rendering
([`Name.render` in `ConLeche/Kernel/Name.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Name.lean#L236)).
A name component that is an identifier prints bare, as in Lean
(`Nat.add_comm`, `α₁.ℕ`); any other is wrapped in `«…»` (`x.«3»`,
`«a.b»`), with `\` doubled and with `»` and every control, format and
separator character other than the ASCII space (ESC, newline, the bidi
overrides, the zero-width characters) written as `\u{XXXX}`:
`«evil\u{001B}[31m\u{000A}::error::x»`. Numeric components print as
decimals and the anonymous name as `[anonymous]`. A raw string field
(a `safety` value, a quotient kind) prints the same way between
`"`…`"`, and a rendering longer than 512 characters ends in
`…[N more characters]`. No input can move the cursor, recolour the
terminal or start a line of the output, such as a GitHub Actions
`::error::` command.

## 1. What is proved

The statement is two theorems: one about the declaration fold
`checkDecls`, the function whose result the `con-leche` binary's
driver returns for a parsed export stream, and one about the chunks
the binary reads. The main theorem,
[`model_exists` in `ConLeche/MainTheorem.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L108-L111):

> For every model `V` of the `SetTheory` interface, every
> `Nat.div`/`Nat.mod` pin list `pins`, every maximum `Nat` size `maxNatSize`
> and every list of declarations `ds`: if `checkDecls`, in the default `--verified` mode, accepts `ds`
> with the environment `env`, then `env` has a model in `V` — one set
> per stored constant and universe assignment under which every stored
> constant is a member of what its type denotes, whatever the built-in
> `False` denotes is the empty set, and whatever the built-in `Eq`
> denotes is set equality.

`pins` is the fold's second argument: the list of pinned
`Nat.div`/`Nat.mod` variants its install gate tries (the bullet on
well-founded operations below says what those are). It is the one
large constant the checker carries, and the theorem quantifies over
it, so consistency does not depend on it at all — the theorem holds at
the empty list too, under which a stream declaring `Nat.div` simply
declines. The shipped binary runs the fold at `natOpPinSets`, the
variants this toolchain committed. `maxNatSize`, the third argument, is the
largest `Nat` numeral in bytes the fold takes in or computes (§6); a
numeral above it only ever makes the fold reject, so the theorem holds
at every `maxNatSize`.

What a term denotes, and what a model is, are one short module a
reader can take in at one sitting: the relation
[`Denotes` in `ConLeche/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L123-L124),
one rule per syntax form on the checker's own terms — a bound variable
reads its environment, `Sort u` the types of a level of the universe
chain, a constant its set, an application the function's graph, a
`let` its body at its value (its type is not read), a
`∀` the dependent function space, or a truth value where its body
denotes a truth value at every value of its domain, a `λ` the graph of
its body, or the proof point where its body denotes the proof point at
every value of its domain — and the structure
[`Model` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L248-L268).
So every theorem the stream proves is true in the model.
Definitional equalities need no clause of their own, because the field
`eq_equality` covers them all: a definition's unfolding or an iota
rule, stated as a theorem proved by `rfl`, is a stored constant whose
type is `a = b`, `mem` puts that constant inside what the type
denotes, `eq_equality` says that set is the truth value of `⟦a⟧ = ⟦b⟧`,
and a truth value with a member is `{pt}`. So the two sides of every
accepted equation denote the same set.

The main corollary,
[`no_False_declaration` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L122-L129):

> … if the chunks are a `jsonWithTheoremFalse` file — a name entry for
> `False`, an expression entry for the constant `False`, a name entry
> for the theorem's own name, and a theorem record whose type is that
> expression, four lines in the exporter's own shapes, in that order,
> with anything at all before, between and after them — then the chain
> "the built-in prelude parses; the chunks parse; `checkDecls` accepts
> the parsed records prepared with the prelude" returns an error.

The hypothesis is the file, and the conclusion is the binary's accept
path erroring: the three pure functions the driver's phases compute —
`Frontend.builtinPreludeE`, `Frontend.parseChunks chunks`,
`checkDecls .verified` over `Frontend.preparePrelude` — written as one
`do` block, and `∃ e, … = .error e` says it returns an error, with no
claim about which of the three produced it. There is one conversion
nowhere in it: the
three steps fail in the same type, the checker's own `CheckError`
paired with the position of the failure, which is the input's line
number in the frontend's half and the record's position in the fold's.
The reasons are the driver's diagnostics, and its exit code is that
`CheckError`'s whichever step produced it. The driver runs the same
three steps with IO between
them — the streaming read loop is `parseChunks` with the reads
interleaved, the preparation is `preparePrelude` plus its receipts,
and the check driver returns its environment with the evidence that
`checkDecls` returns it — and prints its success line from nothing
else. This is the form of the statement a reader can check without
knowing what an `Env`, or even a declaration record, is: it speaks
only of the bytes handed to the binary. The predicate is a whole-file
template over the chunks' concatenation
([`jsonWithTheoremFalse` in `ConLeche/Accepts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Accepts.lean#L62-L72)),
one interpolated Lean string whose five parts are arbitrary — the name
says so: it is ONE way of putting a theorem of type `False` into a JSON
file, not every proof of `False` a file might hold. There is no side
condition: the chunks may be cut anywhere, empty pieces included, and
an input the machine word cannot address is refused by the parser
before any of it is read, which is an error like any other.

The main corollary is lifted to the driver, over `runArgs`, in the model
of its IO (§2), at the fixed arguments `-- <file>`: no flag, so the
default mode, which is the verified one, and the default worker count;
nothing is said about `--help` or the other flags. On a snapshot where
the file's bytes are a `jsonWithTheoremFalse` file, no outcome of
`runArgs` is an exit 0
([theorem `main_no_False` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L158-L160)).
This is a theorem about the outcomes of `runArgs` in the model; that a
run of the binary that exits 0 is one of those outcomes is assumed, not
proved, and §2 states what the assumption is.

The corollary rests on a statement at the stream — the fold's input —
proved beside the fold
([`no_False_theorem_accepted` in `ConLeche/Verify/Cached/StreamThm.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamThm.lean#L103-L106)):

> … if any record of `ds` declares a theorem whose declared type is
> `False`, then `checkDecls` accepts `ds` with no environment at all.
> (`ds` is the array of records the parse returns and the fold folds;
> the proofs read it as a list, which costs nothing at run time.)

That follows from the theorem in a handful of lines, through the
environment in between. A theorem record is installed by statement,
under its own name, with its declared type; and every later step
of the fold only ever extends the list of stored constants — so an
accepted stream that declared such a theorem would leave a constant of
type `False` among the constants of the environment the fold returns.
It cannot: the model the theorem provides puts every stored constant
inside what its type denotes, and what the built-in `False` denotes is
the empty set, which has no members.

What the corollary adds to that is the parser and the preparation. The
byte recogniser never reads past a newline
(`ConLeche/Verify/Frontend/Local.lean`), so every line of the file is
read as a line whatever surrounds it; a stream index is bound once (a
rebinding is a parse error), so the entry a template line bound is the
entry the theorem line reads; the record list only grows; the
streaming parse of any cut of the file is the wholesale parse of the
whole
([`parseChunks_ok_parseBytes` in `ConLeche/Verify/Frontend/Chunks.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Chunks.lean#L363),
with the streaming reader's running byte count as the same guard the
wholesale parse applies up front); and the template's lines scan to
exactly the records the fold then forbids
([`parseChunks_jsonWithTheoremFalse` in `ConLeche/Verify/Frontend/FileFalse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/FileFalse.lean#L174)).
The preparation puts the built-in prelude's records first and moves
the definitions a pinned `Nat` operation's certificates are spelled
over ahead of it (§6); it is a permutation of the
parsed records plus the prelude's, so the record is still there
([`mem_preparePrelude` in `ConLeche/Verify/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L190)).

"Installed under its own name, with its declared type" is a claim in
its own right, and it is proved in general:
[`checkDecls_consts` in `ConLeche/Model/StreamConsts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L220-L225)
says that whenever `checkDecls` accepts `ds`, every record of `ds` that
declares a constant — a definition, a theorem, an opaque, or an axiom
that is neither `sorryAx`, the axiom record that installs nothing, nor
`Quot.sound`, which stores its slot's pin
([`Declaration.Declares` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L89-L95))
— leaves a constant of that very name in the returned environment, with
the record's own level parameters and the record's own type, `let`s
included.

The members of an inductive block are deliberately outside that claim,
and the module says why: a type former's telescope may be stored
reduced to weak head normal form, which is a definitional equality, not a
syntactic one, so the claim would be false of it. The
constructors are stored as declared, but they are installed with their
block and are left out with it.

`checkDecls`
([function `checkDecls` in `ConLeche/Cached/Decls.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L89-L90))
checks every declaration of `ds` in order, each against the environment
of the declarations before it, and pushes what the declaration says.
The driver runs the same checks independently, against views of an index
built from the records, and returns a proof that `checkDecls`
accepts, so the success line is printed from an accept of
`checkDecls` and from nothing else, whatever the loops printed on the
way.

**Modular checking** has its own theorem, about a development of
modules rather than one stream,
[`modular_model_exists` in `ConLeche/MainTheorem.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L199-L206):
if every module passes the local checks of `ConLeche/Modular.lean`
(its interface presents its own records; as an importer, its context
is made of presented records read as their homes read them, and its
own records are accepted from that context by the fold's step), then
the modules' own environments have a compatible family of models: every
module gives each name of its context the value the module it reads it
from gives it, and every theorem the point. The local checks ask that
every copy of a name a module's context reads agree with the one it
reads: the same record (from the same module, perhaps through other
modules), or two proofs of one statement: a statement an earlier module
stores as a theorem, or else one the importer infers to be a proposition
over the part of its context below the name; no module records anything
about its names for others.
Hence no module's own environment stores a constant
of type `False` (`modular_no_False`). An
exit 0 of the binary at one module (`--olean --module`) establishes that
module's part of the local checks (§2, one module alone), and the runs at
every module of a closure compose into a development every module of
which passes them (`Run.localOk`, `ConLeche/Verify/Driver/Routes.lean`):
each module is the closure's module of its rank, its context its worker's,
a name read from the home of the record storing it, and every read the
capture check passed agrees by the branch that passed it. So
`main_modular_no_False` holds of the files: if the private view of a module
of the headers' import closure of `root` holds a theorem of type `False`
and every module of that closure has an exit 0 of `--olean --module` on the
same snapshot, no run of `--check-graph -- <root>` exits 0; and no run of
`--olean --modular -- <root>` exits 0 (`main_modular_one_no_False`).

`False` is not read off the stream: the checker installs it from a
built-in pin, and a stream that declares `False` or `False.rec`
differently is rejected. The theorems use exactly Lean's three standard
axioms, `propext`, `Classical.choice` and `Quot.sound`, which the
[axiom pin in `tests/ConLecheTests/Axioms.lean`](https://github.com/leanprover/con-leche/blob/master/tests/ConLecheTests/Axioms.lean#L111-L115)
checks with `#print axioms` guards under `lake test`.

Everything below explains how those theorems are reached.

## 2. From the binary to the theorem

Read from the outside in:

1. **The driver** (`ConLeche/Driver/Cli.lean`, `Main.lean`). `main` is
   plumbing, a few lines that are read and not proved: it sets the
   runtime's abort variables, runs the generic `runArgs` at `IO`,
   flushes the output and exits with the code `runArgs` returned, or
   with 3 if the flush fails.
   `runArgs` reads the arguments into a request (a
   stream), runs the request's driver
   ([function `runReq` in `ConLeche/Driver/Dispatch.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Dispatch.lean#L49-L50))
   and turns any `IO` error into exit 3.
   All of it — the argument parse, the prelude, the input, the
   preparation, the fold, the verdict and the exit code — is written against
   a type class of the file operations the checker needs — whether a
   path names something, whether it is a directory, its real path, a file's bytes, a file opened
   and read in order, and its size — and one escape, `liftIO`, which runs
   an `IO` action
   ([class `CheckerIO` in `ConLeche/Frontend/CheckerIO.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L141)).
   Everything else the binary does goes through the escape, spelled at
   every call: the output, the clock, the persistent mark,
   and every thread — the rounds of the parallel parse and the fold's
   two phases with their pools. Where the driver needs a fact about
   what such an action returns, the result's type carries it: the
   fold's two phases return the environment with the proof that the
   fold `checkDecls` returns it, a window of the rounds its next state
   with the proof that it advances the serial parse. The binary runs
   the code at `IO`, each file operation the runtime's own call (a
   file is read through the runtime's file handle) and the escape the
   identity. The proofs reason about it at a model: an action is the
   set of its possible outcomes on a snapshot of the files, from the
   files open before it — a value or an exception, and the files open
   after it, each with the position of its next read; a file
   operation's outcome is determined by the snapshot and the open files,
   and the escape may have every outcome and leaves the open files as
   they were
   ([type `ModelIO` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L310)).
   The exit code is computed by the generic code and returned outside
   the escape, whose outcomes would otherwise allow any code. On every
   snapshot, every outcome of `runArgs` at the arguments `-- <file>` that
   is an exit 0 establishes the file's chain to the fold's accept
   ([theorem `runArgs_accept` in `ConLeche/Verify/Driver/Main.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Driver/Main.lean#L250-L254)),
   whose corollary is `main_no_False` in
   `ConLeche/MainTheorem.lean` (§1). That a run of the binary that
   exits 0 is one of those outcomes is assumed, not proved, and the class's file states
   the assumption: the binary's file operations give the model's
   answers on one snapshot of the files, a file handle's reads
   included; the
   actions passed to the escape do not change what those operations
   see and do not end the process with exit code 0 (an abnormal or
   nonzero end, such as a panic's abort, is harmless: that run has no
   exit 0 to explain); and Lean's compiler
   and runtime run the code as written. Then
   the generic code is the same at both instances, every file operation
   answers as the model's, and every escape answers some value or
   exception, which the model allows; so a run that exits 0 has one of
   the model's outcomes, with that code. The run parses the stream
   ([function `parseStreamG` in `ConLeche/Driver/StreamParse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/StreamParse.lean#L118-L119))
   and runs the fold's two phases as two loops. The byte recogniser that reads each line of the
   stream is proved equal to a naive reference over `List UInt8`
   ([theorem `scanLineSpec_eq_scanLineFwd` in `ConLeche/Frontend/Scan/Equiv.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Scan/Equiv.lean#L1002)):
   the driver calls the reference, and the compiler runs the fast
   recogniser on the strength of that equality. The stream is read by
   two folds written over the class's file handle, one over the
   file's reads in order and one over its windows of whole lines; in the
   model they are proved to be the folds over the snapshot's bytes cut
   as the reads cut them. At one worker the parse feeds every read of
   the stream to the pure streaming parse's step over a chunk
   ([function `chunkStep` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/ExportC.lean#L627)),
   on one thread
   ([function `parseFileS` in `ConLeche/Frontend/Stream.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Stream.lean#L310-L312)).
   With more workers the parse runs on as many owner threads and takes
   a window of chunks at a time, one chunk of whole lines per owner,
   the next window read before the current one is computed
   ([function `windowStep` in `ConLeche/Driver/OwnerParse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/OwnerParse.lean#L492-L494)):
   the owner scans its chunk once into syntax records that never leave
   its thread and applies its lines, deferring a line that reads an
   entry of another chunk of the window to a later round, until nothing
   is deferred; after each round the owners publish the entries they
   built, and only raw bytes and finished entries cross between
   threads. The chunks the proof speaks of are the bytes the main
   thread read: an owner's result is taken only for the very bytes it
   was sent. The window's tables then join the finished tables, and each
   owner builds its chunk's records. The finished tables keep their
   entries in the order they were bound, with the runs of consecutive
   indices that say which entry an index has (one run on lean4export's
   output), so they take the memory of their entries whatever gaps an
   exporter leaves between indices. Nothing is checked again: every
   entry the rounds store is good for the index it is stored at — the
   value the builder of the line binding that index yields over lookups
   that answered good entries only, at indices the serial parse may read
   at that line
   ([inductive `Good` in `ConLeche/Verify/Frontend/Good.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Good.lean#L528)),
   which is proved of the round functions once. Tables that hold good
   entries, and one for every line of a window whose lines bind each
   table in increasing order and stand where they may (the `meta`
   header exactly as the file's first line, no blank line), make every
   line of the window right
   ([theorem `allOK_of_good` in `ConLeche/Verify/Frontend/Good.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Good.lean#L712-L716)),
   so a window whose deferred lines are all done is one more stretch of
   the serial parse
   ([theorem `GOK.window` in `ConLeche/Verify/Frontend/Rounds.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Rounds.lean#L1740-L1749)).
   A window whose chunks or rounds meet anything unusual — an index
   below its table's counter, a line out of place, a line the serial
   parse fails at — is handed to the serial parse from the state the
   chunks before reached, which gives the serial verdict at the serial
   line; so are the bytes after the stream's last newline, a final line
   without one. Each
   window's result carries the proof that it advances the serial parse
   over the window's chunks, so that in the model, whatever the owner
   threads answered, every outcome that is an exit 0 is one where the
   file's bytes in the snapshot, as one chunk, parse to records the fold
   accepts
   ([theorem `checkMainG_ndjson_accept` in `ConLeche/Driver/CheckMain.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckMain.lean#L414-L419)):
   the hypothesis of the main corollary about the file itself, read at
   the binary under the assumptions of the class's file.
   What the parser makes of a record
   — index resolution, the smart constructors — is the
   semantic layer the main corollary's line lemmas are about. The fold
   checks every record, each from a fresh memo state, by its step
   ([function `declStep` in `ConLeche/Cached/Decls.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L52-L53))
   and pushes what the record says: a definition or opaque as declared, a
   theorem by its statement alone (the stored constant carrying
   no value: a theorem is opaque to reduction), an axiom or a
   pinned `Nat` operation or `reduce*` opaque as its own constant, a
   quotient record as its slot's pin, and every inductive block, the
   pinned basis blocks among them, as the block says: every constant and table read off the block's
   records, nothing generated
   ([function `declConstants` in `ConLeche/Kernel/Install.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L84-L96)).
   What a check pushes is what its record says, at any index and any mode
   ([theorem `checkDeclC_pushes` in `ConLeche/Verify/Cached/DeclPushes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/DeclPushes.lean#L698-L699)).

   The driver runs those checks in any order. Before any of them it builds
   one index of the whole stream from the records alone
   ([function `buildIndex` in `ConLeche/Cached/StreamIndex.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/StreamIndex.lean#L65)):
   a name's first entry with its counter, a table with its record's
   position. A record's *job* is its check at the index's view of its
   position
   ([function `recordJob` in `ConLeche/Cached/StreamIndex.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/StreamIndex.lean#L96-L97)):
   an empty index over that frozen layer, whose lookups hide everything
   from the record on. A name declared twice keeps its first entry, so the
   later record's job finds it and fails with `duplicate declaration`, at
   that record. Every check reads its index through the lookups alone (the
   constants' and the projection tables'), so at two indices with the same
   lookups it fails alike or pushes the same constants
   ([theorem `checkDeclStepC_twin` in `ConLeche/Verify/Cached/ViewCongr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/ViewCongr.lean#L1340-L1344)).
   The view of a position answers as the fold's index there as long as the
   names so far are distinct, which every passing job before it ensures,
   so every job passing is an accept of the fold
   ([theorem `checkDecls_of_jobs` in `ConLeche/Verify/Cached/StreamIndex.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamIndex.lean#L525-L527)).
   A later job may read an earlier constant before that constant's job has
   run: a declaration may read a pinned operation, and fire its literal
   fast path, before the operation's certificates have been checked. The
   accept needs every job, and a rejection is reported in fold order, so
   the operation's failure, earlier in the fold, is the verdict. A block
   the installer cannot read pushes nothing, and its job refuses it; a
   block the checks reject may read as anything, and never reaches an
   accepted environment.

   The records and the index, read-only from there on, are marked
   persistent once
   ([function `Jobs.build` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L66)),
   so that no check pays reference counting on them, and the jobs run on
   worker threads, a pool of them at every count, one included
   ([function `checkPool` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L214-L216))
   claims jobs one at a time off a shared counter. A job is its own
   evidence: its pass, or its error tagged with the record's position. The
   results, merged by position, are walked in position order
   ([function `collect` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L149-L150))
   — the walk stops at the first failing job in fold order, so the
   pool's verdict is the sequential walk's. Which thread computed a check is
   irrelevant to what it proves, and so is whether the mark happened:
   it is the identity on the value and its result is discarded. The heartbeat is
   printed between the steps and touches neither type. The driver
   ([function `checkDeclsIO` in `ConLeche/Driver/Run.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Run.lean#L85-L88))
   returns the proof that `checkDecls` accepts.
2. **The fold's run**
   ([inductive `DeclsRun` in `ConLeche/Cached/Decls.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L61-L62))
   is stated over the executable steps: a chain of accepting `declStep`s.
   An accept of `checkDecls` is exactly such a run from the empty index
   ([theorem `checkDecls_run` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L130-L132),
   [theorem `checkDecls_of_run` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L144-L146)),
   which is how the theorem about the fold is read off the argument
   of step 3.
3. **The cached checker** (`ConLeche/Cached/*`) is the implementation
   that ships: the same terms with a packed hash on every node, memo
   tables for reduction, inference and definitional equality keyed by
   those hashes, and the direct parser's record type. Nothing is
   interned; the hash is what makes a term a usable memo key. A
   `Nat` literal's hash reads all its bits, so literals that agree in
   their low 64 bits do not share a bucket. It is
   related to the pure checker by a one-directional simulation:
   whatever the cached checker accepts, the pure checker accepts. For
   the fold the simulation is applied step by step along the run, which
   carries the model to the final environment
   ([theorem `declsRun_model` in `ConLeche/Model/DeclsRun.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/DeclsRun.lean#L46-L48)),
   and the statement about the fold
   ([theorem `no_proof_of_False_cached` in `ConLeche/Verify/Cached/MainC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L55-L59))
   is that model read through `checkDecls_run`
   ([theorem `checkDecls_sound` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L34-L37)).
   The same run carries the environment's syntactic well-formedness
   (`EnvWF`: stored constants closed, their level parameters declared,
   the constants they mention stored) without the model, so that fact
   about what the fold accepts needs no set theory
   ([theorem `checkDecls_envWF` in `ConLeche/Semantics/DeclWF.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/DeclWF.lean#L339-L340)).
   A job's check at a view is the fold's step because the cached core
   reads its environment through the lookups alone
   ([theorem `knotI_congr` in `ConLeche/Verify/Cached/KnotCongr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/KnotCongr.lean#L706-L709)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` (and inference at the infer-only grade) are defined by one mutual
   recursion on a fuel parameter
   ([the entry points in `ConLeche/Kernel/TypeChecker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TypeChecker.lean#L29-L54));
   on exhaustion every operation throws
   ([the fuel recursion's base case in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1899-L1904)).
   Its declaration fold is what the model tier proves things about
   ([theorem `no_proof_of_False_pure` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L565-L572)).
5. **The model tier** (`ConLeche/Model/*`, the set model of the checker)
   shows that each declaration step preserves an invariant on the
   environment
   ([theorem `declStep_preserves` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L484)),
   and that the invariant forbids a constant of type `False`, whose
   pinned denotation is the empty set
   ([theorem `no_constant_of_False` in `ConLeche/Model/Capstone.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Capstone.lean#L137-L143)).
   The main theorem's model is the invariant's own, read through the
   statement's relation
   ([definition `Model.ofEnvModelM` in `ConLeche/Model/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L340-L341)).
6. **The semantics** (`ConLeche/Semantics/*`) defines the denotation of
   terms in a model of the **set-theory interface**
   (`ConLeche/SetTheory/*`), and the **pure set constructions**
   (`ConLeche/SetModel/*`) build the sets inductive types denote.

The layering is enforced by a gate
([the import fence `tests/layering.sh`](https://github.com/leanprover/con-leche/blob/master/tests/layering.sh#L1-L3)):
implementation modules never import theory modules, so the binary
cannot depend on a proof.

### The `.olean` reader

`--olean` ends in the same records as the stream parse, so everything
after it is the same checker: the import closure of the named modules is
read, merged as Lean's own import merges it, emitted as `lean4export` emits a constant and
what it mentions, from every constant of the closure or the ones `--constant` names, and
handed to the same record builder
(`ConLeche/Frontend/Olean/Records.lean`). `tests/olean-compare.sh`
compares the two readers record for record on `Init`. Nothing in a file is
trusted: every object the imports and constants reach is decoded and
validated when it is read, a theorem's value in that theorem's check (the environment
extensions' entries are not read), an `.olean` of another
format version is declined, and the toolchain a file's header names is not
looked at.

A module of the module system has three files, each holding the module at one
level (`OLeanLevel`): `.exported`, `.server` and `.private`. Later files point into
earlier ones, so a view reads the files up to its own, and an importer needs
`M.olean` alone. `--olean` reads the private view of each module, as Lean's own import
does outside the module system and as `lean4export` does, so it does not compare a
module's files with each other.

`decodeModuleSpec` is the specification of a view, a plain recursion over the file's
objects: its name table lists the constants' names, each once (`constNamesOk`), every
constant reads, and its imports are those at the start of `M.olean`. It says what a
valid view is and is not executable. `parseView` reads one view and `parseAllViews`
reads all three, each object once; both are proved equal to it on every input
(`parseView_eq_spec`, `parseAllViews_eq`), so each succeeds exactly where the
specification does. `checkViews` is a module's home's check of its three parts against
each other, over the load of its private view: the server and private parts are of the
module system, the other parts' imports and name tables are what they should be, and every
exported and server constant is the private constant of its name or that constant with its
value hidden (the same object decided by position, a hidden value by the statement, so no
theorem's value is read). A mismatch is a malformed file at its home, a reject.

**A theorem's value stays in the file until its check.** Most of what a module stores is
the values of its theorems (on Mathlib's closure, 93 of 138 million expression objects are
reached from nothing else), and nothing but a theorem's own check reads one: a theorem is
stored by its statement, the merge compares statements, and the index never looks at the
value. So the load
([function `loadAt` in `ConLeche/Frontend/Olean/Lazy.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Olean/Lazy.lean#L296))
reads everything of a module except those values, and a theorem's record holds a reference to
where its value is stored. The check reads it
([function `readValue` in `ConLeche/Frontend/Olean/Records.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Olean/Records.lean#L154-L155)),
with a memo of its own, and drops it at the end. A worker keeps the region of the module it
read last, and the checks of one module are next to each other in the records. Two things the
load keeps for this. What each constant mentions is read off the file without building
anything, which is what the emission's order needs of a value. And the *frontier* is what
remains of the load's memo: the objects it read that a value reaches directly (6 million of
48 million on Mathlib's closure), so that a value read later shares those, and all
that lies below them, with the environment; which objects it holds is a matter of speed
alone, as only the specification's values are ever put in it. `frontierExpr_eq` says a read
over such a frontier is the specification, on every input.

The other reads take less of a view: per stored constant its name, kind and position
(`readNamePositions`), one constant (`readEntry`), several with one memo (`readEntries`,
each of them `readEntry`'s on every input), the statements of a few (`readStmts`), their
kinds without expressions (`readKinds`) and the imports off the start of the file (`importsPre`, which reads only a prefix).
They are projections of the full view: where it parses, the read succeeds and returns
its part (`ConLeche/Verify/Frontend/Olean/View.lean`). The converse does not hold, on
purpose: a read looks only at what it needs. In the IO model a home's read of all three
views settles the others on the same snapshot: each view's read is determined and is
the home's (`readView_of_all`), and a view read settles the imports off the file's start
(`moduleImports_of_view`; `ConLeche/Verify/Frontend/Olean/Files.lean`). The interface
is listed in the header of `ConLeche/Frontend/Olean.lean`, the one module of the tree the
rest of the checker imports.

**What a module's own environment loads.** Checking one module against what Lean loads for
it starts from reads of the headers and the name tables alone
(`ConLeche/Frontend/Olean/Levels.lean`, `ConLeche/Frontend/Olean/Index.lean`).
`headerFixpoint` is Lean's `importModulesCore` read off the headers: every module a module's
header loads, at its exported part or (under `import all`, or for a root outside the module
system) its private part, in Lean's module order but for the modules Lean meets first through
a `meta` import for their IR only; `pubClosures` is each loaded module's public-import closure,
which is loaded wherever that module is. `workerReads` then indexes the name tables of the loaded
parts and makes the two checks Lean's import and kernel make over that whole environment, each a
reject: two loaded copies of one name must merge as `finalizeImport` merges them (`subsumesF`,
Lean's `subsumesInfo`; the statements and kinds of the names held twice are read and kept), and
no constant of the module's own private part bears a loaded name. On every fixture and on the
two Mathlib modules measured, the loaded modules, their parts and the number of loaded names are
those of Lean's own `importModules`. `groupRecord` builds one inductive group's record from a
part's constants as the emission does, validated for that group as `blocksOk` validates a merged
block (`groupRecord_from`: the record is made of stored constants of the group's kinds).

**A module's context** (`ConLeche/Driver/Reach.lean`). `reach` builds the records a module's own
records are checked against, from the names they read (their theorems' values included), by a
worklist over the name index. A name the index holds is read at its copy's part, with one memo
per part (`entryWith`, `stmtWith`, `ConLeche/Frontend/Olean/Present.lean`), and presented as a
record: a definition the part holds with its value keeps it, every other definition, theorem
and opaque constant is the axiom of its statement (an imported theorem's value and a hidden
definition's are never read), an inductive group is presented whole, always read from its
home's private part (an exported part lists a group's recursors sorted by name and need not hold
them all), and a compiler-trust name (`Lean.reduceBool`, `Lean.reduceNat`) is presented as its
statement only where its home declares an opaque constant or an axiom there. What a record reads
(`recordReads`: its constants' and tables' names, `RecordScoped`'s) is pushed. A record of home `h` means by a name it reads the copy `h`'s export
holds: `h`'s own, or the copy of a module of `h`'s public-import closure that exports it. A name neither holds is
dangling in `h`'s export and is completed where the export was made: located in `h`'s view by
headers and name tables (`h`'s own private part, then the parts its header fixpoint loads, the
first copy) and read from its module's private part as its statement, its own reads dangling or
not relative to that module; a name located nowhere is a reject. Exports are completed on
demand: for the names the context's records read, and for every copy of every clashing name the
context stores. The capture check is the same rule: a read passes when the context's copy is
the home's own or comes from a module of the home's public-import closure that exports it;
otherwise the copy the home's view locates (on Lean's output, a completed name or a clashing
copy) must agree with the context's: one module, or two proofs of one statement whose every
name is checked so too, as a read of that copy's module. Every name a group stores has no
importer copy or one of the group's home. Else the module is
rejected (name capture). A copy is a proof if it is a theorem,
its home declares a theorem at an exported axiom, or it is a definition, opaque constant or axiom
whose type is a proposition; copies of one statement of which one is a theorem need no inference
(a theorem's type is a proposition, and the copies read their one statement alike), and otherwise
the kernel infers the type to be a proposition over the part of the context below the name. Every
name two loaded modules hold must agree so, which merges every pair Lean's import merges. The context's records are sorted in
read order (`readOrder`: each after the records storing what it reads; records that read each
other are a reject, which Lean's output never has) and validated as untrusted input (`recordOk`:
every constant's and table's syntactic clauses, a constructor's stored family is the one its
type concludes in, and a recursor rule binds the rule prefix and the constructor's fields by the
λs the ι step peels).
At every accepting outcome of `reach` in the IO model, every context record is `RecordScoped` in
the prefix of the context ending with it, so every name it reads is a context record's, and the
context is `EnvWF` (`reach_ok`, `ConLeche/Verify/Driver/Reach.lean`); a copy read is the full parse's constant at
its position (`entryWith_of_view`, `stmtWith_of_view`). Every context record is read at a name
position its source's name table holds on the snapshot (`reach_from`,
`ConLeche/Verify/Driver/ReachFrom.lean`), and where the worker at the source accepted on the same
snapshot, it presents one of the source's own records (`worker_presented`,
`ConLeche/Verify/Driver/Groups.lean`; for an exported copy, by the source's check of its views,
`copy_behind`, `ConLeche/Verify/Driver/Provenance.lean`; for a group, read from the source's
private part, it is the record the source's emission built of the same constants in the same
order, `group_presents`), which gives `InterfaceOk` and `ImportOk.presented` from the workers
(`interfaceOk_of_workers`, `presented_of_worker`). On `Mathlib.GroupTheory.Coxeter.Basic`
the context is 2 874 constants (276 groups) from 151 of the 2 479 loaded modules, with no
completion; on `Mathlib.Analysis.SpecialFunctions.Gamma.Basic`, 7 973 constants (694 groups)
from 581 of 4 092 modules, with one completion.

**One module alone** (`ConLeche/Driver/Worker.lean`, `--olean --module`). The run first reads
the worker's tables (`workerTables`, `ConLeche/Driver/Tables.lean`): the module located on the
search path, its private view's files read and kept and their name positions read off them,
then its header fixpoint, each module it
loads located once and its header read there; every later read of a module's files is at the
location found there (`ModTables.reads`, whose reads refine the search path's,
`modTables_within`). `checkModuleG` reads
the module's home (`homeOf` over its private part's files, the tables' own: its private view
loaded, its three parts checked against each other, a mismatch a reject; the same files give the
region its theorems' values are read from, so the module's files are read once), the reads above, its own records (the loaded constants emitted from
every own constant, a name that is not the module's a context read; a pinned `Nat` operation's
ground hoisted ahead of it), the context (`reach`, its names checked distinct), and then checks
the own records alone over the index of the context's records followed by the own records
(`buildIndex (ctx ++ own)`), each at its view, a theorem's value read in its check. Every own
record's check passing is an accepting run of the own records from the context's environment
(`checkDecls_of_jobs_from`, `ConLeche/Verify/Cached/StreamIndex.lean`). In the IO model
(`ConLeche/Verify/Driver/Worker.lean`), every exit 0 is `WorkerAccepted` (`checkModuleG_accept`,
`runArgs_module_accept`): what the run read and checked, and that run, with the theorems' values
in place, which is `ImportOk.accepted`; with it `worker_local` gives the context's distinct
names, one source per record, its closure and `EnvWF`, and `worker_thm` that every theorem of the
module's private view by the specification is an own record with its value; `worker_local`
gives the read order too (`ImportOk.ordered`). What relates the module to the others (that the
copies its context reads agree with its sources') is not part of one run's theorem;
the presentations are two runs' (`worker_presented`, above). The reach's roots are, beside what the own records read, the constants of
the pins and certificates of every certified `Nat` operation the module declares that a loaded
module holds (`pinGround`): its install check reads them and no record does; each is stored in
the context at every exit 0 (`worker_ground`). Every fixture module Lean compiles is accepted but for the capture case,
which Lean accepts while proving `False`, and an axiom at a certified `Nat` operation's name, both
rejected as on the merged read; two modules declaring one name that the module never reads
together are accepted, where the merged read rejects the pair. `Mathlib.RingTheory.WittVector.MulP`
is accepted against `WittVector.Basic` as Mathlib v4.35.0 builds it, the private constant its
exported values read completed as its statement. Per module (`--jobs=8`, `perf stat -e
instructions:u`): `Init.Data.Nat.Lemmas` 9.0 G, 0.17 GiB; `Init.Data.BitVec.Lemmas` 53.9 G,
0.35 GiB; `Mathlib.GroupTheory.Coxeter.Basic` 8.9 G, 0.28 GiB;
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic` 15.1 G, 0.40 GiB.

**The import graph** (`ConLeche/Driver/Graph.lean`). `--check-graph` reads the imports at the
start of every exported file of the roots' closure (`moduleImports`, level by level on the
worker threads), over imports of every kind (public, private, `import all`, `meta`: a module's
context may hold a copy from a module only a private import reaches), orders the closure by
Kahn's worklist and validates the order: every module has a rank, no two the same, every import
goes to a module of the closure of a smaller rank. A cycle is printed and rejected (exit 1), as
is an import on no directory of the search path; an unreadable header is exit 3. At every exit 0
in the IO model there is the closure `C`, each module's imports its header read's answer on the
snapshot, and a rank one-to-one on `C` and decreasing along every import edge
(`checkGraphG_ok`, `ConLeche/Verify/Driver/Graph.lean`); every module of the roots' closure by
the specification (`InClosure`) is in `C` (`checkGraphG_closure`). The proof is about the
validation; Kahn's algorithm has no theorem.

**Every module of a closure** (`ConLeche/Driver/Modular.lean`, `--olean --modular`;
`ConLeche/Driver/Schedule.lean` and `ConLeche/Driver/Schedule/`, `--olean --schedule`). The one-process mode checks the root's
closure by the graph check (`graphOf`), locates every module of it and reads its two parts' name
positions once (`readModTable`), marks those tables persistent, and then runs every module's
worker steps (`checkModuleG`) on the worker map, one module claimed at a time, each module's own
checks on one thread, its reads of the files answered from the tables (`ModTables.reads`: a
module's imports and name positions from them, a view's files read at the location found once).
A worker's reads go through `OleanReads` (a module's imports, a view's files, a part's name
positions); reads that refine the search path's in the model (`OleanReads.Within`: every outcome
of theirs, from any open files, is one of the files' read from any open files, which has the same
outcomes whatever files are open) make every phase of the worker refine the same phase over
the files (`ConLeche/Verify/Driver/Shared.lean`), so `checkModuleG_accept` holds for the tables'
reads (`modTables_within`). At every exit 0 of the one-process mode there is the graph check's
closure and, at every module of it, `WorkerAccepted` (`checkModularG_accept`,
`runArgs_modular_accept`, `ConLeche/Verify/Driver/Modular.lean`): what `--check-graph` and
`--module` at every module of the closure would give, from one run. Exit 0 needs every module's
worker step to answer 0; a failure names the first failing module in the graph's order, with its
code. The scheduler starts one `--olean --module --jobs=T` process of the binary per module;
here `--jobs=N` is the thread budget, the running workers' `T` summing to at most `N`. A worker gets
one thread, or more where memory, not `N`, keeps workers from starting: `max(1, min(cap,
declarations ÷ 30))` threads, `cap` the free threads less those the room could still fill with
workers at the typical peak (as many as are queued), the declarations read off the module's own
files just before the start (only where `cap` is above 1); a worker's threads share its context,
so they cost far less memory than as many workers, and admission counts each worker at its
measured peak, threads included; a module killed while running with more than one thread runs
with one from then on. The modules form a fixed queue (a hash of the names; `--schedule-order=graph` for the graph's order), in which a killed module is unstarted again at its own position. One worker slot, the head, runs the unstarted module of the lowest position whenever it has none, whether it fits or not, and is never killed for memory; every other start takes the unstarted module of the lowest position that fits, and every admitted module is started at once, within a hard memory limit over the
running workers' resident sets (`--schedule-memory=SIZE`, a number with a unit `K`, `M`, `G` or
`T`, such as `47G`: admission plans against a lower planning budget, the limit minus a margin learned in the run (the larger of 10 % of the limit and the 99th percentile of the recent surprises, how far the current sets ended above what admission had reserved when it last started a worker, the worker furthest above its own reservation left out, since one worker outgrowing its reservation is what the kills and the known sizes handle; at least half the limit), so that growth admission could not foresee lands in the gap; the queued modules whose known size (the largest resident set seen when one was killed, else the typical peak) fits into the planning budget minus the running workers' reservations start (a running worker is reserved at the largest of its peak over the last 5 minutes of its run, sampled every tick, the typical peak and its known size; not at its peak so far, so that a worker that fell back from a peak frees the room); when their current sets exceed the hard limit the youngest workers but the head slot's are killed, by their own child handles, until the sets fit, each unstarted again at its position with its size; a worker alone over the limit has the verdict `memory` if it runs one thread, and is otherwise killed and queued again at one thread (its threads' memos add up); no module starves, since each one in turn becomes the lowest unstarted position and the head slot starts it),
with a time limit per worker (`--schedule-timeout=S`) and an append-only log a restart resumes
from (`--schedule-log=FILE`: per finished module `<verdict>\t<module>\t<ms>\t<peak KiB>\t<ms since the start>\t<declarations>\t<parse ms>\t<check ms>\t<check busy ms>\t<slowest check ms>\t<threads>\t<LEAN_STACK_SIZE_KB>`, the peak prefixed `≥` where it is the scheduler's last sample because the worker reported none, the declarations to the slowest check read from the worker's verdict and statistics lines (`-` where it printed none); per kill `killed\t<module>\t<ms>\t<KiB>\t<threads>`, which is no verdict; while modules wait for room, at most once a minute, per running worker `reserve\t<module>\t<ms>\t<KiB>\t<reserved KiB>\t<term>` (`learned`, `window peak` or `typical`), which is no verdict either, and the heartbeat then names the workers reserved well above their current set (`over-reserved: …`); the reader takes the first two fields of each line, so two-field logs resume too; a resumed run reads the typical peak's window from the log's last 200 exact peaks, and the largest set at the kills of a module that still has to run as its known size (at least the typical peak), with one thread where the kill came with more; a `memory` verdict of a worker with several threads is no verdict, and the module runs again at one thread); its verdict is
its workers' exit codes, and no theorem is about it: the modular statement composes what each
run's exit 0 says. A worker's three standard streams are pipes and it inherits no other
descriptor; its stdout and stderr are read as it runs, and its stderr is passed on for a verdict
other than 0. Every finished-module line (stdout) and every heartbeat (stderr) starts with the same status part in the same fixed columns,
`[ 3804 ( 1.5%)  3 wrkr  25 thds  RSS 34.1G tot 27.7G biggest  15d12h eta]`: the modules with a verdict (a resumed run's logged ones included) and their percentage, the running workers, the threads they hold, the running workers' resident sets now, summed (`tot`), and the largest one's (`biggest`; read every tick from `/proc`, left out where that cannot be read), and the estimate. A finished module's status part is followed by
`t=Ss  rss=0.26 GiB  ×T  M`, the module last and every field padded to a fixed width so the statistics keep their columns; a module with a non-zero outcome (`1`, `2`, `3`, `timeout`, `memory`, `stack`, `oom-kill`, `signal 11 (SIGSEGV)`) has `FAILED V` just before its name, and an accepted one shows no verdict (the log keeps every verdict). A worker that a signal ended gets the signal in its verdict (`Child.tryWait` returns 128 plus the signal; a worker's own codes are 0 to 3); `stack` is a worker that overflowed its thread stack (SIGABRT, and `Stack overflow detected` on its stderr), `oom-kill` a SIGKILL while the `oom_kill` counter of the nearest cgroup with a memory limit rose. The log's last field is the `LEAN_STACK_SIZE_KB` of the run (`-` where unset), and a resumed run runs a `stack` module again only where the value differs. Lean's threads have a 1 GiB stack by default, and a deep recursion (a long list or string literal compared cell by cell) can need more: for large developments set `LEAN_STACK_SIZE_KB` (the workers inherit it; a stack is address space, paid for in memory only as it is used). CFSG's `#text_pieces_d` command, for instance, checks such theorems on threads with 4 GiB stacks:
`×T` is the worker's threads where above 1 (blank otherwise, absent at `--jobs=1`), `rss` is the worker's own peak resident set (its `peak RSS` statistics line; `rss≥` the last value the scheduler sampled where the worker wrote none, as when killed), `done` counts the modules a resumed run found logged, and the estimate is the remaining modules times the mean module time over the average number of running workers: the mean is taken over every finished module with a known time (the log's verdict lines that carry the time field, and this run's), the average is this run's once it has lasted a minute and is at least 1, else the previous runs' from the log (also below 1), else `--jobs`; none where no time is known; in days and hours past 48 hours, in hours from 10, else with minutes. The estimate leans low: logged times come only from finished modules, and the long ones are more often still running or interrupted (`killed` lines are not counted). With
`--progress=N` (milliseconds, at least a second) or `--progress=Ss`, a heartbeat on stderr after
that long without a line is one line: the status part and what explains the wait (`waiting: longest M 7m01s (+2 more), 13 requeued, 5 waiting for room: reserved 43.4 GiB of plan 40.5 GiB`: the longest-running worker and how many others run, the modules a kill has put back, and the killed modules whose known size does not fit the room yet, with what the admission has reserved for the running workers, each at the most of its peak over the last 5 minutes, the typical peak and its known size, against the planning budget; the last two parts only where non-zero). The typical peak, which admission assumes for a worker that has not shown its peak yet, is the median of the last 200 finished workers, the log's recorded ones included (the limit divided by the jobs until 20 are known in total); the final summary line gives the run's peak total. A worker that cannot be started is that module's verdict 3,
with the reason; no further worker starts, and the running ones are waited for. At the end the scheduler prints statistics of its own run on stderr: wall time, the time-weighted mean of running workers, of current and of reserved memory, the planning budget at the end and the largest surprise, mean, median, 90th percentile and maximum of the time and of the peak per module, the kills with the worker time they lost, the head slot's starts that did not fit, and the `memory` and non-zero verdicts. SIGINT or SIGTERM stops the starts, kills the running workers through their own child handles (logged as `killed`, no verdict), flushes the log, prints the statistics and exits 130 or 143.

`--olean --schedule-commands --search-path=DIRS -- ROOT` starts nothing: it prints on stdout,
one per line and shell-quoted, every command that checks the closure, so that any other system
(a batch queue such as slurm, or a shell loop) can run them: first `con-leche --check-graph
--search-path=DIRS -- ROOT`, then one `con-leche --olean --module --verified
--max-nat-size=N --search-path=DIRS -- M` per module of the closure, in the scheduler's start
order (`--schedule-order`), with the binary's own path and the search path as given;
`--jobs=N` is on each worker's line only where it was given. `-memory`, `-log` and `-timeout` are
ignored, and nothing is printed on stderr. The modular guarantee needs every printed command to
exit 0, all of them on one unchanged snapshot of the files; a worker's exit 0 is its module
accepted. A deep check may need `LEAN_STACK_SIZE_KB` in the commands' environment, as above.

The scheduler is the module subtree `ConLeche/Driver/Schedule/`, one executable with the rest:
`Engine.lean` the policy (admission, the planning budget, the head slot, the victims, the thread
budget, the known sizes, the start order), pure and generic in what a job is; `Worker.lean` what
the worker is to it (its arguments, the commands, what it printed, its verdict); `Log.lean` the
log's lines and resuming from it; `Status.lean` the status, finish and heartbeat lines and the
statistics; `Proc.lean` what it reads of `/proc`; `Run.lean` the IO loop, the one module of the
checker that starts or kills a process or writes a file. `ConLeche/Driver/Schedule.lean` is the
glue: the closure, the workers' arguments and the `liftIO` call.

`runArgs_oleans_accept` is `runArgs_accept`'s statement for these arguments:
every exit 0 read records off the snapshot's files that `checkDecls` accepts, with each
theorem's value in place. The check phase reads the values through the IO class, its workers'
map (`CheckerIO.parMapWorkers`) is in the model with a worker's state whatever its own elements
can make of it, so that a value read at any state a worker can reach is what the reference stands
for on the snapshot (`readValue_spec`), and `checkOleansG_accept` is `checkDecls`' accept:
the index does not depend on a theorem's value (`buildIndex_fill`). `readOleansAt_filled` says
those records are the specification's: a theorem's record with its value in place is the
constant the specification reads off that module's files, its statement and its proof.
`readOleansAt_ok` says what those records are made of: the order holds the named modules and
has every module after its imports (`closureOrder_ok`), every constant of their private views
stands in the merge, itself or a constant of its name and statement that Lean's own import lets
stand for it (`mergeAll_ok`), every constant the walk visits and does not filter out has its record,
where the blocks of the merged constants agree, which `blocksOk` checks before the walk
(`emitAll_covers`), and every declaration comes from stored constants (`declsOf_from`).
A theorem of a module of the closure is among the records with its statement (`declsOf_thm`,
`readOleansAt_thm`), so `main_oleans_no_False` holds of the files, at the arguments `--olean
--search-path=<dirs> -- <root>`: if the private view of a module of the closure of `root`, by the
specification (`ViewOf`, `decodeModuleSpec`), holds a theorem of type `False`, no run exits 0. An inductive block's record is
known to be made of stored constants of the right kinds by their statements; its other fields and
the recursor rules are `validateIndF`'s and the installer's to check. The records' order rests
on what a constant mentions, read by a walk that has no theorem, as nothing but the order
depends on it and every record is checked at its place. `olean-compare` compares the
records with lean4export's, with every value read.

## 3. The checker

Two modes exist, `--verified` (default) and `--trusted`
([the type `CheckMode` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L55)).
Trusted mode is verified mode minus the certification-only steps —
checks the official kernel does not make, which exist so that the proof
can rely on their outcome; it is faster and is outside the theorem.
Both use the same core.

The checker is a Lean-kernel-style type checker in the shape of the
official one: `whnfCore` does β/ι/projection/quotient reduction (with
the official `cheap_proj` mode, in which a projection's scrutinee is
reduced by `whnfCore` itself rather than by `whnf`),
`whnf` adds δ-unfolding of definitions — a theorem is opaque to
reduction: its value is never unfolded, so whether a declaration
type-checks never depends on a theorem's value — and the literal fast
paths
([function `whnfBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1157)),
`inferType` computes a type, and `isDefEq` decides conversion in the
order of the official `is_def_eq_core` (cheap head normalization, the
easy cases, the lazy-delta loop — which compares two applications of
the same definition argument by argument before unfolding them, last
argument first as the official `is_def_eq_args` does
([function `defeqSpine` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1431)) —, the
projection-against-projection comparison by scrutinees, the full head
normalization and a restart, then the stuck comparisons) with two
deliberate exceptions. The easy cases and proof irrelevance are tried on
the unreduced pair, before any head normalization, so two proofs are
compared by their types and never reduced (the official kernel reduces
them first, and loops on a proof that has no normal form). And when one
side is a closed constructor application, applied to all its parameters
and fields, of a type that is never a proposition, has no η law and is
not `Nat`, the other side is head-normalized at once: if its head is the
same constructor, the comparison goes on with that normal form, and if
it is another constructor, the answer is `false`, which no rule of
conversion could change for such a type. The official kernel does this
for the constant `Bool.true` alone; elsewhere it unfolds one definition
at a time
([function `defeqBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1866-L1884)). The checker
reduces a proof only where a recursor's value depends on it: the major
premise of a recursor over an inductive proposition, which is
head-normalized to a constructor unless the K rule (which reads only
the major's type) applies — and if the K rule's rescue *fails*, the
major is left exactly as it is, never head-normalized, so a K-like
recursor never reduces a proof. A structure major is likewise rescued
from its type before it is reduced, in the order the official kernel
adopts with its logic renovation (lean4#15371): the constructor of the
major's projections is built from the major as found, and only if no
rescue applies is the major head-normalized, so a major with no normal
form does not stop the recursor. This too deviates from the official
kernel on purpose (it head-normalizes the major regardless of the
rescue's outcome): the rescue already decided the major's type is not
the index the recursor needs, by the same comparison a normalized
major's type would have to pass; the loss is confined to
incompleteness corners of the checker's own conversion. Conversion uses lazy
unfolding, η, proof irrelevance, structure η, unit-likeness and K-like
reduction as each inductive type's flags, read off its records at use,
permit. One proposition, `And`, is additionally rescued: for a major
proof `h`, `And.intro a b h.1 h.2` is built from `h`'s type, before
`h` is reduced, and compared with `h` by proof irrelevance. The official kernel has no such rescue;
this checker needs it because theorems are opaque here, so `And.rec`
applied to a theorem would otherwise never reduce. The rescue is keyed
on the name `And` only, to keep its reach small. Its check is
proof irrelevance, so it would be sound whatever block the stream
declared under that name; `And` is pinned (§5) so that the rescue is
always there to fire. Two things differ from a textbook
presentation and matter for the proof:

* **Two inference grades, and the λ checks.** Inference runs at the
  full grade on a declaration's own terms (application arguments, λ
  domains and `let` values checked) and at the official kernel's
  infer-only grade on the terms reduction and definitional equality
  build on their way
  ([function `inferBodyIO` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1341)).
  Beyond the official kernel, the verified mode compares the opened
  bodies' full-grade types at the innermost level of a λ/λ comparison
  ([function `defeqBindersInner` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1453))
  and at η; the proof consumes them. Two cheap guards are the proof's
  too and never change a verdict on well-typed input: η, unit-likeness
  at a Π-type and the η-expansion of a partially applied constructor
  are tried only against a term whose head is no λ and no `let` (a
  weak-head normal form; a λ meets them through η first), and a
  recursor's stored type is checked to have the spine's number of
  binders. The
  synthetic constructor applications of the K and `And` rescues are
  typed at the io grade only: their io type is compared with the
  major's (both modes), then, at the verified mode, proof irrelevance
  compares them with the major — a certificate family, off at the
  trusted mode, as is the ι rule's case-3 decision (the constructor's
  levels and parameters against the comparands, the constructor
  telescope at the full grade, and the canonical-index comparison).
  Binders carry no data the checker reads, and declarations are stored
  as declared, `let`s included:
  `whnfCore` ζ-reduces and inference runs the official `infer_let`.
* **Fuel and memos.** The pure checker is fueled; the cached checker is
  not, but its memos are proved to agree with the pure functions at
  every fuel large enough to succeed
  ([theorem `checkDeclStepC_run` in `ConLeche/Verify/Cached/BridgeC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/BridgeC.lean#L285)).
  Nesting (a head, a scrutinee, a subterm's type) is bounded by the
  shared fuel, an error when exhausted; the fuel is effectively
  unbounded (2^62), since it exists for the proofs' induction. Each
  level of nesting is native recursion, as in the official kernel, so
  the native stack is the real limit: every checker thread has the Lean
  runtime's 1 GiB stack, a level costs at most about 1.2 KB of it, and
  a recursion of about a million levels or more aborts with a stack
  overflow, an error
  ([definition `checkFuel` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1944)).
  Reduction *chains* are not bounded by it: the
  `whnf` loop's δ steps, the `whnfCore` loop's β, ι and projection steps
  and the lazy-delta loop each iterate in constant native stack, a
  `whnfCore` step returning the term to continue with instead of
  calling the loop. A reduction that does not terminate (a proof built
  from Coquand's paradox, in a position nothing lets the checker skip)
  runs until the external timeout, as in the official kernel.
  As in the official kernel, the head-normalization memos skip the easy
  cases: `whnfCore` returns a sort, a free variable, a Π-type, a
  lambda-expression, a constant or a literal, and `whnf` a sort, a free
  variable, a Π-type or a literal, before any lookup, so a computed
  literal never becomes a memo entry. The `whnfCore` memo is used as
  in the official kernel: every step of a reduction chain looks its
  term up, and at the chain's end the terms of its β, projection, ζ
  and head-normalizing steps are stored with the answer; a step that
  fires ι or answers a stuck application is not stored. An
  application whose head is its own head normal form (a constant, say)
  is answered by itself, nothing rebuilt, with ι tried once, at the one
  argument count where it can fire, as in the official kernel's stuck
  arm; and `whnf` returns a literal that a `Nat` operation computed at
  once. The official kernel's cheap mode (definitional equality's
  `cheap_proj`) reads the one memo and writes nothing; here it reads a
  memo of its own, which the full mode fills with the chains the two
  modes reduce alike (no projection, no head to normalize first), so a
  cheap query is never answered with a result the cheap mode would not
  compute.
  Binder names and binder infos are not stored at all; `Expr` carries a
  packed hash and loose-variable bounds as computed fields, which is
  what makes traversals of shared terms (DAGs) cheap. The
  substitutions memoise only the nodes the runtime reports as shared —
  a reference-count read, with a memo keyed by the node's address and
  validated by pointer identity, so an unshared node costs no key and
  no probe — and every other traversal memo in the checker, structural
  equality (`Expr.beq`) and the syntactic guard traversals included,
  follows the same discipline
  ([`withExclusive`'s account in `ConLeche/Kernel/Exclusive.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Exclusive.lean#L6-L42)).

## 4. The proof idea

There is no syntactic typing judgement and hence no theorem of the form
"accepted ⇒ derivable". The *theory* is the set model. What is proved
about the algorithm is stated only in the accepting direction, and it
is stated semantically.

**Terms.** A kernel `Expr` denotes, under a level valuation, a term
([type `Term` in `ConLeche/Term/Syntax.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Term/Syntax.lean#L188-L219)):
de Bruijn indices, sorts at concrete levels, built-in constants at
concrete level instantiations, no names, no binder infos. The
interpretation reads this syntax.

**Interpretation.** The interpretation maps a term to a set, totally
and term-directed
([function `interp` in `ConLeche/Semantics/Interp.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/Interp.lean#L134-L145)):
a Π whose fibres over its domain are all truth values is a truth value,
otherwise a dependent function space; a λ whose body values over its
domain are all the proof point is the proof point, otherwise its graph
(both read off the values, `piV`/`lamV` in
`ConLeche/SetModel/Ops.lean`; over an empty domain a Π is `{pt}` and a
λ the proof point); β holds on the domain with no other premise; a sort is
the set of *types* in a universe of the chain (truth values, and sets
that neither are the proof point nor contain it), cumulative in the
level; nothing needs to be well-typed to be
interpreted. Propositions are sets with at most one element, so proof
irrelevance and propositional extensionality are built in, and a
propositionally proven equation is a set equality.

**The invariant.** In place of a typing judgement there is a semantic
predicate
([predicate `WellDenoted` in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/WellDenoted.lean#L49-L72)):
hereditarily, every application applies the point to anything, or a
graph to a member of its domain, which is a type; every binder's
domain is a type, every projection hits a pair, and so on. Unlike syntactic typing it is preserved by β and
the other reduction steps
([the preservation lemmas in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/WellDenoted.lean#L123-L287)).
An environment carries the invariant for every stored constant, plus
closedness and the pins of the basis constants
([structure `EnvModel` in `ConLeche/Model/Env/EnvModel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Env/EnvModel.lean#L35-L63)).

**The statement's reading.** The main theorem is not stated over the
`Term` and `interp` but over `Denotes` (§1), a
relation on the checker's own terms. The two agree wherever the
reading of a term is defined: `interp` of the reading is a
`Denotes`-denotation of the term, since both read a binder's regime off
the values
([theorem `Denotes_of_denote` in `ConLeche/Model/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L202-L208)).
The relation reads a binder's body under the binder with de Bruijn
indices while the checker opens it with a fresh free variable; a small
closing operation translates between the two.

**The claims.** Each kernel function gets one claim, in the accepting
direction only
([the claim definitions in `ConLeche/Model/Claims.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Claims.lean#L49-L125)):

* `whnfCore`/`whnf` return a term with the same denotation, with the
  invariant preserved, wherever the term does not denote the proof
  point;
* `isDefEq` answering `true` means the two denotations are equal
  wherever neither is the proof point;
* `inferType` returns a type that denotes a type, and the term's
  denotation is a member of it;
* at the infer-only grade the claim is weaker and hereditary: the term
  is the point, a member of its inferred type, or — where that type is
  syntactically a Π-type — a function on the Π-type's domain, not
  everywhere the point, each of whose applications satisfies the claim
  at the Π-type's body
  ([`IORel` in `ConLeche/Model/Rules/IORel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/IORel.lean)).
  An argument the grade does not check can make an application the
  point where its type has no point, and an abstraction whose body is
  the point at some values is no member of its inferred Π-type; a
  Π-type reduces only to itself, so where the inferred type reduces to
  a family's application, or its sort to `Prop`, the claim is a
  membership or the term is the point, which is all its consumers
  read.

The first two say nothing about proofs. A type is never the point, so
a comparison or reduction of types — which is what declarations,
inference and the certificates run — is claimed outright; between two
members of one type, the point does not separate them either, because
a type's members are all the point or none.

They are proved through a *relational description* of the checker.
Mutually inductive relations over the checker's own terms say what
moves the core makes — a reduction step, a definitional-equality
decision, a λ-telescope comparison, an η-expansion, a unit-like type
and its fields, a type inference (checking, or infer-only as in the
official kernel's `infer_only` mode), and the certificate checks — with the fuel, the unfolding heuristics and the dispatch order
out of sight; a rule's premises are exactly the certificates the
checker ran at that site, and the symmetric and derived variants are
theorems, not constructors
([the relations in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L103-L107)).
Definitional equality has no transitivity rule, deliberately, and
none can be added: the relation is the checker's verdict on terms
that are well-formed together, which no rule states, and every
premise's subject is a subterm of the conclusion or the product of a
reduction or an inference
([the docstring of `DefEq` in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L329-L352)).
The proof then has three parts. The *bridge*: an accepting run of any
kernel entry point, at any fuel, yields a derivation — one induction
on fuel, over both values of the eager flag at once,
mechanical, each checker site landing on one rule
([theorem `bridgeAt` in `ConLeche/Verify/Rules/Bridge.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Rules/Bridge.lean#L29-L32)).
The *soundness*: a derivation implies the claim's conclusion — one
structural induction over the relations, every case one lemma
about one rule, stated over the environment's laws and never over the
implementation, at one valuation at a time. β's lemma reads no premise:
a redex that is not the point has a λ that is not the point, which is
a function on its own domain, and the application's own slot puts the
argument there. The other definitional-equality rules read the point
the same way: two arguments of equal heads lie in one domain, a type,
so they are both the point or neither is. ι reads the point the same
way. A redex's spine is certified against the recursor's type, so the
major lies in the major's domain, an instance of the family. Where the
family is never `Prop` at the recursor's levels, that instance holds
no point, so the major is not the point; its reduction is then an
equation, and the constructor application, which is not the point
either, fits its own type. Above `Prop` an injection reads neither the
family's levels nor its parameters, so the major's membership in the
domain makes the application one of the constructor at the recursor's
levels and parameters, with the same fields; nothing is compared, as in
Lean's kernel. A K-like recursor's value is the minor premise for any
major in the domain, which the environment's law states. Where the
family may be `Prop`, the checker certifies the constructor's spine and
compares its levels, parameters and indices; where the major is the
point, the constructor application is the point too. The comparisons the
ι step ran become equations because both sides fit one telescope of
types. All of this is stated as environment laws the installer proves
(`RecRuleLaw` in `ConLeche/Model/Env/Laws.lean`). The literal
accelerations read the argument's domain off the operation's graph,
`Nat`, and equate the argument with its literal inside that type.
Structure η and the structure-η major rescue read two environment laws
of an η family: a member is the constructor at its type's parameters
and its own projections, and that spine fits the constructor's own
telescope (`EtaCoherent` in `ConLeche/Model/Env/Laws.lean`). The
stuck side's type is a type, so its parameters fit the family's
telescope with no certificate; the constructor side, not being the
point, fits the constructor's telescope, so the comparisons the rule
ran become equations there too.
Unit-likeness reads the same two laws, stated for the family's
projection table at every field count: two members of an η family fit
the constructor's telescope at the same parameters, whose fields are
propositions (every proof is the point) or unit-like (none, at a
fieldless family), so they have the same projections and are the same
member; two members of a Π-type whose codomain is unit-like agree at
every argument. The η of a partially
applied constructor compares the two sides' types, then their
applications to a fresh variable: two members of one Π-type that agree
at every argument are equal.
λ-congruence compares the bodies' types at the innermost level of two
λ-telescopes, and η the λ's body's type with the Π-type's body: two
bodies in one type are both the point or neither, so the bodies' claim
is an equation at every value of the variable, an equation of the λs
([the master induction in `ConLeche/Model/Rules/Sound.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/Sound.lean#L75-L78)).
And the *recomposition*, which is a few lines per claim: bridge the
run, apply the soundness
([theorem `checkSoundAtP5` in `ConLeche/Model/Rules/Recompose.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/Recompose.lean#L49-L54)).
The modules that state the relations and prove them sound import the
term syntax and the environment, not the implementation; the fence
of §12 checks it.
This is where the usual difficulty of intensional soundness proofs, the
injectivity of Π needed to invert the typing of `f` in an application,
does not arise: `inferType` itself reduces `f`'s type to a syntactic Π,
whose denotation *is* a function space, and membership in it is what
`app` needs. Equality flows only from "defeq accepted" to "denotations
equal", never back.

**Declarations.** A definition or theorem is accepted when its value's
inferred type is definitionally equal to its stated type; the claims
then give the value's denotation a membership in the type's, which is
what the environment invariant records. The step theorem covers every
declaration kind, including the inductive installs of §5 and the Nat
operations of §6.

## 5. Inductive types

Inductive blocks are not trusted from the stream. Every block — one type
or several mutually inductive ones, nested or not, the pinned ones
included — goes through one installer, which checks the block the way
the official kernel does and generates the block's recursors itself.
Five inductive types are pinned besides: `Eq`, `Nat`, `Empty` and
`False`, whose meanings the model fixes, and `And`, which the checker
has code for. A pinned block must agree with its pin.

### The pinned basis types

`Eq`, `Nat`, `Empty` and `False` have built-in pins
([the `False` pin in `ConLeche/Kernel/Basis/False.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis/False.lean#L51)).
A block under one of these names is installed and checked like any other
block, from the stream's own records. After a declaration's own checks
comes one more, the only place the checker sets the basis names apart
([function `basisNamesOk` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L144-L151)):
a block whose members' names are a pinned block's must agree with the pin
up to the level-parameter names its records declare, and no other
declaration may take one of the reserved names. A block that fails it is
rejected. A block that passes stores the pin at the names its records
declare, each type former with the capabilities its block gives it, and
no projection table
([theorem `blockInstall_pinned` in `ConLeche/Verify/BasisBlock.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/BasisBlock.lean#L308-L311)),
so the model's account of the pin at its own names carries over.

The quotient `Quot` with its soundness axiom, a kernel primitive rather than an
inductive type, comes as five records: each stores its slot's pin at the
level-parameter names it declares, once the slots it mentions are stored, and a
record that is not its pin up to those names is declined. Each record's names
are its own: references between the constants are positional, and the
eliminators' rules carry the level they compare the constructor's at.

They are pinned so that there is no doubt about what they denote. The
model does not read their denotations off whatever the stream declared,
as it does for every other type; each is a fixed set written down by
hand, and each is one a statement or a primitive of the checker relies
on:

* `False` denotes the empty set and `Eq` denotes set equality. The main
  theorem's `Model` states exactly these two facts (§1), so the theorem
  needs no hypothesis about how the stream declared either, and the
  main corollary rests on the first.
* `Nat` denotes the natural numbers. A numeric literal is a term former
  of its own and denotes its numeral, and the `Nat` operations of §6
  compute on literals.
* `Empty` denotes the empty set, for the companion statements about it
  (`no_proof_of_Empty_cached` and its siblings, checked in the axiom
  test).
* `Quot`, its constructor, its two eliminators and their reduction
  rule are primitives: there is no inductive declaration to check, and
  `Quot.sound` is one of the three standard axioms (§8).

### The pinned `And`

`And` is pinned for a different reason: the checker has code for it.
The stuck-proof rescue of §3 builds `And.intro a b h.1 h.2`, which
works only if `And` is the toolchain's structure `And (a b : Prop) :
Prop` with its one constructor `And.intro (left : a) (right : b)`. So
the fold rejects any record that declares `And`, `And.intro` or
`And.rec` and does not agree with the pin up to renaming of universe
parameters
([function `andPinOk` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L189-L194)),
and the block that does agree goes through the installer below, which
stores its projections as it does for any structure. A stream that does
not declare `And` gets the toolchain's block from the built-in prelude
(§6). The model needs nothing about `And`: the rescue is sound by proof
irrelevance alone. The pin guarantees that the rescue is available in
every accepted stream, rather than silently absent in one whose `And`
differs.

Every other type — `Bool` and `PUnit` among them — is installed by the
installer below, from the stream's own records (for `Bool`, from the
built-in prelude's copy if the stream has none, §6). One of these
names is nevertheless read by the checker: `Bool`, the result type of
the `Nat` comparisons. It needs no pin; §6 says why.

### The installer

The installer first reads the block's shape
([function `readBlock` in `ConLeche/Kernel/Inductives/BlockShape.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockShape.lean#L401)):
its parameter count as the stream declares it, checked against the
type formers' telescopes and against every constructor record before
anything else runs
([function `indParamsOk` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L418-L425)),
and each member's index count off what is left of its type former's
telescope, as the official kernel reads them. Any number of parameters,
indices, constructors and fields is supported; fields may be recursive,
reflexive (a function returning the type) or nested (the type under
construction inside another inductive type, as in `List T`); the block
may live in `Prop` or in `Type`. The install checks the type formers,
then the constructors, then runs the positivity check and the
official kernel's remaining checks — parameters applied uniformly,
universe bound, elimination restriction, index occurrence — and
finally the recursor check. The whole install is one entry
([function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L153)).

**The classes.** The recursors a block comes with eliminate one
*class* each: a member of the block, or — in a nested block — another
inductive type at the instantiation the block uses, such as `List T`
for the auxiliary recursor `T.rec_1`. Before the positivity check the
installer reads the classes off the stream's recursor types and checks
each one as a well-formed major premise
([function `targetMajorOf` in `ConLeche/Kernel/Inductives/RecCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/RecCheck.lean#L239-L240)).

**The positivity check** follows the official kernel's: a field's type
is put in weak head normal form before it is classified, and again
under each Π binder. The difference is nesting. The official kernel
rewrites a nested block into an auxiliary mutual block; this checker
builds no auxiliary block and instead looks through the container at
its concrete instantiation: at a field `List T` it checks `List`'s own
stored constructors with `T` in place of the parameter, after weak
head normal form, and records the instantiation
([function `nestContNew` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L821-L823)).
In the constructors it checks, every application `T_j p⃗` of a block
member to the block's parameters is replaced by a *hole*, a variable
standing for that whole application. The block itself is checked the
same way as a container, as the outermost level of the nesting
([function `nestRoot` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1047)),
and the check starts from every class, so every class a recursor
eliminates is an instantiation it has visited — including one that
weak head normal form erases from every field
([function `classSeeds` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L498)).
Nothing is stated or cached about a container in its parameter. The
normal forms the check records are the fields the model reads
([function `checkBlockPositivity` in `ConLeche/Kernel/Inductives/BlockInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockInstall.lean#L284)).

**The recursor check.** The recursors are generated in the official
kernel's shape: each class's constructors are read off the positivity
check's recorded normal forms, and from them the checker builds every
recursor's type and rules — the minor premises over the constructors'
declared fields, each inductive hypothesis over its field's normal
form. Each generated type must be definitionally equal to the stream's
recursor type
([function `genRecCheck` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L552)).
What is installed is the stream's own recursor — its type and its
rules' right-hand sides, as a tool that loads the input runs them —
once it agrees with the generated one: as many rules, for the same
constructors in the same order with the same field counts; the stream's
type, opened up to its major premise, has the generated type's binders,
each domain definitionally equal to the generated one's, and a residue
definitionally equal to it; each right-hand side is written as a function
of the recursor's leading arguments and the constructor's fields (it
begins with that many lambdas), is closed, type-checks
at a type definitionally equal to the generated rule's, and is
definitionally equal to the generated rule. The comparisons run at the
environment holding the generated recursors
([function `streamRecsCheck` in `ConLeche/Kernel/Inductives/StreamRecs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/StreamRecs.lean#L187)).
What is installed is the record, and the checks make it the generated
recursor with the record's type and right-hand sides: its major premise's
position, its K flag and each rule's firing mode are the generator's
([theorem `blockInstall_of_checks` in `ConLeche/Verify/Cached/BlockPushes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/BlockPushes.lean#L273)).
The rules of a recursor for an outside class fire at the instantiation
read off its type
([function `recFire` in `ConLeche/Kernel/Install.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L45)).
Members of the right shape additionally get primitive projections,
structure η and unit-likeness (one constructor, no indices, not
recursive) and K-like reduction (a proposition with one constructor
and no fields), exactly under the official kernel's conditions.

**In the model** the block's carrier is the least fixed point of its
family functor over the index fibres
([the fixed-point family space in `ConLeche/SetModel/Value.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Value.lean#L387-L388)),
for several members a least fixed tuple of families, and a container
field reads the container's own least fixed point at the holes'
values. That the fixed point is a member of the universe follows from
one abstract theorem about *accessible* operators, those where every
element of the output needs only elements of the input indexed by one
fixed set of the universe
([theorem `closed_of_acc` in `ConLeche/SetModel/Access.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Access.lean#L243)):
such an operator has a closed tuple in the universe. The run of the
positivity check shows the block's operator accessible, for finitary,
reflexive and nested fields alike. Each recursor is read as the unique
value of its *graph*, the least relation closed under the recursor's
rules read over the ways a value decodes as a constructor application;
the block's induction makes that relation a function at every sort
(`ConLeche/SetModel/GraphRec.lean`), and the only sort-dependent fact
it needs is the kernel's own large-elimination guard. The model-tier
theorem for the whole install is
[theorem `declBlock` in `ConLeche/Model/Inductives/BlockRunFacts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/BlockRunFacts.lean#L127-L136).

A block that cannot be read this way is an invalid input and is
rejected, with the reason the reading gives: records out of order, no
inductive type, no recursor record, more parameters than a type's
binders, recursor argument counts that do not fit the block, or types and
constructors whose universe or parameter declarations disagree. The
official kernel rejects each of these too, except a block without
recursor records, which it accepts because it generates the recursors
itself; the input format here carries every block's recursors, so such a
block is invalid input.

### A former stored at a definition

A former may be declared at a term that only reduces to its telescope
(`def MyType := Type`, `inductive S : MyType`), and so may a family a block reads
as a container. The environment stores such a former at its declared type, as the
record gives it. The block's check reduces each such member once, as official's
`check_inductive_types` does: the declared type is checked and compared with its
reduct, and the check after that reads the reduct. A def-headed container is read
through the same loop at each use
([function `familyTelescope` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L99)).
What a use needs of a family's sort is computed at the use, at the environment of
the use.

A container's reduct, computed at a later environment, is the telescope the family's
own check read: a run does not see an extension of the environment. On a term whose
constants and literals resolve at the smaller environment, the fuelled knot at the
two environments is one run, at every entry point and every fuel, and what it returns
resolves at the smaller one
([theorem `knot_ext` in `ConLeche/Verify/EnvExt.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/EnvExt.lean#L480-L482)).
All the knot reads past the term is what a stored constant's record names, and a
declaration boundary has it stored
([structure `StoredFacts` in `ConLeche/Verify/EnvExt/Reads.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/EnvExt/Reads.lean#L29-L30)).
The model therefore keeps one reading of a family: a recorded block's datum says which
reduct it shows for a member (`LfpDatum.telescope`), and a member's model reads its declared
type and its reduct as one value at every valuation
([structure `FormerDeclared` in `ConLeche/Model/Inductives/FormerInEnv.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/FormerInEnv.lean#L29)).

Three limits are verdicts. A declaration at a name a literal's meaning reads (`Nat`, `Nat.zero`,
`Nat.succ`, `String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat`) has the
shape that meaning reads or is declined at the declaration, whether or not the stream uses a
literal; what is checked there is read at a literal's use only as the names being stored
([function `litShapeOk` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L384)).
A `Bool` stored at a definition is declined, since the frontend puts a stream's `Bool` first.
A nested occurrence whose container, or a member of
the container's block, is def-headed and is not among the families the block's
constructor types show syntactically is rejected.

### The installer, step by step

The steps below are in the order the checker runs them. Notation: the
block's members are `T_1 … T_k` with parameters `p⃗`; a class is written
`I us Ds` (an inductive type, its universe levels, its parameter
arguments). A *frame* is one type whose constructors are being checked:
the block itself (the root frame) or a container instantiation met in a
field. Frames nest, so the positivity check carries a stack of them.

**1. Shape.** Split the block into type formers `T_1 … T_k` with one
parameter count, their constructors, and the recursors. Member names
and constructor names are distinct. `isRec` is the official kernel's
syntactic test: some member occurs in a constructor's binder domain.

**2. Type formers** (in the environment `env` before the block).
* Each `T_m` type-checks, and its type, in weak head normal form, is
  `Π (p⃗ : P⃗) (indices), Sort s_m`.
* Every member's parameter domains are definitionally equal to
  `T_1`'s, and every `s_m` is equivalent to `s_1`, called `s`.
* `env1` is `env` plus all type formers, with the η and K
  capability flags computed from `isRec`.

**3. Constructors** (in `env1`), stored as declared.
* Each constructor of `T_m` type-checks, and its type is
  `Π p⃗ (fields), T_m p⃗ idx`, with parameter domains definitionally
  equal to `T_m`'s.
* Every field's sort is at most `s`. In a `Prop` block with a large
  eliminator, every field is a proof or one of the result's index
  expressions (the subsingleton criterion).

**4. Classes** (in `env1`).
* Read off the stream's recursor types, without checking yet: the
  classes (one per motive `∀ ı⃗ (t : I us Ds ı⃗), Sort ℓ`), the layout of
  the shared prefix (the motives, the minor premises and each minor
  premise's inductive hypotheses) and the class of every recursor
  ([function `classRead` in `ConLeche/Kernel/Inductives/ClassRead.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/ClassRead.lean#L130)).
  What is read here is only a guess; the rest of this step and step 8
  check it.
* Every class, its parameter arguments `Ds` moved to the block's
  parameters, is checked as a major premise:
  * a member class is `T_m` at the block's levels and parameters, one
    class per member;
  * an outside class names a stored inductive type other than `Quot`;
    its `Ds` mention only parameters and mention a member (the official
    kernel's nested-occurrence test); its sort is equivalent to `s`;
    `Ds` and `I us Ds` type-check.

**5. Positivity** (in `env1`).
* First, per constructor, on its stored type: every occurrence of a
  member is `T_j` at the block's levels applied to exactly `p⃗`, and no
  parameter's domain mentions a member (the official kernel's
  uniform-parameters check).
* Then the members, as the root frame: `CTORS` of the block's
  constructors, at the instance `(T⃗, the block's levels, p⃗)`, with
  holes `X⃗`, where `X_j` stands for `T_j p⃗`, a family over `T_j`'s
  indices.
* Then every outside class `I us Ds`: `CONT(I, us, Ds)` with an empty
  frame stack.

The three procedures:

*`POS(e)`* classifies one field type `e`. Let `w` be the weak head
normal form of `e`:

| `w` is … | then |
|---|---|
| free of members and holes | an ordinary field |
| `Π a, b` | reject if `a` mentions a member or a hole, else `POS(b)` |
| `H idx`, `H` a hole, `idx` free of holes, fully applied | a recursive field (a root hole `X_j`) or a field of the container being checked (a frame's hole `Y_j`) |
| `C us Ds idx`, `C` a stored inductive type, not a member, not `Quot` | `CONT(C, us, Ds)`, provided `Ds` has no local variables, `idx` no holes, the application is full, `C`'s level count is right, `C`'s index telescope at `Ds` mentions no member or hole, and `C`'s sort is equivalent to `s` |
| anything else | reject (a non-valid occurrence) |

*`CONT(C, us, Ds)`* checks the container instance `(C, us, Ds)`:
1. If that instance is already being checked further down the frame
   stack, reject: the instantiation was reached again through
   reduction.
2. If it was checked before and `Ds` mentions no hole, it is done.
3. Otherwise take `C`'s whole mutual block; each member's application
   `C_j q⃗` to its parameters becomes a fresh hole `Y_j`, typed by
   `C_j`'s type former at `Ds` (each such former is checked at `Ds` as
   in the table above).
4. `C us Ds` type-checks.
5. Run `CTORS` of that block's constructors at the instance, with the
   holes `Y⃗`, as a new frame.
6. Remember the block's instances as checked, if `Ds` mentions no hole.

*`CTORS`* is the one constructor loop, for the root and for every
frame. For each constructor:
1. Take its stored type at the instance's levels and replace every
   application of a block member to the parameters by its hole —
   before the parameters are instantiated at the instance's, so no
   β-step is involved — and type-check the result.
2. Run `POS` on every field.
3. No later field, and not the result, may depend on a field that is
   not ordinary.
4. The result is headed by a hole, with hole-free indices.
5. Record the constructor's normal form at the instance, each hole
   read back as the application it stands for, in a table local to
   the install.

**6. Tail.** The index sorts are read; `env2` is `env1` plus the
constructors.

**7. Generating the recursors** (in `env2`), from the classes and the
table of step 5, as the official kernel's `mk_rec_infos` and
`mk_rec_rules` do.
* Fixed by the checker: the universe parameters (the block's, with one
  elimination level in front for a large eliminator); the names
  `T_m.rec` for member classes and `T_1.rec_1 … T_1.rec_n` for the
  others; which constructors belong to which recursor.
* The stream's recursor types type-check.
* A large eliminator on a block that may be a `Prop` requires one
  member, at most one constructor and no outside class (the official
  kernel's `elim_only_at_universe_zero`).
* For each class and each of its constructors `x`: the table's entries
  for `x` at an instance the class matches (levels equivalent,
  parameters definitionally equal with the members abstracted); the
  first is the *reference entry*. The inductive hypotheses of `x`'s
  minor premise are exactly the reference entry's recursive fields,
  one each.
* The shared prefix: the parameters, then per slot either a motive
  `∀ ı⃗ (t : I us Ds ı⃗), Sort ℓ` or a minor premise
  `∀ (f⃗ : x's declared fields) (ih_i : ∀ a⃗, motive_t e⃗ (f_i a⃗)), motive_c (x's result indices) (x Ds f⃗)`,
  with `a⃗` and `e⃗` taken from the reference entry's field `i`.
* Each recursor, for a class `c`, has the type
  `Π prefix (ı⃗ : c's index telescope) (t : I us Ds ı⃗), motive_c ı⃗ t`,
  and for each constructor `x` the rule
  `λ prefix f⃗, minor_x f⃗ (λ a⃗, rec_t prefix e⃗ (f_i a⃗)) …`, where
  `rec_t` is the recursor for the inductive hypothesis's class
  (reject if there is none).

**8. The recursor check.**
* Each generated type type-checks as a constant and is definitionally
  equal to the stream's recursor type.
* Every generated rule's constants are resolved, and
  it is type-checked in `env2` plus the generated recursors without
  rules.
* The stream's recursors agree with the generated ones: each type
  binder by binder, each rule's right-hand side up to definitional
  equality, compared at `env2` plus the generated recursors with their
  rules.
* `env3` is `env2` plus the stream's recursors, at the generated
  recursors' firing data (an outside class's rules fire at its
  instantiation), plus the projection tables of structure-like members.

**Checks made for the proof alone.** Three checks have no counterpart
in the official kernel; they are there because the proof reads them:
* in step 5, at a `Type` block, the field sorts of the root frame's
  normal forms are at most `s` with the holes in place;
* in `CTORS` at the root, the constructor with its members replaced by
  holes is type-checked with the holes in context (the official kernel
  type-checks only the declared constructor, step 3);
* in step 7, at every table entry of a constructor, every recursive
  field has the reference entry's telescope, head and indices, and a
  class matching its inductive hypothesis's.

Where the steps live: the entry is
[function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L153);
steps 1–5 are
[function `checkBlockPass` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L52),
the constructor check of step 3 is
[function `checkSumCtor` in `ConLeche/Kernel/Inductives/SumInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/SumInstall.lean#L76),
step 4 is
[function `checkBlockClasses` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L522),
with a class's parameters moved in
[function `classKeyOf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L508);
`POS` is
[function `nestPos` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L910),
its hole lookup
[function `nestHoleAt` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L468),
`CONT` is
[function `nestContKey`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L852),
`CTORS` is
[function `nestCtors`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L688),
and the uniform-parameters check
[function `nestUniform`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1019);
step 6 is
[function `checkBlockTail` in `BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L103);
steps 7 and 8 are `genRecCheck` (above), with a constructor's
reference entry and the third proof-only check in
[function `classCtorOf` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L295),
the generated type and rule in
[function `classGenRecTy`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L177)
and
[function `classGenRule`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L189),
and their checks in
[function `classRecTyCheck`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L386)
and
[function `classRuleCheck`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L426).

## 6. The Nat operations

The official kernel accelerates the structural `Nat` operations on
literals with GMP. ConLeche does the same, but certifies the fast path
instead of trusting the operation's name.

* **Structural operations** (`Nat.add`, `sub`, `mul`, `pow`, `beq`,
  `ble`, and `pred` as a dependency;
  [the list `natOpNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L458-L466)):
  when a definition under one of these names arrives, its checked
  step certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([the account of the certified fast path in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L391-L408),
  [function `certifyNatEqs` in `ConLeche/Kernel/Checker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Checker.lean#L105-L112)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The operations a definition's recurrences mention (`Nat.add` for
  `Nat.mul`) need only be stored: at a certified operation's name
  nothing but a definition is accepted, and that definition's own step
  pins its type and certifies its recurrences.
  The model side states the operation's law at its stored name,
  whatever kind of constant is stored there (the fast path fires by
  name), reads the operation's membership off its pinned type shape
  and proves the literal semantics from the certified recurrences
  ([theorem `natOps_install` in `ConLeche/Model/NatEqs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/NatEqs.lean#L1046)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`;
  [the list `natDivModNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L479))
  are defined by well-founded recursion and have no recurrence the
  kernel can check directly. The binary embeds *pinned* copies of
  several supported toolchains' own definitions of each operation,
  each with its pinned *certificate theorems* — `Nat.ble`-guarded
  characterisations of the operation whose proof terms were produced
  by Lean itself at pin-generation time. The install tries the pins in
  order and uses the first whose pinned types of `Decidable.rec` and
  `Decidable.casesOn` (the constants the certificates use whose types
  differ between the supported toolchains) are definitionally equal to
  the stream's, whose copy is definitionally equal to the stream's
  definition, and whose certificates check, as theorem declarations,
  without installing them; each step is a yes-or-no comparison, so
  no error is caught, and a stream matching none of them declines
  ([the pin module `ConLeche/Kernel/NatOpPins.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16),
  [the certificate library `ConLeche/PinGen/Certs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/PinGen/Certs.lean#L7-L18)).
  The pins are committed per toolchain under `pins/`, each generated
  on its toolchain with `lake exe natop-pins-export`. Which list the
  gate tries is the fold's own argument rather than a constant inside
  it, and the model side reads none of it — it is stated for an
  arbitrary variant, because what it consumes is the certificates'
  verdict in the accepted environment and not where the matched
  variant came from:
  [theorem `divMod_install` in `ConLeche/Model/DivModCert.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/DivModCert.lean#L1968).
  That is why the two statements of §1 quantify over the list: the pins
  buy accepted `Nat.div` streams, never consistency.
* **The maximum `Nat` size.** As the official kernel does, the checker
  refuses a `Nat` numeral larger than a byte bound (128 MiB unless
  `--max-nat-size` says otherwise), measured as the official kernel
  measures it: 8 bytes per started 64 bits, at least 8. A literal is
  refused where it is inferred, the result of `Nat.succ`, `Nat.add`,
  `Nat.sub` or `Nat.mul` once computed, and `Nat.pow` and
  `Nat.shiftLeft` before computing, from their operands: `a ^ b` when
  `a > 1` and the size of `a` times `b` exceeds the maximum size, `a <<< b`
  when `a > 0` and the size of `a` plus `b / 8` plus 1 does; both also
  refuse a second argument that does not fit in 32 bits. A refusal
  rejects the declaration
  ([function `natOpRefusal` in `ConLeche/Cached/StateC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/StateC.lean#L227-L240)).
  Within the maximum size every operation folds, whatever the exponent:
  the specification's reduct is the computation itself
  ([function `natOpResult` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L589-L609)),
  and the bound is the cached core's alone, since a refusal only
  throws.
* **`Bool`.** `Nat.beq` and `Nat.ble` return `Bool.true` or
  `Bool.false`, and the well-founded operations' certificates are
  guarded by `Nat.ble`, so these operations install only once `Bool`
  and its two constructors are stored, with no universe parameters,
  the constructors at the type `Bool` itself, and with `Bool : Type`
  ([function `natOpGuard` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L611-L638),
  [function `natOpCod` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L669-L676)).
  That is the only reason the checker knows the name. `Bool` is not
  pinned: it is the stream's own block, installed like any other, and
  nothing depends on what it denotes — the fast path's result is the
  constant `Bool.true` or `Bool.false`, and the model proves from the
  certified recurrences that the operation's application denotes
  whatever that constant denotes. (The compiler-trust axiom
  `Lean.ofReduceBool` of §8 likewise asks for a `Bool` of the standard
  shape.)
* **Order independence.** The certificates are spelled over the
  structural operations, `Bool` and the basis blocks, which an export
  may emit in any order. The checker therefore carries a small built-in
  prelude: the pinned basis blocks, `Bool` and the pinned `And`
  (§5), as the toolchain exports them. One pure pass between the parse and the fold puts every
  prelude declaration at the front of the records — the stream's own
  record where the stream has one, the prelude's copy only where it has
  none — and moves the structural operations a pinned operation's
  certificates are spelled over (`Nat.ble`, `Nat.sub`, `Nat.mul`),
  which are not in its own dependency closure, ahead of it when the
  stream has them later
  ([`preparePrelude` in `ConLeche/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Prepare.lean#L168-L175),
  [the reordering pass `ConLeche/Frontend/NatOpGround.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/NatOpGround.lean#L8-L25)).
  Both are reorderings of the parsed records below the verified fold,
  and that is a theorem about them: the prepared records are a
  permutation of the file's plus prelude records the file did not
  declare
  ([theorem `preparePrelude_perm` in `ConLeche/Verify/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L171-L176)).

## 7. The set-theory assumption

Everything is parametric in a class
([class `SetTheory` in `ConLeche/SetTheory/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L95-L156)):
membership, extensionality, pairing, union, power set, regularity,
replacement for arbitrary Lean functions, and an ω-chain of universes,
each a Tarski–Grothendieck universe
([predicate `IsTGUniverse` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L89))
and a member of the next. Infinity is derivable; choice is inherited
from the meta-logic. The derived operations the model uses live in
`ConLeche/SetTheory/Derive/*`.

The interface is instantiated in a separate Lake package,
`bridge/lean4lean-model`, on Mathlib's `ZFSet` from the ω-many
inaccessible cardinals hypothesis of Carneiro's consistency analysis of
Lean
([theorem `carneiro_implies_conleche` in `bridge/lean4lean-model/ConLecheBridge/Carneiro.lean`](https://github.com/leanprover/con-leche/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202)).
So the assumption is no stronger than the one already accepted for
Lean's own consistency. The main repository does not depend on Mathlib;
the bridge builds in its own CI job.

**Why this does not contradict Gödel.** The theorem is proved in Lean
and says that a Lean kernel checker never accepts a proof of `False`,
which sounds like Lean proving its own consistency. It is not: the
statement is relative to a model of the `SetTheory` interface, and the
existence of such a model is exactly the assumption Lean cannot
discharge about itself. Lean's own universes provide any *finite*
prefix of the universe chain, but never the whole ω-chain at once,
because a universe level is not a term. So what the theorem shows is
"if there is a set-theoretic universe with ω many Grothendieck
universes, then Lean's kernel rules, as this checker implements them,
are consistent", and that hypothesis sits strictly above Lean's own
strength, as Carneiro's analysis shows and the bridge makes precise.
This is the standard shape of a relative consistency proof, and the
place where Gödel's theorem is respected is the one hypothesis the
proof cannot remove.

## 8. Axioms

A stream may use exactly the standard axioms `propext` and
`Classical.choice`, after their types and the shapes of the inductives
they quantify over are pinned to the toolchain's
([the pinned standard axioms in `ConLeche/Kernel/StdAxioms.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/StdAxioms.lean#L33-L37));
both are true in the model, `propext` by extensionality of
propositions and `Classical.choice` by global choice. `Quot.sound` is
part of the pinned `Quot` block. Any other axiom declaration is a
positive decline at its own record, with one tolerated exception:
`sorryAx`. An export declares that axiom whenever the module it came
from mentions `sorry`, whether or not anything uses it, so its record
is checked for well-formedness and then installs nothing — there is no
set model for it and there cannot be one. A stream that merely
declares it is therefore accepted; a stream that *uses* it declines, at
the record that uses it. Any other declaration at its name is
rejected.

The compiler-trust family, `Lean.trustCompiler`, `Lean.reduceBool`,
`Lean.reduceNat` and the axioms `Lean.ofReduceBool` and
`Lean.ofReduceNat`, is neither rejected nor trusted: `trustCompiler`
installs as an opaque with value `True.intro`, the two reduce
operations install as ordinary opaques pinned to the identity
function (any other declaration at their names is rejected, as at a
certified operation's name), and the two axioms are accepted only after the install
certifies, by definitional equality, that the stored reduce operation
is the identity, at which point each axiom's statement is an inhabited
proposition in the model
([the compiler-trust family in `ConLeche/Kernel/TrustAxioms.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TrustAxioms.lean#L9-L38)).
Proofs by `native_decide` and `bv_decide` are declined: each such
proof adds an axiom of its own to the environment, recording the
result the native evaluator computed, and that axiom is not a pinned
one, so the stream declines at its record. The message names the tactic,
read off the axiom's name (`<declaration>._native.<tactic>.ax_…`, as
`decide +native`, `native_decide` and `bv_decide` name it). ConLeche never runs native
code and never evaluates a decision procedure on a proof's behalf.
(The `ofReduceBool` mechanism above is the older, deprecated route to
the same trust, kept only because streams from the toolchain still
declare it.)

## 9. What the theorem does not cover

* The frontend. The theorem is about the list of declarations the
  fold receives, not about the export file. The decoder emits the
  file's records and nothing else; between it and the fold sit pure
  transformations of that list. Two are reorderings, and a theorem says
  so (`preparePrelude`, §6): the declarations the prelude names are
  moved to the front, the prelude's own copy filling in only what the
  file does not declare, and the structural operations a pinned Nat
  operation's certificates mention are moved ahead of it. Nothing is
  rewritten, and nothing is added but the prelude records the file
  lacks.
  Two guarantees have to be kept apart
  here. What §5 and §6 establish is that everything the frontend
  hands over is checked: the prelude's records and a Nat operation's
  certificates are ordinary declarations to the fold. What the
  frontend does *not* establish is that the list it hands over means
  the same as the export: the decoder is written to be
  meaning-preserving, but that is a review claim, not a theorem.
* What Lean makes of an `.olean` file. The theorem is about the files as
  `decodeModuleSpec` reads them; that Lean's own loader reads them the
  same way is tested (`tests/olean-compare.sh`, on `Init`), not proved.
  `--olean` reads each module's private view and does not compare a
  module's files with each other, so the theorem says nothing about the
  exported view that a `module` importing it sees. Beyond the format
  version and the GMP flag, nothing says which toolchain wrote a file.
  With `--constant`, only the named constants and what they mention are
  checked.
* The runtime's IO. The binary is the driver's generic code at `IO`;
  the theorems are about its outcomes in the model of §2. Assumed: that
  the binary's file operations give the model's answers on one snapshot
  of the files — the same value where the model has one, an exception
  where it has none, a read of an open file the next bytes of the
  file, fewer only at its end (`IO.FS.Handle.read`); that the
  actions passed to `liftIO` (output, the clock, `/proc/self/status`,
  the threads and the computations on them) do not change what the
  file operations see and do not end the process with exit code 0 (an
  abnormal or nonzero end is harmless: that run has no exit 0 to
  explain); and that Lean's compiler and runtime run the
  code as written. `tests/trust-surface.sh` checks, textually, that
  the modules written against the class reach the runtime only through
  its operations and the arguments of `liftIO`, and, stricter than the
  assumption needs, that
  `IO.Process.exit` appears only in `main`, which with
  `enableAbortOnNonlinear` is all `Main.lean` declares. Those few lines
  are read, not proved; the theorems cover `runArgs`, at the arguments `-- <file>`, `--olean --search-path=<dirs> -- <root>`, `--olean --module --search-path=<dirs> -- <root>`, `--olean --modular --search-path=<dirs> -- <root>` and `--check-graph --search-path=<dirs> -- <root>`; other flags and `--help` are not
  covered. The scheduler (`--schedule`), which no theorem is about, starts processes of the
  binary, kills its own children and appends to its log under `liftIO`; the trust-surface gate
  confines processes, kills and file writes to `ConLeche/Driver/Schedule/Run.lean`. A statement about several runs assumes one snapshot for all of them: the files do
  not change while the runs read them. The checker carries one C function of its own, the
  hash of a `Nat` literal of 2^64 and more (`native/nat_hash.c`: all its 64-bit words
  mixed, Lean's own fix of the literal hash, vendored until the toolchain ships it); the
  proofs see it as an opaque function of the number, so the assumption is that it is one.
  It and the build file `lakefile.lean` are pinned by content in the trust-surface gate.
* `--trusted` mode.
* Non-acceptance: a decline or a reject carries no claim. The verdict
  line reports the count of accepted stream records.
* Four places where the checker deliberately accepts more than the
  official kernel: a semantic comparison of universe levels; a
  proof-irrelevance fall-through; the large eliminator of a
  single-constructor block whose result sort can be zero — where the
  official kernel generates only the small one, this checker takes the
  subsingleton case under a per-field criterion; and the
  `And` rescue of §3. All four are covered by the soundness proof.
  §14 lists every deliberate departure from the official kernel.

## 10. Naming conventions

Every marker a reader has to know is in this table; **no suffix not
listed here carries meaning**.

| marker | reading |
|---|---|
| `C` | the *cached* checker's twin of a pure definition (`checkDeclC`, `CoreC`, `Expr.instantiate1C`, `SimC`) — the implementation that ships; there is one `Expr` type and one `Declaration` type, so the marker is on the function, never on the type |
| `I` | the variant that also handles an inductive family's index arguments (`checkStructFieldSortsI`) |
| `F` | stated over `FEnv`, the environment together with its lookup index (`natLitSupportedF`) |
| `D` | the direct parse and the functions over its output (`parseExportD`) |
| `AV` | a `Term` spelled by the semantic and model tiers (`sumTyAV`, `mkPisAV`) |
| `WF` | well-formedness (`EnvWF`, `BlockWF`) |
| `_pure` / `_cached` | the final theorems over the pure fueled fold and over the cached fold `checkDecls` |

A few words name things rather than tiers. Every inductive block
that is not pinned is installed by one installer (`checkBlock`,
`Kernel/Inductives/Block*.lean`), whose model is a least fixed point
and which generates the block's recursors. The `Struct*` and `Sum*` files inside
those directories are parts of it, not separate routes: `Sum*` holds
the type-former and constructor stages, `Struct*` the projection tables
of structure-like members and the syntactic pieces of the generated
recursors. `Fueled` marks a
record-parameterised helper applied to the pure functions at a fuel
(`Verify/Knot.lean`).

**The module system.** Every file in the build carries the
`module` header, so a declaration and an import are private unless said
otherwise. The rule that decides which: *checker code is exposed, because
it is the subject of the proofs* — `Kernel/*`, `Cached/*`, `Frontend/*`,
`Driver/*` and `Main.lean` each open one `@[expose] public section`, since the
Verify and Model tiers unfold their bodies — while *proof code is private
by default*: `Model/*` and `Verify/*` open a plain `public section`, so a
proof file's bodies and proof terms are both private and only its statements
are interface.  The term language, the `SetTheory` interface, the pure
set constructions and the denotation (`Term/*`, `SetTheory/*`, `SetModel/*`,
`Semantics/*`) keep the blanket for the same reason the checker does — the
tiers above unfold them. The only `import all` lines read toolchain
bodies the module system hides (`Init.Util`'s `withPtrEq`,
`Init.Data.Repr`, the Nat-op certificate generator's `Init.Data.Nat.*`),
and every such line carries its reason.

## 11. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The binary's entry point: the plumbing around `runArgs` at `IO`, followed by the exit. |
| `ConLeche/Driver/` | The proof-carrying IO driver: the index build and the check phase's worker pool (`CheckPool.lean`), the rounds parse's owner threads (`OwnerParse.lean`), the stream parse over the IO class's folds (`StreamParse.lean`), the end-of-run statistics (`Stats.lean`), `checkDeclsIO` (`Run.lean`), a module's context for checking it on its own (`Reach.lean`), the check of one module against it (`Worker.lean`), the tables a run reads up front, each module located once (`Tables.lean`), the import graph check (`Graph.lean`), every module of a closure in one process (`Modular.lean`) and by one worker process each (`Schedule.lean`, the subtree `Schedule/`: the policy, the worker, the log, the status, `/proc` and the run), the driver's sequencing generic in the IO class (`CheckMain.lean`), the run of a request (`Dispatch.lean`) and the command line and `runArgs` over them (`Cli.lean`). Checker code, like `Kernel/*`; the one tier besides `Main.lean` that may import `ConLeche/Verify/*`. |
| `ConLeche/Kernel/` | The specification, the pure checker the proofs are about: `Expr`/`Level`/`Name`, what a declaration adds (`Install.lean`), `PropWhen`, the mutually recursive core of reduction, inference and conversion (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the inductive installer (`Inductives/`: the recogniser `BlockShape.lean`, the positivity check `Positivity.lean`, the entry `checkBlock` with its constructor stages (`Sum*`) and projection tables (`Struct*`), the recursor generator and check `GenRec.lean`, and `ClassRead.lean`, which reads the classes off the stream's recursor types without checking them), the Nat-op pins, and `natBigHash` (`NatHash.lean`), the hash of a big `Nat` literal, the one function in C (`native/nat_hash.c`). Imports no theory module. The binary runs the cached tier's twins in its place; of this tier it runs only the shared helpers the reach gate lists (§12). |
| `ConLeche/Cached/` | The shipped cached checker: hashed expressions, memo state, the cached core and declaration step, the parsed-record step (`ParsedC.lean`), the cached twins of the whole inductive check (`Ind*.lean`: the formers and constructors, positivity, the classes, the recursor stage and the tail), each related to its specification in `Kernel/Inductives/` by an equation or a simulation triple (`Verify/Cached/Ind*C.lean`, `GenRecC.lean`), the declaration fold `checkDecls` and its accepting runs (`Decls.lean`), the index of a stream and a record's job (`StreamIndex.lean`). |
| `ConLeche/Frontend/` | The export parser: the dialect's byte recogniser and syntax records (`Scan/`) and the semantic layer over them (`ExportC.lean`), which decodes the file's records and nothing else; the checker's IO class, its model over a snapshot of the files, the binary's instance and the folds over a file handle's reads (`CheckerIO.lean`); the serial streaming driver and a chunk's scan into syntax records apart from their application (`Stream.lean`); the rounds parse's counters and finished tables (`Rounds.lean`) and its rounds (`RoundsWork.lean`); the preparation of the fold's input (`Prepare.lean`, with the built-in prelude of `Prelude.lean` and the reordering of `NatOpGround.lean`, which moves what a pinned Nat operation's certificates mention ahead of it); the `.olean` reader (`Olean.lean`, the interface, over `Olean/`: the byte region `Region.lean`, the specification decoder `Spec.lean`, the fast one `Fast.lean`, the sparse one `Sparse.lean`, the imports off a file's start `Header.lean`, the reads of a part of a region `Reads.lean`, a module's views `View.lean` and their checks against each other `Module.lean`, the files through the IO class `Files.lean`, the closure `Closure.lean`, the merge `Merge.lean`, the emission `Emit.lean`, the records `Records.lean`, the header fixpoint `Levels.lean`, the loaded names and the clash rule `Index.lean`, and one group's record `Group.lean`). |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/Term/` | The term language the denotation targets and the interpretation reads, its substitution operations and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and nested tuples, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The interpretation, the semantic invariant, the semantics of inductive blocks, the declaration-level facts. |
| `ConLeche/Rules/` | The relational description of the core checker: mutually inductive relations over the checker's own `Expr` — reduction, definitional equality, η-expansion, unit-likeness, type inference (checking and infer-only), and the certificate checks — with fuel, unfolding heuristics and dispatch order out of sight (`Rel.lean`), the derived rules (`Derived.lean`), and the derivations at an environment holding some definitions as their statements, which are derivations at the environment holding them with their values (`Refine.lean`). Imports the fuel-free helpers of the kernel and nothing else of it. |
| `ConLeche/Verify/Rules/` | The bridge: an accepting run of a kernel function, at any fuel, yields a derivation (`Bridge.lean`, from one step theorem per entry point and the certificate bridges); composed with the rules at a refinement, an accepting run at an environment holding some definitions as their statements, a former's reduced telescope included, is a derivation at the environment holding their values (`Refine.lean`). |
| `ConLeche/Model/` | The graded set model of the checker: the environment invariant and its laws (`Env/`), the facts about the stored-term reading `denote` that read the environment invariant (`Reading/`), the claims, the soundness of the rules tier's derivations (`Rules/`: the motives, the environment inputs, one lemma per rule over shared kits, the master induction, and the recomposition of the claims from the bridge), the run-stated remainder the declaration fold reads (`Tiers.lean`), the declaration step, the inductive installs (`Inductives/`, `Ind*`), the Nat-op certification, the final theorems (`Capstone.lean`), and the model read through the statement's relation (`Denotes.lean`). |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: well-formedness, scoping, the stored-term reading `denote` and its metatheory (`Denote.lean`, `Denote/`: inversions, depth shift, instantiation, closedness, environment extension), the cached-to-pure simulation (`Cached/`: the core's congruence in the lookup (`KnotCongr.lean`), the block tail's in-place pushes (`BlockOverlay.lean`), every stage's congruence in the index (`ViewCongr.lean`), every job passing is an accept of the fold (`StreamIndex.lean`, which `ConLeche/Driver/CheckPool.lean` imports), and a record's constants, tables and names as the worker's reach computes them, the cached twins in the specification's place (`DeclNames.lean`, which `ConLeche/Driver/Reach.lean` imports)), the inductive installer's kernel-side invariants (`Inductives/`), and the parser's (`Frontend/`: line locality, the parse as a line fold, chunk independence, what a line does to the parse state, the template's lines, the characterisation of the serial fold over a stream that binds in increasing order, good entries and the tables they make (`Good.lean`), and that the rounds keep good entries and a window is one more stretch of the serial parse (`RoundsWork.lean`, `Rounds.lean`), the runs of the IO model and the folds over a file's reads in it (`ModelIO.lean`), that the stream's reads in it put together are the file (`StreamModel.lean`), and the `.olean` reader's decoders and reads (`Olean/`)), and all of `main` in the IO model at the arguments `-- <file>` (`Driver/Main.lean`), with an `--olean` run's check phase (`Driver/Oleans.lean`), a module's context (`Driver/Reach.lean`), where it read each record (`Driver/ReachFrom.lean`) and what that record presents (`Driver/Provenance.lean`, `Driver/Groups.lean`), one module checked alone (`Driver/Worker.lean`), reads answered from tables refining the files' (`Driver/Shared.lean`), every module of a closure in one process (`Driver/Modular.lean`) and the import graph check's validation (`Driver/Graph.lean`). |
| `ConLeche/Accepts.lean` | The file-level vocabulary of the statement: `jsonWithTheoremFalse`, the whole-file template of one JSON file that declares a theorem of type `False`. |
| `ConLeche/Denotes.lean` | The statement's semantics: what a term denotes (`Denotes`) and what a model of an environment is (`Model`); imports nothing from the proof tiers. |
| `ConLeche/Modular.lean`, `ConLeche/Modular/` | Modular checking's statement half: a module's context as the records its imports present, the local checks per home (`InterfaceOk`) and per importer (`ImportOk`), copies agreeing (`Agree`: one record, or two proofs of one statement); and the theorem over an abstract interface of models (`Modular/Generic.lean`, the whitepaper fragment's), whose instance for con-leche's models is `ConLeche/Model/Modular/`. |
| `ConLeche/Model/Modular/` | The modular theorem at con-leche's models: a module's own records installed on its context's model, keeping every context leaf and every proof's leaf the canonical proof (`ProofLeaves`, `Proofs.lean`, `Step.lean`); a context read from its sources, stated without modules (`Read.lean`), and derived from the local checks (`Valid.lean`); the context's model built from its sources' models, every law of a context constant read off its source's (`Restrict*.lean`); the instance of the abstract interface (`Instance.lean`) and the compatible family (`Main.lean`). |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The main theorem and the main corollary — about the environment the fold returns and about the chunks the binary reads — and the main corollary lifted to the driver; and the challenge module stating the first two with `sorry`, the statements the comparator pair certifies, kept as its own library and compared with the solution by `tests/challenge.sh`. |
| `native/` | `nat_hash.c`: the hash of a `Nat` literal of 2^64 and more, all its 64-bit words mixed; Lean's own function, vendored until the toolchain ships it. Compiled and linked by `lakefile.lean`. |
| `bridge/lean4lean-model/` | The Mathlib bridge instantiating the interface. |
| `tests/` | The Lean test library (the axiom pin), the arena and end-to-end fixtures with their expectation files, and the gate scripts. |
| `scripts/` | Fixture generators, the PERF battery, stream tools. |

## 12. Gates

`tests/arena.sh` is the standard battery: the layering fence
(`tests/layering.sh`: no base module imports the model tier, no
implementation module (`Kernel/*`, `Cached/*`, `Frontend/*`) imports the
theory, the proof-carrying driver (`Driver/*`, `Main.lean`) imports
`Verify/*` and nothing else of the theory, and no module of the
rules tier of §4 has the pure implementation in the environment it
elaborates in — its direct imports plus, transitively, their
`public import`s, computed from source; the implementation modules
that the base tiers' own re-exports still carry in are listed in the
script and the list may only shrink; and the `.olean` reader imports only
itself and a few base types, only `Files` and `Closure` reach the IO class,
only `Records` the record builder, and the rest of the checker imports only its
interface, `Olean.lean`), the trust-surface scan (`tests/trust-surface.sh`: no `unsafe`, `implemented_by`, `extern` or `native_decide` outside an allowlist, and, textually, no module written against the IO class reaching the runtime but through the class's file operations and the arguments of `liftIO`, and `IO.Process.exit` only in `main`; the build file and the native sources pinned by content), the plain-tier reach gate
(`tests/plain-reach.sh`: every specification-tier definition the compiled binary
reaches from `main` is listed, with its reason, in `tests/plain-reach-allow.txt`, and a
listed one no longer reached fails too; a definition with a cached twin is reached by
nothing executed and is not listed), the
binary link gate (`tests/binary-link.sh`: the compiled binary links no module of the `Lean`
package, so no proof module the driver imports brings `Lean.Meta` along), the pin
dump freshness, the challenge comparison (`tests/challenge.sh`: the
challenge module builds with its `sorry` warnings and nothing else,
and every statement it makes is token-identical to the solution's),
the arena tutorial tests, the end-to-end fixtures and the legacy
binder-field fixtures with
pinned verdicts, the `.olean` gate (`tests/olean.sh`: the committed
fixtures and corrupted copies of them, each verdict pinned, with a home's read of its
parts and a module's reads of what it loads through `olean-compare --home` and `--reads`), the two readers
compared on `Init` (`tests/olean-compare.sh`), the display gate (three fixtures whose names and
`safety` field carry control sequences, run with `--progress=1`; no
raw control, bidi or zero-width character and no line starting with
`::` may reach the output), and the trusted-mode sweep. `lake test` builds the test library with the axiom pins. CI runs
both.

The links in this document are part of the battery: `tests/overview-links.sh`
extracts every linked segment into one text and compares it with
`tests/overview-links-expected.txt`, so moving or changing the cited
lines fails the gate and is the reminder to re-read the paragraph that
cites them and to run `tests/overview-links.sh --update`.

## 13. What the environment stores beyond Lean's

The checker's environment (`ConLeche.Env`, `ConLeche/Kernel/Env.lean`)
holds the declarations as the export gives them, plus the data below.
All of it is read off the declarations themselves. Running directly on a `Lean.Environment`
would mean computing the first group on use, or in a memo outside the
environment, and replacing the second by an on-demand computation.

**Derived per-constant data.** Each entry is either a field Lean
already stores, or a function of the inductive's and its constructors'
types.

| Where | Field | Lean's counterpart, or how it is computed |
|---|---|---|
| `IndCaps` | `all`, `nparams`, `nIdx`, `ctors` | `InductiveVal.all`, `numParams`, `numIndices`, `ctors` |
| `IndCaps` | `neverZero` | whether the former's stored type ends in a sort that is never zero at any level instantiation; read off the declared type at the family's install. The ι step's case split and the structure-η rescue read it before walking to the family's sort |
| `IndCaps` | `eta` | whether the family is structure-like (one constructor, no index, a block that is not recursive); read off the block. Structure η, the structure-η rescue and unit-likeness read the constructor and its counts off the family's projection table, at every field count: a family is unit-like where its constructor's fields are propositions or unit-like (always, without fields), and then all its inhabitants are definitionally equal |
| `ctorInfo` | `induct` | `ConstructorVal.induct`: the block member the constructor is declared under, set by the install; the constructor check has established that the constructor's declared type concludes in it. The ι step's case split, the rescues and η look the family up by it |
| `recInfo` | `majorIdx`, `rulePrefix` | sums of `RecursorVal.numParams`, `numMotives`, `numMinors`, `numIndices` |
| `RecRule` | `fire` | `.plain` for a recursor whose major premise is a member of its own block; for an auxiliary recursor of a nested block, `.nested lvls pins`, the levels and the parameter arguments of the recursor's major domain, read off its stored type and closed over the rule prefix (no lookup: the trailing arguments are the record's index variables) |

A rule stores what Lean's `RecursorRule` stores (constructor, field count,
right-hand side) and the firing mode above. The ι step reads the
right-hand side under its leading lambdas, one per argument of the recursor's
rule prefix and per field of the constructor, and substitutes those
arguments there at once, as Lean's kernel does since lean4 PR #10565: no
β-redex is built, so none becomes a memo key. Every stored rule has
those lambdas: the stored rules are checked for them, the generated ones are
built so. A recursor's K flag is its
record's (`RecursorVal.k`), which the block's check compares with the
generated recursor's. The constructor's parameter count and the structure-η
rescue's condition are read off the stored constructor, the family's
capabilities and its projection table where the rule fires. The family's
result sort is on no record that always has it: whether it is `Prop` or never
zero is read off the former's type where the question is asked.

**Projection tables.** For each structure `T` the installer stores one
projection table (a `ProjTable`, keyed by `T`) in the environment's
table component, beside the constants: for every field the projection's
result-type body (the type of `.proj T i`), read off the block's records. A table is visible exactly where its
structure is. Lean's kernel stores nothing for projections; it computes a
projection's type from the constructor's type when it meets one
(`infer_proj`). What `infer_proj` requires of a `Prop` structure, that the
field and every earlier field a later one uses are propositions, is checked
at the use here too
([function `checkProjGuard` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1207-L1208)),
from the stored constructor type at the environment of the use; nothing
about it is stored.

**Not counted.** The `FEnv` lookup indexes, with the two literal flags
they carry (whether `Nat` and string literals can be expanded), are a
performance device over the same data. The pinned basis blocks and the Nat-op pins are expected
shapes, compared against the input, so they are code. Some things are
stored with less than Lean keeps: a theorem without its value, an opaque
constant as an axiom.

## 14. Where the checker departs from the official kernel

The checker follows the official kernel's algorithm and order (§3,
§5). This section lists the deliberate departures from the current
release; each is described where its mechanism is.

**Ahead of the kernel logic renovation.** The official kernel's logic
renovation (lean4#14977) aims for a decidable definitional equality,
proofs that never have to be reduced, and complete level comparison.
Some of its changes are on lean4 master but in no release yet; others
are still planned. The checker already has these:
* Two proofs are compared by their types before either is reduced, so
  a proof without a normal form does not stop a comparison on which
  the released kernel loops (§3; lean4#15103, on master).
* A theorem's value is never unfolded, so no proof is reduced to
  decide a conversion (§3).
* A recursor's major premise is rescued from its type before it is
  reduced, and a K-like major whose rescue fails is not reduced at all
  (§3; the order of lean4#15371, on master, which also covers more
  structures than the checker does).
* The wider unit-like η (a Π-type into a unit-like type, a structure of
  propositions and unit-like fields) and the η of a partially applied
  constructor (§3, §13; lean4#15372 and lean4#15373, on master).
* Universe levels are compared semantically (§9; the planned complete
  level comparison).
* A single-constructor block whose result sort can be zero gets the
  large eliminator under a per-field criterion, where the released
  kernel generates only the small one (§9; the planned large
  elimination of sort-polymorphic structures).

Not yet followed: `Acc` and the other recursive predicates keep their
large eliminator (lean4#13851), `Quot` of a proposition stays a
proposition (lean4#15023), partial recursor applications are not
η-expanded (lean4#15374), and the inductive types' features are read
off their declarations rather than from explicit flags.

**It accepts more**, beyond the renovation. The soundness proof covers
each of these.
* Proof irrelevance falls through (§9).
* A major premise of `And.rec` is rescued from its type, since a
  theorem's value, being opaque, cannot be reduced to `And.intro` (§3).

**It rejects or declines more.**
* An axiom other than the standard ones declines, with the exceptions
  §8 names, and so does a proof by `native_decide` or `bv_decide` (§8).
* The well-founded `Nat` operations are accelerated only for a
  definition that matches a pin; a stream matching none of them
  declines (§6). The official kernel accelerates by name.
* The names the checker gives a meaning (the pinned basis types and
  `And`, the names a literal's meaning reads, `Bool`) must have the
  expected shape (§5).
* A block without recursor records is invalid input; the official
  kernel generates the recursors itself (§5).
* Any declaration at `Lean.reduceBool` or `Lean.reduceNat` other than
  the opaque constant, and any at `sorryAx` other than the axiom, is
  rejected (§8). Lean refuses these only through the declarations of
  its own `Init`.
* In modular checking (`--olean --module`), a module whose context
  gives a name it reads another meaning than the module it reads it
  from (name capture) is rejected (§2). Lean accepts such a module,
  and can then prove `False`.
* In modular checking, the files are untrusted input: a module's
  three parts must agree with each other, the context's records must
  pass their syntactic clauses (a constructor's family is the one its
  type concludes in; a recursor rule is written as a function of the
  rule prefix and the constructor's fields), and context records that
  read each other are rejected (§2). Lean's own output always passes
  these; the official kernel trusts the imported files.
* Where the opaque theorems and the rescue order of the renovation
  leave a conversion incomplete, the checker rejects what the released
  kernel accepts by reducing a proof (§3).

**The verdict is the same, the route differs.**
* When one side of a comparison is a closed, fully applied constructor
  application of a type that is never a proposition, has no η law and
  is not `Nat`, the other side is head-normalized at once. The official
  kernel does this only for `Bool.true` (§3).
* The structural `Nat` operations' fast path is certified at install
  rather than trusted by name (§6).
* A nested block is checked through its containers at their concrete
  instantiations, with no auxiliary mutual block (§5).
* The stream's recursors are installed once they agree with the
  generated ones; the official kernel installs its own (§5).
* A `Nat` literal's hash reads all its bits, as on lean4 master
  (lean4#16146); the released kernel hashes its low 64 bits, so its
  memo lookups among literals that agree there walk one bucket
  (lean4#15686) (§2).

**Checks that only the proof needs.**
* In verified mode: the full-grade types of the opened bodies at a
  λ/λ comparison and at η, and proof irrelevance between the K and
  `And` rescues' constructor applications and the major (§3).
* Three checks in the inductive installer (§5).
