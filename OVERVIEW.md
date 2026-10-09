# ConLeche: an overview of the proof

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to [`README.md`](./README.md), which is
> human-written and states the main theorem and its corollary in the
> maintainer's own words, with its own links into the source.
> This one is a guided tour of the verification, from the binary that
> runs to the set-theoretic assumption it rests on, with links into the
> source on `master`.

## 0. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format and
prints one verdict line:

```
con-leche [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
          [--progress[=<stride>]] FILE.ndjson
con-leche --help
```

That is every flag the binary takes. `--verified` is the default and
the mode the theorem is about; `--trusted` runs the same checker bodies
with the certification-only work switched off, is faster, and is
outside the theorem; `--jobs=<n>` sets the check phase's worker count
(below); `--no-mark-persistent` turns off the check phase's one-shot
mark of the installed environment (below), which changes no verdict and
is there to measure what the mark is worth;
`--progress[=<stride>]` turns on a heartbeat on stderr
(below); `--help` prints the usage text and exits 0
([the driver's usage text in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L47)).
Any other option is a usage error: the run reports it, prints the
usage text and exits 3 without reading its input, so a verdict's
provenance can be read off the invocation.

The exit code follows the lean kernel arena convention
([the exit-code mapping in `ConLeche/Driver/Run.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Run.lean#L37)):

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
theorem's guarantee. An out-of-memory condition also exits 1: it is the
Lean runtime's own panic — `INTERNAL PANIC: out of memory` on stderr,
then `exit(1)` — which no code of ours can catch, so the stderr message
is what tells it apart from a reject.

A run has two phases: the install phase installs the records in
stream order, and the check phase checks every recorded declaration
against the prefix of the installed environment it was installed at
(see §2). The flag `--jobs=<n>` runs both phases on `n` worker
threads; without it there is one worker per hardware thread. With more
than one worker the parse does not build an expression line that only
one theorem's value reads: each theorem's value is built in its own
check, from lines the parse keeps, and dropped after it. In the
install phase the workers install the records, each against a view of
the records before it, while the main thread commits them in stream
order; at `--jobs=1` the main thread installs everything, and the
check phase runs one worker with no shared counter and no result
table.
The check phase always runs on worker threads, never on the main
thread: its per-record memo state is allocated out of the running
thread's heap, and the main thread's heap is the one the parse and the
install have just fragmented, which at Mathlib scale costs the
single-worker run a factor of two in wall time at the same
instruction count. Each worker thread reserves about 1 GiB of address space (its stack
reservation; the resident set grows by about 25 MB per worker), so a
run under an address-space limit (`ulimit -v`) must lower the count
to what the limit affords — about ten workers under 16 GB. At every
worker count the installed environment is marked persistent once at
the phase boundary, which removes the atomic reference counting the
workers would otherwise pay on it and is worth 18–32 % of wall time on
the pool, growing with the worker count, and 3.5 % at one worker;
`--no-mark-persistent` turns it off. On more than one worker most of
that marking happens earlier: the records are marked before the
install pool starts (a serial walk, about 2.5 s on Mathlib) and each
install result by the worker that computed it, so the mark at the
phase boundary finds little left to do (about 0.1 s on Mathlib). The
verdict, and the declaration a rejection names, are the same at every
`n`: the results are walked in record order, so the first failing
record in fold order is the one reported. The flag
`--progress[=<stride>]` prints a heartbeat on stderr with one line
shape per phase — `install <i>/<N> <decl>` before every `stride`-th
declaration is installed, `check <done>/<M> <decl>` after every
`stride`-th completed check — bracketed by `parse done`, `install
done` (on more than one worker preceded by a `parallel install` line
with the install's own phases), `persistent mark`, `check done` and a
`done:` summary with the three phase
durations and the worker count (bare, the stride is 1); on more than
one worker, each `install` and `check` line ends with the number of
busy workers and the oldest record one of them is on, with its age.
With or without the flag, every run closes its stderr with a few
`stats:` lines: the phase times; per phase (the install pool or the
one-thread install, the check pool or its one worker) the wall time,
the worker count, the workers' busy time and utilisation (busy ÷
(workers × wall)) and, on more than one worker, the tail (from the
last record's start to the end of the phase, how many workers were
still busy then and their busy time inside it); the five slowest
installs and checks with their fold positions; and the peak resident
set. They cost two clock reads per record, kept per worker and merged
when the pool ends, and change neither stdout nor the exit code. The heartbeat
is printed between the steps of the one driver, which returns its
environment together with the proof that `checkDecls` — the function
the theorem is about — returns it (see §2), so a run with the flag is
covered exactly as a run without it, and so is a run on the pool.

## 1. What is proved

The statement is two theorems: one about the declaration fold
`checkDecls`, the function whose result the `con-leche` binary's
driver returns for a parsed export stream, and one about the chunks
the binary reads. The main theorem,
[`model_exists` in `ConLeche/MainTheorem.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L96-L99):

> For every model `V` of the `SetTheory` interface, every
> `Nat.div`/`Nat.mod` pin list `pins` and every list of declarations
> `ds`: if `checkDecls`, in the default `--verified` mode, accepts `ds`
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
variants this toolchain committed.

What a term denotes, and what a model is, are one short module a
reader can take in at one sitting: the relation
[`Denotes` in `ConLeche/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L134-L135),
one rule per syntax form on the checker's own terms — a bound variable
reads its environment, `Sort u` the universe chain, a constant its
set, an application the function's graph, a binder the dependent
product, or the truth value of its body when the checker annotated the
binder as proposition-valued — an annotation it may make only if the
body really denotes a truth value there — and the structure
[`Model` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L270-L290).
So every theorem the stream proves is true in the model, and the
theorem certifies every proposition annotation the checker stored.
Definitional equalities need no clause of their own, because the field
`eq_equality` covers them all: a definition's unfolding or an iota
rule, stated as a theorem proved by `rfl`, is a stored constant whose
type is `a = b`, `mem` puts that constant inside what the type
denotes, `eq_equality` says that set is the truth value of `⟦a⟧ = ⟦b⟧`,
and a truth value with a member is `{pt}`. So the two sides of every
accepted equation denote the same set.

The main corollary,
[`no_False_declaration` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L110-L117):

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

The corollary rests on a statement at the stream — the fold's input —
proved beside the fold
([`no_False_theorem_accepted` in `ConLeche/Verify/Cached/StreamThm.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamThm.lean#L206-L209)):

> … if any record of `ds` declares a theorem whose declared type is
> `False`, then `checkDecls` accepts `ds` with no environment at all.
> (`ds` is the array of records the parse returns and the fold folds;
> the proofs read it as a list, which costs nothing at run time.)

That follows from the theorem in a handful of lines, through the
environment in between. A theorem record is installed by statement,
under its own name, with the annotation of its declared type; the
annotation of a bare constant is that constant; and every later step
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
([`parseChunks_ok_parseBytes` in `ConLeche/Verify/Frontend/Chunks.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Chunks.lean#L353),
with the streaming reader's running byte count as the same guard the
wholesale parse applies up front); and the template's lines scan to
exactly the records the fold then forbids
([`parseChunks_jsonWithTheoremFalse` in `ConLeche/Verify/Frontend/FileFalse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/FileFalse.lean#L173)).
The preparation puts the built-in prelude's records first and moves
the definitions a pinned `Nat` operation's certificates are spelled
over ahead of it (§6); it is a permutation of the
parsed records plus the prelude's, so the record is still there
([`mem_preparePrelude` in `ConLeche/Verify/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L174)).

"Installed under its own name, with the annotation of its declared
type" is a claim in its own right, and it is proved in general:
[`checkDecls_consts` in `ConLeche/Model/StreamConsts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L764-L769)
says that whenever `checkDecls` accepts `ds`, every record of `ds` that
declares a constant — a definition, a theorem, an opaque, or an axiom
that is neither `sorryAx`, the axiom record that installs nothing, nor
`Quot.sound`, which the pinned quotient block installs
([`Declaration.Declares` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L613-L620))
— leaves a constant of that very name in the returned environment, with
the record's own level parameters and with the *annotation* of the
record's own type: the same term with every `let` inlined and the
binder data rewritten, and nothing else touched at all
([`AnnotOf` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L123-L124)).
A `basisDecl` record declares nothing of its own — it names one of the
checker's pinned basis blocks, and what is installed is the pins'.

The members of an inductive block are deliberately outside that claim,
and the module says why: a type former's telescope may be stored
reduced to weak head normal form, which is a definitional equality, not
an annotation, so the relation above would be false of it. The
constructors are stored as declared, but they are installed with their
block and are left out with it.

`checkDecls`
([function `checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L452-L457))
installs every declaration of `ds` first — a definition, theorem or
opaque annotated and pushed with its check recorded, everything else
checked in full as it is installed — and then checks every recorded
declaration against the prefix of the environment it was installed at.
The driver runs the same two phases with a heartbeat between the steps
and returns its environment together with a proof that `checkDecls`
returns it, so the success line is printed from an accept of
`checkDecls` and from nothing else, whatever the loops printed on the
way.

`False` is not read off the stream: the checker installs it from a
built-in pin, and a stream that declares `False` or `False.rec`
differently is rejected. The theorems use exactly Lean's three standard
axioms, `propext`, `Classical.choice` and `Quot.sound`, which the
[axiom pin in `tests/ConLecheTests/Axioms.lean`](https://github.com/leanprover/con-leche/blob/master/tests/ConLecheTests/Axioms.lean#L91-L95)
checks with `#print axioms` guards under `lake test`.

Everything below explains how those theorems are reached.

## 2. From the binary to the theorem

Read from the outside in:

1. **The driver** (`Main.lean`). The run parses the stream
   ([function `parseInput` in `ConLeche/Driver/Run.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Run.lean#L67))
   and runs the fold's two phases as two loops. The byte recogniser that reads each line of the
   stream is proved equal to a naive reference over `List UInt8`
   ([theorem `scanLineSpec_eq_scanLineFwd` in `ConLeche/Frontend/Scan/Equiv.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Scan/Equiv.lean#L1002)):
   the driver calls the reference, and the compiler runs the fast
   recogniser on the strength of that equality. The parse cuts its
   reads into chunks of whole lines and scans each chunk on a worker
   into one flat byte buffer (`ConLeche/Frontend/Flat.lean`: a tag byte
   and fixed-width fields per line, so that what crosses between the
   threads is a few objects, not one per line). At one worker the
   scanned lines are applied in order on one thread, each line's fields
   read where they are applied; a chunk's flat scan, applied, is the
   pure streaming parse's step over that chunk
   ([function `chunkStep` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/ExportC.lean#L642);
   [theorem `chunkStepF_of_encodes` in `ConLeche/Frontend/Pipeline.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Pipeline.lean#L472-L474)).
   With more workers the parse is lazy
   ([function `parseExportLazy` in `ConLeche/Driver/LazyParse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/LazyParse.lean#L548)):
   it reads and scans the whole stream, then a backward *sweep* over
   the scanned lines marks the expression lines the install reads — a
   declaration's statement, a definition's or opaque's value, an
   inductive block — and those that lines of more than one
   declaration's *region* read (the lines between two declaration
   lines). Only the marked lines are built, a window of chunks at a
   time: every chunk applies its lines on its own worker, deferring a
   line that reads an entry of another chunk of the window to a later
   round, until nothing is deferred; the window's tables then join the
   finished tables, and an unmarked line is bound to a placeholder.
   Neither the sweep nor the rounds are believed: every chunk is
   checked, line by line, against the finished tables at the counters
   the serial parse has there — a built line by the entry it must
   yield, a line not built by its references, which must be bound
   below the counters; the line is then kept, re-encoded, in a store,
   and a theorem's record carries a placeholder naming its value's
   index. A chunk that passes is one more step of the serial parse,
   its records related to the serial ones and its kept lines to the
   serial entries
   ([theorem `LGOK.chunk` in `ConLeche/Verify/Frontend/Lazy.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Lazy.lean#L724)).
   A window whose chunks or rounds meet anything unusual — an index
   below its table's counter, a line the serial parse fails at — is
   handed to the serial parse from the state the chunks before reached,
   rebuilt from the finished tables and the store, which gives the
   serial verdict at the serial line. Either way the parse returns its
   result with the proof that the pure streaming parse returns it, or
   returns records that stand for the records it returns, the
   placeholders for theorem values the serial parse's table holds.
   What the parser makes of a record
   — index resolution, the smart constructors — is the
   semantic layer the main corollary's line lemmas are about. The install loop
   ([function `installLoop` in `ConLeche/Driver/ParInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/ParInstall.lean#L158))
   takes every record, each from a fresh memo state, through the install step
   ([function `annotStepC` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L148-L151)):
   a definition or opaque is annotated and pushed with its check
   *recorded* — the annotated header and value and the number of
   constants installed before it — a theorem is installed by its
   statement alone (its header annotated, the stored constant carrying
   no value; the raw value is recorded for the check and never entered
   by this loop: a theorem is opaque to reduction), and
   an axiom, an inductive or
   basis block, and the pinned `Nat`-operation and `reduce*`
   declarations are checked in full as they are installed, by the
   fold's ordinary step. The loop carries the chain of its accepting
   steps, a proposition, and what it returns is an installed
   environment. On more than one worker the same run is built by a
   commit loop
   ([function `ParInstall.commitLoop` in `ConLeche/Driver/ParInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/ParInstall.lean#L833-L844))
   that adds one step per record in stream order — a builder thread
   beside it pushes the committed records' constants into the index the
   run is about — while worker threads
   install the records ahead of it, each at a *worker view*: an empty index over a frozen base layer that maps
   every name the stream will install, predicted from the records, to
   the record that installs it, visible below the record's own
   position, and answering from that record's install once it is done.
   The commit loop keeps the view's lookups equal to the serial index's
   (the installer checks, per constant it pushes, that the predicted slot
   holds that very constant, and hands that verdict over with its
   result), so a worker's install is the serial step
   ([theorem `installStep_commit` in `ConLeche/Verify/Cached/ViewCongr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/ViewCongr.lean#L1351-L1357)):
   every install stage reads its index through the lookup alone and
   writes it by pushes alone, so at two indices with the same lookups
   it pushes the same constants onto each. What it returns is therefore
   the same installed environment, whatever the schedule. The check phase then checks every recorded declaration
   against the *prefix* of the installed index it was installed at — an
   `O(1)` view whose lookup hides everything installed later — from a
   fresh memo state. A record's check is its own evidence
   ([definition `checkRecord` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L367-L369)):
   the fact that the record is checked, or its error tagged with the
   record's position in the stream. The installed environment — read-only from the
   boundary on — is marked persistent once, so that no check pays
   reference counting on it, and the checks are then run on worker
   threads: at `--jobs=1` the check loop
   ([function `checkLoop` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L123))
   runs it on every record on one such thread and carries every fact;
   otherwise a pool of them
   ([function `checkPool` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L278))
   claims records one at a time off a shared counter, and the results,
   merged by record index, are walked in record order
   ([function `collectQ` in `ConLeche/Driver/CheckPool.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckPool.lean#L218))
   — the walk stops at the first failing record in fold order, so the
   pool's verdict is the sequential walk's, and what it assembles is
   the same fact about every record. With the lazy parse's records a
   theorem's check first builds its value from the store, with a memo of
   its own, and drops it after the check
   ([function `lazyCheckRecord` in `ConLeche/Driver/LazyCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/LazyCheck.lean#L60)):
   the value built is the serial parse's entry
   ([theorem `buildVal_sound` in `ConLeche/Verify/Frontend/Lazy.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Lazy.lean#L1161)),
   and the install never reads a theorem's value, so the install of the
   placeholder records is the install of the serial ones and every
   record checked is an accept of the fold on the serial records
   ([theorem `lazy_checkDecls` in `ConLeche/Verify/Cached/LazyInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/LazyInstall.lean#L261)).
   Either way what comes out is a
   fully checked environment; which thread computed a check is
   irrelevant to what it proves, and so is whether the mark happened:
   it is the identity on the value, its result is discarded, and the
   environment the driver goes on to use is the one it already had. The heartbeat is
   printed between the steps and touches neither type. The driver
   ([function `checkDeclsIO` in `ConLeche/Driver/Run.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Run.lean#L247-L250))
   turns the fully checked environment into its environment with the
   proof that `checkDecls` returns it
   ([theorem `fullyChecked_checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L534-L536)).
2. **The fully checked environment**
   ([structure `InstalledEnv` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L254-L258))
   is stated over the executable steps: the installed environment is
   the accepting install run
   ([inductive `InstallRun` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L210-L218)),
   and a record is checked when its check at the prefix view succeeded
   ([definition `GroupChecked` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L287-L291)).
   The records' checks are independent of one another, which is what
   lets a later loop hand them to workers. An accept of `checkDecls`
   is exactly such an environment, and conversely
   ([theorem `checkDecls_fullyChecked` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L545-L546)),
   which is how the theorem about the fold is read off the argument
   of step 3.
3. **The cached checker** (`ConLeche/Cached/*`) is the implementation
   that ships: the same terms with a packed hash on every node, memo
   tables for reduction, inference and definitional equality keyed by
   those hashes, and the direct parser's record type. Nothing is
   interned; the hash is what makes a term a usable memo key. It is
   related to the pure checker by a one-directional simulation:
   whatever the cached checker accepts, the pure checker accepts. For
   the fold the simulation is applied step by step along the install
   run
   ([theorem `installRun_model` in `ConLeche/Model/InstallRun.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/InstallRun.lean#L211-L218)),
   and a record's check at the prefix view is covered by the
   simulation stated at the truncated environment because the view and
   the truncated environment have the same lookup, and the cached core
   reads its environment through that lookup alone
   ([theorem `coreKnotI_congr` in `ConLeche/Verify/Cached/KnotCongr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/KnotCongr.lean#L547-L548)).
   Carried along the install run and then through every record's
   check, the model reaches the final environment
   ([theorem `fullyChecked_sound` in `ConLeche/Model/InstallRun.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/InstallRun.lean#L239-L241)),
   and the statement about the fold
   ([theorem `no_proof_of_False_cached` in `ConLeche/Verify/Cached/MainC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L59-L65))
   is that model read through `checkDecls_fullyChecked`
   ([theorem `checkDecls_sound` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L37-L42)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` and the annotation pass are defined by one mutual
   recursion on a fuel parameter
   ([the entry points in `ConLeche/Kernel/TypeChecker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TypeChecker.lean#L29-L56));
   on exhaustion every operation throws
   ([the fuel recursion's base case in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L2044-L2050)).
   Its declaration fold is what the model tier proves things about
   ([theorem `no_proof_of_False_pure` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L276-L283)).
5. **The model tier** (`ConLeche/Model/*`, the set model of the checker)
   shows that each declaration step preserves an invariant on the
   environment
   ([theorem `declStep_preserves` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L141)),
   and that the invariant forbids a constant of type `False`, whose
   pinned denotation is the empty set
   ([theorem `no_constant_of_False` in `ConLeche/Model/Capstone.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Capstone.lean#L140-L146)).
   The main theorem's model is the invariant's own, read through the
   statement's relation
   ([definition `Model.ofEnvModelM` in `ConLeche/Model/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L378-L379)).
6. **The semantics** (`ConLeche/Semantics/*`) defines the denotation of
   terms in a model of the **set-theory interface**
   (`ConLeche/SetTheory/*`), and the **pure set constructions**
   (`ConLeche/SetModel/*`) build the sets inductive types denote.

The layering is enforced by a gate
([the import fence `tests/layering.sh`](https://github.com/leanprover/con-leche/blob/master/tests/layering.sh#L1-L3)):
implementation modules never import theory modules, so the binary
cannot depend on a proof.

## 3. The checker

Two modes exist, `--verified` (default) and `--trusted`
([the type `CheckMode` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L57)).
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
([function `whnfBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1148)),
`inferType` computes a type, and `isDefEq` decides conversion in the
order of the official `is_def_eq_core` (cheap head normalization, the
easy cases, proof irrelevance, the lazy-delta loop, the
projection-against-projection comparison by scrutinees, the full head
normalization and a restart, then the stuck comparisons) with lazy
unfolding, η, proof irrelevance, structure η, unit-likeness and K-like
reduction as the flags the install stored for each inductive type
permit. One proposition, `And`, is additionally rescued when its
recursor is stuck on a proof `h`: `And.intro a b h.1 h.2` is built and
certified by proof irrelevance. The official kernel has no such rescue;
this checker needs it because theorems are opaque here, so `And.rec`
applied to a theorem would otherwise never reduce. The rescue is keyed
on the name `And` only, to keep its reach small. Its certificate is
proof irrelevance, so it would be sound whatever block the stream
declared under that name; `And` is pinned (§5) so that the rescue is
always there to fire. Two things differ from a textbook
presentation and matter for the proof:

* **Annotation.** Before a declaration's terms are checked, an
  annotation pass
  ([function `annotateBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1922))
  records at every binder the sort of its codomain as a "Prop-when"
  datum, a function of the level parameters
  ([the `PropWhen` module's account in `ConLeche/Kernel/PropWhen.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/PropWhen.lean#L1-L40)),
  stored in the binder's metadata
  ([structure `BinderMeta` in `ConLeche/Kernel/Expr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Expr.lean#L100-L102)).
  The checker validates the coherence of these annotations at run time;
  the proof consumes them. This is the price of not having a syntactic
  type theory (see §4). The annotation pass also ζ-expands `let`, so
  stored terms are let-free: the reduction and inference arms raise an
  internal error on a `let` node, and the term language the denotation
  targets has no `let` former.
* **Fuel and memos.** The pure checker is fueled; the cached checker is
  not, but its memos are proved to agree with the pure functions at
  every fuel large enough to succeed
  ([theorem `checkDecls_skels` in `ConLeche/Verify/Cached/AgreeFloor.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/AgreeFloor.lean#L1142-L1144)).
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

**Terms.** A kernel `Expr` denotes, under a level valuation, an
*erased* term
([type `Term` in `ConLeche/Term/Syntax.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Term/Syntax.lean#L186-L214)):
de Bruijn indices, sorts at concrete levels, built-in constants at
concrete level instantiations, no names, no binder infos. The
*annotated* variant is the same syntax with a numeral sort at each
binder
([type `AnnotTerm` in `ConLeche/Semantics/Syntax.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/Syntax.lean#L72-L98)).

**Interpretation.** The interpretation maps an annotated term to a
set, totally and term-directed
([function `interp` in `ConLeche/Semantics/Interp.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/Interp.lean#L153-L164)):
a Π whose body sort is `0` is a predicate space with a single proof
point, otherwise a dependent function space; a λ likewise; a sort is a
universe of the chain; nothing needs to be well-typed to be
interpreted. Propositions are sets with at most one element, so proof
irrelevance and propositional extensionality are built in, and a
propositionally proven equation is a set equality.

**The invariant.** In place of a typing judgement there is a semantic
predicate
([predicate `WellDenoted` in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/WellDenoted.lean#L56-L86)):
hereditarily, every application applies a function to an argument of
its domain, every λ has a bounded codomain, every projection hits a
pair, and so on. Unlike syntactic typing it is preserved by β and
the other reduction steps
([the preservation lemmas in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/WellDenoted.lean#L133-L301)).
An environment carries the invariant for every stored constant, plus
closedness and the pins of the basis constants
([structure `EnvModel` in `ConLeche/Model/Annot/EnvModel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Annot/EnvModel.lean#L38-L67)).

**The statement's reading.** The main theorem is not stated over the
annotated terms and `interp` but over `Denotes` (§1), a relation on
the checker's own terms with no annotated intermediate. The two agree
where the invariant reads: wherever the invariant's reading of a term
is defined and satisfies the invariant, `interp` of the reading is a
`Denotes`-denotation of the term, with the invariant's sort facts
discharging the binder rules' premises about which bodies are
propositions
([theorem `Denotes_of_denoteMeta` in `ConLeche/Model/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L220-L226)).
The relation reads a binder's body under the binder with de Bruijn
indices while the checker opens it with a fresh free variable; a small
closing operation translates between the two.

**The claims.** Each kernel function gets one claim, in the accepting
direction only
([the claim definitions in `ConLeche/Model/Claims.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Claims.lean#L47-L113)):

* `whnfCore`/`whnf` return a term with the same denotation, with the
  invariant preserved;
* `isDefEq` answering `true` means the two denotations are equal;
* `inferType` returns a type such that the term's denotation is a
  member of the type's denotation.

They are proved through a *relational description* of the checker.
Six mutually inductive relations over the checker's own terms say what
moves the core makes — a reduction step, a definitional-equality
decision, a type inference (checking, or infer-only as in the official
kernel's `infer_only` mode), and three certificate checks — with the fuel, the unfolding heuristics and the dispatch order
out of sight; a rule's premises are exactly the certificates the
checker ran at that site, and the symmetric and derived variants are
theorems, not constructors
([the relations in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L92-L96)).
Definitional equality has no transitivity rule, deliberately, and
none can be added: the relation is the checker's verdict on terms
that are well-formed together, which no rule states, and every
premise's subject is a subterm of the conclusion or the product of a
reduction or an inference
([the docstring of `DefEq` in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L309-L332)).
The proof then has three parts. The *bridge*: an accepting run of any
kernel entry point, at any fuel, yields a derivation — one induction
on fuel, mechanical, each checker site landing on one rule
([theorem `bridge` in `ConLeche/Verify/Rules/Bridge.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Rules/Bridge.lean#L22-L27)).
The *soundness*: a derivation implies the claim's conclusion — one
structural induction over the six relations, every case one lemma
about one rule, stated over the environment's laws and never over the
implementation
([the master induction in `ConLeche/Model/Rules/Sound.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/Sound.lean#L41-L44)).
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

Inductive blocks are not trusted from the stream. Five inductive types
are pinned: four the checker installs from its own copy, and `And`,
which must agree with its pin and is then installed like any other
block. Every other block — one type or several mutually inductive ones, nested or not —
goes through one installer, which checks the block the way the official
kernel does and generates the block's recursors itself.

### The pinned basis types

`Eq`, `Nat`, `Empty` and `False` are installed from built-in pins
([the `False` pin in `ConLeche/Kernel/Basis/False.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis/False.lean#L52)),
and so is the quotient `Quot` with its soundness axiom, which is a
kernel primitive rather than an inductive type. The fold recognises
them: a block whose members carry a pin's names and agree with it up
to renaming of universe parameters installs the pin
([the recogniser `basisPinHit` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L64-L66)),
a block under one of those names that does not agree is rejected (the
names are reserved), and a quotient record that does not match its pin
is declined.

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
([function `andPinOk` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L90-L96)),
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

The recogniser reads the block's shape
([function `blockParts?` in `ConLeche/Kernel/Inductives/BlockParts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockParts.lean#L446)):
its parameter count as the stream declares it, checked against the
type formers' telescopes and against every constructor record before
anything else runs
([function `indParamsOk` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L614-L621)),
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
([function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L143)).

**The classes.** The recursors a block comes with eliminate one
*class* each: a member of the block, or — in a nested block — another
inductive type at the instantiation the block uses, such as `List T`
for the auxiliary recursor `T.rec_1`. Before the positivity check the
installer reads the classes off the stream's recursor types and checks
each one as a well-formed major premise
([function `targetMajorOf` in `ConLeche/Kernel/Inductives/RecCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/RecCheck.lean#L384-L386)).

**The positivity check** follows the official kernel's: a field's type
is put in weak head normal form before it is classified, and again
under each Π binder. The difference is nesting. The official kernel
rewrites a nested block into an auxiliary mutual block; this checker
builds no auxiliary block and instead looks through the container at
its concrete instantiation: at a field `List T` it checks `List`'s own
stored constructors with `T` in place of the parameter, after weak
head normal form, and records the instantiation
([function `nestContNew` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1363-L1365)).
In the constructors it checks, every application `T_j p⃗` of a block
member to the block's parameters is replaced by a *hole*, a variable
standing for that whole application. The block itself is checked the
same way as a container, as the outermost level of the nesting
([function `nestRoot` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1592)),
and the check starts from every class, so every class a recursor
eliminates is an instantiation it has visited — including one that
weak head normal form erases from every field
([function `classSeeds` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L496)).
Nothing is stated or cached about a container in its parameter. The
normal forms the check records are the fields the model reads
([function `checkBlockPositivity` in `ConLeche/Kernel/Inductives/BlockInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockInstall.lean#L284)).

**The recursor check.** The recursors are generated in the official
kernel's shape: each class's constructors are read off the positivity
check's recorded normal forms, and from them the checker builds every
recursor's type and rules — the minor premises over the constructors'
declared fields, each inductive hypothesis over its field's normal
form. Each generated type must be definitionally equal to the stream's
recursor type; the stream's rules are never read, and the generated
recursors are the ones installed
([function `genRecCheck` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L560)).
The rules of a recursor for an outside class fire at the instantiation
read off its type
([function `tgtStoredRules` in `ConLeche/Kernel/Inductives/RecCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/RecCheck.lean#L592-L593)).
Members of the right shape additionally get primitive projections,
structure η and unit-likeness (one constructor, no indices, not
recursive) and K-like reduction (a proposition with one constructor
and no fields), exactly under the official kernel's conditions.

**In the model** the block's carrier is the least fixed point of its
family functor over the index fibres
([the fixed-point family space in `ConLeche/SetModel/Value.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Value.lean#L365-L372)),
for several members a least fixed tuple of families, and a container
field reads the container's own least fixed point at the holes'
values. That the fixed point is a member of the universe follows from
one abstract theorem about *accessible* operators, those where every
element of the output needs only elements of the input indexed by one
fixed set of the universe
([theorem `closed_of_acc` in `ConLeche/SetModel/Access.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Access.lean#L244)):
such an operator has a closed tuple in the universe. The run of the
positivity check shows the block's operator accessible, for finitary,
reflexive and nested fields alike. Each recursor is read as the unique
value of its *graph*, the least relation closed under the recursor's
rules read over the ways a value decodes as a constructor application;
the block's induction makes that relation a function at every sort
(`ConLeche/SetModel/GraphRec.lean`), and the only sort-dependent fact
it needs is the kernel's own large-elimination guard. The model-tier
theorem for the whole install is
[theorem `declBlock` in `ConLeche/Model/Inductives/DeclBlockStep.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/DeclBlockStep.lean#L69-L74).

A block the recogniser does not read has its type formers checked as
constants, so that the official kernel's rejects stay rejects, and is
then positively declined
([function `checkShapeless` in `ConLeche/Kernel/CheckDecl.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CheckDecl.lean#L32-L33)),
never accepted.

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
* `env1` is `env` plus all type formers, with the η, unit-like and K
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
  parameters and annotated, is checked as a major premise:
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
* Every generated rule is annotated, its constants are resolved, and
  it is type-checked in `env2` plus the generated recursors without
  rules.
* `env3` is `env2` plus the generated recursors with their generated
  rules (an outside class's rules fire at its instantiation), plus the
  projection tables of structure-like members.

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
[function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L143);
steps 1–5 are
[function `checkBlockPass` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L62),
the constructor check of step 3 is
[function `checkSumCtor` in `ConLeche/Kernel/Inductives/SumInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/SumInstall.lean#L114),
step 4 is
[function `checkBlockClasses` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L524),
with a class's parameters moved and annotated in
[function `classKeyOf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L509);
`POS` is
[function `nestPos` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1453),
its hole lookup
[function `nestHoleAt` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L733),
`CONT` is
[function `nestContKey`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1395),
`CTORS` is
[function `nestCtors`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1213),
and the uniform-parameters check
[function `nestUniform`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1564);
step 6 is
[function `checkBlockTail` in `BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L129);
steps 7 and 8 are `genRecCheck` (above), with a constructor's
reference entry and the third proof-only check in
[function `classCtorOf` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L299),
the generated type and rule in
[function `classGenRecTy`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L181)
and
[function `classGenRule`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L193),
and their checks in
[function `classRecTyOk`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L394)
and
[function `classRuleOk`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L427).

## 6. The Nat operations

The official kernel accelerates the structural `Nat` operations on
literals with GMP. ConLeche does the same, but certifies the fast path
instead of trusting the operation's name.

* **Structural operations** (`Nat.add`, `sub`, `mul`, `pow`, `beq`,
  `ble`, and `pred` as a dependency;
  [the list `natOpNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L385-L393)):
  when a definition under one of these names arrives, the install
  certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([the account of the certified fast path in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L331-L348),
  [function `certifyNatEqs` in `ConLeche/Kernel/Checker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Checker.lean#L109-L116)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The model side reads the operation's membership off its pinned type
  shape and proves the literal semantics from the certified
  recurrences
  ([theorem `natOps_install` in `ConLeche/Model/NatEqs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/NatEqs.lean#L1094)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`;
  [the list `natDivModNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L395-L410))
  are defined by well-founded recursion and have no recurrence the
  kernel can check directly. The binary embeds *pinned* copies of
  several supported toolchains' own definitions of each operation,
  each with its pinned *certificate theorems* — `Nat.ble`-guarded
  characterisations of the operation whose proof terms were produced
  by Lean itself at pin-generation time. The install tries the pins in
  order and uses the first whose copy is definitionally equal to the
  stream's definition and whose certificates check, as theorem
  declarations, without installing them; a stream matching none of
  them declines
  ([the pin module `ConLeche/Kernel/NatOpPins.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16),
  [the certificate library `ConLeche/PinGen/Certs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/PinGen/Certs.lean#L7-L18)).
  The pins are committed per toolchain under `pins/`, each generated
  on its toolchain with `lake exe natop-pins-export`. Which list the
  gate tries is the fold's own argument rather than a constant inside
  it, and the model side reads none of it — it is stated for an
  arbitrary variant, because what it consumes is the certificates'
  verdict in the accepted environment and not where the matched
  variant came from:
  [theorem `divMod_install` in `ConLeche/Model/DivModCert.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/DivModCert.lean#L2014).
  That is why the two statements of §1 quantify over the list: the pins
  buy accepted `Nat.div` streams, never consistency.
* **`Bool`.** `Nat.beq` and `Nat.ble` return `Bool.true` or
  `Bool.false`, and the well-founded operations' certificates are
  guarded by `Nat.ble`, so these operations install only once `Bool`
  and its two constructors are stored, with no universe parameters and
  with `Bool : Type`
  ([function `natOpGuard` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L542-L554),
  [function `natOpCod` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L597-L604)).
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
  ([`preparePrelude` in `ConLeche/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Prepare.lean#L165-L172),
  [the reordering pass `ConLeche/Frontend/NatOpGround.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/NatOpGround.lean#L8-L25)).
  Both are reorderings of the parsed records below the verified fold,
  and that is a theorem about them: the prepared records are a
  permutation of the file's plus prelude records the file did not
  declare
  ([theorem `preparePrelude_perm` in `ConLeche/Verify/Frontend/Prepare.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L157-L162)).

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
([the pinned standard axioms in `ConLeche/Kernel/StdAxioms.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/StdAxioms.lean#L38-L42));
both are true in the model, `propext` by extensionality of
propositions and `Classical.choice` by global choice. `Quot.sound` is
part of the pinned `Quot` block. Any other axiom declaration is a
positive decline at its own record, with one tolerated exception:
`sorryAx`. An export declares that axiom whenever the module it came
from mentions `sorry`, whether or not anything uses it, so its record
is checked for well-formedness and then installs nothing — there is no
set model for it and there cannot be one. A stream that merely
declares it is therefore accepted; a stream that *uses* it declines, at
the record that uses it.

The compiler-trust family, `Lean.trustCompiler`, `Lean.reduceBool`,
`Lean.reduceNat` and the axioms `Lean.ofReduceBool` and
`Lean.ofReduceNat`, is neither rejected nor trusted: `trustCompiler`
installs as an opaque with value `True.intro`, the two reduce
operations install as ordinary opaques pinned to the identity
function, and the two axioms are accepted only after the install
certifies, by definitional equality, that the stored reduce operation
is the identity, at which point each axiom's statement is an inhabited
proposition in the model
([the compiler-trust family in `ConLeche/Kernel/TrustAxioms.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TrustAxioms.lean#L10-L39)).
Proofs by `native_decide` and `bv_decide` are declined: each such
proof adds an axiom of its own to the environment, recording the
result the native evaluator computed, and that axiom is not a pinned
one, so the stream declines at its record. ConLeche never runs native
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
* `--trusted` mode.
* Non-acceptance: a decline or a reject carries no claim. The verdict
  line reports the count of accepted stream records.
* Four places where the checker deliberately accepts more than the
  official kernel: a semantic comparison of universe levels; a
  proof-irrelevance fall-through; the large eliminator of a
  single-constructor block whose result sort can be zero — where the
  official kernel generates only the small one, this checker takes the
  subsingleton case under the per-field `PropWhen` criterion; and the
  `And` rescue of §3. All four are covered by the soundness proof.

## 10. Naming conventions

Every marker a reader has to know is in this table; **no suffix not
listed here carries meaning**.

| marker | reading |
|---|---|
| `C` | the *cached* checker's twin of a pure definition (`checkDeclC`, `CoreC`, `Expr.instantiate1C`, `SimC`) — the implementation that ships; there is one `Expr` type and one `Declaration` type, so the marker is on the function, never on the type |
| `I` | the variant that also handles an inductive family's index arguments (`checkStructFieldSortsI`) |
| `F` | stated over `FEnv`, the environment together with its lookup index (`natLitSupportedF`) |
| `D` | the direct parse and the functions over its output (`parseExportD`, `trusted_agrees_skels_D`) |
| `AV`, `Annot` | annotated terms: `AnnotTerm` is `Term` with a numeral sort at every binder, and `*AV` names are its readers (`sumTyAV`, `natLitAV`) |
| `WF` | well-formedness (`EnvWF`, `BlockWF`) |
| `_pure` / `_cached` / `_checked` | the final theorems over the pure fueled fold, over the cached fold `checkDecls`, and over the driver's fully checked environment (`no_proof_of_False_pure`, `no_proof_of_False_cached`, `no_proof_of_False_checked`) |

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
it is the subject of the proofs* — `Kernel/*`, `Cached/*`, `Frontend/*`
and `Driver/*` each open one `@[expose] public section`, since the
Verify and Model tiers unfold their bodies — while *proof code is private
by default*: `Model/*` and `Verify/*` open a plain `public section`, so a
proof file's bodies and proof terms are both private and only its statements
are interface.  The erased term language, the `SetTheory` interface, the pure
set constructions and the denotation (`Term/*`, `SetTheory/*`, `SetModel/*`,
`Semantics/*`) keep the blanket for the same reason the checker does — the
tiers above unfold them. The one module
deliberately kept opaque is `Kernel/PropWhen`, whose representation stays hidden behind its
API and laws; the proofs that need to see through it say `import all
ConLeche.Kernel.PropWhen`, and every such line carries its reason.

## 11. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The CLI: argument parsing, usage, exit codes; calls `ConLeche.Driver.checkMain`. |
| `ConLeche/Driver/` | The proof-carrying IO driver: the install and check loops, the parallel install (the prediction, the schedule, the commit loop; `ParInstall.lean`), phase B's worker pool (`CheckPool.lean`), the lazy parse's driver (`LazyParse.lean`) with its pool and rounds (`ParParse.lean`), the lazy check that builds a theorem's value in its check (`LazyCheck.lean`), the phase sequencing and `checkDeclsIO` (`Run.lean`). Checker code, like `Kernel/*`; the one tier besides `Main.lean` that may import `ConLeche/Verify/*`. |
| `ConLeche/Kernel/` | The pure checker: `Expr`/`Level`/`Name`, `PropWhen`, the mutually recursive core of reduction, inference and conversion (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the inductive installer (`Inductives/`: the recogniser `BlockParts.lean`, the positivity check `Positivity.lean`, the entry `checkBlock` with its constructor stages (`Sum*`) and projection tables (`Struct*`), the recursor generator and check `GenRec.lean`, and `ClassRead.lean`, which reads the classes off the stream's recursor types without checking them), the Nat-op pins. Imports no theory module. |
| `ConLeche/Cached/` | The shipped cached checker: hashed expressions, memo state, the cached core and declaration step, the parsed-record step (`ParsedC.lean`), the declaration fold `checkDecls` with its install and check phases and the fully checked environment the driver assembles (`Installed.lean`); the install skeleton (`InstallSkel.lean`, which the parallel install predicts from and the trusted/verified agreement floor is stated over). |
| `ConLeche/Frontend/` | The export parser: the dialect's byte recogniser and syntax records (`Scan/`) and the semantic layer over them (`ExportC.lean`), which decodes the file's records and nothing else; the pipelined driver that scans chunks on worker tasks and applies them in order (`Pipeline.lean`), with the flat byte format the scanned lines cross between the threads in (`Flat.lean`); the rounds' counters, finished tables and line check (`Rounds.lean`) and the rounds, which nothing trusts (`RoundsWork.lean`); the lazy parse's sweep, its check of a chunk, the store of the lines it does not build and the builds of a theorem's value from it (`Lazy.lean`); the preparation of the fold's input (`Prepare.lean`, with the built-in prelude of `Prelude.lean` and the reordering of `NatOpGround.lean`, which moves what a pinned Nat operation's certificates mention ahead of it). |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/Term/` | The erased term language, its substitution algebra and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and nested tuples, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The annotated term language, the interpretation, the semantic invariant, the semantics of inductive blocks, the declaration-level facts. |
| `ConLeche/Rules/` | The relational description of the core checker: six mutually inductive relations over the checker's own `Expr` — reduction, definitional equality, type inference (checking and infer-only), and three certificate checks — with fuel, unfolding heuristics and dispatch order out of sight (`Rel.lean`), and the derived rules (`Derived.lean`). Imports the fuel-free helpers of the kernel and nothing else of it. |
| `ConLeche/Verify/Rules/` | The bridge: an accepting run of a kernel function, at any fuel, yields a derivation (`Bridge.lean`, from one step theorem per entry point and the certificate bridges). |
| `ConLeche/Model/` | The graded set model of the checker: the environment invariant and its laws (`Annot/`), the claims, the soundness of the rules tier's derivations (`Rules/`: the motives, the environment inputs, one lemma per rule over shared kits, the master induction, and the recomposition of the claims from the bridge), the run-stated remainder the declaration fold reads (`Tiers.lean`), the declaration step, the inductive installs (`Inductives/`, `Ind*`), the Nat-op certification, the final theorems (`Capstone.lean`), and the model read through the statement's relation (`Denotes.lean`). |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: well-formedness, scoping, the cached-to-pure simulation (`Cached/`: the core's congruence in the lookup (`KnotCongr.lean`), the block tail's in-place pushes (`BlockOverlay.lean`), every install stage's and the parallel install's commit step (`ViewCongr.lean`, `ParInstall.lean`), which `ConLeche/Driver/ParInstall.lean` imports), the inductive installer's kernel-side invariants (`Inductives/`), and the parser's (`Frontend/`: line locality, the parse as a line fold, chunk independence, what a line does to the parse state, the template's lines, the characterisation of the serial fold over a stream that binds in increasing order, the soundness of the lazy parse's check and builds, and the lazy preparation), and that the install of placeholder records is the serial records' (`Cached/LazyInstall.lean`). |
| `ConLeche/Accepts.lean` | The file-level vocabulary of the statement: `jsonWithTheoremFalse`, the whole-file template of one JSON file that declares a theorem of type `False`. |
| `ConLeche/Denotes.lean` | The statement's semantics: what a term denotes (`Denotes`) and what a model of an environment is (`Model`); imports nothing from the proof tiers. |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The main theorem and the main corollary — about the environment the fold returns and about the chunks the binary reads — and the challenge module stating both with `sorry`, kept as its own library and compared with the solution by `tests/challenge.sh`. |
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
script and the list may only shrink), the trust-surface scan (`tests/trust-surface.sh`: no `unsafe`, `implemented_by` or `native_decide` outside an allowlist), the pin
dump freshness, the challenge comparison (`tests/challenge.sh`: the
challenge module builds with its `sorry` warnings and nothing else,
and every statement it makes is token-identical to the solution's),
the arena tutorial tests, the end-to-end and annotation fixtures with
pinned verdicts, and the trusted-mode sweep. `lake test` builds the test library with the axiom pins. CI runs
both.

The links in this document are part of the battery: `tests/overview-links.sh`
extracts every linked segment into one text and compares it with
`tests/overview-links-expected.txt`, so moving or changing the cited
lines fails the gate and is the reminder to re-read the paragraph that
cites them and to run `tests/overview-links.sh --update`.
