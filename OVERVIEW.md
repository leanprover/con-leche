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
([the driver's usage text in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L651)).
Any other option is a usage error: the run reports it, prints the
usage text and exits 3 without reading its input, so a verdict's
provenance can be read off the invocation.

The exit code follows the lean kernel arena convention
([the exit-code mapping in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L42)):

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

A run has two phases: the install phase reads the records in order
in one thread, and the check phase checks every recorded declaration
against the prefix of the installed environment it was installed at
(see §2). The flag `--jobs=<n>` runs the check phase on `n` worker
threads; without it there is one worker per hardware thread, and
`--jobs=1` runs one worker with no shared counter and no result table.
The check phase always runs on worker threads, never on the main
thread: its per-record memo state is allocated out of the running
thread's heap, and the main thread's heap is the one the parse and the
install have just fragmented, which at Mathlib scale costs the
single-worker lane a factor of two in wall time at the same
instruction count. Each worker thread reserves about 1 GiB of address space (its stack
reservation; the resident set grows by about 25 MB per worker), so a
run under an address-space limit (`ulimit -v`) must lower the count
to what the limit affords — about ten workers under 16 GB. At every
worker count the installed environment is marked persistent once at
the phase boundary, which removes the atomic reference counting the
workers would otherwise pay on it and is worth 18–32 % of wall time on
the pool, growing with the worker count, and 3.5 % at one worker;
`--no-mark-persistent` turns that off
and is how the difference is measured. The
verdict, and the declaration a rejection names, are the same at every
`n`: the results are walked in record order, so the first failing
record in fold order is the one reported. The flag
`--progress[=<stride>]` prints a heartbeat on stderr with one line
shape per phase — `install <i>/<N> <decl>` before every `stride`-th
declaration is installed, `check <done>/<M> <decl>` after every
`stride`-th completed check — bracketed by `parse done`, `install
done`, `check done` and a `done:` summary with the three phase
durations and the worker count (bare, the stride is 1). The heartbeat
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
product or the truth value of its body depending on the *regime* the
checker annotated it with, which it may claim only if the body really
denotes a truth value there — and the structure
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
([`no_False_theorem_accepted` in `ConLeche/Verify/Cached/StreamThm.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamThm.lean#L207-L210)):

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
([`parseChunks_ok_parseBytes` in `ConLeche/Verify/Frontend/Chunks.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Chunks.lean#L352),
with the streaming reader's running byte count as the same guard the
wholesale parse applies up front); and the template's lines scan to
exactly the records the fold then forbids
([`parseChunks_jsonWithTheoremFalse` in `ConLeche/Verify/Frontend/FileFalse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/FileFalse.lean#L173)).
The preparation puts the built-in prelude's records first and hoists
the ground of the pinned `Nat` operations; it is a permutation of the
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
and the module says why. On the uniform route a type former's telescope
may be stored reduced to weak head normal form. That is a definitional
equality, not an annotation, so the relation above would be false of
it; the constructors are stored as declared, but they are installed
with their block and are left out with it.

`checkDecls`
([function `checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L440-L445))
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
   ([function `parseExportStreamD` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/ExportC.lean#L652))
   and runs the fold's two phases as two loops. The byte recogniser that reads each line of the
   stream is proved equal to a naive reference over `List UInt8`
   ([theorem `scanLineSpec_eq_scanLineFwd` in `ConLeche/Frontend/Scan/Equiv.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Scan/Equiv.lean#L1002)):
   the driver calls the reference, and the compiler runs the fast
   recogniser on the strength of that equality. The streaming loop is
   a pure step over each chunk
   ([function `chunkStep` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/ExportC.lean#L577))
   with the reads interleaved, and what the parser makes of a record
   — index resolution, the smart constructors — is the
   semantic layer the main corollary's line lemmas are about. The install loop
   ([function `installLoop` in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L99))
   takes every record through the install step
   ([function `annotStepC` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L148-L151)):
   a definition or opaque is annotated and pushed with its check
   *recorded* — the annotated header and value and the number of
   constants installed before it — a theorem is installed by its
   statement alone (its header annotated, its value recorded raw and
   never entered by this loop: a theorem is opaque to reduction), and
   an axiom, an inductive or
   basis block, and the pinned `Nat`-operation and `reduce*`
   declarations are checked in full as they are installed, by the
   fold's ordinary step. The loop carries the chain of its accepting
   steps, a proposition, and what it returns is an installed
   environment. The check phase then checks every recorded declaration
   against the *prefix* of the installed index it was installed at — an
   `O(1)` view whose lookup hides everything installed later — from a
   fresh memo state. A record's check is its own evidence
   ([definition `checkRecord` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L355-L357)):
   the fact that the record is checked, or its error tagged with its
   fold position. The installed environment — read-only from the
   boundary on — is marked persistent once, so that no check pays
   reference counting on it, and the checks are then run on worker
   threads: at `--jobs=1` the check loop
   ([function `checkLoop` in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L169))
   runs it on every record on one such thread and carries every fact;
   otherwise a pool of them
   ([function `checkPool` in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L295))
   claims records one at a time off a shared counter, and the results,
   merged by record index, are walked in record order
   ([definition `collectChecks` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L389-L393))
   — the walk stops at the first failing record in fold order, so the
   pool's verdict is the sequential walk's, and what it assembles is
   the same fact about every record. Either way what comes out is a
   fully checked environment; which thread computed a check is
   irrelevant to what it proves, and so is whether the mark happened:
   it is the identity on the value, its result is discarded, and the
   environment the driver goes on to use is the one it already had. The heartbeat is
   printed between the steps and touches neither type. The driver
   ([function `checkDeclsIO` in `Main.lean`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L334-L337))
   turns the fully checked environment into its environment with the
   proof that `checkDecls` returns it
   ([theorem `fullyChecked_checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L524-L526)).
2. **The fully checked environment**
   ([structure `InstalledEnv` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L242-L246))
   is stated over the executable steps: the installed environment is
   the accepting install run
   ([inductive `InstallRun` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L200-L208)),
   and a record is checked when its check at the prefix view succeeded
   ([definition `GroupChecked` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L275-L279)).
   The records' checks are independent of one another, which is what
   lets a later loop hand them to workers. An accept of `checkDecls`
   is exactly such an environment, and conversely
   ([theorem `checkDecls_fullyChecked` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L535-L536)),
   which is how the theorem about the fold is read off the walk of
   step 3.
3. **The cached checker** (`ConLeche/Cached/*`) is the implementation
   that ships: the same terms with a packed hash on every node, memo
   tables for reduction, inference and definitional equality keyed by
   those hashes, and the direct parser's record type. Nothing is
   interned; the hash is what makes a term a usable memo key. It is
   related to the pure checker by a one-directional simulation:
   whatever the cached checker accepts, the pure checker accepts. For
   the fold the simulation is applied step by step along the install
   run
   ([theorem `installRun_model` in `ConLeche/Model/InstallRun.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/InstallRun.lean#L214-L221)),
   and a record's check at the prefix view is covered by the
   simulation stated at the truncated environment because the view and
   the truncated environment have the same lookup, and the cached core
   reads its environment through that lookup alone
   ([theorem `coreKnotI_congr` in `ConLeche/Verify/Cached/KnotCongr.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/KnotCongr.lean#L514-L515)).
   The walk carries the model to the final environment
   ([theorem `fullyChecked_sound` in `ConLeche/Model/InstallRun.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/InstallRun.lean#L242-L244)),
   and the fold's letter
   ([theorem `no_proof_of_False_cached` in `ConLeche/Verify/Cached/MainC.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L59-L65))
   is that model read through `checkDecls_fullyChecked`
   ([theorem `checkDecls_sound` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L37-L42)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` and the annotation pass are tied in a knot over a fuel
   parameter
   ([the entry points in `ConLeche/Kernel/TypeChecker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TypeChecker.lean#L28-L54));
   on exhaustion every operation throws
   ([the fuel knot's base case in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1907-L1913)).
   Its declaration fold is what the model tier proves things about
   ([theorem `no_proof_of_False_pure` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L277-L284)).
5. **The model tier** (`ConLeche/Model/*`, the graded set model)
   shows that each declaration step preserves an invariant on the
   environment
   ([theorem `declStep_preserves` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Fold.lean#L142)),
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
Trusted mode is verified mode minus certification-only steps; it is
faster and is outside the theorem. Both use the same core.

The checker is a Lean-kernel-style type checker in the shape of the
official one: `whnfCore` does β/ι/projection/quotient reduction,
`whnf` adds δ-unfolding of definitions — a theorem is opaque to
reduction: its value is never unfolded, so whether a declaration
type-checks never depends on a theorem's value — and the literal fast
paths
([function `whnfBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1089)),
`inferType` computes a type, and `isDefEq` decides conversion with lazy
unfolding, η, proof irrelevance, structure η, unit-likeness and K-like
reduction as the environment's capability flags permit; one
proposition, the pinned `And`, is additionally rescued when its
recursor is stuck on a proof (`And.intro a b h.1 h.2` is fabricated
and certified by proof irrelevance — `And` only, by ruling). Two things
differ from a textbook presentation and matter for the proof:

* **Annotation.** Before a declaration's terms are checked, an
  annotation pass
  ([function `annotateBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1785))
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
  ([theorem `checkDecls_skels` in `ConLeche/Verify/Cached/AgreeFloor.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/AgreeFloor.lean#L1280-L1282)).
  Binder names and binder infos are not stored at all; `Expr` carries a
  packed hash and loose-variable bounds as computed fields, which is
  what makes the DAG-safe traversals cheap.  The substitution walks
  memoise only the nodes the runtime reports SHARED — a reference-count
  read, with a memo keyed by the node's address and validated by
  pointer identity, so an unshared node costs no key and no probe —
  and that is the tree's ONE discipline for every traversal memo,
  structural equality (`Expr.beq`) and the syntactic guard walks
  included
  ([`withExclusive`'s account in `ConLeche/Kernel/Exclusive.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Exclusive.lean#L6-L42)).

## 4. The proof idea

There is no syntactic typing judgement and hence no theorem of the form
"accepted ⇒ derivable". The *theory* is the set model. What is proved
about the algorithm is stated only in the accepting direction, and it
is stated semantically.

**Terms.** A kernel `Expr` denotes, under a level valuation, an
*erased* term
([type `Term` in `ConLeche/Term/Syntax.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Term/Syntax.lean#L187-L215)):
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
is defined and graded, `interp` of the reading is a `Denotes`-denotation
of the term, with the invariant's sort facts discharging the regime
premises of the binder rules
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
decision, an inference at one of two grades, and three certificate
walks — with the fuel, the unfolding heuristics and the dispatch order
out of sight; a rule's premises are exactly the certificates the
checker ran at that site, and the symmetric and derived variants are
theorems, not constructors
([the relations in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L92-L96)).
Definitional equality has no transitivity rule, deliberately, and
none can be added: the relation is the checker's verdict on terms
that are well-formed together, which no rule states, and every
premise's subject is a subterm of the conclusion or the product of a
reduction or an inference
([the docstring of `DefEq` in `ConLeche/Rules/Rel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L310-L333)).
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

Inductive blocks are not trusted from the stream. Three cases:

* **Pinned basis blocks.** `Eq`, `Nat`, `PUnit`, `Empty`, `False` and
  `Quot` (with its soundness axiom) are installed from built-in pins
  ([the `False` pin in `ConLeche/Kernel/Basis/False.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis/False.lean#L52)).
  The fold recognises them: a block whose members carry the pin's
  names and agree with it up to level-parameter renaming installs the
  PIN
  ([the recogniser `basisPinHit` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L63-L65)),
  and a block under one of those names that does not agree is rejected
  at the reserved-name check. Their denotations are fixed sets, which
  is why the main theorem can name `False` without a hypothesis about
  how the stream declared it. `Bool` and `And` are not pinned: they are
  installed from the stream's own records, and the checker carries a
  copy of the toolchain's only to supply a stream that declares
  neither.
* **The uniform route** takes every other block, whether it has one
  member or several mutually inductive ones, and whether or not it is
  nested: any number of parameters, indices, constructors and fields,
  recursive, reflexive and nested fields, `Prop` or `Type`. The
  recogniser reads the block's shape
  ([function `blockParts?` in `ConLeche/Kernel/Inductives/BlockParts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockParts.lean#L446)) —
  its parameter count as the stream DECLARES it,
  checked against the type formers' telescopes and against every
  constructor record before either route runs
  ([function `indParamsOk` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L614-L621)),
  each member's index count off what is left of its type former's
  telescope, as official reads them; the stream's recursor records are
  read there but pinned only later, by the recursor stage. The install
  checks every type former, then the constructors against the whole
  member list, stores each constructor as declared, reads the classes
  the stream's recursors eliminate (below), and runs one positivity
  function over them — official's walk, weak head normal form before
  classifying and again under each Π binder, the block itself its root
  frame, walked like any container's
  ([function `nestRoot` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1621)) —
  whose normal forms are the fields the model reads
  ([function `checkBlockPositivity` in `ConLeche/Kernel/Inductives/BlockInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockInstall.lean#L284)),
  and runs official's checks — uniform occurrences (every member
  applied to exactly the parameters, before anything reduces),
  universe bound, elimination restriction and index occurrence. The recursors are then GENERATED, as official
  generates them: the stream's recursor types name the classes they
  eliminate (the block's members and, at a nested block, containers at
  instantiations), each class's constructors are read off the positivity
  function's recorded normal forms, and from them the checker builds
  every recursor's type and rules — the minor premises over the
  constructors' declared fields, each inductive hypothesis over its
  field's normal form. A generated type must be definitionally equal to
  the stream's; the stream's rules are never read, the generated
  recursors are installed
  ([function `genRecCheck` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L560)).
  Where a class is visited at several places of the positivity walk, the
  checker also requires every visit to agree with the one it generated
  from — the only step made for the proof alone.
  The whole install is one entry
  ([function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L143)).
  In the model the block's carrier is the least fixed point of its
  family functor over the index fibres
  ([the fixed-point family space in `ConLeche/SetModel/Value.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Value.lean#L388-L395)),
  for several members a least fixed TUPLE of families. That it is a
  member of the universe follows from one abstract theorem about
  *accessible* operators, those where every element of the output needs
  only elements of the input indexed by one fixed set of the universe
  ([theorem `closed_of_acc` in `ConLeche/SetModel/Access.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Access.lean#L242)):
  such an operator has a closed tuple in the universe. The run of the
  positivity check shows the block's operator accessible, for finitary
  and reflexive fields alike.
  Each recursor is read as the unique value of its GRAPH, the least
  relation closed under the recursor's rules read over the ways a
  value decodes as a constructor application; the block's induction
  makes that relation a function at every sort
  (`ConLeche/SetModel/GraphRec.lean`), and the only sort-dependent
  fact it needs is the kernel's own large-elimination guard.
  The model-tier theorem for the whole install is
  [theorem `declBlock` in `ConLeche/Model/Inductives/DeclBlockStep.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/DeclBlockStep.lean#L72-L77).
  Structure-like members additionally get first-class projections, η,
  unit-likeness and K exactly under official's conditions.
* **Nested blocks** go through the same install. The positivity
  function looks through a container at its CONCRETE instantiation: at
  a field `List T` it walks `List`'s own constructors with `T` in place
  of the parameter, after weak head normal form, and records the
  instantiation
  ([function `nestContNew` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1361-L1363)).
  Nothing is stated or cached about a container in its parameter, and
  no auxiliary block is built: official's nested-to-mutual encoding is
  not mirrored. The stream's auxiliary recursors (`T.rec_1`, …) name the
  instantiations they eliminate: before the positivity check, the
  install reads each class off the stream's recursor types and checks it
  as a major
  ([function `targetMajorOf` in `ConLeche/Kernel/Inductives/RecCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/RecCheck.lean#L384-L386)),
  and the positivity function then walks every class from the empty
  stack — the members as the root frame, every outside class like a
  container instance met there — so every class the recursors eliminate
  is a walked instantiation, one that weak head normal form erases from
  every field included
  ([function `classSeeds` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L496)).
  The auxiliary recursors are then generated like the block's own, at
  their classes.
  Their rules fire at the major's instantiation, read off the recursor
  type
  ([function `tgtStoredRules` in `ConLeche/Kernel/Inductives/RecCheck.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/RecCheck.lean#L592-L593)).
  In the model a nested block is still the least fixed point of its
  constructor types with holes at its members; a container field reads
  the container's own least fixed point at the holes' values, and the
  closure witness comes from accessibility rather than from a
  presentation as a member container
  ([theorem `closed_of_acc` in `ConLeche/SetModel/Access.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Access.lean#L242-L243)).
  Nested blocks go through the same model-tier theorem,
  [theorem `declBlock` in `ConLeche/Model/Inductives/DeclBlockStep.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/DeclBlockStep.lean#L72-L77).

A block the recogniser does not read has its type formers checked
as constants, so that official's rejects stay rejects, and is then a
positive decline
([function `checkShapeless` in `ConLeche/Kernel/CheckDecl.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CheckDecl.lean#L32-L33)),
never an acceptance.

### The uniform install in pseudo-code

The idea in one sentence: instead of building official's auxiliary
mutual types, the positivity check walks every container at its
concrete instantiation, as the container's own stored constructors with
the types under construction as holes; that one walk is the positivity
check and is what the monotonicity proof is read off, and the recursors
are generated for the instantiations the stream's recursors name (the
classes), every one of which that walk visits from the empty stack.

The steps, in the order the checker runs them. A line marked
`[proof]` is a check official has no counterpart to, made only because
the checker's own proof reads it.

```
checkBlock(env, block):          -- block = formers, constructors, recursors from the stream
  -- 0. shape
  split into type formers T_1..T_k (one parameter count nP), their constructors, recursors
  member names distinct, constructor names distinct
  isRec := official's syntactic is_rec (a member in a constructor's binder domain)

  -- 1. formers (at env)
  each T_m: type-check; whnf its type as Π (p⃗ : P⃗) (indices) → Sort s_m
  every member's parameter domains defeq to T_1's; every s_m ≡ s_1 =: s
  env1 := env + all formers   (η / unit-like / K capability flags, read at isRec)

  -- 2. constructors (at env1), as declared
  each constructor c of T_m: type-check; its type is Π p⃗ (fields) → T_m p⃗ idx
  parameter domains defeq to T_m's
  field sorts ≤ s; at a Prop block with a large eliminator: every field a proof
    or one of the result's index expressions (the subsingleton criterion)

  -- 3. the classes (at env1)
  [unverified] read off the stream's recursor types (raw): the CLASSES (one per
        motive ∀ ı⃗ (t : I us Ds ı⃗), Sort ℓ), the prefix layout (the motives, the
        minor premises and each one's ihs) and every recursor's class
  every class I us Ds, its Ds moved to p⃗ and annotated, checked as a major:
     a member  → I = T_m at the block's levels and parameters (one class per member)
     outside   → I a stored inductive, not Quot; Ds mention only parameters and name a
                 member (official's is_nested); I's sort ≡ s; Ds and I us Ds type-check

  -- 4. positivity check (at env1): every class from the empty frame stack
  first official's uniform occurrences, per constructor, on its stored type: every
    member occurrence is T_j at the block's levels applied to exactly p⃗, and no
    parameter's domain mentions a member
  the members first, as the ROOT frame:
    CTORS(the block's constructors, key (T⃗, the block's levels, p⃗), holes X⃗)
    [proof] (at a Type block) its normal form's field sorts are ≤ s at the holes
  then every outside class: CONT(I, us, Ds, [])

POS(e, frames):
  w := whnf e
  if w mentions no member and no hole          → ordinary field
  if w = Π a. b                                → reject if a mentions a member or hole,
                                                 else POS(b, frames)
  if w = H D⃗ idx, H a hole — the root frame's (a member X_j, D⃗ = p⃗) or a
       container frame's (Y) — D⃗ its key's parameters, idx hole-free, fully applied
                                               → a recursive field (X_j) or a field of
                                                 the container in progress (Y)
  if w = C us Ds idx, C a stored inductive (not a member, not Quot):
       Ds free of local variables; idx hole-free; fully applied
       [proof] every member hole in Ds applied to exactly p⃗ (never fires after the
         uniform occurrences: reduction keeps a hole applied)
       C's level count right; C's index telescope at Ds mentions no member or hole;
       C's sort ≡ s
       CONT(C, us, Ds, frames)
  else reject ("non-valid occurrence")

CONT(C, us, Ds, frames):
  key := (C, us, Ds)
  if key is being walked                           → reject (an instantiation in
                                                     progress, reached through reduction)
  if key is cached and Ds mention no frame hole    → done
  group := C's whole mutual block, each member C_j ↦ a fresh frame hole Y_j
           (each C_j's former checked at Ds as above)
  C us Ds type-checks
  CTORS(the group's constructors, key, holes Y⃗)
  cache the group's keys if Ds mention no frame hole

CTORS(constructors, key, holes):    -- the one constructor loop: the root's, every frame's
  for each constructor:
      instantiate its stored type at the key's levels and parameters, the group ↦ its
        holes (no β-step); type-check it
        [proof, at the root] the member-abstracted constructor typed with the holes
        in context (official types the declared one, step 2)
      for each field: POS(field, frames)
      no later field and not the result reads a non-ordinary field
      the result is headed by a hole; its indices are hole-free
      record its normal form at the key (holes read back as constants)
                                                   [a table local to the install]

  -- 5. tail
  index sorts read
  env2 := env1 + constructors

  -- 6. the recursors, GENERATED (at env2), from the classes and step 4's table
  pins: level parameters (the block's, one elimination level in front when large);
        names {T_m.rec} for member classes, {T_1.rec_1 .. T_1.rec_n} for the others;
        constructor grouping
  the stream's recursor types type-checked
  a large eliminator on a block that may be a Prop: one member with at most one
     constructor and no outside class (official's elim_only_at_universe_zero)
  per class, per constructor x:
     its entries := the recorded normal forms of x at a key the class matches (levels
        equivalent, parameters defeq with the members abstracted); the first is the DATUM
     x's minor premise's ihs are exactly the datum's recursive fields (a field whose
        walked type names a member), one each
     [proof] node agreement: at EVERY entry every recursive field has the datum's
        telescope, leaf head and indices, and a leaf class matching the ih's class
  GENERATE (official's mk_rec_infos / mk_rec_rules):
     the shared prefix: the parameters, then per slot a motive ∀ ı⃗ (t : I us Ds ı⃗), Sort ℓ
        or a minor premise ∀ (f⃗ : x's DECLARED fields at the class)
        (ih_i : ∀ a⃗, motive_t e⃗ (f_i a⃗)), motive_c (x's result indices) (x Ds f⃗),
        a⃗ and e⃗ off the datum's walked field i
     per recursor (class c): Π prefix (ı⃗ : c's index telescope) (t : I us Ds ı⃗), motive_c ı⃗ t
     per recursor and constructor x: λ prefix f⃗, minor_x f⃗ (λ a⃗, rec_t prefix e⃗ (f_i a⃗))…
        with rec_t the family's recursor at the ih's class (none: reject)
  per recursor: its generated type type-checked as a constant, and isDefEq to the
     stream's (reject-only)
  envR := env2 + the generated recursors without rules
  per generated rule: annotated, resolved and type-checked at envR
  env3 := env2 + the GENERATED recursors with their GENERATED rules (an outside class's
          fire at its instantiation) + projection tables for structure-like members
```

The entry is
[function `checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L143);
steps 1–4 are
[function `checkBlockPass` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L62),
the constructor check of step 2 is
[function `checkSumCtor` in `ConLeche/Kernel/Inductives/SumInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/SumInstall.lean#L114),
step 3 is
[function `checkBlockClasses` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L524),
with the unverified reading of the stream's recursor types in
[function `classRead` in `ConLeche/Kernel/Inductives/ClassRead.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/ClassRead.lean#L130)
and a class's parameters moved and annotated in
[function `classKeyOf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L509),
`POS` is
[function `nestPos` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1461),
its hole's entry (the root frame's, then the frames')
[function `nestHoleAt` in the same file](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L933),
`CONT` is
[function `nestContKey`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1393),
`CTORS` is
[function `nestCtors`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1211),
and the uniform occurrences
[function `nestUniform`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L1593),
step 5 is
[function `checkBlockTail` in `BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L129),
and step 6 is `genRecCheck` (above), with
a constructor's datum and node agreement in
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
  [the list `natOpNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L438-L446)):
  when a definition under one of these names arrives, the install
  certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([the account of the certified fast path in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L370-L387),
  [function `certifyNatEqs` in `ConLeche/Kernel/Checker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Checker.lean#L109-L116)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The model side reads the operation's membership off its pinned type
  shape and proves the literal semantics from the certified
  recurrences
  ([theorem `natOps_install` in `ConLeche/Model/NatEqs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/NatEqs.lean#L1094)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`;
  [the list `natDivModNames` in `ConLeche/Kernel/CoreDefs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L448-L463))
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
* **Order independence.** The certificates are spelled over the
  structural operations and the basis blocks, which an export may emit
  in any order. One pure pass between the parse and the fold puts every
  declaration the checker's prelude names at the front of the records —
  the stream's own record where the stream has one — and moves a pinned
  operation's dependency closure ahead of it when the stream has it
  later
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
  file does not declare, and a pinned Nat operation's dependencies are
  moved ahead of it. Nothing is rewritten and nothing is added.
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
* Three deliberate accept-supersets relative to the official kernel, a
  semantic comparison of universe levels, a proof-irrelevance
  fall-through, and the large eliminator of a single-constructor block
  whose result sort can be zero — where the official kernel generates
  only the small one, this checker takes the subsingleton case under
  the per-field `PropWhen` criterion. All three are licensed by the
  soundness proof.

## 10. Naming conventions

Every marker a reader has to know is in this table; **no suffix not
listed here carries meaning**.

| marker | reading |
|---|---|
| `C` | the *cached* checker's twin of a pure definition (`checkDeclC`, `CoreC`, `Expr.instantiate1C`, `SimC`) — the implementation that ships; there is one `Expr` type and one `Declaration` type, so the marker is on the function, never on the type |
| `I` | indexed (`nativeRecAVI`-style readings that carry an index) |
| `F` | stated over the environment-with-index `FEnv` (`checkNativeRecF`) |
| `D` | the direct parse and the functions over its output (`parseExportD`, `trusted_agrees_skels_D`) |
| `AV`, `Annot` | annotated terms: `AnnotTerm` is `Term` with a numeral sort at every binder, and `*AV` names are its readers (`sumTyAV`, `natLitAV`) |
| `WF` | well-formedness (`EnvWF`, `BlockWF`) |
| `_pure` / `_cached` / `_checked` | the capstones over the pure fueled fold, over the cached fold `checkDecls`, and over the driver's fully checked environment (`no_proof_of_False_pure`, `no_proof_of_False_cached`, `no_proof_of_False_checked`) |

A few words name things rather than tiers. An inductive block is
installed by the **uniform** route (`checkBlock`,
`Kernel/Inductives/Block*.lean`), which builds the block's carrier as
a least fixed point and generates its recursors; it is the only one.
`Struct*` and `Sum*` inside those directories are the two stage kits
the uniform route builds on —
the structure-shaped kit (projections, η, the entry telescope) and the
tagged-sum kit (the constructors as a sum). `Fueled` marks a
record-parameterised helper applied to the pure functions at a fuel
(`Verify/Knot.lean`).

**The module system.** Every file in the build carries the
`module` header, so a declaration and an import are private unless said
otherwise. The rule that decides which: *checker code is exposed, because
it is the subject of the proofs* — `Kernel/*`, `Cached/*`, `Frontend/*`
and `Main.lean` each open one `@[expose] public section`, since the
Verify and Model tiers unfold their bodies — while *proof code is private
by default*: `Model/*` and `Verify/*` open a plain `public section`, so a
proof file's bodies and proof terms are both private and only its statements
are interface.  The erased term language, the `SetTheory` interface, the pure
set constructions and the denotation (`Term/*`, `SetTheory/*`, `SetModel/*`,
`Semantics/*`) keep the blanket for the same reason the checker does — the
tiers above unfold them. The one deliberate
seal is `Kernel/PropWhen`, whose representation stays hidden behind its
API and laws; the proofs that need to see through it say `import all
ConLeche.Kernel.PropWhen`, and every such line carries its reason.

## 11. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The driver: argument parsing, the stream parse, the install and check loops, verdict and exit codes. |
| `ConLeche/Kernel/` | The pure checker: `Expr`/`Level`/`Name`, `PropWhen`, the core reduction/inference/conversion knot (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the inductive installer (`Inductives/`: the recogniser `BlockParts.lean`, the positivity check `Positivity.lean`, the entry `checkBlock` with its structure and sum kits, the recursor generator `GenRec.lean` and its unverified pre-pass `ClassRead.lean`), the Nat-op pins. Imports no theory module. |
| `ConLeche/Cached/` | The shipped cached checker: hashed expressions, memo state, the cached core and declaration step, the parsed-record step (`ParsedC.lean`), the declaration fold `checkDecls` with its install and check phases and the fully checked environment the driver assembles (`Installed.lean`). |
| `ConLeche/Frontend/` | The export parser: the dialect's byte recogniser and syntax records (`Scan/`) and the semantic layer over them (`ExportC.lean`), which decodes the file's records and nothing else; the preparation of the fold's input (`Prepare.lean`, with the built-in prelude of `Prelude.lean` and the Nat-op ground reordering of `NatOpGround.lean`). |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/Term/` | The erased term language, its substitution algebra and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and tuple towers, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The annotated term language, the interpretation, the semantic invariant, the tower semantics of inductive blocks, the declaration-level facts. |
| `ConLeche/Rules/` | The relational description of the core checker: six mutually inductive relations over the checker's own `Expr` — reduction, definitional equality, type inference at two grades, and three certificate walks — with fuel, unfolding heuristics and dispatch order out of sight (`Rel.lean`), and the derived rules (`Derived.lean`). Imports the fuel-free helpers of the kernel and nothing else of it. |
| `ConLeche/Verify/Rules/` | The bridge: an accepting run of a kernel function, at any fuel, yields a derivation (`Bridge.lean`, from one step theorem per entry point and the certificate bridges). |
| `ConLeche/Model/` | The graded set model of the checker: the environment invariant and its laws (`Annot/`), the claims, the soundness of the rules tier's derivations (`Rules/`: the motives, the environment inputs, one lemma per rule over shared kits, the master induction, and the recomposition of the claims from the bridge), the run-stated remainder the declaration fold reads (`Tiers.lean`), the declaration step, the inductive installs (`Inductives/`, `Ind*`), the Nat-op certification, the capstones, and the model read through the statement's relation (`Denotes.lean`). |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: well-formedness, scoping, the cached-to-pure simulation (`Cached/`), the inductive installer's kernel-side invariants (`Inductives/`), and the parser's (`Frontend/`: line locality, the parse as a line fold, chunk independence, what a line does to the parse state, the template's lines). |
| `ConLeche/Accepts.lean` | The file-level vocabulary of the statement: `jsonWithTheoremFalse`, the whole-file template of one JSON file that declares a theorem of type `False`. |
| `ConLeche/Denotes.lean` | The statement's semantics: what a term denotes (`Denotes`) and what a model of an environment is (`Model`); imports nothing from the proof tiers. |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The main theorem and the main corollary — about the environment the fold returns and about the chunks the binary reads — and the challenge module stating both with `sorry`, kept as its own library and compared with the solution by `tests/challenge.sh`. |
| `bridge/lean4lean-model/` | The Mathlib bridge instantiating the interface. |
| `tests/` | The Lean test library (the axiom pin), the arena and end-to-end fixtures with their expectation files, and the gate scripts. |
| `scripts/` | Fixture generators, the PERF battery, stream tools. |

## 12. Gates

`tests/arena.sh` is the standard battery: the layering fence
(`tests/layering.sh`: no base module imports the model lane, no
implementation module imports the theory, and no module of the
rules tier of §4 has the pure implementation in the environment it
elaborates in — its direct imports plus, transitively, their
`public import`s, computed from source; the implementation modules
that the base tiers' own re-exports still carry in are listed in the
script and the list may only shrink), the compiler-escape scan, the pin
dump freshness, the Comparator pair (`tests/challenge.sh`: the
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
