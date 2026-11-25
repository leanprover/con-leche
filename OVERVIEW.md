# ConLeche: an overview of the proof

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to [`README.md`](./README.md), which is
> human-written and states the main theorem and its corollary in the
> maintainer's own words, with its own links into the source.
> This one is a guided tour of the verification, from the binary that
> runs to the set-theoretic assumption it rests on, with links into the
> source on `master`.

## 0. Using the checker

`con-leche` checks the declarations of a Lean development, as the Lean
kernel does, and reports one verdict. It reads either an export file in
[`lean4export`](https://github.com/leanprover/lean4export)'s NDJSON
format, or compiled modules from their `.olean` files.

Only a run that exits with code 0 in the default mode (`--verified`)
carries the guarantee of [§1](#1-what-is-proved).

### Building

```
lake build con-leche
```

The binary is `.lake/build/bin/con-leche`. Lake takes the Lean toolchain
from the `lean-toolchain` file.

### Quick start

Check an export file:

```
con-leche Init.ndjson
```

Check a module and everything it imports, from `.olean` files:

```
con-leche --olean --search-path="$(lean --print-libdir)" Init
```

In a Lake project, after `lake build`, check a module of the project:

```
con-leche --olean --search-path="$(lake env printenv LEAN_PATH)" MyProject
```

On success, the last line of the output is the verdict, and the exit
code is 0:

```
con-leche: accepted 12 declarations (--verified)
```

`con-leche --help` prints every invocation form and option
([`helpText` in `ConLeche/Driver/Cli.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L138)).

### Command-line rules

* An option's value follows an `=`: `--jobs=4`, not `--jobs 4`.
* Options and arguments can come in any order.
* `--` ends the options. Every argument after it is a file or module
  name, even if it starts with `-`.
* A usage error (an unknown option, a bad value, options that do not go
  together) exits with code 3 before the checker reads any input.
* Every setting is a command-line option. The checker has no
  configuration file.

### Input: a `lean4export` file

```
con-leche [OPTIONS] [--] FILE.ndjson
```

The run takes exactly one file and checks every declaration in it. The
checker reads the file once, front to back, and writes no temporary
files.

### Input: `.olean` files

```
con-leche [OPTIONS] --olean --search-path=DIRS [--] MODULE...
```

The run reads the named modules (`Init`, `Mathlib`) and all modules they
import, and checks every constant in them as one development. You do
not need `lean4export`. [§2](#the-olean-reader) describes the reader.

* `--olean`: read the arguments as module names, not as a file.
* `--search-path=DIRS`: the directories that hold the `.olean` files,
  separated by `:`, as in `LEAN_PATH`. Required. You can repeat the
  option; the lists add up. In a Lake project, take the search path
  from Lake: `--search-path="$(lake env printenv LEAN_PATH)"` covers the
  project, its dependencies and the toolchain (build the project
  first). For the toolchain's own modules alone, use
  `--search-path="$(lean --print-libdir)"`.
* `--constant=NAME`: check only the constant `NAME` and everything it
  mentions, not the whole import closure. Use it to check one theorem
  quickly. You can repeat the option. A name that the closure does not
  hold is an error (exit 3).

The checker finds a module as Lean does. It looks for the module's root
(the first component of its name) as a directory `Root/` or a file
`Root.olean` in the search path, and expects all files of the module in
that directory. It is stricter than Lean in one point: a root that two
different directories of the search path hold is an error (exit 3).
Listing the same directory twice is not.

In a module or constant name, write a component in `«»` to have it taken
literally, dots included: `Challenge.«12.34».«5»`. In a `--constant`
name, an unescaped component of digits is a number, as in
`_private.M.0.foo`.

The reader reads `.olean` format version 2. It declines a file of
another version (exit 2).

### General options

* `--verified` (default): check in the mode that the soundness theorem
  covers.
* `--trusted`: skip the checks that only the soundness proof needs. The
  run is faster, but the theorem does not cover it
  ([§9](#9-what-the-theorem-does-not-cover)). Use it for debugging
  only. The verdict line names the mode, so a log cannot pass a trusted
  run for a verified one.
* `--jobs=N`: the number of worker threads. Default: one per hardware
  thread. The verdict, and the declaration that a rejection names, do
  not depend on `N`. Each worker thread reserves about 1 GiB of address
  space; if you run under an address-space limit (`ulimit -v`), lower
  `N`, or the run aborts at start with `failed to create thread`.
* `--max-nat-size=N`: the largest `Nat` numeral, in bytes, that the
  checker takes in or computes. A declaration that needs a larger one
  is rejected. Default: 134217728 (128 MiB), the default of the official
  kernel's `LEAN_NAT_MAX_SIZE` ([§6](#6-the-nat-operations)).
* `--progress[=PACE]`: report progress on stderr. `PACE` is `N` (a line
  every `N` declarations), `P%` (a line per `P` percent of each phase)
  or `Ss` (a line when a declaration finishes and `S` seconds have
  passed since the last line). Without a value, the checker prints
  every declaration with its name. Default: no progress lines. The
  option changes neither the verdict nor what the theorem covers.
* `--help`: print the help text and exit with code 0.

### Comparing a challenge with a solution

`--compare` takes two developments. The *challenge* states definitions
and theorems and can leave holes. The *solution* fills them. A hole is
an axiom of the challenge (other than Lean's standard axioms) or a
declaration whose value uses `sorry`. The checker accepts a hole as an
axiom of its statement if the solution has a constant of the same name
and the same type (up to the names of universe level parameters), and
everything that the type mentions is the same in both. The run checks
the solution in full, and everything in the challenge that is not a
hole. [§1](#1-what-is-proved) ("A challenge and its solution") states
what an accepting run proves.

* `--compare CHALLENGE.ndjson SOLUTION.ndjson`: compare two
  `lean4export` files.
* `--olean --compare --search-path=DIRS CHALLENGE SOLUTION`: compare
  two modules, each with its import closure. With `--constant=NAME`
  (a declaration of `CHALLENGE` itself), the run checks only `NAME` and
  what it mentions.
* `--compare` together with `--check-graph`, `--olean --module`,
  `--olean --modular` or `--olean --schedule` (see
  [Checking module by module](#checking-module-by-module)): the same
  comparison, module by module. The challenge is one more module of a modular run
  over both import closures. `--constant` is a usage error here.
* `--trusted-search-path=DIRS` (with `--olean` or `--check-graph`): the
  directories of the challenge. The challenge and everything it imports
  must be in `DIRS`, and the checker reads them from there only. It
  looks for the solution's modules in `DIRS` first, then in
  `--search-path`. Use it when you do not trust the solution's
  directories: the solution then cannot replace a module that the
  challenge imports. Without the option, the checker reads both through
  `--search-path`. The option also goes with `--olean --module` alone:
  the module's closure is then looked up in `DIRS` first.

An accepting run prints the verdict and one line per justified hole:

```
con-leche: accepted 300 declarations, 3 axioms justified by the solution S.ndjson (101 declarations accepted) (--verified)
con-leche: def big justified by the solution
con-leche: theorem big_lt justified by the solution
con-leche: axiom ax justified by the solution
```

A hole that the solution does not justify is a rejection (exit 1), with
the reason.

### Checking module by module

By default, an `--olean` run loads the whole import closure into one
environment. The modular modes check each module on its own, against
what it reads of the modules it imports. Use them to limit memory, to
isolate modules from each other, or to spread the work over several
processes or machines.

The modular guarantee ([§1](#1-what-is-proved), "Modular checking")
needs two things, on the same unchanged set of files: the import graph
check exits 0, and the `--module` run of every module in the closure
exits 0.

* `--check-graph --search-path=DIRS MODULE...`: read only the headers of
  the modules' import closure. Check that the import graph has no cycle
  and that every import is on the search path. This mode does not take
  `--olean`.
* `--olean --module --search-path=DIRS MODULE`: check the declarations
  of the one module `MODULE`, and no others.
* `--olean --schedule --search-path=DIRS MODULE`: check every module of
  `MODULE`'s import closure. The run does the graph check, then starts
  one `--module` process per module. This is the usual way to check a
  whole development module by module. No theorem is about the scheduler
  itself: it only starts the runs and reports their exit codes.
* `--olean --modular --search-path=DIRS MODULE`: check every module of
  `MODULE`'s import closure as `--module` does, in one process. It does
  much more work than the default `--olean` run and has no process
  isolation. Prefer the default run or `--schedule`.

The three `--olean` modes take exactly one module and no `--constant`.

#### Scheduler options

These options go with `--olean --schedule`. Each of them also selects
the scheduler, so `--schedule` itself can be left out.

* `--jobs=N`: here, the thread budget of the whole run. The threads of
  all running workers add up to at most `N`.
* `--schedule-memory=SIZE`: a hard limit on the memory of all running
  workers together. `SIZE` needs a unit: `512M`, `47G` (`K`, `M`, `G` or
  `T`). The scheduler starts workers so that they fit. If the workers
  pass the limit, it kills the youngest ones and runs them again later.
  Default: no limit.
* `--schedule-timeout=S`: a time limit per worker, in seconds. Default:
  none.
* `--schedule-log=FILE`: append each finished module to `FILE`. If you
  start the run again with the same log, it continues where it stopped.
* `--schedule-order=shuffled|graph`: the order in which the modules
  start. `shuffled` (default) is a fixed order from a hash of the module
  names; `graph` is the order of the import graph.
* `--worker-stack-size=SIZE`: the thread stack size of the workers,
  with a unit (`8G`). Use it when a worker's verdict is `stack` (a stack
  overflow). Default: the workers inherit `LEAN_STACK_SIZE_KB` from the
  environment.
* `--schedule-commands`: start nothing. Print the commands that check
  the closure, one per line and quoted for a shell: the `--check-graph`
  run, then one `--module` run per module. Use it to run the checks with
  your own job system. All of them must exit 0.
* `--progress=N` or `--progress=Ss`: print a line on stderr after `N`
  milliseconds (at least one second) or `S` seconds without output. A
  percentage is a usage error here.

The scheduler prints one line per finished module on stdout: a status
part in brackets (modules finished, workers and threads running, memory
in use, estimated time left), then the module's time, its peak memory,
`FAILED` with the verdict if the module was not accepted, and the
module's name. It prints statistics on
stderr at the end. On `SIGINT` or `SIGTERM` it kills its workers, prints
the statistics and exits with code 130 or 143.
[§2](#2-from-the-binary-to-the-theorem) ("Every module of a closure")
describes the scheduler and the format of the log.

### Exit codes

The exit code is the verdict. The codes follow the convention of the
Lean kernel arena
([the exit-code mapping in `ConLeche/Driver/CheckMain.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckMain.lean#L37)).

| exit | verdict | meaning |
|---|---|---|
| 0 | accepted | Every declaration checked. |
| 1 | rejected | A declaration is invalid: for example a type error, a bad inductive type, or a proof of the wrong statement. |
| 2 | declined | The checker found a feature that it does not support, and says which. It claims nothing about the input. |
| 3 | error | Bad usage, malformed or missing input, or an internal failure. |

* A rejection says something about the input. A decline says something
  about the checker.
* A modular run (`--modular`, `--schedule`) that does not accept every
  module exits with the code of the first such module in the order of
  the import graph.
* An internal panic, or running out of memory, is not a verdict. The
  process aborts with `SIGABRT`, which a shell reports as status 134.
  An abort can write a core dump; for a large run, switch core dumps
  off first (`ulimit -c 0`).

## 1. What is proved

For each covered way of running the binary, ConLeche proves the same
guarantee: any input the checker accepts has a model in every set
theory. This section explains what a model is, which theorem covers each
run, and what the theorems assume. Later sections explain the proofs.

### The main theorem

The theorems in this section express this guarantee in several forms.
The run theorems are in `ConLeche/MainTheorem.lean`;
`ConLeche/Challenge.lean` states them without proofs and explains every
name in their statements.

> **Main theorem.** Let `V` be any model of the `SetTheory` interface
> (§7). If the checker accepts an input, the input has a model in `V`:
> a set for each constant at each list of universe level values. Each
> constant's set belongs to the set denoted by its type, each definition's
> set equals the set denoted by its value, and each recursor rule's ι
> equation holds.

Every theorem proved by the input is therefore true in the model: the
theorem is a constant, and its interpretation belongs to the set denoted
by its statement. In particular, an input that declares `False` as Lean
does contains no constant of type `False`.

### What a model is

The definitions that give the theorem its meaning are in one module,
`ConLeche/IsModel.lean`, written to be read from top to bottom. They
refer only to the constants in the input, not to the environment that
the checker builds.

A model is a function `model : Name → List Nat → V`. It gives the set
that a constant denotes at the values of its universe level parameters.
[`IsModel V model C`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L212-L213)
says that `model` satisfies every constant in the set `C`. It satisfies
a constant `c`
([`ModelOf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L201-L202))
if, at every list of level values, one per level parameter of `c`:

* `model c.name vals` is a member of what the type of `c` denotes;
* if `c` is a definition, `model c.name vals` equals the set denoted
  by its value;
* if `c` is a recursor, each of its rules holds (`RuleHolds`).

The conditions for `c` use its own record, without consulting the
records of other constants. The order of the constants therefore does
not matter. If two constants have the same
name, the model's interpretation of that name must satisfy both sets of
conditions.

#### The constants of a declaration

For a list of declarations `ds`, the set `C` is
`(· ∈ constantsOf ds)`. Each declaration contributes these constants
([`Declaration.constants`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L160-L168)):

| Declaration | Constants |
|---|---|
| Axiom | Its statement. `sorryAx` contributes nothing. |
| Definition | Its statement and its value. If the value uses `sorry`: the axiom of its statement. |
| Theorem | Its statement. The proof is not read. |
| `opaque` | The axiom of its statement. The value is not read. |
| Inductive block | Its type formers, constructors and recursors, each on its own. |
| Quotient constant, `Quot.sound` | The quotient package's constant of that kind. `Quot.lift` and `Quot.ind` carry their ι rule. |

For `.olean` input, `C` is the set of constants of the modules that
the run reads (`ConLeche/OleanInput.lean`); "Modular checking" below
names its parts.

#### Recursor rules

A recursor's rule holds
([`RuleHolds`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L189-L191))
if its ι equation denotes an inhabited set. The ι equation
(`iotaEqOf`) is a closed term: an `@Eq`, under the binders it needs,
between the recursor applied to a constructor and the rule's
right-hand side.

The equation is constructed from the recursor's own type, without
looking up a constructor. The checker accepts a recursor only when this
construction agrees with the one obtained through its constructor (§14).

### How a term denotes a set

[`Expr.eval model φ ρ e`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L128-L129)
is the set that the term `e` denotes, where `φ` gives a natural number
to every universe parameter and `ρ` a set to every bound variable. It
is a total function on the checker's own terms, with one equation per
syntax form:

| Term | Denotation |
|---|---|
| Bound variable | Its value in `ρ`. |
| `Sort u` | The types at level `u` of the universe chain. Level 0 is the set of truth values. |
| Constant `c.{us}` | `model c` at the values of `us`. |
| Application | The value of the function's graph at the argument. |
| `∀` | The set of dependent function graphs over its domain. If the body denotes a truth value at every value of the domain: a truth value. |
| Lambda-expression | The graph of its body over its domain. If the body denotes the proof point at every value of the domain: the proof point. |
| `let` | Its body at its value. |
| Projection | A component of the pair chain that the structure value denotes. |
| Literal | What its constructor form denotes. |

Propositions denote subsets of a one-element set, whose element is the
proof point. This interpretation incorporates proof irrelevance and
impredicativity; it does not consult typing information.

Some terms denote junk; for example, a free variable denotes the empty
set. The theorems concern only closed terms in the input, so these junk
values do not affect their conclusions.

### `False` and `Eq` get their meaning from their declarations

The interpretation treats no constant specially: `False` and `Eq` denote
whatever the model gives them. Their own declarations fix that meaning.

* Where `C` declares `False.rec` as the prelude does
  (`DeclaresFalse`), `False` denotes the empty set
  ([`IsModel.false_empty` in `ConLeche/Semantics/IsModelBasis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/IsModelBasis.lean#L44)).
* Where `C` declares `Eq`, `Eq.refl` and `Eq.rec` as the prelude does
  (`DeclaresEq`), `@Eq A a b` denotes the truth value of `a = b`
  (`IsModel.eq_eqv` in the same file).

The checker accepts a stream that declares `False` or `Eq` only if it
declares them as the prelude does. An accepted stream that contains a
constant of type `False` therefore declares the prelude's `False`
([`checkDecls_declaresFalse_of_constant` in `ConLeche/Semantics/NoFalse.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/NoFalse.lean#L41-L45)).
That constant would be a member of the empty set, so an accepted
stream contains no such constant.

### The theorems about a run

Each theorem is about `Driver.runArgs`, which is all of the binary's
`main` except its plumbing, at one fixed argument list. The hypothesis
[`ModelIO.CanGive (Driver.runArgs args) fs 0`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L325)
says that exit code 0 is a possible outcome on the snapshot `fs` of
the files, in the model `ModelIO` of the file operations. That a real
run of the binary is one of the model's outcomes is assumed, not
proved; §2 states the assumption.

| Run | Theorem | What has a model |
|---|---|---|
| `-- <file>` | `main_json_model` | The records parsed from the file. |
| `--compare -- <c> <s>` | `main_compare_json_model` | The records parsed from the challenge file `c`. |
| `--olean --search-path=<dirs> -- <root>` | `main_oleans` | The constants of `root` and of every module it imports. |
| `--olean --compare … -- <c> <s>` | `main_compare_model` | The constants of the challenge's closure. |
| `--check-graph` and `--olean --module`, or `--olean --modular` | `main_modular`, `main_modular_one` | Each module's constants, one model per module. |
| The same with `--compare` | `main_modular_compare`, `main_modular_compare_one` | Each module's constants in the challenge's closure. |

The argument lists are exactly those of the statements. A theorem says
nothing about a run with another flag. No theorem covers `--trusted`:
with no mode flag, the run is in the verified mode.

The first row, in full:

```lean
open Frontend in
theorem main_json_model (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList)
```

If exit 0 is possible on a snapshot where the file contains the bytes
`b`, then `b` parses, and the parsed records have a model.

### No accepted file declares a theorem of type `False`

[Theorem `main_no_False`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L55-L57)
is the consistency corollary for a lean4export file: no exit 0 of
`-- <file>` is possible on a snapshot where the file is a
`jsonWithTheoremFalse` file.

[`jsonWithTheoremFalse`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Accepts.lean#L53-L63)
describes the file as text. The file contains four lines in the
exporter's own shapes, in this order, with any text before, between
and after them:

1. a name entry for `False`;
2. an expression entry for the constant `False`;
3. a name entry for the theorem's own name;
4. a theorem record whose type is that expression.

This describes one way a file can contain a theorem of type `False`;
it does not cover every proof of `False` that a file can contain. Because
the predicate describes the bytes, the corollary applies directly to the
file without assumptions about how the parser handles those lines.

### The checking function

Every run calls one function on parsed declarations,
[`checkDecls`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L106-L108).
It checks every declaration of `ds` in order, each against the
environment of the declarations before it. It accepts no axiom other
than the built-in ones. The main theorem for this function is
[`model_exists` in `ConLeche/Model/PureChecker.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/PureChecker.lean#L31-L34):

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (ds : Array Declaration)
    (accepted : (checkDecls .verified pins maxNatSize ds).isOk) :
    ∃ model, IsModel V model (· ∈ constantsOf ds.toList)
```

The theorem holds for every value of the two parameters, so
consistency does not depend on them:

* `pins` is the list of pinned `Nat.div`/`Nat.mod` variants that the
  checker tries when a stream declares these operations (§6). The
  binary runs at `natOpPinSets`.
* `maxNatSize` is the largest `Nat` numeral, in bytes, that the
  checker takes in or computes (§6). A larger numeral only makes it
  reject.

A second theorem describes how the accepted declarations are stored.
[`checkDecls_consts` in `ConLeche/Model/StreamConsts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L215-L220)
says that if `checkDecls` accepts `ds`, then every definition, theorem and
opaque of `ds`, and every axiom other than `sorryAx` and `Quot.sound`
([`Declaration.Declares`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L84-L90)),
has a constant with the same name in the returned environment, with the
record's own level parameters and type. The members of an inductive
block are outside this claim: the checker may store a type former's
telescope in weak head normal form.

### A challenge and its solution

A comparison checks a challenge whose holes a solution fills (§0). A
hole is an axiom of the challenge other than the standard ones, or a
declaration whose value uses `sorry`; the model treats it as an axiom
with that statement. The theorems are about the challenge's input alone.

For two lean4export files,
[`main_compare_json_model`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L63-L66)
says that if `--compare -- <c> <s>` can exit 0, the run read the file
`c`, the file parses, and its records have a model. The corresponding
theorem for the checking functions is
[`solution_model_exists`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/PureChecker.lean#L43-L47):
if `checkDecls` accepts the solution's records, and
[`checkChallenge`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L114-L116)
accepts the challenge's records with them, the challenge's records
have a model.

For `.olean` files,
[`main_compare_model`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L88-L94)
is about `--olean --compare --trusted-search-path=<T> --search-path=<D> -- <c> <s>`.
The challenge's directories are `T`, or `D` if `T` names none
(`Driver.trustedOr`). If the run can exit 0 on a snapshot, then on
every snapshot that agrees with it under the challenge's directories
(`FS.AgreeUnder`), the closure of the challenge module, read through
those directories, has a model.

The solution's files are not in the conclusion. The challenge's
directories alone fix what the challenge means, and the solution only
justifies the holes: at each hole, the challenge's model takes the
value that the solution's constant has in the solution's model.

Because the conclusion is a model, it excludes a challenge that states
something false and leaves its proof as a hole. In a closure that
declares `Nat` and `Eq` as Lean does, a challenge with
`def f : Nat := 3` and a hole `t : f = 5` has no model, whatever the
solution contains.

### Modular checking

A development can be checked one module at a time (§0). The theorems
then give one model per module, and the models agree on what the
modules see of each other.

[Theorem `main_modular`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L109-L120)
has two hypotheses, on one snapshot `fs`:

* `--check-graph --search-path=<dirs> -- <root>` can exit 0;
* for every module of the headers' closure of `root`
  (`Olean.HdrClosure`),
  `--olean --module --search-path=<dirs> -- <module>` can exit 0.

It concludes that there is a family `model : Name → (Name → List Nat → V)`
with two properties:

* for every module `m` of the closure of `root` (`Olean.InClosure`),
  `model m` is a model of the constants of `m`
  (`Olean.moduleConstants`: those of its private part, which is the
  whole module);
* if `m` sees the name `n` as the module `m'`'s (`Olean.Sees`), then
  `model m n = model m' n`.

A module `m` sees `n` as `m'`'s if the header of `m` loads a part of
`m'` that contains a constant named `n`. The loaded part is the private
part where some path of imports loads `m'` whole, else the exported
part (`Olean.Loads`).

[`main_modular_one`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L126-L134)
gives the same family from one exit 0 of
`--olean --modular --search-path=<dirs> -- <root>`.

#### A modular comparison

[`main_modular_compare`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L143-L160)
combines modular checking with comparison. Its hypotheses are the
commands that `--schedule-commands --compare -- <c> <s>` prints, each with
`--trusted-search-path=<T> --search-path=<D>`, on one snapshot:

* the graph check, `--check-graph --compare`;
* `--olean --module` at every module of the headers' closure of `C`
  and `S`, except `C`;
* the compare worker at `C`, `--olean --module --compare`.

On every snapshot that agrees with that one under the challenge's
directories, it gives the family of `main_modular` for the closure of
`C`. The constants of `C` include its holes, each as the axiom of its
statement. `main_modular_compare_one` gives the same from one exit 0
of `--olean --modular --compare`.

[`main_modular_compare_no_False`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L183-L198)
adds, under the same hypotheses, that the private part of `C` contains no
constant of type `False`, including a hole `x : False`. The family
alone does not give this: the compare worker reads `C` with the
solution loaded whole, so `C` may see `False` through `S` only, which
is outside the family.

#### The theorem over modules

The run theorems rest on a theorem about a sequence of modules
`dev : Nat → Module`,
[`modular_isModel` in `ConLeche/Model/Modular/IsModel.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Modular/IsModel.lean#L55-L61).
If every module up to `i` passes the local checks (`LocalOk`,
`ConLeche/Modular.lean`), then every such module has a model of its
own constants. Its model assigns each name in its context the value
assigned by the module from which it reads that name.

### The axioms of the proofs

The theorems use Lean's three standard axioms, `propext`,
`Classical.choice` and `Quot.sound`, and no other. The
[axiom pin in `tests/ConLecheTests/Axioms.lean`](https://github.com/leanprover/con-leche/blob/master/tests/ConLecheTests/Axioms.lean#L126-L130)
checks this with `#print axioms` guards under `lake test` (§8).

## 2. From the binary to the theorem

This section traces the path from a binary run to the model theorem in
§1. It also explains how the `.olean` reader and modular runs fit into
that path.

### The driver and its IO model

The driver parses the arguments, reads the input, and runs the checker.
Its file operations use [`CheckerIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L141),
which also provides an escape, `liftIO`, for actions such as output and
threading. The executable uses the `IO` instance of this interface.

The proofs use [`ModelIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L310),
where an action describes possible outcomes on a snapshot of the files
and a state of open handles. File operations answer according to the
snapshot; `liftIO` may return any value or exception without changing the
open handles. Results needed by the proof, such as the result of a
parallel checking phase, carry evidence of their relation to the serial
checker.

The connection to a real binary run is assumed, not proved: its file
operations must agree with one snapshot, including reads through open
handles; actions passed to `liftIO` must not change what those operations
see or end the process with exit 0; and Lean's compiler and runtime must
execute the code as written. Under those assumptions, an exit 0 of the
binary is an outcome covered by the IO model.

For the default lean4export invocation,
[`runArgs_accept`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Driver/Main.lean#L323-L327)
connects exit 0 in the model to parsing the snapshot's bytes and
acceptance by the declaration fold. The run theorems in §1 give the
corresponding statements for the covered argument lists.

### Parsing and checking declarations

The stream parser produces declaration records for the checker. Its
parallel path processes windows of lines and falls back to serial parsing
when necessary; the result of each window carries evidence that it
advances the serial parse. Thus
[`checkMainG_ndjson_accept`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/CheckMain.lean#L414-L419)
relates an accepted stream run to parsing the file as a whole and
accepting its records.

The driver can check records in parallel. It first builds an index of the
records, then checks each record against a view that exposes only earlier
declarations. Results are collected in record order. If all jobs pass,
[`checkDecls_of_jobs`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamIndex.lean#L527-L531)
gives acceptance by the sequential fold `checkDecls`.

### From the fold to a model

The proof connects the executable checker to the model in stages:

* An acceptance of `checkDecls` gives a chain of accepting declaration
  steps, [`DeclsRun`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L61-L62).
* The cached checker uses memoization. Its verified accepting steps
  correspond to steps of the fueled, memo-free checker in
  `ConLeche/Kernel/`.
* The model proof carries its environment invariant along the run
  ([`declsRun_model`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/DeclsRun.lean#L46-L48)).
  In particular, [`checkDecls_sound`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/MainC.lean#L34-L37)
  gives a model for an environment accepted in verified mode.
* `ConLeche/Semantics/` defines term denotations over the set-theory
  interface; `ConLeche/SetModel/` supplies set constructions for
  inductive types. The invariant yields the model of the input stated
  in §1.

The [layering gate](https://github.com/leanprover/con-leche/blob/master/tests/layering.sh#L1-L3)
checks the import boundaries between implementation and proof modules.

### The `.olean` reader

The `.olean` reader translates module constants into the declaration
records used by the same checker. For a closure run it reads the named
modules and their imports, merges their constants, and emits records
from the selected constants and their dependencies. The reader validates
the objects it decodes and declines unsupported format versions.

A module can have exported, server, and private views. The reader's
view specification and the executable reads are related by proofs in
`ConLeche/Verify/Frontend/Olean/`. A module's home check also checks
that its views agree. The closure run reads private views; a theorem's
value is left in the file until its declaration is checked
([`readValue`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Olean/Records.lean#L168-L169)).
The acceptance theorem for a closure run accounts for the records with
their theorem values filled in.

### Checking one module

A module worker checks a module against a context built from the
constants its records need. [`checkModuleG`](ConLeche/Driver/Worker.lean)
checks the module's views and loaded names, constructs and validates the
context, then checks the module's own records against it. Imported
statements can be used without checking imported proofs again in that
worker.

The worker's acceptance theorem describes its own run. The modular proof
relates the context records to the workers that checked their source
modules, so that their models agree on the constants visible between
modules (§1).

### Every module of a closure

Modular checking combines an import graph check with a worker for each
module in the closure. The graph check validates an ordering in which
imports precede their importers. `--olean --modular` runs the checks in
one process; `--olean --schedule` starts separate module workers. The
scheduler's result is based on the workers' exit codes, while the modular
theorem composes the graph and worker results on one snapshot. See §0 for
commands and scheduler options.

### Comparing a challenge and a solution

Comparison checks the solution and uses it to justify the challenge's
holes (§1). For lean4export files and ordinary `.olean` comparison, the
solution is checked first, then the challenge is checked with the
solution's environment. A hole must have a matching name and statement,
and the constants its statement depends on must agree across the two
environments. The `.olean` comparison reads the challenge through the
trusted search path and the solution through the trusted path followed by
the ordinary search path.

Modular comparison instead adds the solution to the challenge worker's
imports. The worker checks challenge records against that context and
compares records whose names are already loaded. The graph and the other
module workers check the combined closure; §1 states the resulting
model guarantee.

`ConLeche/Challenge.lean` states the binary's main theorems with holes
for functions of the implementation. `comparator.json` identifies the
targets for `lake comparator`, and the self-check also compares the
challenge with `ConLeche/MainTheorem.lean` using ConLeche itself.

## 3. The checker

The checker infers types, reduces terms and compares them for definitional
equality. It follows the shape of Lean's kernel, with the differences
described below and in §14.

### Checking modes

The checker has two [modes](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L55):

* `--verified` is the default and is covered by the soundness theorem.
* `--trusted` omits checks used for the soundness proof that the official
  kernel does not make. It is outside the theorem.

Both modes use the same core. Verified mode includes extra checks on lambda
expressions and certificates for some reduction steps; the proof uses their
results.

### Reduction and definitional equality

The checker reduces terms to weak-head normal form and uses reduction to
compare terms for definitional equality. `whnfCore` performs β, ζ, ι,
projection and quotient reduction; [`whnf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1157)
also unfolds definitions and reduces supported `Nat` operations on literals.
Theorems are opaque: reduction never unfolds their values.

[Definitional equality](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1866-L1884)
uses lazy unfolding, function and structure η, proof irrelevance, and the
inductive type's flags for unit-likeness and K-like reduction. It tries easy
cases and proof irrelevance before head-normalizing the terms. For certain
fully applied constructors of non-propositional types, it can head-normalize
the other term immediately to compare constructor heads.

### Recursor reduction

A recursor normally reduces when its major premise reduces to a constructor.
The checker can also construct a suitable major premise from its type or
projections before reducing it. This rescue applies to K-like recursors and
eligible structures. If a K-like rescue fails, the major premise is left
unreduced.

The checker also rescues a stuck proof `h` of `And a b` by constructing
`And.intro a b h.1 h.2`. In verified mode it checks the constructed proof
against `h` using proof irrelevance. This allows `And.rec` to reduce even
when `h` is an opaque theorem. The declaration of `And` is pinned (§5).

### Type inference

The checker uses full inference for a declaration's own terms and
[infer-only inference](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1341)
for terms encountered during reduction and equality checking. Infer-only
inference skips checks on application arguments, lambda domains, and
let-expression types and values. Verified mode also compares the types of
opened lambda bodies when comparing lambda expressions and during η
comparison.

### Fuel and caching

The pure checker uses fuel to bound recursion; exhausting it is an error,
not a rejection of the input. Reduction loops have separate fuel budgets.
The cached checker uses memoization, and
[`checkDeclStepC_run`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/BridgeC.lean#L285)
relates a successful verified cached declaration check to a successful pure
check with sufficient fuel.

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
([theorem `Denotes_of_denote` in `ConLeche/Model/Denotes.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L194-L200)).
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
([function `recFire` in `ConLeche/Kernel/Install.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L39)).
After the install, each recursor's ι equations must read off its own
type the way the main theorem's statement reads them: the minor premise
of each rule, found by position among the minor premises of the
recursor's motive, has the constructor's fields, indices and parameters
— the indices, levels and parameters syntactically, the fields' types
syntactically up to equivalent universe levels and up to Lean's type
annotations (`optParam`, `autoParam`, `outParam`, `semiOutParam`),
which Lean's kernel consumes in every local of an inductive declaration
and which are consumed here only where the annotation is stored as the
identity on its type, as the prelude defines it, and only in a rule at
the recursor's own parameters whose parameter types are the
constructor's up to the same consumption
([function `blockReadsOk` in `ConLeche/Kernel/Inductives/IotaRead.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/IotaRead.lean#L211)).
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
([structure `StoredFacts` in `ConLeche/Verify/EnvExt/Reads.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/EnvExt/Reads.lean#L28-L29)).
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
[function `checkSumCtor` in `ConLeche/Kernel/Inductives/SumInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/SumInstall.lean#L77),
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
bodies the module system hides (`Init.Data.Repr`, the Nat-op certificate generator's `Init.Data.Nat.*`),
and every such line carries its reason.

## 11. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The binary's entry point: the plumbing around `runArgs` at `IO`, followed by the exit. |
| `ConLeche/Driver/` | The proof-carrying IO driver: the index build and the check phase's worker pool (`CheckPool.lean`), the rounds parse's owner threads (`OwnerParse.lean`), the stream parse over the IO class's folds (`StreamParse.lean`), the end-of-run statistics (`Stats.lean`), `checkDeclsIO` (`Run.lean`), a module's context for checking it on its own (`Reach.lean`), the check of one module against it (`Worker.lean`), the tables a run reads up front, each module located once (`Tables.lean`), the import graph check (`Graph.lean`), every module of a closure in one process (`Modular.lean`) and by one worker process each (`Schedule.lean`, the subtree `Schedule/`: the policy, the worker, the log, the status, `/proc` and the run), a challenge compared with its solution (`Compare.lean`, and as two lean4export files `CompareJson.lean`) and as one module of a modular run, with the compared graph check (`CompareModule.lean`), the driver's sequencing generic in the IO class (`CheckMain.lean`), the run of a request (`Dispatch.lean`) and the command line and `runArgs` over them (`Cli.lean`). Checker code, like `Kernel/*`; the one tier besides `Main.lean` that may import `ConLeche/Verify/*`. |
| `ConLeche/Kernel/` | The specification, the pure checker the proofs are about: `Expr`/`Level`/`Name`, what a declaration adds (`Install.lean`), `PropWhen`, the mutually recursive core of reduction, inference and conversion (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the inductive installer (`Inductives/`: the recogniser `BlockShape.lean`, the positivity check `Positivity.lean`, the entry `checkBlock` with its constructor stages (`Sum*`) and projection tables (`Struct*`), the recursor generator and check `GenRec.lean`, the ι equations read off a recursor's own type (`IotaEq.lean`) and the rule that they are the ones through its constructors (`IotaRead.lean`), and `ClassRead.lean`, which reads the classes off the stream's recursor types without checking them), the Nat-op pins, and `natBigHash` (`NatHash.lean`), the hash of a big `Nat` literal, the one function in C (`native/nat_hash.c`). Imports no theory module. The binary runs the cached tier's twins in its place; of this tier it runs only the shared helpers the reach gate lists (§12). |
| `ConLeche/Cached/` | The shipped cached checker: hashed expressions, memo state, the cached core and declaration step, the parsed-record step (`ParsedC.lean`), the cached twins of the whole inductive check (`Ind*.lean`: the formers and constructors, positivity, the classes, the recursor stage and the tail), each related to its specification in `Kernel/Inductives/` by an equation or a simulation triple (`Verify/Cached/Ind*C.lean`, `GenRecC.lean`), the declaration fold `checkDecls` and its accepting runs (`Decls.lean`), the index of a stream and a record's job (`StreamIndex.lean`). |
| `ConLeche/Frontend/` | The export parser: the dialect's byte recogniser and syntax records (`Scan/`) and the semantic layer over them (`ExportC.lean`), which decodes the file's records and nothing else, and its result type (`ParseResult.lean`); the checker's IO class, its model over a snapshot of the files, the binary's instance and the folds over a file handle's reads (`CheckerIO.lean`); the serial streaming driver and a chunk's scan into syntax records apart from their application (`Stream.lean`); the rounds parse's counters and finished tables (`Rounds.lean`) and its rounds (`RoundsWork.lean`); the preparation of the fold's input (`Prepare.lean`, with the built-in prelude of `Prelude.lean` and the reordering of `NatOpGround.lean`, which moves what a pinned Nat operation's certificates mention ahead of it); the `.olean` reader (`Olean.lean`, the interface, over `Olean/`: the byte region `Region.lean`, the specification decoder `Spec.lean`, the fast one `Fast.lean`, the sparse one `Sparse.lean`, the imports off a file's start `Header.lean`, the reads of a part of a region `Reads.lean`, a module's views `View.lean` and their checks against each other `Module.lean`, the files through the IO class `Files.lean`, what a snapshot's files say by the specification (a module's view, the closure, what a header loads, snapshots that agree under some directories) `Snapshot.lean`, the closure `Closure.lean`, the merge `Merge.lean`, the emission `Emit.lean`, the records `Records.lean`, the header fixpoint `Levels.lean`, the loaded names and the clash rule `Index.lean`, and one group's record `Group.lean`). |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/Term/` | The term language the denotation targets and the interpretation reads, its substitution operations and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and nested tuples, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The interpretation, the semantic invariant, the semantics of inductive blocks, the declaration-level facts, what `False` and `Eq` are in every model of a stream declaring them (`IsModelBasis.lean`), and that an accepted stream with a constant of type `False` declares `False`, whose models hold no such constant (`NoFalse.lean`). |
| `ConLeche/Rules/` | The relational description of the core checker: mutually inductive relations over the checker's own `Expr` — reduction, definitional equality, η-expansion, unit-likeness, type inference (checking and infer-only), and the certificate checks — with fuel, unfolding heuristics and dispatch order out of sight (`Rel.lean`), the derived rules (`Derived.lean`), and the derivations at an environment holding some definitions as their statements, which are derivations at the environment holding them with their values (`Refine.lean`). Imports the fuel-free helpers of the kernel and nothing else of it. |
| `ConLeche/Verify/Rules/` | The bridge: an accepting run of a kernel function, at any fuel, yields a derivation (`Bridge.lean`, from one step theorem per entry point and the certificate bridges); composed with the rules at a refinement, an accepting run at an environment holding some definitions as their statements, a former's reduced telescope included, is a derivation at the environment holding their values (`Refine.lean`). |
| `ConLeche/Model/` | The graded set model of the checker: the environment invariant and its laws (`Env/`), the facts about the stored-term reading `denote` that read the environment invariant (`Reading/`), the claims, the soundness of the rules tier's derivations (`Rules/`: the motives, the environment inputs, one lemma per rule over shared kits, the master induction, and the recomposition of the claims from the bridge), the run-stated remainder the declaration fold reads (`Tiers.lean`), the declaration step, the inductive installs (`Inductives/`, `Ind*`), the Nat-op certification, the final theorems (`Capstone.lean`), the model read through the relation `Denotes` (`Denotes.lean`), and that model carried to a model of the input (`IsModelBridge.lean`, with what the ι reading rule means, `IotaReadSem.lean`). |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: what an accepted stream stores of its records and which pinned blocks it declares (`IsModelRecords.lean`), the ι reading rule as a fact about the stored recursors (`Inductives/IotaRead.lean`), the terms every part of which reads (`Resolves.lean`), well-formedness, scoping, the stored-term reading `denote` and its metatheory (`Denote.lean`, `Denote/`: inversions, depth shift, instantiation, closedness, environment extension), the cached-to-pure simulation (`Cached/`: the core's congruence in the lookup (`KnotCongr.lean`), the block tail's in-place pushes (`BlockOverlay.lean`), every stage's congruence in the index (`ViewCongr.lean`), every job passing is an accept of the fold (`StreamIndex.lean`, which `ConLeche/Driver/CheckPool.lean` imports), and a record's constants, tables and names as the worker's reach computes them, the cached twins in the specification's place (`DeclNames.lean`, which `ConLeche/Driver/Reach.lean` imports)), the inductive installer's kernel-side invariants (`Inductives/`), and the parser's (`Frontend/`: line locality, the parse as a line fold, chunk independence, what a line does to the parse state, the template's lines, the characterisation of the serial fold over a stream that binds in increasing order, good entries and the tables they make (`Good.lean`), and that the rounds keep good entries and a window is one more stretch of the serial parse (`RoundsWork.lean`, `Rounds.lean`), the runs of the IO model and the folds over a file's reads in it (`ModelIO.lean`), that the stream's reads in it put together are the file (`StreamModel.lean`), and the `.olean` reader's decoders and reads (`Olean/`)), and all of `main` in the IO model at the arguments `-- <file>` (`Driver/Main.lean`), its accept on a `jsonWithTheoremFalse` file a stream with a constant of type `False` (`FalseRuns.lean`), with an `--olean` run's check phase (`Driver/Oleans.lean`), a module's context (`Driver/Reach.lean`), where it read each record (`Driver/ReachFrom.lean`) and what that record presents (`Driver/Provenance.lean`, `Driver/Groups.lean`), one module checked alone (`Driver/Worker.lean`), reads answered from tables refining the files' (`Driver/Shared.lean`), every module of a closure in one process (`Driver/Modular.lean`), a compared run (`Driver/CompareRun.lean`) and one of two lean4export files (`Driver/CompareJsonRun.lean`), a compared closure's run, its challenge's worker one with the solution added (`Driver/ComposeCompare.lean`), the challenge's read local to the trusted directories (`Frontend/Olean/Local.lean`), the import graph check's validation (`Driver/Graph.lean`), and what a module of a run sees against its worker: the header fixpoint loads what `Loads` derives (`Driver/LoadsAll.lean`), a seen name is a copy of the worker's index (`Driver/SeesLoads.lean`), a module's constants are its own records', or at a compared challenge the copies' loaded constants (`Driver/SeesOwn.lean`), a seen name agrees with the context (`Driver/SeesCtx.lean`), and what a module sees moved between snapshots and to a lookup's full form (`Driver/SeesMoves.lean`). |
| `ConLeche/Accepts.lean` | The file-level vocabulary of the statement: `jsonWithTheoremFalse`, the whole-file template of one JSON file that declares a theorem of type `False`. |
| `ConLeche/IsModel.lean` | The statement's semantics: the total reading of a term (`Expr.eval`), the recursors' rules as propositions read off their own types (`RuleHolds`), and what a model of a declaration stream is (`ModelOf`, `IsModel`); imports nothing from the proof tiers. |
| `ConLeche/Denotes.lean` | The proofs' model of an environment: what a term denotes (`Denotes`) and what a model of an environment is (`Model`), which the proofs build and read; the theorems state `IsModel` (`ConLeche/IsModel.lean`). |
| `ConLeche/Modular.lean`, `ConLeche/Modular/` | Modular checking's statement half: a module's context as the records its imports present, the local checks per home (`InterfaceOk`) and per importer (`ImportOk`), copies agreeing (`Agree`: one record, or two proofs of one statement); and the theorem over an abstract interface of models (`Modular/Generic.lean`, the whitepaper fragment's), whose instance for con-leche's models is `ConLeche/Model/Modular/`. |
| `ConLeche/Model/Modular/` | The modular theorem at con-leche's models: a module's own records installed on its context's model, keeping every context leaf and every proof's leaf the canonical proof (`ProofLeaves`, `Proofs.lean`, `Step.lean`); a context read from its sources, stated without modules (`Read.lean`), and derived from the local checks (`Valid.lean`); the context's model built from its sources' models, every law of a context constant read off its source's (`Restrict*.lean`); the instance of the abstract interface (`Instance.lean`) and the compatible family (`Main.lean`); the family over what each module sees, at an accepted run and at the driver (`Sees.lean`, `SeesMain.lean`), and at a compared run, over the challenge's closure (`SeesCompare.lean`); a copy at other level-parameter names holds where its stored constant does (`ConLeche/Model/IsModelRename.lean`). |
| `ConLeche/Model/Solution/`, `ConLeche/Model/Solution.lean` | A stream checked with a solution has a model: the solution's model renamed to the input's level-parameter names (`Rename.lean`, over `ConLeche/Model/CopyStmt.lean`), a record of shared names given the solution's leaves (`Shared.lean`, through the context reading of `Model/Modular`), a justified axiom given the solution's value (`Justified.lean`), the input's fold (`Fold.lean`) and the assembly (`Solution.lean`). The justification's accept read as a closed shared set is `ConLeche/Verify/Cached/Cone.lean`, the record mates `Mates.lean`. |
| `ConLeche/Model/IsModelCompare.lean`, `ConLeche/Verify/CompareInput.lean` | `--olean --compare`'s accept has a model of the challenge's closure read through the trusted directories: the checked records store every constant of the closure (`chalChecked_inputStored`, a theorem read as a hole stored as the axiom of its statement), the closure's constants are the same on every snapshot agreeing under those directories (`closureConstants_local`), and a theorem of type `False` there is never accepted |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The main theorems: for each way of running the binary, its accepted input has a model, and some say that it holds no constant of type `False`. The JSON ones' proofs are `ConLeche/Model/IsModelJson.lean`'s, over the checking function's own theorems (`model_exists`, `solution_model_exists`, `ConLeche/Model/PureChecker.lean`). `Challenge.lean` states the theorems about the runs with `sorry`, with the binary's functions they name as holes and specification imports only; `scripts/selfcheck.sh` checks it against `MainTheorem.lean` with con-leche itself. |
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
dump freshness, the challenge gate (`tests/challenge.sh`: the
challenge module builds with its `sorry` warnings and nothing else),
the self-check (`scripts/selfcheck.sh`: con-leche's `--compare` of the
challenge against the solution, from the `.olean` files and from the
exporter's JSON, accepts both and justifies exactly the names
`comparator.json` lists),
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
* A recursor's minor premise may consume a type annotation of its
  constructor's field only where the annotation is stored as the
  identity on its type (an `autoParam`'s argument type inhabited by a
  stored constant), in a rule at the recursor's own parameters whose
  types are the constructor's up to the same consumption (§5). The
  official kernel consumes `optParam`, `autoParam`, `outParam` and
  `semiOutParam` by name. No recursor Lean writes is rejected.
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
* In modular checking, every name two loaded modules store has the
  statement of each copy checked as its own module reads it, and a
  name whose statement means two things there is rejected (§2). Lean's
  import accepts the pair, since it compares the two statements as
  expressions. This is a bug in Lean's module system: such a pair
  arises only where a module exports a constant whose statement reads
  a name of a private import, which a correct build rejects; only a
  stale or hand-made build produces it.
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
