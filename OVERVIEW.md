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
([`helpText` in `ConLeche/Driver/Cli.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L131)).

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
[`checkDecls_of_jobs`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/StreamIndex.lean#L529-L533)
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
projection and quotient reduction; [`whnf`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1211)
also unfolds definitions and reduces supported `Nat` operations on literals.
Theorems are opaque: reduction never unfolds their values.

[Definitional equality](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1941-L1959)
uses lazy unfolding, function and structure η, proof irrelevance, and the
inductive type's flags for unit-likeness and K-like reduction. A recursor of a
K-like or η type, applied to fewer arguments than its major premise needs, is
η-expanded and ι-reduced
([`recEtaCert`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1006)). It tries easy
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
[infer-only inference](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1395)
for terms encountered during reduction and equality checking. Infer-only
inference skips checks on application arguments, lambda domains, and
let-expression types and values. Verified mode also compares the types of
opened lambda bodies when comparing lambda expressions and during η
comparison, and the type of the reduct with the expected type when it
η-expands a partially applied recursor.

### Fuel and caching

The pure checker uses fuel to bound recursion; exhausting it is an error,
not a rejection of the input. Reduction loops have separate fuel budgets.
The cached checker uses memoization, and
[`checkDeclStepC_run`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Cached/BridgeC.lean#L289)
relates a successful verified cached declaration check to a successful pure
check with sufficient fuel.

## 4. The proof idea

The proof connects successful checker runs to the set model of §1.
It establishes semantic guarantees directly, without a syntactic typing
judgement or an accepted-implies-derivable theorem.

### Terms and interpretation

The proof interprets an intermediate term language before relating it
to the statement of the main theorem. A checker expression is read at
concrete universe levels as a
[`Term`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Term/Syntax.lean#L188-L219),
with de Bruijn indices and built-in constants.

[`interp`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/Interp.lean#L134-L145)
maps every such term to a set, without requiring it to be well typed.
As in §1, propositions are subsets of a one-element set; its element
is the proof point. The interpretation chooses the treatment of a
Π-type or lambda-expression from the values of its body.

The model that the proofs build for an environment instead uses
`Denotes`, a relation on checker expressions; the main theorem's
`IsModel` (§1) is obtained from that model. [`Denotes_of_denote`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Denotes.lean#L194-L200)
connects the two: under its scoping and closedness assumptions, the
interpretation of a successful reading is a `Denotes`-denotation of
the expression after closing its free variables.

### The semantic invariant

[`WellDenoted`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Semantics/WellDenoted.lean#L49-L72)
records the conditions the interpretation needs, recursively through a
term. For example, a binder's domain must denote a type, and an
application must apply either the proof point or a function graph to a
member of its domain. The environment model
[`EnvModel`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Env/EnvModel.lean#L35-L63)
records the invariant and closedness for constant readings, together
with facts about the stored environment and pinned basis constants.

### Claims about the checker

The proof states semantic claims for successful reduction, equality
checking and inference, subject to their scoping, environment and
reading assumptions. The
[claim definitions](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Claims.lean#L49-L125)
give the precise conditions:

* Reduction preserves the denotation and `WellDenoted` when the original
  term does not denote the proof point.
* If definitional equality succeeds, the denotations are equal wherever
  neither is the proof point.
* Full type inference returns a type whose denotation contains the
  term's denotation.

The point condition still gives equality when comparing types, since a
type is not the proof point. It also gives equality between two members
of the same type: either both are the point or neither is.

Infer-only mode has a weaker, recursive guarantee,
[`IORel`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/IORel.lean#L53-L79).
The term denotes the point, belongs to its inferred type, or, when that
type is syntactically a Π-type, denotes a graph whose applications
satisfy the same guarantee at the Π-type's body. This weaker claim
accommodates checks that infer-only mode omits.

### From checker runs to claims

The proof factors the checker claims through a relational description
of its operations. The
[relations](https://github.com/leanprover/con-leche/blob/master/ConLeche/Rules/Rel.lean#L18-L47)
describe reduction, definitional equality, inference and auxiliary
checks on the checker's expressions. Their rules capture the checks
needed for soundness while leaving fuel and dispatch details out.

The argument has three steps:

1. The [bridge](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Rules/Bridge.lean#L29-L32)
   turns a successful checker run into a derivation of the corresponding
   relation.
2. The [soundness proof](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/Sound.lean#L76-L79)
   proves the semantic conclusion by induction on the derivation, using
   laws of the environment.
3. [Recomposition](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Rules/Recompose.lean#L49-L54)
   combines the bridge and soundness to establish the checker claims at
   every fuel value.

The proof does not need Π-injectivity. For an application, inference
reduces the function's type to a syntactic Π-type; the interpretation
of that type supplies the function-space property needed for the
application. The argument uses accepted definitional equality to prove
equality of denotations, not the converse.

### From claims to declarations

The declaration checker uses these claims to extend the environment
model. For a definition or theorem, it checks the value against the
stated type; inference and definitional equality justify membership in
the type's denotation. The declaration step also covers inductive
installs (§5) and the Nat operations (§6).

## 5. Inductive types

The checker installs inductive declarations as blocks, including mutual and
nested blocks. It checks the input records and generates recursors against
which to compare the recursors supplied by the stream.

### The installer

The installer checks type formers, constructors, positivity and recursors
before adding a block to the environment
([`checkBlock` in `ConLeche/Kernel/Inductives/BlockTail.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockTail.lean#L161)).
It supports parameters and indices, recursive and function-valued recursive
fields, and nested occurrences such as `List T`. Blocks may be in `Prop` or
`Type`. The checks include uniform application of parameters, universe bounds
and elimination restrictions.

For a nested occurrence, the positivity check examines the stored
constructors of the container at the actual instantiation. It records their
normal forms for recursor generation and the model
([`checkBlockPositivity` in `ConLeche/Kernel/Inductives/BlockInstall.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockInstall.lean#L284)).
The official kernel instead transforms nested declarations into an auxiliary
mutual block.

The checker generates recursor types and rules from the checked constructors
([`genRecCheck` in `ConLeche/Kernel/Inductives/GenRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/GenRec.lean#L552)).
It compares the stream's recursors with the generated ones, including their
rules, and installs the stream's records when they agree
([`streamRecsCheck` in `ConLeche/Kernel/Inductives/StreamRecs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/StreamRecs.lean#L187)).
The input must contain recursor records; the official kernel generates its own.
The checker also verifies that the recursors' minor premises describe the
constructors as required by the theorem's ι equations
([`blockReadsOk` in `ConLeche/Kernel/Inductives/IotaRead.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/IotaRead.lean#L211)).

A type former may be declared at a type that reduces to a telescope, such as
`def MyType := Type` followed by `inductive S : MyType`. The environment keeps
the declared type; the checks use its reduced telescope
([`familyTelescope` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L99)).
Some such declarations are declined, including a `Bool` former at a
definition. A nested occurrence is rejected if its container or a member of the
container's block is def-headed and is absent from the families shown
syntactically in the block's constructor types.

### Feature flags

An inductive type's record may declare the feature flags `isImpredicative`,
`isK`, `hasProjections`, `hasEta` and `hasLargeElim`. The checker takes them as
inputs and rejects a block whose declaration does not allow them
([`blockFlagsCheck` in `ConLeche/Kernel/Inductives/StreamRecs.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/StreamRecs.lean#L258)):

* `isImpredicative` and `hasLargeElim` agree across the block;
  `isImpredicative` holds only at a proposition.
* `hasLargeElim` matches the eliminator of the recursor records. It requires
  a block that is not impredicative and either has a sort that is never zero,
  or is a single type with no constructor, or has one constructor with
  `hasEta` or `isK`.
* `isK` holds only at the first type of a single-type block that is a
  proposition with one constructor without fields.
* `hasProjections` requires one constructor, no index and a type that is not
  impredicative; `hasEta` requires `hasProjections` and a block that is not
  recursive.

A flag that is off withdraws its feature. Without `hasProjections` a type has
no projection table, so its projections are rejected; without `hasEta` it has
no structure η and is not unit-like; without `isK` it has no K-like reduction;
without `hasLargeElim` the recursors have no rules, and a recursor record with
rules is rejected. A proposition that is neither impredicative nor large
eliminating must have propositions as fields.

Nested occurrences are checked against the flags the official kernel's
auxiliary types would get: a nested proposition with one constructor without
fields is rejected, an impredicative block may not nest a type with
projections, and in a proposition whose fields must be propositions, so must
the fields of a nested container's constructors
([`nestFrameSorts` in `ConLeche/Kernel/Inductives/Positivity.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/Positivity.lean#L794)).

A block whose records declare no flags is checked at flags derived from its
declaration
([`derivedFlags` in `ConLeche/Kernel/Inductives/BlockShape.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Inductives/BlockShape.lean#L155)):
impredicative exactly at a proposition, K-like under the conditions above,
projections and η where the type is structure-like (η only in a block that is
not recursive), and the eliminator its recursor records declare. Its large
eliminator is allowed by the per-field criterion of §14, and a small
eliminator keeps its rules. The records' `isReflexive` key is optional and
ignored.

### Pinned declarations

The checker reserves the declarations of `Eq`, `Nat`, `Empty` and `False`.
Their blocks pass through the ordinary installer, but must also match their
pins up to the names of universe parameters; other declarations cannot take
the reserved names
([`basisNamesOk` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L144-L151)).
The pins support the model's interpretation of these types and the checker's
handling of numeric literals and `Nat` operations (§6). The declarations of
`False` and `Eq` also determine their meanings in any model as described in §1.

`Quot` is a kernel primitive, not an inductive type. Its records, including
`Quot.sound`, must match their pins; the quotient eliminators and their
reduction rule are primitive as well (§8)
([`quotPinHit` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L205-L206)).
`Quot` and `Quot.sound` have two forms: `Quot` at `Sort u` with `Quot.sound`'s
equation in `Eq.{u}`, or at `Sort (max 1 u)` with `Eq.{max 1 u}`, in which a
quotient of a proposition is a type. The checker stores the form a record
declares, so proof irrelevance applies to quotients of propositions only in
the first form. A `Quot.sound` in a different form from the stored `Quot` is
rejected
([`quotFormOk`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L231)). The model builds
the quotient at the level of `Quot`'s declared sort.

`And` is pinned because the checker constructs an `And.intro` application
when rescuing a stuck proof (§3). A declaration using a name in the `And`
block must match the pin
([`andPinOk` in `ConLeche/Kernel/Basis.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis.lean#L251-L256)).
The matching block uses the ordinary installer. If the stream does not declare
`And`, the built-in prelude supplies it (§6).

### The model of a block

The model interprets an inductive block using a least fixed point of families
indexed by the types' indices. For mutual blocks it uses a least fixed tuple of
families; nested fields use the container's own fixed point. The positivity
check supports the accessibility argument that places the fixed point in the
universe
([`closed_of_acc` in `ConLeche/SetModel/Access.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/Access.lean#L243)).

A recursor is interpreted using the least relation closed under its rules. The
block's induction principle shows that this relation gives a unique value at
each major premise
([`ConLeche/SetModel/GraphRec.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetModel/GraphRec.lean#L36-L40)).
The model construction for an installed block is proved by
[`declBlock` in `ConLeche/Model/Inductives/BlockRunFacts.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/Inductives/BlockRunFacts.lean#L127-L136).

## 6. The Nat operations

ConLeche reduces certain `Nat` operations on literals using Lean's `Nat`
implementation. It checks the definitions and certificates needed to justify
this fast path.

### Structural operations

The checker certifies the recurrence equations for `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.beq` and `Nat.ble`. It also certifies `Nat.pred`,
which is used by `Nat.sub` but has no literal fast path of its own. The
[operation list](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L458-L466)
identifies the certified names.

When checking a definition at one of those names, the checker verifies its
expected type and checks its recurrence equations by definitional equality.
It performs the equation checks before storing the operation, so the operation's
own fast path cannot justify them. A definition that fails these checks is
declined. The model proof derives the literal results
from the certified equations
([`natOps_install`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/NatEqs.lean#L1046)).

### Well-founded operations

The checker also accelerates `Nat.div`, `Nat.mod`, `Nat.gcd`, `Nat.land`,
`Nat.lor`, `Nat.xor`, `Nat.shiftLeft` and `Nat.shiftRight`. For these
operations it embeds definitions and certificate proofs from supported Lean
toolchains ([`NatOpPins.lean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16)).

To accept a definition, the checker must match it by definitional equality to
a pinned definition, match the relevant pinned types, and check the associated
certificate proofs. The certificates characterize the operation using
`Nat.ble`; the model proof uses their checked statements to justify literal
reduction ([`divMod_install`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/DivModCert.lean#L1968)).
The soundness theorem is parameterized by the list of pins.

### Bool and declaration order

The comparisons return `Bool` constructors, and the well-founded operations'
certificates use `Nat.ble`. The checker therefore requires `Bool` and its
constructors to have the expected types before accepting the relevant
operations ([`natOpGuard`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L611-L638),
[`natOpCod`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/CoreDefs.lean#L669-L676)).
`Bool` is installed from the stream like other inductive blocks; it is not
pinned.

The built-in prelude holds the four pinned inductive blocks, `Bool` and
`And`; quotient records come only from the stream. Before checking
declarations, the frontend puts the built-in prelude first,
using the stream's own declarations where available, and moves the structural
operations needed by certificates ahead of the corresponding well-founded
operations ([`preparePrelude`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Prepare.lean#L167-L174)).
The prepared records are a permutation of the stream's records together with
any missing prelude records
([`preparePrelude_perm`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L171-L176)).

### Maximum numeral size

The checker rejects numerals and certain computed results above a byte limit,
defaulting to 128 MiB and configurable with `--max-nat-size`. Size is measured
in 8-byte units, with a minimum of 8 bytes. The checker tests literals when
inferring their types, and tests results of `Nat.succ`, `Nat.add`, `Nat.sub`
and `Nat.mul` after computing them.

For `Nat.pow` and `Nat.shiftLeft`, the checker can refuse an operation before
computing its result based on its operands. It also refuses an exponent that
does not fit in 32 bits, and a shift count that does not fit in 32 bits when
the shifted value is nonzero
([`natOpRefusal`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/StateC.lean#L239-L252)).
A refusal rejects the declaration.

## 7. The set-theory assumption

The soundness theorem assumes a set theory in which to construct a model
of the accepted declarations. This section describes that assumption and
its relation to a consistency analysis of Lean.

### The interface

The [`SetTheory` class](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L95-L133)
specifies membership, extensionality, pairing, union, power set,
regularity and replacement for arbitrary Lean functions. It also assumes
an ω-chain of Grothendieck universes, each a member of the next; the
[`IsTGUniverse` predicate](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L89-L93)
states universehood in Tarski's form with transitivity.

Infinity is derived from the interface, and choice comes from Lean's
meta-logic. The derived set operations are in `ConLeche/SetTheory/Derive/*`.

### The bridge and relative consistency

The separate `bridge/lean4lean-model` package relates the interface to
Carneiro's consistency analysis of Lean. Its theorem
[`carneiro_implies_conleche`](https://github.com/leanprover/con-leche/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202)
constructs a `SetTheory` instance on Mathlib's `ZFSet` from a strictly
increasing ω-sequence of inaccessible cardinals, the hypothesis used in
that analysis. The main ConLeche libraries do not depend on Mathlib.

The consistency result is relative to the existence of a `SetTheory`
instance: under that assumption, an accepted input with Lean's `False`
declaration cannot also declare a constant of type `False` (§1). The
Lean proof does not establish the existence of such an instance without
an additional assumption, so it does not prove Lean's own consistency
unconditionally.

## 8. Axioms

This section describes which axiom declarations the checker accepts and
how it handles compiler-trust declarations.

### Standard axioms and `sorryAx`

The checker accepts `propext` and `Classical.choice` after checking their
[pinned types and prerequisite inductive shapes](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/StdAxioms.lean#L185-L214).
Both are true in the set model: `propext` by extensionality of
propositions and `Classical.choice` by choice. `Quot.sound` belongs to
the pinned `Quot` block.

The checker checks a `sorryAx` declaration for well-formedness but
installs nothing for it. A declaration that uses `sorryAx` is declined,
and a declaration of another kind at that name is rejected. In ordinary
checking, other non-standard axioms are declined; comparison mode can
accept a challenge axiom justified by the solution (§1).

### Compiler-trust declarations

The checker handles the [compiler-trust family](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/TrustAxioms.lean#L9-L38)
using pinned declarations:

* `Lean.trustCompiler` is installed as an opaque with value `True.intro`.
* `Lean.reduceNat` and `Lean.reduceBool` are checked as opaques, with
  their values checked for definitional equality to the identity function.
* `Lean.ofReduceNat` and `Lean.ofReduceBool` are accepted with pinned
  types only after the corresponding reduce operation has been installed.
  Their statements are true in the model because that operation is the
  identity.

### Native evaluation

Axioms generated by `native_decide`, `decide +native` and `bv_decide`
are declined in ordinary checking. The diagnostic identifies the tactic
from the generated axiom's name. ConLeche does not run native code or
run a decision procedure to establish the proof.

## 9. What the theorem does not cover

The soundness theorem has limits at the input, runtime and command-line
boundaries. This section describes those limits and points to the covered
runs in §1.

### Input interpretation

For lean4export input, the theorem describes the parsed declaration records;
it does not prove that the decoder preserves the meaning of the export file.
[`preparePrelude_perm`](ConLeche/Verify/Frontend/Prepare.lean) shows that
preparation retains every parsed record unchanged and adds only prelude
records; the fold checks the resulting declarations (§5 and §6).

For `.olean` input, the theorem uses ConLeche's
[`decodeModuleSpec`](ConLeche/Frontend/Olean/View.lean). Agreement with
Lean's loader is tested on `Init` by `tests/olean-compare.sh`, not proved.
The ordinary `--olean` closure run reads private views without comparing a
module's views, so its theorem does not describe the exported view seen by
an importing module. A module home check compares the views (§2).

### Runtime assumptions

The connection between a real run and the IO model is assumed (§2): file
operations must agree with one snapshot, `liftIO` actions must not change
what those operations see or terminate the process with exit code 0, and
Lean's compiler and runtime must execute the code as written. A theorem
composing several runs assumes the same snapshot for all of them.

The checker also uses a C function to hash large `Nat` literals; the proof
assumes it behaves as a function of the number. The boundary is described
in [`CheckerIO`](ConLeche/Frontend/CheckerIO.lean), and
`tests/trust-surface.sh` checks parts of it textually.

### Runs and results

The run theorems cover the exact argument forms listed in §1. They do not
cover `--trusted` or the scheduler's own result (`--schedule`); the modular
theorem instead composes the graph check and module worker results (§2).
A decline or rejection carries no soundness claim.

The soundness proof does cover the checker's deliberate acceptances beyond
the official kernel. §14 lists those and the other departures.

## 10. Naming conventions

Names in the checker and its proofs use recurring markers for variants and
well-formedness conditions.

| Marker | Meaning | Example |
|---|---|---|
| `C` | A cached-checker counterpart of a pure definition | [`checkDeclC`](./ConLeche/Cached/ParsedC.lean) |
| `I` | A variant that also handles an inductive family's index arguments | [`checkStructFieldSortsI`](./ConLeche/Kernel/Inductives/SumInstall.lean) |
| `F` | A definition over `FEnv`, an environment with a lookup index | [`natLitSupportedF`](./ConLeche/Kernel/FEnv.lean) |
| `D` | The direct parser or a function over its output | [`parseExportD`](./ConLeche/Frontend/ExportC.lean) |
| `AV` | A `Term` used by the semantic and model tiers | [`sumTyAV`](./ConLeche/Semantics/Tower/SumTower.lean) |
| `WF` | Well-formedness | `EnvWF`, `BlockWF` |
| `_pure`, `_cached` | Theorems about the pure fueled fold and the cached fold, respectively | [`no_proof_of_False_pure`](./ConLeche/Model/Fold.lean), [`no_proof_of_False_cached`](./ConLeche/Verify/Cached/MainC.lean) |
| `Fueled` | A helper applied to the pure functions at a given fuel | [`iotaRecFueled`](./ConLeche/Verify/Knot.lean) |

### Module visibility

The module headers distinguish exposed implementation bodies from proof
interfaces. Checker files use `@[expose] public section` so the proofs can
unfold their definitions. The term language, set-theory interface, set
constructions, and semantics likewise expose their bodies. Model and
verification files use `public section`, exposing statements while keeping
proof bodies private.

## 11. Module map

This map points to the checker, its soundness proof, and supporting tools.

### Running and checking

These modules turn input files into declarations and check them.

| Location | Contents |
|---|---|
| [Main.lean](./Main.lean), [ConLeche/Driver/](./ConLeche/Driver/) | The binary entry point, command-line interface, IO driver, modular checking, scheduling, and comparison. |
| [ConLeche/Frontend/](./ConLeche/Frontend/) | The lean4export parser, `.olean` reader, input preparation, and IO interface. |
| [ConLeche/Kernel/](./ConLeche/Kernel/) | The pure checker specification, including expression checking, declaration installation, inductive types, and pinned declarations. |
| [ConLeche/Cached/](./ConLeche/Cached/) | The cached checker used by the binary, including declaration checking and stream indexing. |
| [ConLeche/PinGen/](./ConLeche/PinGen/), [pins/](./pins/) | Generation of the Nat operation pins and certificates, and their committed output. |
| [native/](./native/) | The C implementation of the hash for large `Nat` literals. |

### Semantics and proofs

These modules define the model and connect it to accepted checker runs.

| Location | Contents |
|---|---|
| [ConLeche/Term/](./ConLeche/Term/), [ConLeche/SetTheory/](./ConLeche/SetTheory/), [ConLeche/SetModel/](./ConLeche/SetModel/) | The term language, set-theory interface, and set constructions used in the model. |
| [ConLeche/IsModel.lean](./ConLeche/IsModel.lean), [ConLeche/Denotes.lean](./ConLeche/Denotes.lean) | The semantics of declaration streams and the environment model built by the proofs. |
| [ConLeche/Semantics/](./ConLeche/Semantics/) | Interpretation, the semantic invariant, and facts about models of declarations. |
| [ConLeche/Rules/](./ConLeche/Rules/), [ConLeche/Verify/Rules/](./ConLeche/Verify/Rules/) | Relational rules for the core checker and proofs connecting checker runs to those rules. |
| [ConLeche/Verify/](./ConLeche/Verify/) | Proofs about checker functions, the cached implementation, input parsing, and driver runs. |
| [ConLeche/Model/](./ConLeche/Model/) | Soundness of the rules and declaration checking, construction of models, and proofs for modular checks and comparisons. |
| [ConLeche/Modular.lean](./ConLeche/Modular.lean), [ConLeche/Modular/](./ConLeche/Modular/) | The modular checking conditions and the theorem over an abstract interface of models. |
| [ConLeche/Accepts.lean](./ConLeche/Accepts.lean), [ConLeche/MainTheorem.lean](./ConLeche/MainTheorem.lean) | The file-level statement used for `False` and the main theorems about accepted runs. |
| [ConLeche/Challenge.lean](./ConLeche/Challenge.lean) | The theorem statements with checker functions and proofs left as holes, used by `scripts/selfcheck.sh`. |

### Supporting files

These directories contain the set-theory bridge, tests, and development tools.

| Location | Contents |
|---|---|
| [bridge/lean4lean-model/](./bridge/lean4lean-model/) | The Mathlib bridge instantiating the set-theory interface. |
| [tests/](./tests/) | Lean tests, fixtures, expectations, and gate scripts. |
| [scripts/](./scripts/) | Fixture generators, performance and stream tools. |

## 12. Gates

The test gates check the project's boundaries, proof dependencies, and
checker behavior. CI runs `lake test` and the standard battery,
`tests/arena.sh`.

### Boundaries and proof dependencies

These gates check what the checker and its proofs depend on:

- `tests/layering.sh` enforces import boundaries between the implementation,
  theory, driver, and `.olean` reader.
- `tests/trust-surface.sh` scans for compiler escapes and checks restrictions
  on runtime IO. It also pins the build file and native sources by content.
- `tests/plain-reach.sh` checks the specification-tier declarations reachable
  from the compiled `main` against a list of permitted declarations and their
  reasons. `tests/binary-link.sh` checks that the binary links no module of
  the `Lean` package.
- `lake test` builds the test library, including the axiom pins for the
  proofs. The standard battery also builds that library and checks that the
  generated pin dump is current.

### Checker tests

The standard battery checks verdicts and behavior across input formats and
execution modes:

- The arena tutorial and end-to-end fixtures have pinned verdicts; the suites
  also run in trusted mode and with different worker counts.
- `tests/challenge.sh` checks that the challenge builds with only its expected
  `sorry` warnings. `scripts/selfcheck.sh` compares the challenge with the
  solution using both `.olean` files and exported JSON, and checks the
  justified names against `comparator.json`.
- `tests/olean.sh` checks committed and corrupted `.olean` fixtures, while
  `tests/olean-compare.sh` compares the reader's records for `Init` with the
  exporter's records.
- Other fixtures check command-line behavior, output sanitization, and shared
  expressions.

### Documentation checks

The documentation gates keep quoted declarations and source links current.
`tests/quote-gate.sh` compares declaration-headed Lean quotes with their
source. `tests/overview-links.sh` checks relative link targets and compares
cited source lines in `OVERVIEW.md` and `README.md` with
`tests/overview-links-expected.txt`.

When a citation moves or its source changes, re-read the citing text and fix
it if needed, then run `tests/overview-links.sh --update`.

## 13. What the environment stores beyond Lean's

The checker's [`Env`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L477-L480)
stores constants and projection tables derived from declarations. Some stored
information corresponds to Lean's environment; other information is computed
from the declarations to support checking.

### Information about inductives and recursors

The environment records information about inductive families, constructors
and recursors alongside their types
([`IndCaps`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L203-L238) and
[`ConstantInfo`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L304-L326)).

| Entry | Stored information |
|---|---|
| Inductive family | Its block members, parameter and index counts, constructors, whether it has structure η (structure-like, in a block that is not recursive, and `hasEta` where the record declares flags), and a flag indicating that its result sort is never zero at any universe instantiation. |
| Constructor | Its family name and its parameter and field counts. |
| Recursor | Its major premise's argument position, the length of the argument prefix used by its rules, its K flag and its rules. |

A [`RecRule`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L134-L140)
stores the constructor, field count and right-hand side, as Lean's rule does.
It also stores a [firing mode](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L118-L121): ordinary, nested, or the level instantiation used
by a quotient eliminator. The installer derives the mode for inductive rules
from the recursor declaration
([`recFire`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L38-L50)).

### Projection tables

A [`ProjTable`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Env.lean#L268-L279)
stores the constructor and the result-type body of each field projection of a
structure-like member, or, where the record declares flags, of a member with
`hasProjections`. The installer derives the table from the constructor type
([`blockTables`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L60-L69)).
Lean's kernel instead computes projection types from the constructor type when
needed. For a projection from a propositional structure, the checker verifies
the required proposition restrictions at the use, rather than storing them
([`checkProjGuard`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Core.lean#L1259-L1269)).

### Lookup indexes and omitted values

[`FEnv`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/FEnv.lean#L193-L218)
adds lookup indexes and flags for whether `Nat` and string literals can be
expanded. The indexes support lookup over the same environment data.

The checker stores less than Lean for some declarations: it keeps a theorem
without its value and stores an opaque constant as an axiom
([`declConstants`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Install.lean#L78-L91)).

## 14. Where the checker departs from the official kernel

ConLeche follows the shape of Lean's kernel, but differs in conversion,
accepted declarations and module checking. This section summarizes the
differences; §3, §5, §6 and §8 describe the relevant checks.

### Conversion and elimination

ConLeche uses the following conversion and elimination rules:

* Proofs are compared by their types before either is reduced, so a proof
  without a normal form need not stop the comparison (§3).
* Theorems are opaque: their values are never unfolded (§3).
* A recursor's major premise is rescued from its type or projections before
  reduction; a K-like major whose rescue fails is left unreduced (§3).
* The checker supports η for partially applied constructors and a wider
  notion of unit-likeness, including function spaces into unit-like types
  and structures whose fields are propositions or unit-like types (§3).
* A partially applied recursor of a K-like or η type is η-expanded and
  ι-reduced, as in lean4#15374 (§3).
* An input whose inductive types declare the feature flags is checked at them,
  so `Acc` and other recursive predicates have only a small eliminator there
  (§5). Without flags, the features are derived from the declarations.
* An input that declares `Quot` at `Sort (max 1 u)` has quotients of
  propositions as types, as in lean4#15023 (§5).
* Universe levels are compared semantically.
* Without declared feature flags, a non-nested block with one family and one constructor, whose result sort
  can be zero, can have a large eliminator; the released kernel gives it a
  small eliminator. For a `Prop` family, each field must be a proof or a
  result index; otherwise each field's sort must be at most the result sort.
* When proof irrelevance does not establish equality, the checker continues
  the comparison; the official kernel can stop with failure.
* `And.rec` can rescue its major premise from an opaque proof of `And` and
  its projections (§3).
* Opaque theorems and the order of recursor reduction can make conversion
  incomplete: the checker can reject a declaration that Lean accepts by
  reducing a proof (§3).
* When one side is a closed, fully applied constructor of a type that is
  never a proposition, has no η law and is not `Nat`, the other side is
  head-normalized at once. The official kernel does this only for
  `Bool.true` (§3).
* Two applications of the same projection to equally many arguments,
  `s.i a₁ … aₙ` and `t.i b₁ … bₙ`, are compared like bare projections:
  `s` and `t` are unfolded lazily, and once they agree the arguments are
  compared; otherwise the comparison continues as in the official kernel.
  The official kernel reduces `s` and `t` to constructors first,
  which can be expensive where one unfolding step makes them equal
  ([lean4#16613](https://github.com/leanprover/lean4/issues/16613)).
* A `Nat` literal's hash reads all its bits; the released kernel hashes its
  low 64 bits, so literals that agree there share a memo bucket (§9).

The soundness proof covers the checker's acceptances beyond the official
kernel.

### Restrictions on declarations

ConLeche checks declarations against requirements needed by its model and
its treatment of input records:

* In ordinary checking, non-standard axioms and proofs by `native_decide`
  or `bv_decide` are declined, subject to the exceptions in §8.
* Well-founded `Nat` operations are accelerated only when their definitions
  match supported pins; a stream matching none is declined. The official
  kernel accelerates by name (§6).
* The pinned basis and `And` declarations must have the expected shapes (§5).
* Declarations at names read by literals must have the expected level
  parameters and types.
* `Bool` must have the expected types where `Nat` operations require it (§6).
* Inductive blocks must include recursor records; the official kernel
  generates its own (§5).
* A recursor's minor premise may consume a constructor field annotation only
  when it is stored as the identity on its type, in a rule at the recursor's
  own parameters whose types match the constructor's up to that consumption.
  The official kernel consumes `optParam`, `autoParam`, `outParam` and
  `semiOutParam` by name.
* Declarations at `Lean.reduceBool` and `Lean.reduceNat` must be opaque
  constants, and `sorryAx` must be an axiom (§8).
* The structural `Nat` operations' fast path is certified at install, and a
  definition that fails the certification is declined; the official kernel
  trusts the fast path by name (§6).
* With declared feature flags, a nested occurrence of a proposition with one
  constructor without fields is rejected even where that type is declared
  without `isK`; the official kernel rejects it only where it is declared
  with `isK`. The checker does not store a type's flags (§5).
* A nested block is checked through its containers at their concrete
  instantiations, without an auxiliary mutual block (§5).
* The stream's recursors are installed after comparison with the generated
  recursors; the official kernel installs its own (§5).

### Modular checking

Modular checking validates the `.olean` views and imported contexts instead
of trusting the files (§2):

* A module is rejected if its context gives a name it reads a different
  meaning from the module it reads it from. Lean accepts such name capture.
* A module's three parts must agree, its context records must satisfy their
  syntactic clauses, and context records that read each other are rejected.
  The official kernel trusts imported files.
* Each loaded copy of a name has its statement checked as its own module
  reads it; copies whose statements have different meanings are rejected.
  Lean compares the statements as expressions and can accept such copies.

### Checks used by the proof

Verified mode performs checks that the soundness proof uses and the official
kernel does not make:

* It checks the full-grade types of opened bodies in lambda comparisons and
  η, the type of the reduct at the η of a partially applied recursor, and proof irrelevance between the major and the constructor application
  in K-like and `And` rescues (§3).
* It performs three additional checks in the inductive installer:
  * For a `Type` block, the fields of each constructor's positivity normal
    form have sorts bounded by the family's sort with members replaced by
    variables.
  * Each constructor type with its block members replaced by variables
    type-checks in their context.
  * At every recorded normal form of a constructor, each recursive field
    agrees with the reference form's telescope, head and indices, and with
    the class of its inductive hypothesis.

Trusted mode omits checks used only by the proof and is outside the soundness
theorem.
