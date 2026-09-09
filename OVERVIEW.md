# ConLeche: an overview of the proof

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to `README.md`, which is human-written.
> It is a guided tour of the verification, from the binary that runs to
> the set-theoretic assumption it rests on, with links into the source
> on `master`.

## 0. Using the checker

The binary reads a Lean export in `lean4export`'s NDJSON format and
prints one verdict line:

```
con-leche [--verified|--trusted] [--progress[=<stride>]] FILE.ndjson
con-leche --help
```

That is every flag the binary takes. `--verified` is the default and
the mode the theorem is about; `--trusted` runs the same checker bodies
with the certification-only work switched off, is faster, and is
outside the theorem; `--progress[=<stride>]` turns on a heartbeat on
stderr (below); `--help` prints the usage text and exits 0
([the driver's usage text in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L518)).
A retired spelling — `--set-model[=p|=r]`, `--no-model`, `--tt-model`,
`--yolo`, `--infer-only`, `--pre`, `--core[=<c>]`, `--install-only`,
`--check-range[=<r>]` — is never a silent alias: it is rejected with a
message naming what stands in its place, so a verdict's provenance can
be read off the invocation.

The exit code follows the lean kernel arena convention
([the exit-code mapping in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L44)):

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

The flag `--progress[=<stride>]` prints a heartbeat on stderr: one line
before every `stride`-th record is installed and one before every
`stride`-th recorded declaration is checked (bare, the stride is 1),
with a line at the end of the parse, of the install phase and of the
fold. The lines are printed between the steps of the one driver, which
returns its environment together with the proof that `checkDecls` — the
function the theorem is about — returns it (see §2), so a run with the
flag is covered exactly as a run without it.

## 1. What is proved

The statement is one theorem about the declaration fold `checkDecls`,
the function whose result the `con-leche` binary's driver returns for
a parsed export stream, the theorem
[`no_proof_of_False` in `ConLeche/MainTheorem.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/MainTheorem.lean#L40-L43):

> For every model `V` of the `SetTheory` interface and every list of
> declarations `ds`: if `checkDecls`, in the default `--verified` mode,
> accepts `ds` with the environment `env`, then `env` stores no
> constant whose type is `False`.

`checkDecls`
([function `checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L342-L346))
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
differently is rejected. The theorem uses exactly Lean's three standard
axioms, `propext`, `Classical.choice` and `Quot.sound`, which the
[axiom pin in `tests/ConLecheTests/Axioms.lean`](https://github.com/leanprover/lech/blob/master/tests/ConLecheTests/Axioms.lean#L87-L88)
checks with `#print axioms` guards under `lake test`.

Everything below explains how that theorem is reached.

## 2. From the binary to the theorem

Read from the outside in:

1. **The driver** (`Main.lean`). The run parses the stream
   ([function `parseExportStreamD` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/ExportC.lean#L863))
   and runs the fold's two phases as two loops. The install loop
   ([function `installLoop` in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L96))
   takes every record through the install step
   ([function `annotStepC` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L136-L138)):
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
   environment. The check loop
   ([function `checkLoop` in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L165))
   then checks every recorded declaration against the *prefix* of the
   installed index it was installed at — an `O(1)` view whose lookup
   hides everything installed later — from a fresh memo state, and
   carries every check; what it returns is a fully checked environment.
   The heartbeat and the route trace are printed between the steps and
   touch neither type. The driver
   ([function `checkDeclsIO` in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L197-L200))
   turns the fully checked environment into its environment with the
   proof that `checkDecls` returns it
   ([theorem `fullyChecked_checkDecls` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L423-L424)).
2. **The fully checked environment**
   ([structure `InstalledEnv` in `ConLeche/Cached/Installed.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L223-L227))
   is stated over the executable steps: the installed environment is
   the accepting install run
   ([inductive `InstallRun` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L186-L191)),
   and a record is checked when its check at the prefix view succeeded
   ([definition `GroupChecked` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L259-L262)).
   The records' checks are independent of one another, which is what
   lets a later loop hand them to workers. An accept of `checkDecls`
   is exactly such an environment, and conversely
   ([theorem `checkDecls_fullyChecked` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/Installed.lean#L433-L434)),
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
   ([theorem `installRun_model` in `ConLeche/Verify/Cached/InstalledC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/InstalledC.lean#L311-L318)),
   and a record's check at the prefix view is covered by the
   simulation stated at the truncated environment because the view and
   the truncated environment have the same lookup, and the cached core
   reads its environment through that lookup alone
   ([theorem `coreKnotI_congr` in `ConLeche/Verify/Cached/KnotCongr.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/KnotCongr.lean#L543-L544)).
   The walk carries the model to the final environment
   ([theorem `fullyChecked_sound` in `ConLeche/Verify/Cached/InstalledC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/InstalledC.lean#L460-L462)),
   and the fold's letter
   ([theorem `no_proof_of_False_cached` in `ConLeche/Verify/Cached/MainC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L65-L71))
   is that model read through `checkDecls_fullyChecked`
   ([theorem `checkDecls_sound` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L43-L48)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` and the annotation pass are tied in a knot over a fuel
   parameter
   ([the entry points in `ConLeche/Kernel/TypeChecker.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/TypeChecker.lean#L28-L54));
   on exhaustion every operation throws
   ([the fuel knot's base case in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2862-L2871)).
   Its declaration fold is what the model tier proves things about
   ([theorem `no_proof_of_False_pure` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Fold.lean#L294-L301)).
5. **The model tier** (`ConLeche/Model/*`, the graded set model)
   shows that each declaration step preserves an invariant on the
   environment
   ([theorem `declStep_preserves` in `ConLeche/Model/Fold.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Fold.lean#L161)),
   and that the invariant forbids a constant of type `False`, whose
   pinned denotation is the empty set
   ([theorem `no_constant_of_False` in `ConLeche/Model/Capstone.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Capstone.lean#L151-L157)).
6. **The semantics** (`ConLeche/Semantics/*`) defines the denotation of
   terms in a model of the **set-theory interface**
   (`ConLeche/SetTheory/*`), and the **pure set constructions**
   (`ConLeche/SetModel/*`) build the sets inductive types denote.

The layering is enforced by a gate
([the import fence `tests/layering.sh`](https://github.com/leanprover/lech/blob/master/tests/layering.sh#L1-L3)):
implementation modules never import theory modules, so the binary
cannot depend on a proof.

## 3. The checker

Two modes exist, `--verified` (default) and `--trusted`
([the type `CheckMode` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Env.lean#L69)).
Trusted mode is verified mode minus certification-only steps; it is
faster and is outside the theorem. Both use the same core.

The checker is a Lean-kernel-style type checker in the shape of the
official one: `whnfCore` does β/ι/projection/quotient reduction,
`whnf` adds δ-unfolding of definitions — a theorem is opaque to
reduction: its value is never unfolded, so whether a declaration
type-checks never depends on a theorem's value — and the literal fast
paths
([function `whnfBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2028)),
`inferType` computes a type, and `isDefEq` decides conversion with lazy
unfolding, η, proof irrelevance, structure η, unit-likeness and K-like
reduction as the environment's capability flags permit; one
proposition, the pinned `And`, is additionally rescued when its
recursor is stuck on a proof (`And.intro a b h.1 h.2` is fabricated
and certified by proof irrelevance — `And` only, by ruling). Two things
differ from a textbook presentation and matter for the proof:

* **Annotation.** Before a declaration's terms are checked, an
  annotation pass
  ([function `annotateBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2750))
  records at every binder the sort of its codomain as a "Prop-when"
  datum, a function of the level parameters
  ([the `PropWhen` module's account in `ConLeche/Kernel/PropWhen.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/PropWhen.lean#L1-L40)),
  stored in the binder's metadata
  ([structure `BinderMeta` in `ConLeche/Kernel/Expr.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Expr.lean#L102-L104)).
  The checker validates the coherence of these annotations at run time;
  the proof consumes them. This is the price of not having a syntactic
  type theory (see §4). The annotation pass also ζ-expands `let`, so
  stored terms are let-free: the reduction and inference arms raise an
  internal error on a `let` node, and the term language the denotation
  targets has no `let` former.
* **Fuel and memos.** The pure checker is fueled; the cached checker is
  not, but its memos are proved to agree with the pure functions at
  every fuel large enough to succeed
  ([theorem `checkDecls_skels` in `ConLeche/Verify/Cached/AgreeFloor.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/AgreeFloor.lean#L1334-L1336)).
  Binder names and binder infos are not stored at all; `Expr` carries a
  packed hash and loose-variable bounds as computed fields, which is
  what makes the DAG-safe traversals cheap.

## 4. The proof idea

There is no syntactic typing judgement and hence no theorem of the form
"accepted ⇒ derivable". The *theory* is the set model. What is proved
about the algorithm is stated only in the accepting direction, and it
is stated semantically.

**Terms.** A kernel `Expr` denotes, under a level valuation, an
*erased* term
([type `Term` in `ConLeche/Term/Syntax.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Term/Syntax.lean#L176-L205)):
de Bruijn indices, sorts at concrete levels, built-in constants at
concrete level instantiations, no names, no binder infos. The
*annotated* variant is the same syntax with a numeral sort at each
binder
([type `AnnotTerm` in `ConLeche/Semantics/Syntax.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Syntax.lean#L73-L99)).

**Interpretation.** The interpretation maps an annotated term to a
set, totally and term-directed
([function `interp` in `ConLeche/Semantics/Interp.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Interp.lean#L153-L164)):
a Π whose body sort is `0` is a predicate space with a single proof
point, otherwise a dependent function space; a λ likewise; a sort is a
universe of the chain; nothing needs to be well-typed to be
interpreted. Propositions are sets with at most one element, so proof
irrelevance and propositional extensionality are built in, and a
propositionally proven equation is a set equality.

**The invariant.** In place of a typing judgement there is a semantic
predicate
([predicate `WellDenoted` in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/WellDenoted.lean#L81-L111)):
hereditarily, every application applies a function to an argument of
its domain, every λ has a bounded codomain, every projection hits a
pair, and so on. Unlike syntactic typing it is preserved by β and
the other reduction steps
([the preservation lemmas in `ConLeche/Semantics/WellDenoted.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/WellDenoted.lean#L303-L361)).
An environment carries the invariant for every stored constant, plus
closedness and the pins of the basis constants
([structure `EnvModel` in `ConLeche/Model/Annot/EnvModel.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Annot/EnvModel.lean#L64-L100)).

**The claims.** Each kernel function gets one claim, in the accepting
direction only
([the claim definitions in `ConLeche/Model/Claims.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Claims.lean#L92-L160)):

* `whnfCore`/`whnf` return a term with the same denotation, with the
  invariant preserved;
* `isDefEq` answering `true` means the two denotations are equal;
* `inferType` returns a type such that the term's denotation is a
  member of the type's denotation.

They are proved by one simultaneous induction on fuel, clause by
clause
([the reduction step in `ConLeche/Model/Steps/Whnf.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Steps/Whnf.lean#L831-L832),
[the definitional-equality step in `ConLeche/Model/Steps/DefEq.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Steps/DefEq.lean#L1338-L1347),
[the inference step in `ConLeche/Model/Steps/Infer.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Steps/Infer.lean#L1036-L1043)).
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

* **Pinned basis blocks.** `Eq`, `Nat`, `PUnit`, `Empty`, `False`,
  `Quot` (with its soundness axiom), `Bool` and `And` are installed
  from built-in pins
  ([the `False` pin in `ConLeche/Kernel/Basis/False.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Basis/False.lean#L52))
  as a prelude prepended to every stream
  ([the built-in prelude in `ConLeche/Frontend/Prelude.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/Prelude.lean#L7-L22));
  a stream record under one of those names is dropped if identical and
  declined if different. Their denotations are fixed sets, which is why
  the main theorem can name `False` without a hypothesis about how the
  stream declared it.
* **The fixpoint route** takes every other single, non-nested block:
  any number of parameters, indices, constructors and fields, recursive
  and reflexive fields, `Prop` or `Type`. The recogniser reads the
  block's shape — its parameter count as the stream DECLARES it,
  checked against the type formers' telescopes and against every
  constructor record before either route runs
  ([function `indParamsOk` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Env.lean#L581-L588)),
  its index count off what is left of the type former's telescope, as
  official reads them, and
  nothing of the stream's recursor record, which official never reads as
  an input either; the install normalises every constructor field domain
  by official's positivity walk — weak head normal form before
  classifying, again under each Π binder
  ([function `normPosDom` in `ConLeche/Kernel/Inductives/SumInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Inductives/SumInstall.lean#L162)) —
  and classifies each field on the constructors it stored
  ([function `classifyFixKinds` in `ConLeche/Kernel/Inductives/NativeInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Inductives/NativeInstall.lean#L496)),
  runs official's checks — universe bound, elimination restriction and
  index occurrence — generates the recursor and its rules, and compares
  the generated recursor with the stream's, rejecting a record that is
  not it; the whole install is one entry
  ([function `checkNative` in `ConLeche/Kernel/Inductives/NativeInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Inductives/NativeInstall.lean#L512)).
  The two halves are deliberately independent: a block whose
  recursor record is a stub is still rejected by its own type and
  constructors, as official rejects it, instead of being declined for a
  recursor the checker was going to generate anyway.
  In the model the block's carrier is the least fixed point of its
  family functor over the index fibres
  ([the fixed-point family space in `ConLeche/SetModel/Value.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetModel/Value.lean#L510-L517));
  the recursor is the choice of a fixed point of the graph functor,
  and the recursion theorem says that fixed point is a function
  (`ConLeche/SetModel/RecGraph.lean`). That the least fixed point is a
  member of the universe follows from one abstract theorem about
  *member containers*, functors built from constants, sums, products
  and arrows with member domains
  ([theorem `container_closed_exists` in `ConLeche/SetModel/Container.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetModel/Container.lean#L598)),
  which covers finitary and reflexive fields alike. The model-tier
  theorem for the whole install is
  [theorem `declNative` in `ConLeche/Model/Inductives/DeclNative.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/Inductives/DeclNative.lean#L63).
  Structure-like blocks additionally get first-class projections, η,
  unit-likeness and K exactly under official's conditions.
* **Mutual and nested blocks** are handled by an in-process modeller
  (`ConLeche/Frontend/InModel/*`): at parse time the checker generates,
  over its own `Expr`, a *model* of the block, an auxiliary family plus
  definitions and theorems stating the constructors' and recursor's
  equations, and installs the block through the modeled route, which
  checks those theorems like any other declaration and uses their
  equations semantically
  ([function `checkIotaThm` in `ConLeche/Kernel/Inductives/Modeled.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Inductives/Modeled.lean#L68-L79)).
  The construction and the code are a port of the maintainer's
  [lean-inductive-models](https://github.com/nomeata/lean-inductive-models),
  a standalone tool that translates mutual and nested inductive types
  into single ones with a syntactic correspondence between the original
  and its model; ConLeche originally ran that tool as a preprocessor and
  now performs the same construction in process
  ([the modeller's kit in `ConLeche/Frontend/InModel/Kit.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/InModel/Kit.lean#L7-L15)).
  The model is generated and checked; nothing external is trusted, and
  nothing is read from the input: a stream record whose name happens to
  carry a `_model` component is an ordinary declaration with no effect
  on any block, and the install dispatch is the RECOGNISER alone — a
  mutual or nested block carries several type formers, resp. several
  recursors, so the fixpoint route's recogniser refuses it outright and
  no model lookup is needed to route it. A nested occurrence under a
  binder is outside the scheme and declines
  ([the modeller's residual in `ConLeche/Frontend/InModel/Nested.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/InModel/Nested.lean#L47-L54)).

A block no route takes is a positive decline naming its class, never
an acceptance.

## 6. The Nat operations

The official kernel accelerates the structural `Nat` operations on
literals with GMP. ConLeche does the same, but certifies the fast path
instead of trusting the operation's name.

* **Structural operations** (`Nat.add`, `sub`, `mul`, `pow`, `beq`,
  `ble`, and `pred` as a dependency;
  [the list `natOpNames` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L545-L553)):
  when a definition under one of these names arrives, the install
  certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([the account of the certified fast path in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L477-L494),
  [function `certifyNatEqs` in `ConLeche/Kernel/Checker.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Checker.lean#L110-L117)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The model side reads the operation's membership off its pinned type
  shape and proves the literal semantics from the certified
  recurrences
  ([theorem `natOps_install` in `ConLeche/Model/NatEqs.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/NatEqs.lean#L1100)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`;
  [the list `natDivModNames` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L555-L570))
  are defined by well-founded recursion and have no recurrence the
  kernel can check directly. Their install compares the stream's
  definition by definitional equality against a *pinned* copy of the
  toolchain's own definition, and then checks pinned *certificate
  theorems*, `Nat.ble`-guarded characterisations of each operation
  whose proof terms were produced by Lean itself at pin-generation
  time, as theorem declarations, without installing them
  ([the pin module `ConLeche/Kernel/NatOpPins.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16),
  [the certificate library `ConLeche/PinGen/Certs.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/PinGen/Certs.lean#L7-L18)).
  The pins are committed per toolchain under `pins/` and regenerated
  with `lake exe natop-pins-export`. The model side is
  [theorem `divMod_install` in `ConLeche/Model/DivModCert.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Model/DivModCert.lean#L2023).
* **Order independence.** The certificates are spelled over the
  structural operations and the basis blocks, which an export may emit
  in any order. The built-in prelude supplies the basis blocks, and a
  parse-time pass moves a pinned operation's dependency closure ahead
  of it when the stream has it later
  ([the reordering pass `ConLeche/Frontend/NatOpGround.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/NatOpGround.lean#L8-L25)).
  Both are pure transformations of the parsed list below the verified
  fold.

## 7. The set-theory assumption

Everything is parametric in a class
([class `SetTheory` in `ConLeche/SetTheory/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L95-L156)):
membership, extensionality, pairing, union, power set, regularity,
replacement for arbitrary Lean functions, and an ω-chain of universes,
each a Tarski–Grothendieck universe
([predicate `IsTGUniverse` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L89))
and a member of the next. Infinity is derivable; choice is inherited
from the meta-logic. The derived operations the model uses live in
`ConLeche/SetTheory/Derive/*`.

The interface is instantiated in a separate Lake package,
`bridge/lean4lean-model`, on Mathlib's `ZFSet` from the ω-many
inaccessible cardinals hypothesis of Carneiro's consistency analysis of
Lean
([theorem `carneiro_implies_conleche` in `bridge/lean4lean-model/ConLecheBridge/Carneiro.lean`](https://github.com/leanprover/lech/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202)).
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
([the pinned standard axioms in `ConLeche/Kernel/StdAxioms.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/StdAxioms.lean#L39-L51));
both are true in the model, `propext` by extensionality of
propositions and `Classical.choice` by global choice. `Quot.sound` is
part of the pinned `Quot` block. Any other axiom declaration is a
positive decline at its own record, with one tolerated exception:
`sorryAx` is dropped rather than declined, and every declaration that
uses it is skipped and taints the run, so a stream with a `sorry` in
it declines at the end rather than at the first library file that
happens to mention the axiom.

The compiler-trust family, `Lean.trustCompiler`, `Lean.reduceBool`,
`Lean.reduceNat` and the axioms `Lean.ofReduceBool` and
`Lean.ofReduceNat`, is neither rejected nor trusted: `trustCompiler`
installs as an opaque with value `True.intro`, the two reduce
operations install as ordinary opaques pinned to the toolchain's
definitions, and the two axioms are accepted only after the install
certifies, by definitional equality, that the stored reduce operation
is the identity, at which point each axiom's statement is an inhabited
proposition in the model
([the compiler-trust family in `ConLeche/Kernel/TrustAxioms.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/TrustAxioms.lean#L10-L36)).
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
  fold receives, not about the export file. Between the two sit pure
  transformations of the parsed stream: the prelude is prepended and
  duplicates dropped, a pinned Nat operation's dependencies are moved
  ahead of it, a projection function is rewritten to its recursor form
  (`ConLeche/Frontend/ProjRec.lean`), and the models of mutual and
  nested blocks are generated — here and nowhere else; the input is
  never read for one, and the generated records are counted as what
  they are, declarations of the fold rather than records of the file.
  Two guarantees have to be kept apart
  here. What §5 and §6 establish is that everything the frontend
  *generates* is checked: a model's declarations and a Nat operation's
  certificates are ordinary declarations to the fold, so a wrong
  generation cannot be accepted. What the frontend does *not* establish
  is that the list it hands over means the same as the export: a
  rewrite that changed a declaration's statement would be checked and
  accepted as the changed statement. The rewrites are written to be
  meaning-preserving and each is small and inspectable, but that is a
  review claim, not a theorem.
* `--trusted` mode.
* Non-acceptance: a decline or a reject carries no claim. The verdict
  line reports the count of accepted stream records.
* Two deliberate accept-supersets relative to the official kernel, a
  semantic comparison of universe levels and a proof-irrelevance
  fall-through, both licensed by the soundness proof.

## 10. Naming conventions

The tree once carried a suffix per verification tier. Those tiers are
gone — the collapsed set model, the declarative type-theory lane and
the "tier B" two-regime interpretation were all deleted — and with them
their markers: **no `2`, `P`, `S2` or `Direct` suffix survives**, and
**no suffix not listed here carries meaning**. What a reader still has
to know is short:

| marker | reading |
|---|---|
| `C` | the *cached* checker's twin of a pure definition (`checkDeclC`, `CoreC`, `ExprC`, `SimC`) — the implementation that ships |
| `I` | indexed (`nativeRecAVI`-style readings that carry an index) |
| `F` | stated over the environment-with-index `FEnv` (`checkNativeRecF`) |
| `D` | the direct-parse record type `DeclC` and the functions over it |
| `AV`, `Annot` | annotated terms: `AnnotTerm` is `Term` with a numeral sort at every binder, and `*AV` names are its readers (`structTyAV`, `natLitAV`) |
| `WF` | well-formedness (`EnvWF`, `StructWF`) |
| `_pure` / `_cached` / `_checked` | the capstones over the pure fueled fold, over the cached fold `checkDecls`, and over the driver's fully checked environment (`no_proof_of_False_pure`, `no_proof_of_False_cached`, `no_proof_of_False_checked`) |

Three words name things rather than tiers. An inductive block is
installed by one of two routes: the **native** one (`checkNative`,
`Kernel/Inductives/Native*.lean`), which builds the block's carrier as
a least fixed point, and the **modeled** one (`checkModeled`,
`Kernel/Inductives/Modeled.lean`), which installs a mutual or nested
block through a generated `_model` family. `Struct*` and `Sum*` inside
those directories are the two stage kits the native route builds on —
the structure-shaped kit (projections, η, the entry telescope) and the
tagged-sum kit (the constructors as a sum). `Gated` marks the parked
β-certificate lane (`Kernel/CoreGated.lean`), which nothing executable
reaches, and `Fueled` marks a record-parameterised helper applied to
the pure functions at a fuel (`Verify/Knot.lean`).

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
| `ConLeche/Kernel/` | The pure checker: `Expr`/`Level`/`Name`, `PropWhen`, the core reduction/inference/conversion knot (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the two inductive routes (`Inductives/`: `Native*.lean` and `Modeled.lean`), the Nat-op pins. Imports no theory module. |
| `ConLeche/Cached/` | The shipped cached checker: hashed expressions, memo state, the cached core and declaration step, the parsed-record step (`ParsedC.lean`), the declaration fold `checkDecls` with its install and check phases and the fully checked environment the driver assembles (`Installed.lean`). |
| `ConLeche/Frontend/` | The export parser: the dialect's byte recogniser and syntax records (`Scan/`) and the semantic layer over them (`ExportC.lean`); the built-in prelude, the Nat-op ground reordering, the projection-function rewrite, the in-process modeller (`InModel/`) — the only source of a block's model. |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/Term/` | The erased term language, its substitution algebra and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and tuple towers, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The annotated term language, the interpretation, the semantic invariant, the tower semantics of inductive blocks, the declaration-level facts. |
| `ConLeche/Model/` | The graded set model of the checker: the environment invariant, the claims and their proofs per kernel function (`Steps/`), the declaration step, the inductive installs (`Inductives/`, `Ind*`), the Nat-op certification, the capstones. |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: well-formedness, scoping, the cached-to-pure simulation (`Cached/`), the native route's kernel-side invariants (`Inductives/`). |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The theorem, and the challenge statement kept as its own library. |
| `bridge/lean4lean-model/` | The Mathlib bridge instantiating the interface. |
| `tests/` | The Lean test library (axiom pin, proof-dependency roots), the arena and end-to-end fixtures with their expectation files, and the gate scripts. |
| `scripts/` | Fixture generators, the PERF battery, stream tools. |

## 12. Gates

`tests/arena.sh` is the standard battery: the layering fence, the
proof-term module pin (`tests/proofdeps.sh`, which fails if a new
module enters a capstone's closure), the compiler-escape scan, the pin
dump freshness, the arena tutorial tests, the end-to-end and annotation
fixtures with pinned verdicts, the route census, and the trusted-mode
sweep. `lake test` builds the test library with the axiom pins. CI runs
both.

The links in this document are part of the battery: `tests/overview-links.sh`
extracts every linked segment into one text and compares it with
`tests/overview-links-expected.txt`, so moving or changing the cited
lines fails the gate and is the reminder to re-read the paragraph that
cites them and to run `tests/overview-links.sh --update`.
