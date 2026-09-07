# ConLeche: an overview of the proof

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to `README.md`, which is human-written.
> It is a guided tour of the verification, from the binary that runs to
> the set-theoretic assumption it rests on, with links into the source.
> The links point at `master` and are checked by `tests/overview-links.sh`
> (see the last section), so a link that is out of date fails the gate.

## 1. What is proved

The statement is one theorem about the function the `con-leche` binary
runs on a parsed export stream
([`ConLeche/MainTheorem.lean#L27-L31`](https://github.com/leanprover/lech/blob/master/ConLeche/MainTheorem.lean#L27-L31)):

> For every model `V` of the `SetTheory` interface, if the checker in its
> default `--verified` mode accepts a list of declarations, the resulting
> environment stores no constant whose type is `False`.

`False` is not read off the stream: the checker installs it from a
built-in pin, and a stream that declares `False` or `False.rec`
differently is rejected. The theorem uses exactly Lean's three standard
axioms, which `tests/ConLecheTests/Axioms.lean` pins with
`#print axioms` guards that run under `lake test`.

Everything below explains how that theorem is reached.

## 2. From the binary to the theorem

Read from the outside in:

1. **The driver** (`Main.lean`). The default run parses the stream and
   calls the pure fold `checkDeclsSPCachedD`, printing nothing per
   declaration
   ([`Main.lean#L59-L63`](https://github.com/leanprover/lech/blob/master/Main.lean#L59-L63)).
   The optional progress lane (`CON_LECHE_PROGRESS`) runs a separate,
   plainly unverified fold of the same steps with a line printed before
   each declaration; a run with it set is not covered by the theorem.
2. **The shipped fold**
   ([`ConLeche/Cached/ParsedC.lean#L276-L279`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/ParsedC.lean#L276-L279))
   folds the per-declaration step of the *cached* checker over the
   records, threading the hash-consed environment and the memo state.
   Its error carries the position of the failing declaration.
3. **The cached checker** (`ConLeche/Cached/*`) is the implementation
   that ships: interned expressions, memo tables for equality,
   reduction, inference and definitional equality, and the direct
   parser's record type. It is related to the pure checker by a
   one-directional simulation: whatever the cached checker accepts, the
   pure checker accepts
   ([`ConLeche/Verify/Cached/MainC.lean#L155-L163`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L155-L163)).
   The capstone about the shipped fold is a corollary
   ([`ConLeche/Verify/Cached/MainC.lean#L181-L188`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L181-L188)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` and the annotation pass are tied in a knot over a fuel
   parameter
   ([`ConLeche/Kernel/TypeChecker.lean#L24-L50`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/TypeChecker.lean#L24-L50));
   on exhaustion every operation throws
   ([`ConLeche/Kernel/Core.lean#L2637-L2646`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2637-L2646)).
   Its declaration fold is what the model tier proves things about
   ([`ConLeche/SetP/FoldP.lean#L291-L298`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/FoldP.lean#L291-L298)).
5. **The model tier** (`ConLeche/SetP/*`, "P" for the graded set model)
   shows that each declaration step preserves an invariant on the
   environment
   ([`ConLeche/SetP/FoldP.lean#L158`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/FoldP.lean#L158)),
   and that the invariant forbids a constant of type `False`, whose
   pinned denotation is the empty set
   ([`ConLeche/SetP/CapstoneP.lean#L147-L153`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/CapstoneP.lean#L147-L153)).
6. **The semantics** (`ConLeche/Semantics/*`) defines the denotation of
   terms in a model of the **set-theory interface**
   (`ConLeche/SetTheory/*`), and the **pure set constructions**
   (`ConLeche/SetModel/*`) build the sets inductive types denote.

The layering is enforced by `tests/layering.sh`: implementation modules
never import theory modules, so the binary cannot depend on a proof.

## 3. The checker

Two modes exist, `--verified` (default) and `--trusted`. Trusted mode is
verified mode minus certification-only steps; it is faster and is
outside the theorem. Both use the same core.

The checker is a Lean-kernel-style type checker in the shape of the
official one: `whnfCore` does β/ζ/ι/projection/quotient reduction,
`whnf` adds δ-unfolding and the literal fast paths, `inferType` computes
a type, and `isDefEq` decides conversion with lazy unfolding, η, proof
irrelevance, structure η, unit-likeness and K-like reduction as the
environment's capability flags permit. Two things differ from a
textbook presentation and matter for the proof:

* **Annotation.** Before a declaration's terms are checked, an
  annotation pass records at every binder the sort of its codomain as a
  "Prop-when" datum, a function of the level parameters
  ([`ConLeche/Kernel/PropWhen.lean#L1-L40`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/PropWhen.lean#L1-L40)),
  stored in the binder's metadata
  ([`ConLeche/Kernel/Expr.lean#L101-L104`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Expr.lean#L101-L104)).
  The checker validates the coherence of these annotations at run time;
  the proof consumes them. This is the price of not having a syntactic
  type theory (see §4). The annotation pass also ζ-expands `let`, so
  stored terms are let-free.
* **Fuel and memos.** The pure checker is fueled; the cached checker is
  not, but its memos are proved to agree with the pure functions at
  every fuel large enough to succeed. Binder names and binder infos are
  not stored at all; `Expr` carries a packed hash and loose-variable
  bounds as computed fields, which is what makes the DAG-safe
  traversals cheap.

## 4. The proof idea

There is no syntactic typing judgement and hence no theorem of the form
"accepted ⇒ derivable". The *theory* is the set model. What is proved
about the algorithm is stated only in the accepting direction, and it
is stated semantically.

**Terms.** A kernel `Expr` denotes, under a level valuation, an
*erased* term `VExpr`
([`ConLeche/VExpr/Syntax.lean#L165-L178`](https://github.com/leanprover/lech/blob/master/ConLeche/VExpr/Syntax.lean#L165-L178)):
de Bruijn indices, sorts at concrete levels, built-in constants at
concrete level instantiations, no names, no binder infos. The
*annotated* variant `AVExpr` is the same syntax with a numeral sort at
each binder
([`ConLeche/Semantics/Syntax.lean#L69-L85`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Syntax.lean#L69-L85)).

**Interpretation.** `interp2` maps an `AVExpr` to a set, total and
term-directed
([`ConLeche/Semantics/Interp.lean#L149-L159`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Interp.lean#L149-L159)):
a Π whose body sort is `0` is a predicate space with a single proof
point, otherwise a dependent function space; a λ likewise; a sort is a
universe of the chain; nothing needs to be well-typed to be
interpreted. Propositions are sets with at most one element, so proof
irrelevance and propositional extensionality are built in, and a
propositionally proven equation is a set equality.

**The invariant.** In place of a typing judgement there is a semantic
predicate `AnnotOk2`
([`ConLeche/Semantics/Ok2.lean#L78-L112`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Ok2.lean#L78-L112)):
hereditarily, every application applies a function to an argument of
its domain, every λ has a bounded codomain, every projection hits a
pair, and so on. Unlike syntactic typing it is preserved by β, ζ and
the other reduction steps
([`ConLeche/Semantics/Ok2.lean#L282-L340`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Ok2.lean#L282-L340)).
An environment carries the invariant for every stored constant, plus
closedness and the pins of the basis constants
([`ConLeche/SetP/Annot/EnvS2Core.lean#L60-L96`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Annot/EnvS2Core.lean#L60-L96)).

**The claims.** Each kernel function gets one claim, in the accepting
direction only
([`ConLeche/SetP/Claims2P.lean#L88-L156`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Claims2P.lean#L88-L156)):

* `whnfCore`/`whnf` return a term with the same denotation, with the
  invariant preserved;
* `isDefEq` answering `true` means the two denotations are equal;
* `inferType` returns a type such that the term's denotation is a
  member of the type's denotation.

They are proved by one simultaneous induction on fuel, clause by
clause
([`ConLeche/SetP/Step2/WhnfP.lean#L468-L488`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/WhnfP.lean#L468-L488),
[`ConLeche/SetP/Step2/DefEqP.lean#L1328-L1337`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/DefEqP.lean#L1328-L1337),
[`ConLeche/SetP/Step2/InferP.lean#L1128-L1135`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/InferP.lean#L1128-L1135)).
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
  `Quot` (with its soundness axiom) and `Bool` are installed from
  built-in pins as a prelude prepended to every stream
  ([`ConLeche/Frontend/Prelude.lean#L1-L15`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/Prelude.lean#L1-L15));
  a stream record under one of those names is dropped if identical and
  declined if different. Their denotations are fixed sets, which is why
  the main theorem can name `False` without a hypothesis about how the
  stream declared it.
* **The fixpoint route** takes every other single, non-nested block:
  any number of parameters, indices, constructors and fields, recursive
  and reflexive fields, `Prop` or `Type`. The recogniser reads the
  block's constructor data, runs official's checks (universe bound,
  positivity, elimination restriction, index occurrence), generates the
  recursor and its rules, and compares the generated recursor with the
  stream's
  ([`ConLeche/Kernel/Direct/RecInstall.lean#L211`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Direct/RecInstall.lean#L211)).
  In the model the block's carrier is the least fixed point of its
  family functor over the index fibres; the recursor is the choice of a
  fixed point of the graph functor, and the recursion theorem says that
  fixed point is a function. That the least fixed point is a member of
  the universe follows from one abstract theorem about *member
  containers*, functors built from constants, sums, products and arrows
  with member domains
  ([`ConLeche/SetModel/Container.lean#L622`](https://github.com/leanprover/lech/blob/master/ConLeche/SetModel/Container.lean#L622)),
  which covers finitary and reflexive fields alike. The model-tier
  theorem for the whole install is
  [`ConLeche/SetP/DirectFix/DeclDirectFixP.lean#L60`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/DirectFix/DeclDirectFixP.lean#L60).
  Structure-like blocks additionally get first-class projections, η,
  unit-likeness and K exactly under official's conditions.
* **Mutual and nested blocks** are handled by an in-process modeller
  (`ConLeche/Frontend/InModel/*`): at parse time the checker generates,
  over its own `Expr`, a *model* of the block, an auxiliary family plus
  definitions and theorems stating the constructors' and recursor's
  equations, and installs the block through the modeled route, which
  checks those theorems like any other declaration and uses their
  equations semantically
  ([`ConLeche/Kernel/Modeled.lean#L64-L75`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Modeled.lean#L64-L75)).
  The model is generated and checked; nothing external is trusted. A
  nested occurrence under a binder is outside the modeller's scheme and
  declines
  ([`ConLeche/Frontend/InModel/Nested.lean#L43-L48`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/InModel/Nested.lean#L43-L48)).

A block no route takes is a positive decline naming its class, never
an acceptance.

## 6. The Nat operations

The official kernel accelerates the structural `Nat` operations on
literals with GMP. ConLeche does the same, but certifies the fast path
instead of trusting the operation's name.

* **Structural operations** (`Nat.add`, `sub`, `mul`, `pow`, `beq`,
  `ble`, and `pred` as a dependency)
  ([`ConLeche/Kernel/Core.lean#L521-L529`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L521-L529)):
  when a definition under one of these names arrives, the install
  certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([`ConLeche/Kernel/Core.lean#L453-L470`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L453-L470),
  [`ConLeche/Kernel/Checker.lean#L100-L107`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Checker.lean#L100-L107)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The model side reads the operation's membership off its pinned type
  shape and proves the literal semantics from the certified
  recurrences
  ([`ConLeche/SetP/NatEqsP.lean#L1102`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/NatEqsP.lean#L1102)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`)
  ([`ConLeche/Kernel/Core.lean#L531-L546`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L531-L546))
  are defined by well-founded recursion and have no recurrence the
  kernel can check directly. Their install compares the stream's
  definition by definitional equality against a *pinned* copy of the
  toolchain's own definition, and then checks pinned *certificate
  theorems*, `Nat.ble`-guarded characterisations of each operation
  whose proof terms were produced by Lean itself at pin-generation
  time, as theorem declarations, without installing them
  ([`ConLeche/Kernel/NatOpPins.lean#L1-L16`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16),
  [`ConLeche/PinGen/Certs.lean#L1-L12`](https://github.com/leanprover/lech/blob/master/ConLeche/PinGen/Certs.lean#L1-L12)).
  The pins are committed per toolchain under `pins/` and regenerated
  with `lake exe natop-pins-export`; `tests/pindump.sh` fails if the
  committed dump is stale. The model side is
  [`ConLeche/SetP/DivModCertP.lean#L2031`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/DivModCertP.lean#L2031).
* **Order independence.** The certificates are spelled over the
  structural operations and the basis blocks, which an export may emit
  in any order. The built-in prelude supplies the basis blocks, and a
  parse-time pass moves a pinned operation's dependency closure ahead
  of it when the stream has it later
  ([`ConLeche/Frontend/NatOpGround.lean#L1-L20`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/NatOpGround.lean#L1-L20)).
  Both are pure transformations of the parsed list below the verified
  fold.

## 7. The set-theory assumption

Everything is parametric in a class `SetTheory V`
([`ConLeche/SetTheory/Core.lean#L91-L152`](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L91-L152)):
membership, extensionality, pairing, union, power set, regularity,
replacement for arbitrary Lean functions, and an ω-chain of universes,
each a Tarski–Grothendieck universe
([`ConLeche/SetTheory/Core.lean#L85`](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L85))
and a member of the next. Infinity is derivable; choice is inherited
from the meta-logic. The derived operations the model uses live in
`ConLeche/SetTheory/Derive/*`.

The interface is instantiated in a separate Lake package,
`bridge/lean4lean-model`, on Mathlib's `ZFSet` from the ω-many
inaccessible cardinals hypothesis of Carneiro's consistency analysis of
Lean
([`bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202`](https://github.com/leanprover/lech/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202)).
So the assumption is no stronger than the one already accepted for
Lean's own consistency. The main repository does not depend on Mathlib;
the bridge builds in its own CI job.

## 8. What the theorem does not cover

* The parser: the theorem is about the parsed declaration list. The
  frontend's transformations (prelude, dedupe, the Nat-op reordering,
  the projection-function rewrite, the in-process models) are pure
  functions of the stream that produce a list the fold then checks.
* `--trusted` mode and the `CON_LECHE_PROGRESS` lane.
* Non-acceptance: a decline or a reject carries no claim. The verdict
  line reports the count of accepted stream records.
* Two deliberate accept-supersets relative to the official kernel are
  recorded in `DESIGN.md` (a semantic level comparison and a
  proof-irrelevance fall-through); both are licensed by the soundness
  proof.

## 9. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The driver: argument parsing, the stream parse, the two folds, verdict and exit codes. |
| `ConLeche/Kernel/` | The pure checker: `Expr`/`Level`/`Name`, `PropWhen`, the core reduction/inference/conversion knot (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the fixpoint route (`Direct/`), the modeled route (`Modeled.lean`), Nat-op pins. Imports no theory module. |
| `ConLeche/Cached/` | The shipped cached checker: interned expressions, memo state, the cached core and declaration step, the parsed-record fold. |
| `ConLeche/Frontend/` | The export parser (`Export*.lean`), the built-in prelude, the Nat-op ground reordering, the projection-function rewrite, the in-process modeller (`InModel/`). |
| `ConLeche/PinGen/` | Elaboration-time generation of the Nat-op pins and certificate proofs; the committed dump lives in `pins/`. |
| `ConLeche/VExpr/` | The erased term language, its substitution algebra and the basis constants. |
| `ConLeche/SetTheory/` | The `SetTheory` class and the derived set operations. |
| `ConLeche/SetModel/` | Pure set constructions with no expressions in sight: tuples and tuple towers, tagged sums, the fixpoint iteration, the recursor's graph, member containers. |
| `ConLeche/Semantics/` | The annotated term language, the interpretation, the semantic invariant, the tower semantics of inductive blocks, the declaration-level facts. |
| `ConLeche/SetP/` | The graded set model of the checker: the environment invariant, the claims and their proofs per kernel function (`Step2/`), the declaration step, the inductive installs (`DirectFix/`, `Ind*`), the Nat-op certification, the capstones. |
| `ConLeche/Verify/` | Proofs about kernel functions that need no model: well-formedness, scoping, the cached-to-pure simulation (`Cached/`), the fixpoint route's kernel-side invariants (`Direct/`). |
| `ConLeche/MainTheorem.lean`, `ConLeche/Challenge.lean` | The theorem, and the challenge statement kept as its own library. |
| `bridge/lean4lean-model/` | The Mathlib bridge instantiating the interface. |
| `tests/` | The Lean test library (axiom pin, proof-dependency roots), the arena and end-to-end fixtures with their expectation files, and the gate scripts. |
| `scripts/` | Fixture generators, the PERF battery, stream tools. |
| `DESIGN.md` | The design journal: every task's record, decisions and measurements. |

## 10. Gates, and keeping this document honest

`tests/arena.sh` is the standard battery: the layering fence, the
proof-term module pin (`tests/proofdeps.sh`, which fails if a new
module enters a capstone's closure), the compiler-escape scan, the pin
dump freshness, the arena tutorial tests, the end-to-end and annotation
fixtures with pinned verdicts, the route census, and the trusted-mode
sweep. `lake test` builds the test library with the axiom pins. CI runs
both.

The links in this file are checked by `tests/overview-links.sh`: it
extracts every `blob/master/<path>#L<a>-L<b>` link, copies the linked
lines into one text, and compares it with
`tests/overview-links-expected.txt`. Moving the linked lines changes the
text and fails the gate, which is the reminder to update the link;
changing their content fails it too, which is the reminder to re-read
the paragraph that cites them. Regenerate the expectation with
`tests/overview-links.sh --update` after checking that the prose still
matches.
