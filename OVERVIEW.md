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
con-leche [--verified|--trusted] FILE.ndjson
```

`--verified` is the default and the mode the theorem is about;
`--trusted` runs the same checker bodies with the certification-only
work switched off, is faster, and is outside the theorem
([the driver's usage text in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L419)).
The exit code follows the lean kernel arena convention
([the exit-code mapping in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L37)):

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
theorem's guarantee.

`CON_LECHE_PROGRESS=<stride>` prints a heartbeat line before every
`stride`-th declaration on stderr; it runs a separate, unverified copy
of the fold (see §2).

## 1. What is proved

The statement is one theorem about the function the `con-leche` binary
runs on a parsed export stream, the theorem
[`no_proof_of_False` in `ConLeche/MainTheorem.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/MainTheorem.lean#L27-L31):

> For every model `V` of the `SetTheory` interface, if the checker in its
> default `--verified` mode accepts a list of declarations, the resulting
> environment stores no constant whose type is `False`.

`False` is not read off the stream: the checker installs it from a
built-in pin, and a stream that declares `False` or `False.rec`
differently is rejected. The theorem uses exactly Lean's three standard
axioms, `propext`, `Classical.choice` and `Quot.sound`, which the
[axiom pin in `tests/ConLecheTests/Axioms.lean`](https://github.com/leanprover/lech/blob/master/tests/ConLecheTests/Axioms.lean#L85-L86)
checks with `#print axioms` guards under `lake test`.

Everything below explains how that theorem is reached.

## 2. From the binary to the theorem

Read from the outside in:

1. **The driver** (`Main.lean`). The default run parses the stream
   ([function `parseExportStreamD` in `ConLeche/Frontend/ExportC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/ExportC.lean#L884))
   and calls the pure fold `checkDeclsSPCachedD`, printing nothing per
   declaration
   ([the default run's call in `Main.lean`](https://github.com/leanprover/lech/blob/master/Main.lean#L331)).
   The optional progress lane (`CON_LECHE_PROGRESS`) runs a separate,
   plainly unverified fold of the same steps with a line printed before
   each declaration; a run with it set is not covered by the theorem.
2. **The shipped fold**
   ([function `checkDeclsSPCachedD` in `ConLeche/Cached/ParsedC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/ParsedC.lean#L276-L279))
   folds the per-declaration step of the *cached* checker
   ([function `checkDeclStepIdxC` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Cached/ParsedC.lean#L244))
   over the records, threading the hash-consed environment and the memo
   state. Its error carries the position of the failing declaration.
3. **The cached checker** (`ConLeche/Cached/*`) is the implementation
   that ships: interned expressions, memo tables for equality,
   reduction, inference and definitional equality, and the direct
   parser's record type. It is related to the pure checker by a
   one-directional simulation: whatever the cached checker accepts, the
   pure checker accepts
   ([theorem `checkDeclsSPCachedD_sound_P` in `ConLeche/Verify/Cached/MainC.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L155-L163)).
   The capstone about the shipped fold is a corollary
   ([theorem `no_proof_of_False_SPCD_P` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/MainC.lean#L181-L188)).
4. **The pure checker** (`ConLeche/Kernel/*`) is a fueled, memo-free
   presentation of the same algorithm: `whnfCore`, `whnf`, `inferType`,
   `isDefEq` and the annotation pass are tied in a knot over a fuel
   parameter
   ([the entry points in `ConLeche/Kernel/TypeChecker.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/TypeChecker.lean#L24-L50));
   on exhaustion every operation throws
   ([the fuel knot's base case in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2646-L2655)).
   Its declaration fold is what the model tier proves things about
   ([theorem `no_proof_of_False_P` in `ConLeche/SetP/FoldP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/FoldP.lean#L291-L298)).
5. **The model tier** (`ConLeche/SetP/*`, "P" for the graded set model)
   shows that each declaration step preserves an invariant on the
   environment
   ([theorem `declStepPM` in `ConLeche/SetP/FoldP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/FoldP.lean#L158)),
   and that the invariant forbids a constant of type `False`, whose
   pinned denotation is the empty set
   ([theorem `no_constant_of_False_P` in `ConLeche/SetP/CapstoneP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/CapstoneP.lean#L147-L153)).
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
([the type `CheckMode` in `ConLeche/Kernel/Env.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Env.lean#L65)).
Trusted mode is verified mode minus certification-only steps; it is
faster and is outside the theorem. Both use the same core.

The checker is a Lean-kernel-style type checker in the shape of the
official one: `whnfCore` does β/ζ/ι/projection/quotient reduction,
`whnf` adds δ-unfolding and the literal fast paths
([function `whnfBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L1809)),
`inferType` computes a type, and `isDefEq` decides conversion with lazy
unfolding, η, proof irrelevance, structure η, unit-likeness and K-like
reduction as the environment's capability flags permit. Two things
differ from a textbook presentation and matter for the proof:

* **Annotation.** Before a declaration's terms are checked, an
  annotation pass
  ([function `annotateBody` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L2530))
  records at every binder the sort of its codomain as a "Prop-when"
  datum, a function of the level parameters
  ([the `PropWhen` module's account in `ConLeche/Kernel/PropWhen.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/PropWhen.lean#L1-L40)),
  stored in the binder's metadata
  ([structure `BinderMeta` in `ConLeche/Kernel/Expr.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Expr.lean#L101-L103)).
  The checker validates the coherence of these annotations at run time;
  the proof consumes them. This is the price of not having a syntactic
  type theory (see §4). The annotation pass also ζ-expands `let`, so
  stored terms are let-free.
* **Fuel and memos.** The pure checker is fueled; the cached checker is
  not, but its memos are proved to agree with the pure functions at
  every fuel large enough to succeed
  ([theorem `checkDeclsSPCachedD_skels` in `ConLeche/Verify/Cached/AgreeFloor.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Verify/Cached/AgreeFloor.lean#L1268)).
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
([type `VExpr` in `ConLeche/VExpr/Syntax.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/VExpr/Syntax.lean#L165-L179)):
de Bruijn indices, sorts at concrete levels, built-in constants at
concrete level instantiations, no names, no binder infos. The
*annotated* variant is the same syntax with a numeral sort at each
binder
([type `AVExpr` in `ConLeche/Semantics/Syntax.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Syntax.lean#L69-L86)).

**Interpretation.** The interpretation maps an annotated term to a
set, totally and term-directed
([function `interp2` in `ConLeche/Semantics/Interp.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Interp.lean#L149-L159)):
a Π whose body sort is `0` is a predicate space with a single proof
point, otherwise a dependent function space; a λ likewise; a sort is a
universe of the chain; nothing needs to be well-typed to be
interpreted. Propositions are sets with at most one element, so proof
irrelevance and propositional extensionality are built in, and a
propositionally proven equation is a set equality.

**The invariant.** In place of a typing judgement there is a semantic
predicate
([predicate `AnnotOk2` in `ConLeche/Semantics/Ok2.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Ok2.lean#L78-L112)):
hereditarily, every application applies a function to an argument of
its domain, every λ has a bounded codomain, every projection hits a
pair, and so on. Unlike syntactic typing it is preserved by β, ζ and
the other reduction steps
([the preservation lemmas in `ConLeche/Semantics/Ok2.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Semantics/Ok2.lean#L282-L340)).
An environment carries the invariant for every stored constant, plus
closedness and the pins of the basis constants
([structure `EnvS2Core` in `ConLeche/SetP/Annot/EnvS2Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Annot/EnvS2Core.lean#L60-L96)).

**The claims.** Each kernel function gets one claim, in the accepting
direction only
([the claim definitions in `ConLeche/SetP/Claims2P.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Claims2P.lean#L88-L156)):

* `whnfCore`/`whnf` return a term with the same denotation, with the
  invariant preserved;
* `isDefEq` answering `true` means the two denotations are equal;
* `inferType` returns a type such that the term's denotation is a
  member of the type's denotation.

They are proved by one simultaneous induction on fuel, clause by
clause
([the reduction step in `ConLeche/SetP/Step2/WhnfP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/WhnfP.lean#L908-L909),
[the definitional-equality step in `ConLeche/SetP/Step2/DefEqP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/DefEqP.lean#L1328-L1337),
[the inference step in `ConLeche/SetP/Step2/InferP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/Step2/InferP.lean#L1128-L1135)).
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
  built-in pins
  ([the `False` pin in `ConLeche/Kernel/Basis/False.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Basis/False.lean#L48))
  as a prelude prepended to every stream
  ([the built-in prelude in `ConLeche/Frontend/Prelude.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/Prelude.lean#L1-L15));
  a stream record under one of those names is dropped if identical and
  declined if different. Their denotations are fixed sets, which is why
  the main theorem can name `False` without a hypothesis about how the
  stream declared it.
* **The fixpoint route** takes every other single, non-nested block:
  any number of parameters, indices, constructors and fields, recursive
  and reflexive fields, `Prop` or `Type`. The recogniser reads the
  block's shape; the install normalises every constructor field domain
  by official's positivity walk — weak head normal form before
  classifying, again under each Π binder
  ([function `normPosDom` in `ConLeche/Kernel/Direct/SumInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Direct/SumInstall.lean#L158)) —
  and classifies each field on the constructors it stored
  ([function `classifyFixKinds` in `ConLeche/Kernel/Direct/RecInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Direct/RecInstall.lean#L212)),
  runs official's checks — universe bound, elimination restriction and
  index occurrence — generates the recursor and its rules, and compares
  the generated recursor with the stream's; the whole install is one entry
  ([function `checkDirectFix` in `ConLeche/Kernel/Direct/RecInstall.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Direct/RecInstall.lean#L228)).
  In the model the block's carrier is the least fixed point of its
  family functor over the index fibres
  ([the fixed-point family space in `ConLeche/SetModel/Value.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetModel/Value.lean#L517-L524));
  the recursor is the choice of a fixed point of the graph functor,
  and the recursion theorem says that fixed point is a function
  (`ConLeche/SetModel/RecGraph.lean`). That the least fixed point is a
  member of the universe follows from one abstract theorem about
  *member containers*, functors built from constants, sums, products
  and arrows with member domains
  ([theorem `container_closed_exists` in `ConLeche/SetModel/Container.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetModel/Container.lean#L622)),
  which covers finitary and reflexive fields alike. The model-tier
  theorem for the whole install is
  [theorem `declDirectFixP` in `ConLeche/SetP/DirectFix/DeclDirectFixP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/DirectFix/DeclDirectFixP.lean#L60).
  Structure-like blocks additionally get first-class projections, η,
  unit-likeness and K exactly under official's conditions.
* **Mutual and nested blocks** are handled by an in-process modeller
  (`ConLeche/Frontend/InModel/*`): at parse time the checker generates,
  over its own `Expr`, a *model* of the block, an auxiliary family plus
  definitions and theorems stating the constructors' and recursor's
  equations, and installs the block through the modeled route, which
  checks those theorems like any other declaration and uses their
  equations semantically
  ([function `checkIotaThm` in `ConLeche/Kernel/Modeled.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Modeled.lean#L64-L75)).
  The construction and the code are a port of the maintainer's
  [lean-inductive-models](https://github.com/nomeata/lean-inductive-models),
  a standalone tool that translates mutual and nested inductive types
  into single ones with a syntactic correspondence between the original
  and its model; ConLeche originally ran that tool as a preprocessor and
  now performs the same construction in process
  ([the modeller's kit in `ConLeche/Frontend/InModel/Kit.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/InModel/Kit.lean#L1-L12)).
  The model is generated and checked; nothing external is trusted. A
  nested occurrence under a binder is outside the scheme and declines
  ([the modeller's residual in `ConLeche/Frontend/InModel/Nested.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/InModel/Nested.lean#L43-L50)).

A block no route takes is a positive decline naming its class, never
an acceptance.

## 6. The Nat operations

The official kernel accelerates the structural `Nat` operations on
literals with GMP. ConLeche does the same, but certifies the fast path
instead of trusting the operation's name.

* **Structural operations** (`Nat.add`, `sub`, `mul`, `pow`, `beq`,
  `ble`, and `pred` as a dependency;
  [the list `natOpNames` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L521-L529)):
  when a definition under one of these names arrives, the install
  certifies its defining recurrence equations by definitional
  equality, in the environment *before* the operation is stored, with
  the operation's self-references replaced by its definition value, so
  the not-yet-enabled fast path cannot discharge its own equations
  vacuously
  ([the account of the certified fast path in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L453-L470),
  [function `certifyNatEqs` in `ConLeche/Kernel/Checker.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Checker.lean#L100-L107)).
  A nonstandard definition is rejected; presence in the store is the
  certificate, and `whnf` folds literals for stored operations only.
  The model side reads the operation's membership off its pinned type
  shape and proves the literal semantics from the certified
  recurrences
  ([theorem `natOpsP_install` in `ConLeche/SetP/NatEqsP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/NatEqsP.lean#L1102)).
* **Well-founded operations** (`Nat.div`, `mod`, `gcd`, `land`, `lor`,
  `xor`, `shiftLeft`, `shiftRight`;
  [the list `natDivModNames` in `ConLeche/Kernel/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/Core.lean#L531-L546))
  are defined by well-founded recursion and have no recurrence the
  kernel can check directly. Their install compares the stream's
  definition by definitional equality against a *pinned* copy of the
  toolchain's own definition, and then checks pinned *certificate
  theorems*, `Nat.ble`-guarded characterisations of each operation
  whose proof terms were produced by Lean itself at pin-generation
  time, as theorem declarations, without installing them
  ([the pin module `ConLeche/Kernel/NatOpPins.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/NatOpPins.lean#L1-L16),
  [the certificate library `ConLeche/PinGen/Certs.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/PinGen/Certs.lean#L1-L12)).
  The pins are committed per toolchain under `pins/` and regenerated
  with `lake exe natop-pins-export`. The model side is
  [theorem `divModP_install` in `ConLeche/SetP/DivModCertP.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetP/DivModCertP.lean#L2031).
* **Order independence.** The certificates are spelled over the
  structural operations and the basis blocks, which an export may emit
  in any order. The built-in prelude supplies the basis blocks, and a
  parse-time pass moves a pinned operation's dependency closure ahead
  of it when the stream has it later
  ([the reordering pass `ConLeche/Frontend/NatOpGround.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Frontend/NatOpGround.lean#L1-L20)).
  Both are pure transformations of the parsed list below the verified
  fold.

## 7. The set-theory assumption

Everything is parametric in a class
([class `SetTheory` in `ConLeche/SetTheory/Core.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L91-L152)):
membership, extensionality, pairing, union, power set, regularity,
replacement for arbitrary Lean functions, and an ω-chain of universes,
each a Tarski–Grothendieck universe
([predicate `IsTGUniverse` in the same file](https://github.com/leanprover/lech/blob/master/ConLeche/SetTheory/Core.lean#L85))
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
([the pinned standard axioms in `ConLeche/Kernel/StdAxioms.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/StdAxioms.lean#L34-L46));
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
([the compiler-trust family in `ConLeche/Kernel/TrustAxioms.lean`](https://github.com/leanprover/lech/blob/master/ConLeche/Kernel/TrustAxioms.lean#L8-L34)).
The consequence for `native_decide` and `bv_decide` proofs, which
appeal to `ofReduceBool`, is that ConLeche never runs native code: the
boolean the proof claims reduces to `true` must reduce to `true` under
the checker's own reduction, which for a large decision procedure
means a very long reduction rather than a rejection. Such proofs
are correct in the model and are accepted when that reduction
completes.

## 9. What the theorem does not cover

* The frontend. The theorem is about the list of declarations the
  fold receives, not about the export file. Between the two sit pure
  transformations of the parsed stream: the prelude is prepended and
  duplicates dropped, a pinned Nat operation's dependencies are moved
  ahead of it, a projection function is rewritten to its recursor form
  (`ConLeche/Frontend/ProjRec.lean`), and the models of mutual and
  nested blocks are generated. Two guarantees have to be kept apart
  here. What §5 and §6 establish is that everything the frontend
  *generates* is checked: a model's declarations and a Nat operation's
  certificates are ordinary declarations to the fold, so a wrong
  generation cannot be accepted. What the frontend does *not* establish
  is that the list it hands over means the same as the export: a
  rewrite that changed a declaration's statement would be checked and
  accepted as the changed statement. The rewrites are written to be
  meaning-preserving and each is small and inspectable, but that is a
  review claim, not a theorem.
* `--trusted` mode and the `CON_LECHE_PROGRESS` lane.
* Non-acceptance: a decline or a reject carries no claim. The verdict
  line reports the count of accepted stream records.
* Two deliberate accept-supersets relative to the official kernel, a
  semantic comparison of universe levels and a proof-irrelevance
  fall-through, both licensed by the soundness proof.

## 10. Module map

| Directory | Contents |
|---|---|
| `Main.lean` | The driver: argument parsing, the stream parse, the two folds, verdict and exit codes. |
| `ConLeche/Kernel/` | The pure checker: `Expr`/`Level`/`Name`, `PropWhen`, the core reduction/inference/conversion knot (`Core.lean`), declaration checking (`Checker.lean`, `DeclCheck.lean`), the basis pins (`Basis/`), the fixpoint route (`Direct/`), the modeled route (`Modeled.lean`), the Nat-op pins. Imports no theory module. |
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

## 11. Gates

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
