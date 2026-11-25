# con-leche – a CONsistent LEan CHEcker

This is an external checker for the Lean theorem prover that is proven (in Lean) to be consistent in that it does not accept a proof of False.

The core idea of this project is: What if we allow the checker implementation to do extra work (type comparisons) that is not strictly necessary for soundness, but makes the proof easier.

It was implemented and proven to be consistent by Claude, under heavy supervision by Joachim Breitner at the Lean FRO.

This README is actually human written (with AI only doing copy-editing, fact checking and filling in numbers). It is essentially the only human written thing in this repository. There is an AI-written overview of the project in [OVERVIEW.md](./OVERVIEW.md).

## Design of the checker implementation

* The checker is implemented in Lean.
* It uses its own term representation, so it does not rely on Lean’s `Lean.Expr`, and thus does not rely on the unverified C++ routines for that type.
* Term representation is locally nameless, with open variables represented as deBruijn level + type (inspired by [nanoda](https://github.com/ammkrn/nanoda_lib)).
* Memoization of core checker routines via hash maps and hashes pre-computed using `@[computed_field]`, like in the official checker and [lean4lean](https://github.com/digama0/lean4lean/).
* The checker has a uniform strategy for handling inductive types, including mutual and nested, based on a positivity analysis. It does not perform the nested-to-mutual reduction that the official kernel uses. (Early versions of con-leche used an extensional modelling approach based on [lean-inductive-models](https://github.com/nomeata/lean-inductive-models), but has since phased that out.)
* In anticipation of [lean4#14896](https://github.com/leanprover/lean4/pull/14896), theorem bodies are opaque. A k-rule like hack for `And` allows processing proofs built by Lean versions before that change.
* Accelerated Nat operations are performed using Lean’s `Nat` type.
* It accepts only the three standard Lean axioms in the input stream.

  For practicality reasons, it silently *ignores* the [`sorryAx`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/ParsedC.lean#L304-L305) axiom declarations from the standard library, but will complain it is actually used. The (deprecated) `trustCompiler`, `ofReduceBool` and `ofReduceNat` axioms are replaced with simple definitions of the same type.

  With [`--compare`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L142), axioms in the challenge are accepted when justified by the solution.

  The checker (at the moment) will reject any other axiom.
* The checker processes files in two phases: *parsing* the input stream and *checking*. Both stages can use parallelism with [`--jobs`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L139).
* The JSON and olean parsers are fast agentic-hand-written parsers over the input bytes (verified with respect to naive ones).
* It can optionally check a development in a modular fashion, and also compare challenges against solutions (see below).

## Design of the checker proof

The idea of the consistency proof is that we define a model in set theory, classical and extensional, and show that our checker only accepts Lean terms that have a model in that world.

Depending on your background and your level of interest you may want to look at the Main Corollary or the Main Theorem.

### The Main Corollary

A declaration called [`False`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis/False.lean#L50-L51) is only accepted if it really is that, so no tricks involving odd definitions for `False` will confuse the checker. This allows us to state the main idea of the consistency proof concisely: A JSON file that obviously and syntactically declares a theorem of type `False` (see [`jsonWithTheoremFalse`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Accepts.lean#L53)) is never accepted:

```lean
open Frontend in
theorem main_no_False (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b)
    (hF : jsonWithTheoremFalse [b]) : False
```

### The Main Theorem

The theorem [`main_no_False`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L55-L57) is mostly a corollary of [a stronger statement](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L47-L49), namely that the declarations of an accepted file have a model in a suitable set theory:

```lean
open Frontend in
theorem main_json_model (V : Type w) [SetTheory V] {file : String} {fs : FS} {b : ByteArray}
    (h : ModelIO.CanGive (Driver.runArgs ["--", file]) fs 0) (hb : fs.file file = some b) :
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList)
```

This is the interesting theorem if you want to be sure that con-leche interprets your Lean terms and types the way you intend them. In particular, every accepted theorem's statement is true in the model. The [`IsModel`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L212-L213) expresses that a model (a mapping from Lean names to such sets) is valid for a set of Lean declarations, expressed using the function [`Expr.eval`](https://github.com/leanprover/con-leche/blob/master/ConLeche/IsModel.lean#L128-L129), which gives each Lean expression (types and terms) an interpretation as sets.

### Proofs about IO

The theorems above talk about the whole checker, including the driver that parses arguments, reads files, runs parallel threads, all in the `IO` monad. This is out of reach for a completely rigorous verification, but we can still do something meaningful here.

To that end the driver function [`runArgs`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L324) runs in a generic monad with a [`CheckerIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L141) type class modelling three kinds of operations:

* File access (existence, reading)
* A [`parMapExcept`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L168) operator for parallelism
* Running other `IO` with [`liftIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L184)

We perform proofs about such generic code in an idealized (pure, nondeterministic) model, [`ModelIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/CheckerIO.lean#L310). These proofs are meaningful under some assumptions, which are not enforced:

* The files accessed are not changing under our nose. Later reads during the process see the same state of the file system.
* The code run by `liftIO` has no side effects affecting the file reading operations and does not exit with code 0. We use this method for (otherwise pure) concurrency, diagnostic output and measuring time.

In the model, we assume nothing about `liftIO a` or its return value, except of course its type. Using a subtype there allows us to run, say, parallel code and still know that the result is what we need for the proof (e.g. [`checkDeclsIO`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Run.lean#L85) returning a subtype mentioning [`checkDecls`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Decls.lean#L106-L107)).

The real [`main`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L95) calls the generic [`runArgs`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L324) at the `IO` instance, and additionally takes care of [enabling the linearity protection](https://github.com/leanprover/con-leche/blob/master/Main.lean#L28), flushing the output and exiting the process.

If you find this deeply unnerving, you can look at [`model_exists`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/PureChecker.lean#L31-L34) theorem that talks about the pure parts of the checker, and convince yourself that that is what the driver calculates.

### Set theory assumption

The set model we assume in [`[SetTheory V]`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L95-L133) is fairly standard. It assumes ZF without infinity and choice (extensionality, pairing, union, power set, regularity, replacement) plus an ω-chain of Grothendieck universes `univ 0 ∈ univ 1 ∈ …`, stated in Tarski's form. Choice is inherited from Lean as the meta-logic. See [`ConLeche/SetTheory/Core.lean`](./ConLeche/SetTheory/Core.lean) for the precise formulation of our set theory.

The interface is instantiated on Mathlib's `ZFSet` from the ω-many-inaccessible-cardinals hypothesis of Carneiro's consistency analysis in [lean4lean-model](https://github.com/digama0/lean4lean-model): see the theorem [`carneiro_implies_conleche`](https://github.com/leanprover/con-leche/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202) in [`bridge/lean4lean-model`](./bridge/lean4lean-model) (separate package due to the Mathlib dependency).

Future work: The assumption that we need a ω-chain is maybe unnecessarily strong. Every concrete stream has an upper bound of universe levels it needs, and we could assume only a chain of length `k`. For every concrete `k` we can prove their existence in lean without further assumptions, just not for all `k`.

### Interpreting Pi and the certification tax

In our set interpretation, false propositions are *∅* and true propositions are *{•}* for a special point *•*, so proof irrelevance and propositional extensionality is built in. This causes problems when interpreting Lean’s `∀`: If the pi type is building a proposition we need to model this differently than if we are building a type. But we want the interpretation to be syntax directed, and *not* depend on type inference!

For most types `∀ (x : A), B x`, we can look at the semantic values `[B] x` for all `x ∈ [A]`: If they are all propositions, then we interpret the pi type as a proposition, else as a proper dependent function.

Unfortunately, this rule can make a function type look like it is a proposition: If `[A]` is the empty set, then there is no value to peek at, so we have no choice but to interpret such a function as *•*, even if syntactically it produces a type. This allows a syntax-driven interpretation.

A consequence of this is we have a bit less structure in the semantic value of a function type than we would like to. In particular, we may not be able to read the domain off a value in `[∀ (x : Empty), B x]`. The proof still goes through if we do some extra calls to `infer` and `defeq`. For example when comparing two `.lambda` expressions we additionally check whether their bodies have the same type.

We call this extra work the *certification tax* of our proof: Work we only do because our proof is not better. The checker can be run in [`--trusted`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L138) mode where these checks are omitted to quantify the cost.

### Nat operations

The checker performs fast reduction of `Nat` operations on literals, using Lean's own `Nat` type. When functions like `Nat.add` are declared it checks if the definition is defeq to the expected definition (embedded at build time based on the functions in the building toolchain) for this to be sound. The checker embeds versions of these definitions from different toolchain releases to be able to accept proofs from more than just its own toolchain.

Bugs in the Lean runtime support for `Nat` can lead to unsoundness here. It should be straightforward to hook up a different (verified) bignum implementation.

### The proof idea

We have an (AI written) account of [the core proof idea](https://leanprover.github.io/con-leche/con-leche-proof-idea.html), in the shape of something resembling a research paper. If this leaves questions open, please let me know.

## Relation to lean4lean

This project intentionally explores a different point in the design space than [lean4lean](https://github.com/digama0/lean4lean/): We compromise on the checker implementation (extra checks) so that we can have a direct model-based proof of consistency that does not need some of the hard-to-prove metatheoretical properties of Lean.

The lean4lean project aims at something bigger: Produce a verified checker that does *not* do steps that we assume to be not necessary, and understand the metatheory of the Lean logic, beyond just consistency.

Additionally, this project relies on Mario Carneiro's thesis (*The Type Theory of Lean*, master's thesis, Carnegie Mellon University, 2019) for much of the set theoretical modelling.

## The `.olean` parser

In addition to reading the official export format (`.ndjson`), `con-leche` can also read `.olean` files directly. This avoids the need to run `lean4export`. You can either check all modules reachable from a root module, or just [the dependencies of a specific constant](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L153). See the usage section in [OVERVIEW.md](./OVERVIEW.md#0-using-the-checker) for how to use it.

The `.olean` “format” is not well-specified. We ship our own “naive” parser [`decodeModuleSpec`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Olean/View.lean#L81), used by the [`InModulePart`](https://github.com/leanprover/con-leche/blob/master/ConLeche/OleanInput.lean#L83-L85) you see in the main theorem, as a specification, and then prove that the actual parsers we use (which are optimized, and may read partial data as needed) are correct with regard to that one. We cannot prove that `decodeModuleSpec` matches how Lean interprets its data structures, only test it (using the [`olean-compare`](./OleanCompare.lean) tool).

## Modular checking

In addition to checking all declarations of a development in one go, `con-leche` can perform checks in a modular fashion, building on [Lean's module system](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/#module-scopes). In this mode, every module's content is checked in the context of just its imports. That, plus one check that the module dependency graph is acyclic, proves consistency. The main theorem is [`main_modular_one`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L126-L134):

```lean
open Frontend in
theorem main_modular_one (V : Type w) [SetTheory V] {dirs root : String} {r : Name} {fs : FS}
    (hr : Olean.parseModName root = some r)
    (h : ModelIO.CanGive
      (Driver.runArgs ["--olean", "--modular", "--search-path=" ++ dirs, "--", root]) fs 0) :
    ∃ model : Name → (Name → List Nat → V),
      (∀ m, Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        IsModel V (model m) (Olean.moduleConstants (Driver.searchPathOf dirs) fs m)) ∧
      (∀ m n m', Olean.InClosure (Driver.searchPathOf dirs) fs #[r] m →
        Olean.Sees (Driver.searchPathOf dirs) fs m n m' → model m n = model m' n)
```

Note that this theorem does *not* say that there is one global model that works for every module. The Lean module system allows the same name with different meaning, as long as these are visible from disjoint parts of the module tree. Therefore, this theorem states that

* each module has a model
* whenever two modules `m` and `m'` [see](https://github.com/leanprover/con-leche/blob/master/ConLeche/OleanInput.lean#L97-L98) the same name `n`, the model agrees. This means [Lean's module system visibility rules](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Olean/Snapshot.lean#L52-L66) are part of the trusted specification here.

The [`--modular`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L156) flag loads and checks all modules in one process, and is not that useful – if you can do that, you might as well use the [`--olean`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L148) that ignores the module system. To get the benefit of modular checking (e.g. lower memory usage) you can use [`con-leche --schedule`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L157). Then an (unverified) scheduler will invoke a fresh `con-leche` process on each module, keep memory usage in check, resumes from aborted runs, etc. See `con-leche --help` or the OVERVIEW section. The meaning of the commands that are executed by the scheduler together forms theorem [`main_modular`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L109-L120).

If the scheduler does not serve you well you can use [`con-leche --schedule-commands`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L164) to get the list of commands to run and schedule them yourself (possibly even distributed to multiple machines, if that is necessary).

## --compare

In addition to just checking one set of declarations, con-leche can also perform comparisons between a challenge and a solution, like [`lake comparator`](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator). This is available in all the various reading modes (JSON file, merged `--olean`, `--modular`).

The rules of comparison differ from `lake comparator`. You do not explicitly specify which declarations are to be filled by the solution. Instead, [every axiom and every definition or theorem with a `:= sorry` body are holes](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Justify.lean#L73), and `con-leche` [checks that the solution has a regular declaration](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Justify.lean#L187) with the same type, with all the used definitions agreeing between challenge and solution.

The main theorem [`main_compare_json_model`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L63-L66) shows this in action:

```lean
open Frontend in
theorem main_compare_json_model (V : Type w) [SetTheory V] {c s : String} {fs : FS}
    (h : ModelIO.CanGive (Driver.runArgs ["--compare", "--", c, s]) fs 0) :
    ∃ bC rC, fs.file c = some bC ∧ parseChunks [bC] = .ok rC ∧
      ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList)
```

It is worth noting that the conclusion of the theorem says nothing about the solution. It just says that the challenge has a model. This is intentional: The solution is what allows the checker to *accept* the challenge, but it does not and must not affect what the challenge *means*.

When reading olean files, one can pass different search directories for the challenge and the solution. The proof also says that the meaning of the challenge, i.e. whether it has a model or not, only depends on the files in the [trusted search path](https://github.com/leanprover/con-leche/blob/master/ConLeche/Driver/Cli.lean#L151), nothing else on the file system. This is part of the statement of [`main_compare_model`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L88-L94) (and of [`main_modular_compare`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L143-L155) for `--modular`):

```lean
open Frontend in
theorem main_compare_model (V : Type w) [SetTheory V] {T D c s : String} {C S : Name} {fs : FS}
    (hc : Olean.parseModName c = some C) (hs : Olean.parseModName s = some S)
    (h : ModelIO.CanGive (Driver.runArgs ["--olean", "--compare", "--trusted-search-path=" ++ T,
      "--search-path=" ++ D, "--", c, s]) fs 0) :
    ∀ fs', FS.AgreeUnder (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs fs' →
      ∃ model, IsModel V model (Olean.closureConstants
        (Driver.trustedOr (Driver.searchPathOf T) (Driver.searchPathOf D)) fs' #[C])
```

## Performance

This checker is usually faster than the official kernel, and competitive with other external checkers. It supports parallelism and should scale to large proofs. See [`PERF.md`](./PERF.md) and the [Kernel Arena](https://arena.lean-lang.org/) for more details.

This required pulling some low-level stunts that the kernel does in C++ in Lean, in particular around the memo tables (peeking at the RC to decide if something is worth caching, implementing whole expression traversals without touching the RC field and using pointer addresses for hashing). This is possible, to some extent, with functions like [`withPtrAddr`](https://leanprover-community.github.io/mathlib4_docs/Init/Util.html#withPtrAddr) that expose such runtime information to safe code, given a proof that this runtime information cannot affect the logical result of the function. This is also already anticipating that a safe `withExclusive` ([RFC #15235](https://github.com/leanprover/lean4/issues/15235)) will become part of the standard library; until then we have [this code here](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Exclusive.lean).

## Acknowledgements

Joachim would like to thank Mario Carneiro for all the groundwork this builds on, and Arthur Adjedj for helpful discussions to understand what I actually built here.

## Contributions

Code contributions are likely not useful. Issues are welcome, and the more detailed and precise they are, the more likely is that I will let an agent work on them.
