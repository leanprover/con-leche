# con-leche – a CONsistent LEan CHEcker

This is an external checker for the Lean theorem prover that is proven (in Lean) to be consistent in that it does not accept a proof of False.

The core idea of this project is: What if we allow the checker implementation to do extra work (annotations, checks) that is not strictly necessary for soundness, but makes the proof easier.

## Status

The checker is practically useful; it can process a mathlib export in about 20 minutes on a single worker thread (a few minutes with eight) within 8GB of memory. It is a relatively slow checker (see below for why), executing roughly 1.1–1.3× the instructions of the official kernel on common workloads.

It was implemented and proven to be consistent by Claude (Fable and Opus), under heavy supervision by Joachim Breitner at the Lean FRO. See the git history for all the detours and dead ends it took. It is a huge pile of code and a mess. Maybe this will improve over time. Until then: It works and is proven. 

This README is actually human written (with AI only doing copy-editing, fact checking and filling in numbers). It is probably the only human written thing in this repository.

There is an AI-written overview of the project in [OVERVIEW.md](./OVERVIEW.md).

## Design of the checker implementation

* The checker is implemented in Lean.
* It uses its own term representation, so it does not rely on Lean’s `Lean.Expr`, and thus does not rely on the unverified C++ routines for that type.
* Term representation is locally nameless, with open variables represented as deBruijn level + type (inspired by [nanoda](https://github.com/ammkrn/nanoda_lib)).
* Memoization of core checker routines via hash maps and hashes pre-computed using `@[computed_field]`, like in the official checker and [lean4lean](https://github.com/digama0/lean4lean/).
* The checker has two strategies for handling inductives:

  * Non-mutual non-nested inductives are supported natively: The checker checks the shape of the inductives, and the proof can models them abstractly.
  * For mutual and nested inductives the checker creates, at runtime, an explicit model of these inductives, with theorems proving the iota rules of the recursor. The proof then leans on these models to justify the inductive. This step requires extensionality in the model to turn the propositional equality into a definitional equality.

    The modelling code is taken from [lean-inductive-models](https://github.com/nomeata/lean-inductive-models). During development, that tool was run as a preprocessor to handle almost all inductive types, and this was very conductive to bootstrap the project. Later the naive support was extended and we dropped the dependency.

* Accepted incompleteness: Primitive projections are only supported
  - for structures that are not mutually recursive
  - inside the projection *functions* that the elaborator produces.
* In anticipation of [lean4#14896](https://github.com/leanprover/lean4/pull/14896), theorem bodies are opaque. A k-rule like hack for `And` allows processing proofs built by Lean versions before that change.
* Accelerated Nat operations are performed using Lean’s `Nat` type.
* It accepts only the three standard Lean axiom in the input stream.

  For practicality reasons, it silently *ignores* the the `sorryAx` axiom declarations from the standard library, but will complain it is actually used. The (deprecated) `trustCompiler`, `ofReduceBool` and `ofReduceNat` axioms are replaced with simple definitions of the same type.

  The checker (at the moment) will reject any other axiom.
* The checker processes files in three phases: parsing the input stream, *installing* all declarations (including annotating) and *checking*. The last stage can be run parallel using `--jobs`.
* The parser is an agentic-hand-written parser over the input bytes.

## Design of the checker proof

The idea of the consistency proof is that we define a model in set theory, classical and extensional, and show that our checker only accepts Lean terms that have a model in that world.

Depending on your background and your level of interest you may want to look at the Main Corollary or the Main Theorem.

### The Main Corollary

At the end of [`ConLeche/MainTheorem.lean`](./ConLeche/MainTheorem.lean) we prove that an export file containing a `theorem … : False := …` declaration (in JSON), with arbitrary declarations before and after, will not be accepted by `con-leche`:

```lean
theorem no_False_declaration (V : Type w) [SetTheory V] (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified ds) = .error e
```

The meaning of `False` is hard-coded, so no tricks involving odd definitions for `False` will confuse the checker. This is a meaningful theorem if you assume that worrisome kernel implementation bugs or flaws in the theory are those that can be used to prove anything, in particular `False`.

The program's actual `main` function is of course more than this; in particular it performs IO (reading the input file in chunks, reporting progress, spawning threads). You are invited to read through the `main` function and convince yourself that the above theorem says something about the data flow through the actual main function.

### The Main Theorem

The theorem `no_False_declaration` is mostly a corollary of a stronger statement, namely that every accepted environment has a model in a suitable set theory. This theorem is also found in [`ConLeche/MainTheorem.lean`](./ConLeche/MainTheorem.lean):

```lean
theorem model_exists (V : Type w) [SetTheory V]
  (ds : List DeclC) (env : Env)
  (accepted : checkDecls .verified ds = .ok env) :
  Nonempty (Model V env)
```

This is the interesting theorem if you want to be sure that con-leche interprets your Lean terms and types the way you intend them. The relation `Model V env` (in [ConLeche/Denotes.lean](./ConLeche/Denotes.lean)) states that every constant in the environment denotes a member of its type's denotation (and that `False` denotes the empty set and that `Eq` denotes set equality). In particular, every accepted theorem's statement is true in the model.

Denotation of terms and types is captured by the inductive relation `Denotes` in the same file. It depends on some set-theoretical constructions (e.g. function spaces).

The `Model` relation is *not* the strongest property proven (and carried through the induction) about the environment, but a simplified one. For example, it does not contain the delta and iota equations – but since they can easily be added as an explicit `theorem : lhs = rhs := rfl`, this is hopefully not an oversimplification.

This theorem only talks about `checkDecls` and its output `env`, which has the form that we define our semantics about. You may want to look through the code and consult additional theorems that relate this to your input in a meaningful way. You may want to check that

* The parser is faithful.
* `preparePrelude` only reorders declarations and adds missing prelude declarations, but does not drop any (see `theorem Frontend.preparePrelude_perm`).
* The definitions, theorems and axioms in the output of `checkDecls` are as they are in the input, up to annotations, zeta-reduction and dropping the `sorryAx` declaration (see `theorem checkDecls_consts`).

### Set theory assumption

The set model we assume in `[SetTheory V]` is fairly standard. It assumes ZF without infinity and choice (extensionality, pairing, union, power set, regularity, replacement) plus an ω-chain of Grothendieck universes `univ 0 ∈ univ 1 ∈ …`, stated in Tarski's form. Choice is inherited from Lean as the meta-logic. See [`ConLeche/SetTheory/Core.lean`](./ConLeche/SetTheory/Core.lean) for the precise formulation of our set theory.

The interface is instantiated on Mathlib's `ZFSet` from the ω-many-inaccessible-cardinals hypothesis of Carneiro's consistency analysis in [lean4lean-model](https://github.com/digama0/lean4lean-model): see the theorem `carneiro_implies_conleche` in [`bridge/lean4lean-model`](./bridge/lean4lean-model) (separte package due to the Mathlib depenency).

Future work: The assumption that we need a ω-chain is maybe unnecessary strong. Every concrete stream has an upper bound of universe levels it needs, and we could assume only a chain of length `k`. For every concrete `k` we can prove their existence in lean without further assumptions, just not for all `k`.

### Level annotation

In our set interpretation, false propositions are *∅* and true propositions are *{∅}*, so proof irrelevance and propositional extensionality is built in. This causes problems when interpreting Lean’s `∀`: If the pi type is building a proposition we need to model this differently than if we are building a type. But we want the interpretation to be syntax directed, and *not* depend on type inference!

To resolve this, the checker annotates every `.pi` and `.lambda` with a `PropWhen` datum that says under which level assignments this is a proposition or a type. This is either “always type” or “prop when all of these level parameters are zero”.

With this annotation we can have a syntactic interpretation `[e]`. On top of this we define a *semantic* typing predicate that we can then show is preserved by reduction.

What's more: For functions producing types (but not those that are propositions) we can read the domain of the function off its semantic value. This means beta reduction can be proven to be semantics preserving without a run-time argument check, and it allows a faster `infer_only` operation that infers the type of a previously checked expression without re-checking the whole term. This was the crucial observation that unblocked this project.

### The certification tax

For sort-polymorphic functions the checker does perform an extra `infer` of the argument at run time. This happens relatively rarely in practice, so we still get a usable checker, but is part of what we call the *certification tax* in this project: Work we only do because our proof is not better. The checker can be run in `--trusted` mode where these checks are omitted to quantify the cost.

### Nat operations

The checker performs fast reduction of `Nat` operations on literals, using Lean's own `Nat` type. When functions like `Nat.add` are declared it checks if the definition is defeq to the expected definition (embedded at build time based on the functions in the building toolchain) for this to be sound. This check can be extended to recognize multiple variants of the functions to support multiple prelude versions, should this be needed.

Bugs in the Lean runtime support for `Nat` can lead to unsoundness here. It should be straightforward to hook up a different (verified) bignum implementation.

### Proof structure

The structure of the proof is … messy. Very path dependent and the result of lots of experimentation and refactoring and pivots. Instead of describing it here, I’d rather let an agent work on refactoring and cleaning it up, and then describing that. If you are still curious, let your favorite agent give you an overview and summary.

## Relation to lean4lean

This project intentionally explores a different point in the design space than [lean4lean](https://github.com/digama0/lean4lean/): We compromise on the checker implementation (annotations, extra checks, generated inductive models) so that we can have a direct model-based proof of consistency that does not need some of the hard-to-prove metatheoretical properties of Lean.

The lean4lean project aims at something bigger: Produce a verified checker that does *not* do steps that we assume to be not necessary, and understand the metatheory of the Lean logic, beyond just consistency.

Additionally, this project relies on Mario Carneiro's thesis (*The Type Theory of Lean*, master's thesis, Carnegie Mellon University, 2019) for much of the set theoretical modelling.

## The parser

The parser is proven equivalent to a naive reference parser written over a list of bytes, but this proof is unconnected to the rest of the development. It only serves to allow performance tweaks in the parser.

## Performance

This checker is rather slow, compared to the official kernel or lean4lean. See [`PERF.md`](./PERF.md) for details.

The main reason seems to be that the official kernel, written in C++, has access to more low-level optimizations around the memo tables (peeking at the RC to decide if something is worth caching, implementing whole expression traversals without touching the RC field and using pointer addresses for hashing). The lean4lean kernel uses `Lean.Expr`, including some functions on that data structure that are implemented in C++, so it benefits some from this.

On top of that there is the overhead of annotating terms and some extra checks; the certification tax explained above.

And on top of that there is surely plenty of optimizations still possible.

## Next steps

This project was published when it was barely useable – able to process mathlib within reasonable memory usage and not absurdly slow. There is more to be done:

* Make it faster.
* Direct support for mutual and nested types, dropping the run-time model generation.
* Use a verified bignum library for `Nat` handling.
* Lots of proof refactoring to clean up oddities and detours introduced by path dependencies.
* AI-translate the implementation to a different programming language, to be relisient against runtime and compiler bugs

## Acknowledgements

Joachim would like to thank Mario Carneiro for all the groundwork this builds on, and Arthur Adjedj for helpful discussions to understand what I actually built here.

## Contributions

Since I did not write the code, I am not interested in code contributions, because I cannot review them. Issues are welcome, and the more detailed and precise they are, the more likely is that I will let an agent work on them.
