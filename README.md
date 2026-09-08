# con-leche – a CONsistent LEan CHEcker

This is an external checker for the Lean theorem prover that is proven (in Lean) to be consistent in that it does not accept a proof of False.

The core idea of this project is: What if we allow the checker implementation to do extra work (annotations, checks) that is not strictly necessary for soundness, but makes the proof easier.

## Status

The checker is practically useful; it can process a mathlib export in about an hour within 12GB of memory. It is a relatively slow checker (see below for why), roughly 1.6× slower than the official kernel on common workloads.

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
* Accelerated Nat operations are performed using Lean’s `Nat` type.
* It accepts only the three standard Lean axiom in the input stream.

  For practicality reasons, it silently *ignores* the other axiom declarations from the standard library, including `sorryAx`, but will complain if they are used.

  The checker (at the moment) will reject any other axiom.

## Design of the checker proof

The idea of the consistency proof is that we define a model in set theory, classical and extensional, and show that our checker only accepts Lean terms that have a model in that world.

### The main theorem

In [`ConLeche/MainTheorem.lean`](./ConLeche/MainTheorem.lean) we prove that if the `checkDecls` function (which is called from `main`), when run in `--verified` mode, accepts a list of declarations `ds`, then no declaration of type `False` was included:

```lean
theorem no_proof_of_False (V : Type w) [SetTheory V]
  (ds : List DeclC) (env : Env)
  (accepted : checkDecls .verified ds = .ok env) :
  ¬ ∃ c ∈ env.consts, c.toConstantVal.type = .const falseName []
```

Of course this is just a corollary of a stronger statement that every environment built by this function has a model in the set theory.

The meaning of `False` is hard-coded, so no tricks involving odd definitions for `False` will confuse the checker.

The parser is not covered by the verification.

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


## Contributions

Since I did not write the code, I am not interested in code contributions, because I cannot review them. Issues are welcome, and the more detailed and precise they are, the more likely is that I will let an agent work on them.
