# Setlec -- a lean checker that's never False

Setlec is an external checker for the Lean theorem prover that is proven (in Lean) to be consistent in that it does not accept a proof of False.

The core idea of this project is: What if we allow the checker implementation to do extra work (annotations, checks) that is not strictly necessary for soundness, but makes the proof easier.

## Status

The checker is practically useful; it can process all of mathlib in TODO minutes and within TODO memory. It is a relatively slow checker (see below for why), roughly 2.5× slower than the official kernel on common workloads.

It was implemented and proven to be consistent by Claude (Fable and Opus), under heavy supervision by Joachim Breitner. See the git history for all the detours and dead ends it took. It is a huge pile of code and a mess. Maybe this will improve over time. Until then: It works and is proven. 

This README is actually human written (with AI only doing copy-editing, fact checking and filling in numbers).

## Design of the checker implementation

* The checker is implemented in Lean.
* It uses its own term representation, so it does not rely on Lean’s `Lean.Expr`, and thus not the unverified C++ routines related to that.
* Term representation is locally nameless, with open variables represented as deBruijn level + type (inspired by nanoda).
* Memoization of core checker routines via hash maps and hashes pre-computed using `@[computed_field]`, like in the official checker and lean4lean.
* Only few inductive types are supported natively: `Empty`, `PUnit`, `Eq`, `Nat`, `Quot` and structures. For all other types, this checker relies on [lean-inductive-models](https://github.com/nomeata/lean-inductive-models) as a preprocessor that validates them.
* Accepted incompleteness: Primitive projections are only supported
  - on non-recursive non-indexed structures or
  - inside the projection *functions* that the elaborator produces.
* Accelerated Nat operations are performed using Lean’s `Nat` type.

## Design of the checker proof

The idea of the consistency proof is that we define a model in set theory, classical and extensional, and show that our checker only accepts Lean terms that have a model in that world.

### Set theory assumption

The set model is fairly standard. It assumes ZF without infinity and choice (extensionality, pairing, union, power set, regularity, replacement) plus an ω-chain of Grothendieck universes `univ 0 ∈ univ 1 ∈ …`, stated in Tarski's form; infinity and choice are derivable from that. See [`Setlec/SetTheory/Core.lean`](./Setlec/SetTheory/Core.lean) for the precise formulation of our set theory. We also show that this interface can be realized within Lean by Aczel's sets-as-trees construction, with the universe chain as the one remaining assumption ([`Setlec/SetTheory/Aczel.lean`](./Setlec/SetTheory/Aczel.lean)); that is the ω-many-inaccessible-cardinals hypothesis of Carneiro's consistency analysis, the same assumption as in the [lean4lean-model](https://github.com/digama0/lean4lean-model).

### Level annotation

In our set interpretation, false propositions are $\emptyset$ and true propositions are $\{\emptyset\}$, so proof irrelevance and propositional extensionality is built in. This causes problems when interpreting Lean’s `∀`: If the pi type is building a proposition we need to model this differently than if we are building a type. But we want the interpretation to be syntax directed, and *not* depend on type inference!

To resolve this, the checker annotates every `.pi` and `.lambda` with a `PropWhen` datum that says under which level assignments this is a proposition or a type. This is either “always type” or “prop when all of these level parameters are zero”.

With this annotation we can have a syntactic interpretation `[e]`.

What's more: For functions producing types (but not those that are propositions) we can read the domain of the function off its semantic value. This means beta reduction can be proven to be semantics preserving without a run-time argument check, the crucial observation that unblocked this project.

### The certification tax

For sort-polymorphic functions the checker does perform an extra `infer` of the argument at run time. This happens relatively rarely in practice, so we still get a usable checker, but is part of what we call the *certification tax* in this project: Work we only do because our proof is not better. The checker can be run in `--trusted` mode where these checks are omitted to quantify the cost.

### Nat operations

The checker performs fast reduction of `Nat` operations on literals, using Lean's own `Nat` type. When functions like `Nat.add` are declared it checks if the definition is defeq to the expected definition (embedded at build time based on the functions in the building toolchain) for this to be sound. This check can be extended to recognize multiple variants of the functions to support multiple prelude versions, should this be needed.

Bugs in the Lean runtime support for `Nat` can lead to unsoundness here. It should be straightforward to hook up a different (verified) bignum implementation.

## Relation to lean4lean

This project intentionally explores a different point in the design space than lean4lean: We compromise on the checker implementation (annotations, extra checks, preprocessed inductive models) so that we can have a direct model-based proof of consistency that does not need some of the hard-to-prove metatheoretical properties of Lean.

The lean4lean project aims at something bigger: Produce a verified checker that does *not* do steps that we assume to be not necessary, and understand the metatheory of the Lean logic, beyond just consistency, better.

Additionally, this project heavily relies on Mario Carneiro's thesis (*The Type Theory of Lean*, master's thesis, Carnegie Mellon University, 2019) for much of the set theoretical modelling.

## Performance

This checker is rather slow, compared to the official kernel or lean4lean. See [`PERF.md`](./PERF.md) for details.

The main reason seems to be that the official kernel, written in C++, has access to more low-level optimizations around the memo tables (peeking at the RC to decide if something is worth caching, implementing whole expression traversals without touching the RC field and using pointer addresses for hashing). The lean4lean kernel uses `Lean.Expr`, including some functions on that data structure that are implemented in C++, so it benefits some from this.

On top of that there is the overhead of annotating terms and some extra checks; the certification tax explained above.

And on top of that there is surely plenty of optimizations still possible.

## Next steps

This project was published when it was barely useable – able to process mathlib within reasonable memory usage and not absurdly slow. There is more to be done:

* Faster code.
* Direct support for more and more inductive types, thus reducing the dependency on `lean-inductive-models.`
* Lots of proof refactoring to clean up oddities and detours introduced by path dependencies.


## Contributions

Since I did not write the code, I am not interested in code contributions, because I cannot review them. Issues are welcome, and the more detailed and precise they are, the more likely is that I will let an agent work on them.


