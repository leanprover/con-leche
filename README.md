# con-leche – a CONsistent LEan CHEcker

This is an external checker for the Lean theorem prover that is proven (in Lean) to be consistent in that it does not accept a proof of False.

The core idea of this project is: What if we allow the checker implementation to do extra work (type comparisons) that is not strictly necessary for soundness, but makes the proof easier.

## Status

The checker is practically useful and has good performance. I consider it production ready.

It was implemented and proven to be consistent by Claude (Fable and Opus), under heavy supervision by Joachim Breitner at the Lean FRO. See the git history for all the detours and dead ends it took.

This README is actually human written (with AI only doing copy-editing, fact checking and filling in numbers). It is probably the only human written thing in this repository.

There is an AI-written overview of the project in [OVERVIEW.md](./OVERVIEW.md).

## Design of the checker implementation

* The checker is implemented in Lean.
* It uses its own term representation, so it does not rely on Lean’s `Lean.Expr`, and thus does not rely on the unverified C++ routines for that type.
* Term representation is locally nameless, with open variables represented as deBruijn level + type (inspired by [nanoda](https://github.com/ammkrn/nanoda_lib)).
* Memoization of core checker routines via hash maps and hashes pre-computed using `@[computed_field]`, like in the official checker and [lean4lean](https://github.com/digama0/lean4lean/).
* The checker has a uniform strategy for handling inductive types, including mutual and nested, based on a positivity analysis. It does not perform the nested-to-mutual reduction that the official kernel uses. (Early versions of con-leche used an extensional modelling approach based on [lean-inductive-models](https://github.com/nomeata/lean-inductive-models), but has since phased that out.)
* In anticipation of [lean4#14896](https://github.com/leanprover/lean4/pull/14896), theorem bodies are opaque. A k-rule like hack for `And` allows processing proofs built by Lean versions before that change.
* Accelerated Nat operations are performed using Lean’s `Nat` type.
* It accepts only the three standard Lean axioms in the input stream.

  For practicality reasons, it silently *ignores* the [`sorryAx`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/ParsedC.lean#L213-L214) axiom declarations from the standard library, but will complain it is actually used. The (deprecated) `trustCompiler`, `ofReduceBool` and `ofReduceNat` axioms are replaced with simple definitions of the same type.

  The checker (at the moment) will reject any other axiom.
* The checker processes files in three phases: *parsing* the input stream, *installing* all declarations into the environment and then *checking*. All stages can use parallelism with [`--jobs`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L125).
* The parser is a fast agentic-hand-written parser over the input bytes (verified with respect to a naive one, see below).

## Design of the checker proof

The idea of the consistency proof is that we define a model in set theory, classical and extensional, and show that our checker only accepts Lean terms that have a model in that world.

Depending on your background and your level of interest you may want to look at the Main Corollary or the Main Theorem.

### The Main Corollary

At the end of [`ConLeche/MainTheorem.lean`](./ConLeche/MainTheorem.lean) we prove that an export file containing a `theorem … : False := …` declaration (in JSON), with arbitrary declarations before and after, will not be accepted by `con-leche`:

```lean
open Frontend in
theorem no_False_declaration (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (h : jsonWithTheoremFalse chunks) :
    ∃ e, (do
      let pre ← builtinPreludeE
      let r ← parseChunks chunks
      let ds := preparePrelude pre r.decls
      checkDecls .verified pins ds) = .error e
```

The meaning of [`False`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Basis/False.lean#L50-L51) is hard-coded, so no tricks involving odd definitions for `False` will confuse the checker. This is a meaningful theorem if you assume that worrisome kernel implementation bugs or flaws in the theory are those that can be used to prove anything, in particular `False`.

The program's actual [`main`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L520) and [`run`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L392) function is of course more than this; in particular it performs IO (reading the input file in chunks, reporting progress, spawning threads). You are invited to follow the `main` function and convince yourself that the above theorem says something about the data flow through the actual driver.

### The Main Theorem

The theorem [`no_False_declaration`](https://github.com/leanprover/con-leche/blob/master/ConLeche/MainTheorem.lean#L110-L117) is mostly a corollary of a stronger statement, namely that every accepted environment has a model in a suitable set theory. This theorem is also found in [`ConLeche/MainTheorem.lean`](./ConLeche/MainTheorem.lean):

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env)
```

This is the interesting theorem if you want to be sure that con-leche interprets your Lean terms and types the way you intend them. The relation [`Model V env`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L248-L268) (in [ConLeche/Denotes.lean](./ConLeche/Denotes.lean)) states that every constant in the environment denotes a member of its type's denotation (and that `False` denotes the empty set and that `Eq` denotes set equality). In particular, every accepted theorem's statement is true in the model.

Denotation of terms and types is captured by the inductive relation [`Denotes`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Denotes.lean#L123-L124) in the same file. It depends on some set-theoretical constructions (e.g. function spaces).

The `Model` relation is *not* the strongest property proven (and carried through the induction) about the environment, but a simplified one. For example, it does not contain the delta and iota equations – but since they can easily be added as an explicit `theorem : lhs = rhs := rfl`, this is hopefully not an oversimplification.

This theorem only talks about [`checkDecls`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Cached/Installed.lean#L441-L446) and its output `env`, which has the form that we define our semantics about. You may want to look through the code and consult additional theorems that relate this to your input in a meaningful way. You may want to check that

* The parser is faithful.
* [`preparePrelude`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Frontend/Prepare.lean#L165-L172) only reorders declarations and adds missing prelude declarations, but does not drop any (see [`theorem Frontend.preparePrelude_perm`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Verify/Frontend/Prepare.lean#L157-L162)).
* The definitions, theorem statements and axioms in the output of `checkDecls` are as they are in the input, up to dropping the `sorryAx` declaration (see [`theorem checkDecls_consts`](https://github.com/leanprover/con-leche/blob/master/ConLeche/Model/StreamConsts.lean#L237-L242)).

### Set theory assumption

The set model we assume in [`[SetTheory V]`](https://github.com/leanprover/con-leche/blob/master/ConLeche/SetTheory/Core.lean#L95-L133) is fairly standard. It assumes ZF without infinity and choice (extensionality, pairing, union, power set, regularity, replacement) plus an ω-chain of Grothendieck universes `univ 0 ∈ univ 1 ∈ …`, stated in Tarski's form. Choice is inherited from Lean as the meta-logic. See [`ConLeche/SetTheory/Core.lean`](./ConLeche/SetTheory/Core.lean) for the precise formulation of our set theory.

The interface is instantiated on Mathlib's `ZFSet` from the ω-many-inaccessible-cardinals hypothesis of Carneiro's consistency analysis in [lean4lean-model](https://github.com/digama0/lean4lean-model): see the theorem [`carneiro_implies_conleche`](https://github.com/leanprover/con-leche/blob/master/bridge/lean4lean-model/ConLecheBridge/Carneiro.lean#L200-L202) in [`bridge/lean4lean-model`](./bridge/lean4lean-model) (separate package due to the Mathlib dependency).

Future work: The assumption that we need a ω-chain is maybe unnecessarily strong. Every concrete stream has an upper bound of universe levels it needs, and we could assume only a chain of length `k`. For every concrete `k` we can prove their existence in lean without further assumptions, just not for all `k`.

### Interpreting Pi and the certification tax

In our set interpretation, false propositions are *∅* and true propositions are *{•}* for a special point *•*, so proof irrelevance and propositional extensionality is built in. This causes problems when interpreting Lean’s `∀`: If the pi type is building a proposition we need to model this differently than if we are building a type. But we want the interpretation to be syntax directed, and *not* depend on type inference!

For most types `∀ (x : A), B x`, we can look at the semantic values `[B] x` for all `x ∈ [A]`: If they are all propositions, then we interpret the pi type as a proposition, else as a proper dependent function.

Unfortunately, this rule can make a function type look like it is a proposition: If `[A]` is the empty set, then there is no value to peek at, so we have no choice but to interpret such a function as *•*, even if syntactically it produces a type. This allows a syntax-driven interpretation.

A consequence of this is we have a bit less structure in the semantic value of a function type than we would like to. In particular, we may not be able to read the domain off a value in `[∀ (x : Empty), B x]`. The proof still goes through if we do some extra calls to `infer` and `defeq`. For example when comparing two `.lambda` expressions we additionally check whether their bodies have the same type.

We call this extra work the *certification tax* of our proof: Work we only do because our proof is not better. The checker can be run in [`--trusted`](https://github.com/leanprover/con-leche/blob/master/Main.lean#L108) mode where these checks are omitted to quantify the cost.

### Nat operations

The checker performs fast reduction of `Nat` operations on literals, using Lean's own `Nat` type. When functions like `Nat.add` are declared it checks if the definition is defeq to the expected definition (embedded at build time based on the functions in the building toolchain) for this to be sound. The checker embeds versions of these definitions from different toolchain releases to be able to accept proofs from more than just its own toolchain.

Bugs in the Lean runtime support for `Nat` can lead to unsoundness here. It should be straightforward to hook up a different (verified) bignum implementation.

### The proof idea

We have an (AI written) account of [the core proof idea](https://leanprover.github.io/con-leche/con-leche-proof-idea.html), in the shape of something resembling a research paper. If this leaves questions open, please let me know.

## Relation to lean4lean

This project intentionally explores a different point in the design space than [lean4lean](https://github.com/digama0/lean4lean/): We compromise on the checker implementation (extra checks) so that we can have a direct model-based proof of consistency that does not need some of the hard-to-prove metatheoretical properties of Lean.

The lean4lean project aims at something bigger: Produce a verified checker that does *not* do steps that we assume to be not necessary, and understand the metatheory of the Lean logic, beyond just consistency.

Additionally, this project relies on Mario Carneiro's thesis (*The Type Theory of Lean*, master's thesis, Carnegie Mellon University, 2019) for much of the set theoretical modelling.

## The parser

The fast byte-wise parser is proven equivalent (`@[csimp]`) to a naive reference parser, and is covered by the Main Corollary mentioned above, which is stated in terms of the actual bytes entering the pipeline. (The Main Theorem does not cover the parser; it is not clear how to express the main theorem in terms of the raw input bytes.)

## Performance

This checker is usually faster than the official kernel, and competitive with other external checkers. It supports parallelism and should scale to large proofs. See [`PERF.md`](./PERF.md) and the [Kernel Arena](https://arena.lean-lang.org/) for more details.

This required pulling some low-level stunts that the kernel does in C++ in Lean, in particular around the memo tables (peeking at the RC to decide if something is worth caching, implementing whole expression traversals without touching the RC field and using pointer addresses for hashing). This is possible, to some extent, with functions like [`withPtrAddr`](https://leanprover-community.github.io/mathlib4_docs/Init/Util.html#withPtrAddr) that expose such runtime information to safe code, given a proof that this runtime information cannot affect the logical result of the function. This is also already anticipating that a safe `withExclusive` ([RFC #15235](https://github.com/leanprover/lean4/issues/15235)) will become part of the standard library; until then we have [this code here](https://github.com/leanprover/con-leche/blob/master/ConLeche/Kernel/Exclusive.lean).

## Next steps

This project was published when it was barely usable – able to process mathlib within reasonable memory usage and not absurdly slow. Since then we have come a long way – significant perf improvements, a much simpler proof – but there is more to be done:

* Make it even faster.
* Use a verified bignum library for `Nat` handling.

## Acknowledgements

Joachim would like to thank Mario Carneiro for all the groundwork this builds on, and Arthur Adjedj for helpful discussions to understand what I actually built here.

## Contributions

Since I did not write the code, I am not interested in code contributions, because I cannot review them. Issues are welcome, and the more detailed and precise they are, the more likely is that I will let an agent work on them.
