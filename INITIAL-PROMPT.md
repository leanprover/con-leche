This is the inital design prompt. It outlines most of the decisions, but is not gospel: If something is clearly amistake or type, fix it. Remove this file once it has been absorbed into more permanent documenation.

You are building a verified lean checker. It is implemented in Lean, and eventually needs to be performance wise competitive with lean4lean or even the official kernel.

You will be proving consistency, by proving that for everything that the checker accepts there is a model in a suitable set theory.

In that target set theory, propositional and definiional equality coincide and are just plain equality. This means that the checker can use  https://github.com/nomeata/lean-inductive-models. as a preprocessor: This tool builds, in lean, models of inductives (type former, constructors, recursors, projections as defs and their iota rules as theorems). The checker only needs to check that the model matches the declared inductive. See the REAMDE there for instructions.

Begin with a trivial checker that just rejects any declaratoin as “not implemented yet”, and prove it to be consistent. Then iteratelive add one feature at a time, updating the verification.. You can use the lean arena tutorial tests to work through, or define your own sequence of tests. Of course, maintain your own test suite of regression tests and tests that you write to exercise the next step.

The model should be in Tarski-Grothendik set theory. See https://github.com/nomeata/nanodatg/ for a certifying (not verified) checker for the target theory (see kernel/) and lots insights on the construction that can transfer. This is ultimately derived from Mario’s thesis (https://github.com/digama0/lean-type-theory/releases). Find a suitable way to express this model inside Lean, likely with some extra assumption for cardinality reasons or so; https://github.com/digama0/lean4lean-model/blob/master/Lean4LeanModel/Consistency.lean may be interesting.

I suggest you use nanodas term representation, where opened variables are represented by debruijn level + their type, and the type is part of the identity. This means the context of implicit in a term, which I assume simplifies verification a lot.

We start from scratch because verifying a checker that wasn't built with verification in mind is usually hard. Nevertheless, we need to build something that can handle real lean code, so look at nanoda and the official kernel for the order of clauses and checks, so that reduction happens the same way. In particular you will have to implement (and verify) the same pervasive caching we see in real kernels, and implement the same lazy unfolding strategy. Build and verify the checker piece by piece, but always in the right direction to converge on a working design.

The model should be level-polymorphic. In the latest iteration of the certified checker, level-polymorphic functions/types/etc. are mapped to functions from omega, and there is a sequence of universes. 


The following hints were sent to the certifying checker, but most apply (suitably adapted) to the verificaion as well (only that we don't put LCF certificates in the runtime environment, but rather perform extrinsic verification):

* [[Prop]] maps to `{ {}, \dot }`, so a proposition is either the empty set or a singleton set. Proof irrelevance is immediate.
* Whenever the checker produes or assumes `e : t`, a correspodning  `[[e]] ∈ [[t]]` certificate has to be produced or assumed.
* The global environment is extended with certification related machinery:
  - Every constant: its interpretation symbol and it typing theorem
  - The kernel fvar caches for local variables, for level parameters and any possible expr-based construction
  - For every inductive:
    Symbols for type former, constructor, recursors and (if applicable) projections
    Theorems for the iota rules for recursors and projections, and (if applicable) unit-like, eta and rule-k theorem.
  - For definitions: the delta unfolding theorem
  - For axioms: Only the three standard axioms are supported (the rest are “declined”, in the lean kernel arena exit convention). These map to custom constructions in derived/
* The typing assumptions about local environment are hypotheses of the kernel theorem. Only these typing theorems may be in the hyps of a theorem returned by the `*_ev` functions.
  (Remember that the local environment is implicit in nanodas' term representation, as local variables are debruijn levels annotated with their type)
* The Inductive construction relies on https://github.com/nomeata/lean-inductive-models. This preprocessor, which should be transparently called by the binary you are writing, creates models for inductives that create declarations for exactly the components just listed. So by processing them in order, whenever an inductive declarations comes, the environment will have the necessary symbols and theorems.
  - Only the “basis” inductives need hand-written models (Eq, Nat, PSigma', PUnit, Quot). Some of these you will find in derived/ already, else write them. Do *not* write a general construction for inductives (W-types or so)
  - `Eq` direclty maps to equality in the set model. This collapsees definitional and propositional equality, a crucial design point.
  - `PSigma'` and `PUnit` get custom models with code in derived/. Here the level-zero-or-not may be necessary.
  - Additionall, `Empty` gets a direct clause to the empty set (and of course `Empty.rec`). This makes it possible to phrase consistency as “no declaration of type Empty is accepted”.
  - For inductives with `_model` from the preprocessor, `[[T]] := [[T._model]]` so that they model theorems apply without rewriting.
  - **No** general construction of inductives, no W-types etc. This is what makes verifying a lean kernel a huge task, so we avoid it. Lots of Mario's thesis is about that and can be ignored for our purposes; the parts of the thesis about the core type theory construction is relevant.
* Write certifying variants of the type checker functions (infer, whnf, defeq).
  - infer_ev(e) should return a proof of `[[e]] ∈ [[infer(e)]]`
  - whnf_ev(e) should return a proof of `[[e]] = [[whnf(e]]`
  - defeq_ev(e1, e2) should succeed if `def_eq(e1, e2)` is true and return a proof of `[[e1]] = [[e2]]`

  Similar for the level operations.

  These functions should follow in their structure closely the unverified ones. Steps that need non-trivial constructions should use a helper function in its own module, to keep file sizes reasonable and context-friendly.
* Memoize all these operations, so that we do not re-derive proofs. This is important for realisitc performance. The caches should live as long as the existing caches for the normal operations. Make sure that the cache data structure you define makes verification of soundness feasible.
* No union-find defeq cache, these are now known to be unsound with a non-transitive defeq implementation.
* The model of `Nat` should be the omega set in the set theory
  - Nat literals map to the binary representation for elements of this set.
  - Justifying optimized Nat operations comes later. We’ll talk about that then.

Iteration guidance:

* Set up the project using latest stable lean and lakefile.toml (not lakefile.lean)
* Build the theory first.
* Depending on mathlib is ok if necessary (ordinals or so), although a self-contained library is also good.
* Start with a rejecting, trivialy consistent checker. Then add one feature as a time, verifying it. Be guided by the tutorial tests, but if there the next one is too big of a step, create your own test cases that help you focus on the next thing that needs doing.
* Constructions that are not tied to Lean specific, or at least not to a particular Lean syntax representation go into their own modules, similar to derived/ in the nanodatg repo.
* Small modules with clearly defined narrow interfaces. Isolate user of a construction/abstraction in the set theory from its implementation.
* Carefully write the necessary correctness theorems for each function involved, so that the actual proof work can be done locally, on each case, with very little 
* If the checker becomes too slow to run to iterate quickly, see if there are algorithmic improvements (e.g. caching) to tackle now, rathr than the next step towards completeness.
* For the proofs, try to achieve a high level of grind automation. Lots of proofs are likely boring but tedious induction (or fun_induction) followed by not very clever reasoning. Ideally the not-very clever reasoning is just `grind`, so do invest in good grind annotations.
* Many type checker function is likely not easily proven to be terminating. You can peek in the lean4lean repo for how Mario handles that. Or just use simple fuel. Or use `partial_fixpoint`.
* Commit often.



Env information:

* This is a sandbox. /tmp and /home are tmpfs, so put large things (checkouts of repositories, worktrees) into `_tmp/` in the project repository.
* If there is a risk that the checker will OOM, put a timeout and memory limit on it. A process eating through all available memory can cause the whole session to be killed.
* When working on lean proofs, see if https://github.com/ejgallego/lean-beam/ speeds you up

