# Setlec — a verified Lean checker

Setlec is a checker for Lean declarations, implemented in Lean, verified in
Lean. The goal is a checker that is performance-competitive with lean4lean or
even the official kernel, together with a machine-checked consistency proof:

> For everything the checker accepts there is a model in a suitable set
> theory. In particular, no declaration of type `Empty` is ever accepted.

This document records the design decisions. It was distilled from the initial
project prompt and is updated as decisions evolve.

**Project goal** (set 2026-08-19): the lean kernel arena *tutorial* tests
(except those involving custom axioms) are accepted by the checker, and the
checker is verified to be consistent.

## The model

* The target theory is **Tarski–Grothendieck set theory**. Inside Lean it is
  expressed as an interface (`Setlec.SetTheory`), a class over a universe
  type `V`; all verification is parametric in a model of that interface, which
  serves as the "extra assumption for cardinality reasons". Constructing an
  instance from `ZFSet`-style machinery (cf.
  https://github.com/digama0/lean4lean-model, `Consistency.lean`) can be done
  separately. The interface only grows on demand, so it stays evident what the
  consistency proof assumes.
* In the target theory, **propositional and definitional equality coincide**
  and are plain set equality. `Eq` maps directly to equality in the model;
  this collapse is a crucial design point.
* `Prop` maps to `{ {}, {•} }`: a proposition is either the empty set or a
  fixed singleton. Proof irrelevance is immediate.
* `Empty` maps directly to the empty set (as does `Empty.rec` suitably), which
  is what lets us phrase consistency as "no declaration of type `Empty` is
  accepted".
* The model of `Nat` is the omega set; `Nat` literals map to the binary
  representation of elements of omega. Justifying optimized `Nat` operations
  comes later.
* The model is **level-polymorphic**: level-polymorphic constants map to
  functions from omega (level assignments) into a sequence of universes.
* **No general construction of inductives** (no W-types). This is the main
  simplification over Mario Carneiro's thesis
  (https://github.com/digama0/lean-type-theory/releases): the parts of the
  thesis about the core type theory construction remain relevant, the
  inductive construction does not.

## Inductives via preprocessing

The checker uses https://github.com/nomeata/lean-inductive-models as a
preprocessor (eventually invoked transparently by the `setlec` binary). For
each inductive it builds, *in Lean*, a model: type former, constructors,
recursors, projections as `def`s, and their iota rules as theorems. The
checker then only needs to check that this model matches the declared
inductive. For an inductive with a `_model` from the preprocessor,
`⟦T⟧ := ⟦T._model⟧`, so the model theorems apply without rewriting.

Only the "basis" inductives get hand-written models: `Eq`, `Nat`, `PSigma'`,
`PUnit`, `Quot` (plus the direct `Empty` clause). `PSigma'` and `PUnit` get
custom models (level-zero-or-not case distinction may be needed). These live
in modules analogous to `derived/` in nanodatg.

Axioms: only the three standard axioms are supported; anything else is
"declined" (lean kernel arena exit convention). They map to custom
constructions.

## Term representation

* Our own inductives (`Setlec.Expr` etc.), not `Lean.Expr`: no cached
  metadata, clean verification.
* nanoda-style free variables: an `fvar` is a **de Bruijn level plus its
  type** (binder name is display-only); the type is part of the variable's
  identity. Hence the local context is implicit in every open term, which
  simplifies verification substantially. Input terms from declarations are
  closed and use only `bvar` (de Bruijn indices).
* No metavariables, no `mdata`.

## Checker structure and verification style

* **Strict layering**: implementation code (`Setlec/Kernel/*`, `Main.lean`)
  must not depend on any module from the theory/verification part
  (`Setlec/SetTheory/*`, `Setlec/Model/*`, `Setlec/Verify/*`). The
  verification imports the implementation, never the other way around.
* Verification is **extrinsic**: alongside each checker function there is a
  certifying variant producing the model-level fact
  (we don't put LCF-style certificates in the runtime environment):
  - `infer_ev e` returns a proof of `⟦e⟧ ∈ ⟦infer e⟧`
  - `whnf_ev e` returns a proof of `⟦e⟧ = ⟦whnf e⟧`
  - `defeq_ev e₁ e₂` succeeds iff `defEq e₁ e₂` and returns a proof of
    `⟦e₁⟧ = ⟦e₂⟧`
  - similarly for level operations.
  Whenever the checker produces or assumes `e : t`, a corresponding
  `⟦e⟧ ∈ ⟦t⟧` fact is produced or assumed. Typing assumptions about the local
  environment are hypotheses of the kernel theorems (only such typing facts
  may appear as hypotheses of `*_ev` results); recall the local environment is
  implicit in the term representation.
* The `*_ev` functions follow the structure of the unverified ones closely.
  Steps needing non-trivial constructions go into helper functions in their
  own modules, keeping files small and context-friendly.
* Per constant the (conceptual) global environment carries: its
  interpretation and typing theorem; for inductives the symbols/theorems
  listed above (iota, and where applicable unit-like/eta/K theorems); for
  definitions the delta-unfolding theorem.
* **Match real kernels**: follow nanoda and the official kernel for the order
  of clauses and checks, so reduction happens the same way — same lazy
  unfolding strategy, same pervasive caching. Caches (including the fvar
  caches and any expr-keyed construction) must be memoized with data
  structures whose soundness is feasible to verify, and the certifying
  operations are memoized alongside so proofs are not re-derived. Cache
  lifetime equals that of the corresponding unverified caches.
* **No union-find defeq cache**: known unsound with a non-transitive defeq
  implementation.
* Reference material: https://github.com/nomeata/nanodatg (a certifying, not
  verified, checker for the same target theory; see its `kernel/`) — much of
  its construction transfers. Local clones of reference repos live in
  `_tmp/`.

## Iteration protocol

1. Started from a trivial checker that rejects every declaration as
   "not implemented yet", proved consistent (vacuously, but with
   non-degenerate definitions: the interpretation function is undefined
   everywhere, so only the empty environment has a model).
2. Add **one feature at a time**, updating the verification each step. Use
   the lean kernel arena tutorial tests as a guide; when the next tutorial
   step is too big, write intermediate test cases. Maintain a regression test
   suite (`tests/`, run via `lake test`).
3. Termination of checker functions: use fuel, `partial_fixpoint`, or the
   lean4lean approach — whatever keeps verification simple.
4. Proof style: aim for high `grind` automation. Most proofs should be
   induction / `fun_induction` followed by `grind`; invest in good grind
   annotations.
5. If the checker becomes too slow to iterate quickly, prefer algorithmic
   fixes (caching) over pressing on with features.
6. Constructions not tied to Lean specifics (or to a particular syntax
   representation) go into their own modules (analogous to nanodatg's
   `derived/`). Small modules, narrow interfaces; isolate users of a
   set-theoretic construction from its implementation.
7. Depending on mathlib is acceptable if necessary (ordinals etc.), but
   self-contained is preferred.
8. Commit often.

## Environment notes

* Sandbox: `/tmp` and `/home` are tmpfs — large artifacts (repo checkouts,
  worktrees) go into `_tmp/` inside this repository (gitignored).
* If the checker may OOM, run it under a timeout and memory limit; a process
  eating all memory can kill the whole session.
* For Lean proof work, https://github.com/ejgallego/lean-beam/ may speed
  things up.

## Current state

* Project scaffold: latest stable Lean (`lean-toolchain`), `lakefile.toml`.
* `Setlec.Kernel.{Expr,Env,Checker}`: term representation, environment,
  trivial always-rejecting checker.
* `Setlec.Verify.Checker`: proofs about the checker functions themselves.
* `Setlec.SetTheory.Basic`: minimal TG interface (membership + empty set).
* `Setlec.Model.{Interp,Consistency}`: everywhere-undefined interpretation,
  `EnvModel`, and the theorems `accepted_env_has_model` / `consistency`.
* `Main.lean`: stub CLI.
* `tests/SetlecTests.lean`: `#guard`-based tests, run with `lake test`.

### Next steps

1. Input pipeline: parse lean4export format (or drive via `Lean.Environment`)
   so real declarations reach the checker.
2. First accepting feature: `axiom` declarations whose type is `Sort u` /
   simple sorts — requires `infer`/`whnf`/`defeq` skeletons and the
   corresponding interpretation of sorts as sets of sets.
3. Grow `SetTheory` interface as needed (universes, omega, pairing, …).
