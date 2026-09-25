# The whitepaper: plan and shared brief

This directory holds a self-contained, human-accessible account of the core
proof idea of ConLeche: the modelling and consistency proof that bridges
annotated expressions, the *inductive* (relational) description of checking,
and a set theory given *with libraries*. Authorship line on every rendering:
"Claude, under the supervision of Joachim Breitner, Lean FRO". Maintainer rulings of 2026-09-25
are recorded here so every lane works from the same spec. Task #323.

## Deliverables

* `whitepaper/main.typ` (+ `sections/*.typ`): one Typst source, rendered to
  `whitepaper.pdf` and to HTML by `whitepaper/build.sh`; HTML output is
  synced to `_out/whitepaper/` (gitignored) after every merge so the
  maintainer can read it.
* `whitepaper/Fragment/*.lean`: a self-contained Lean verification of the
  fragment and its theorems (its own lake library, off the default targets,
  imports NOTHING from `ConLeche.*`; carries the `module` header like the
  rest of the tree, `public section` proofs-private style is fine but not
  required). No `sorry`, no axioms beyond the library class.
* `whitepaper/flake.nix` + `.envrc` (direnv): the document toolchain.
* `whitepaper/links-gate.sh`: an INDEPENDENT copy of the idea of
  `tests/overview-links.sh` — every `blob/master/<path>#L<a>-L<b>` link in
  the sources (to `ConLeche/*` and to `whitepaper/Fragment/*`) has its cited
  lines snapshotted in `whitepaper/links-expected.txt`; `--update` rewrites.
  Plus a build gate for the fragment (warning-free, no sorry/axioms) and for
  the document. Wired into `tests/arena.sh` and CI at the end.
* `whitepaper/NOTES.md`: places where, thinking at this level of
  abstraction, the con-leche proof itself could be simplified or made more
  elegant. Every lane appends to it (dated, one paragraph each).

## The fragment (rulings)

* **Terms**: in the LEAN FRAGMENT `bvar` (de Bruijn) with a typing CONTEXT
  Γ; in the PAPER named variables `x, y, …` with the usual pen-and-paper
  convention (terms up to renaming, capture-avoiding substitution `B[x:=a]`),
  stated once with a remark that the Lean development uses de Bruijn
  indices and the real checker uses `fvar`s (a performance device: the
  variable carries its own type, so the checker keeps no context). No index
  shifting in the paper — if a rule's presentation would need it, the
  named form is the one to write. `sort l`,
  `const c ls`, `app`, `lam A (pw) b`, `pi A (pw) B`. No `let` (the real
  checker's annotation pass inlines it — say so), no literals, no `proj`,
  no `mdata`.
* **Annotation**: each binder carries the coloured datum `pw : PropWhen`
  (= "never a proposition" | "a proposition exactly when these level
  parameters are all zero"), exactly con-leche's sealed `PropWhen`
  (`ConLeche/Kernel/PropWhen.lean`). In grammars, rules, premises and terms
  the annotation is typeset in ONE distinguished colour: a reader who
  ignores the colour sees Lean as it is.
* **Levels**: zero, succ, max, imax, param. Universe polymorphism stays
  (declarations have level parameters; `pw` refers to them). The
  operations ≤ and = on levels are ASSUMED correct and complete (a
  parameter of the development with a specification, not a definition).
  `zeroness : Level → PropWhen` IS defined (it is exact and small).
* **Reduction**: β at a `never` gate (uncertified), β certified (the
  argument's type is inferred and compared to the domain), δ, and in the
  environment section ι. Head-reduction closed under `appFn` and `trans`.
* **Definitional equality**: refl, symm, reduce-left, sort (level oracle),
  const, congruences for app/λ/∀, η, proof irrelevance. NO transitivity
  rule — and the paper explains why none can be added.
* **Inference**: one grade (drop the io grade, `appSkip`, `proofFast`).
  The ∀/λ rules CHECK the annotation: infer the body's sort `v`, require
  `zeroness v = pw`.
* **Certificate walks** (`Certs`, `DefEqList`, `EtaProjCerts`): folded into
  the rules that use them.
* **Environment section**: `def`s (δ) and single, non-mutual, non-nested
  inductives with parameters, indices, recursive AND reflexive fields
  (reflexive fields make types large and matter to the modelling); the
  recursor with large elimination and the subsingleton criterion for Prop
  inductives (the annotation reappears here). No `theorem`/`opaque`
  distinction, no axioms, no Quot, no pinned basis blocks: `False` is
  whatever empty Prop inductive the stream declares.
* **Consistency corollary**: no accepted environment stores a constant
  whose type is an inductive in Prop with zero constructors.
* **Dropped, with one sentence each in a "what we left out" list**:
  projections, mutual/nested blocks, Nat/String literals and the Nat fast
  path, Quot, pinned blocks, axioms/trust, K-like reduction, structure η,
  unit-likeness, the And rescue, fuel/caches/the executable checker and its
  bridge theorem, the two-phase parallel fold, the AnnotTerm intermediate
  layer (the paper has ONE denotation, directly on annotated terms).
* **A later section**: K-like reduction, η for structures, unit-likeness
  etc. all FOLLOW from extensionality of the model — show this.
* **Set theory with libraries**: ONE abstract structure, stated
  declaratively: sets, membership, extensionality; a point `pt`; truth
  values; n-ary tuples; dependent function spaces with application and
  abstraction and their laws; a universe chain with closure laws; least
  fixed points for the inductive section. The reader is not shown any
  construction and is assured that nothing beyond the stated laws is used
  — which the fragment Lean makes literal: the library is a class, and
  every theorem is proved against the class.

## Order of presentation

1. Introduction: what is being proved, the shape of the argument, why
   there is no typing judgement, what the colour means.
2. The env-free fragment, completely: terms and annotations; levels; the
   relations (reduction, defeq, inference); the library; the denotation;
   the invariant; the three claims and their proof — "by induction" where
   nothing interesting happens, and full discussion where the annotation
   plays a role or a syntactic proof would fail (no subject reduction for
   proof-λs, no Π-injectivity, why defeq cannot be transitive, proof
   irrelevance for free).
3. The environment: defs, then inductives (the fixpoint in the model,
   the recursor, ι, large elimination), the consistency corollary.
4. Extensionality corollaries (K, η, unit-like).
5. What we left out, and how the real proof differs from the fragment
   (fvar, AnnotTerm layer, bridge, ...), with links.

Links: unobtrusive, `blob/master/...#L..-L..` into the real proof AND into
`whitepaper/Fragment`, at the point where a definition/theorem is stated.

## Process

* Branch `whitepaper`; agents work in worktrees under `_tmp/wp/<lane>`
  (own `.lake`), rebase onto `whitepaper` and merge (fast-forward) THEMSELVES
  when done; after every merge run `whitepaper/build.sh` and sync
  `_out/whitepaper/`. Commit messages end with
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`.
* Every prose section gets a critical review pass (accessible? jargon
  free? to the point?) before it is considered done.
* Keep this file current when rulings change.

## Writing rules added on the way

* (2026-09-25) Make NO claims about the state of research in type-theory
  metatheory ("hard", "open", "unsolved"): researchers keep moving those
  goalposts. Say what THIS proof does not need, and stop there.
* (2026-09-25) Every mention of `OVERVIEW.md` (or `README.md`) with a
  section number is a LINK to that section on GitHub: use the
  `#overview(n)[…]` macro (anchor checked by `links-gate.sh`).
* (2026-09-25) Say "the semantic invariant" (`WellDenoted`), never a
  bare "the invariant": there are many invariants around.
* (2026-09-25) Say "how to interpret a `∀` or a `λ`" (two interpretations,
  function space vs truth value), not "read a binder": a binder `(x : A)`
  is something the reader can read just fine.
