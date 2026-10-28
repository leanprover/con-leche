# The whitepaper: plan and shared brief

This directory holds a self-contained, human-accessible account of the core
proof idea of con-leche: the modelling and consistency proof that bridges
Lean's terms, the *inductive* (relational) description of checking,
and a set theory given *with libraries*. Authorship line on every rendering:
"Joachim Breitner, Lean FRO" (the AI-authorship note at the top says the rest). Maintainer rulings of 2026-09-25
are recorded here so every lane works from the same spec. Task #324.

## Deliverables

* `whitepaper/main.typ` (+ `sections/*.typ`): one Typst source, rendered to
  `con-leche-proof-idea.pdf` and to HTML by `whitepaper/build.sh`; HTML output is
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
  `const c ls`, `app`, `lam A b`, `pi A B`, `let x : T := v; b` (by
  substitution, as the checker does). No literals, no `proj`, no
  `mdata`.
* **The model reads binders off the values** (ruling of 2026-10-12): a
  function space is propositional iff every fibre is a truth value, an
  abstraction is the point iff every body value is; over an empty
  domain both read "proposition". Sorts denote the types of their
  universe (truth values included above `Prop`); the point is
  `{ptTag}` in con-leche. The claims of reduction and equality say
  nothing about the point.
* **The colour** marks the certification tax: the checks con-leche
  makes that the official kernel does not (the lambda congruence/η
  body-type premises; in the certified case of ι, the comparisons of
  the constructor's levels, parameters and index expressions with the
  recursor's, and the check of the constructor application's parameters
  and fields). A reader who ignores the colour sees the official
  kernel's rules.
* **Levels**: zero, succ, max, imax, param. Universe polymorphism stays
  (declarations have level parameters). The
  operations ≤ and = on levels are ASSUMED correct and complete (a
  parameter of the development with a specification, not a definition).
* **Reduction**: β (no premise), ζ, δ, and in the environment section ι
  (with K, and the step through projections as theorems).
  Head-reduction closed under `appFn` and `trans`.
* **Definitional equality**: refl, symm, reduce-left, sort (level oracle),
  const, congruences for app/lambda/∀, η, proof irrelevance; lambda
  congruence and η compare the bodies' types (innermost level of a
  lambda telescope only).
  NO transitivity rule — and the paper explains why none can be added.
* **Inference**: Lean's rules at the full grade; the cheaper grade
  (`infer_only`, the hereditary claim) as its own subsection.
* **Certificate walks** (`CertsF`, `DefEqList`): folded into
  the rules that use them.
* **Environment section**: `def`s (δ) and single, non-mutual, non-nested
  inductives with parameters, indices, recursive AND reflexive fields
  (reflexive fields make types large and matter to the modelling); the
  recursor with large elimination and the subsingleton criterion for Prop
  inductives. No `theorem`/`opaque`
  distinction, no axioms, no Quot, no pinned basis blocks: `False` is
  whatever empty Prop inductive the stream declares.
* **Consistency corollary**: no accepted environment stores a constant
  whose type is an inductive in Prop with zero constructors.
* **Dropped, with one sentence each in a "what we left out" list**:
  projections, mutual/nested blocks, Nat/String literals and the Nat fast
  path, Quot, pinned blocks, axioms/trust, structure η,
  unit-likeness, the And rescue, fuel/caches/the executable checker and its
  bridge theorem, the two-phase parallel fold, the `Term` intermediate
  layer (the paper has ONE denotation, directly on the terms).
* **A later section**: K-like reduction, η for structures, unit-likeness
  etc. all FOLLOW from extensionality of the model — show this.
* **Set theory with libraries**: ONE abstract structure, stated
  declaratively: sets, membership, extensionality, separation (the
  genuine axiom, for every predicate of Lean's logic); a point `pt`
  and its singleton; truth values as an ABBREVIATION `{x ∈ {pt} | P}`,
  not a law (ruling of 2026-09-26); n-ary tuples; dependent function spaces with application and
  abstraction and their laws; a universe chain with closure laws; least
  fixed points for the inductive section. The reader is not shown any
  construction and is assured that nothing beyond the stated laws is used
  — which the fragment Lean makes literal: the library is a class, and
  every theorem is proved against the class.

## Order of presentation

1. Introduction: what is being proved, the shape of the argument, why
   there is no typing judgement, how a `∀` or a lambda is interpreted.
2. The env-free fragment, completely: terms; levels; the
   relations (reduction, defeq, inference); the library; the denotation;
   the invariant; the three claims and their proof — "by induction" where
   nothing interesting happens, and full discussion where the reading of
   a binder or the point plays a role or a syntactic proof would fail (no
   Π-injectivity, why defeq cannot be transitive, proof irrelevance for
   free); the certification tax; the cheaper grade.
3. Adding definitions: the environment, what a definition's check is,
   δ, the model contract and how the model grows with a definition.
4. Adding inductive types: what is checked, the fixpoint in the model,
   the recursor, ι and when it needs a certificate (K, the step through
   projections), large elimination; the consistency corollary.
5. Nested inductive types (the full check, the model as a sketch).
6. Extensionality corollaries (η for structures, unit-like).
7. Checking module by module (tasks #370, #375): abstract first —
   what the argument needs from a consistency proof (models with values,
   assembly and amalgamation of a compatible family, the conservative
   step; refinement and restriction derived); then modules, refinement
   and keys (home module, or a proof's statement), the local checks per
   home and per importer, the per-module theorem (a compatible family
   of models, one per module; corollary: every module has a model),
   parallelism, comparison; NO global environment and NO renaming;
   Lean's levels, `import all`, re-exports and merge rule appear only
   in a mapping table at the end; con-leche in a `#real` block.
8. What we left out, and how the real proof differs from the fragment
   (fvar, `Term` layer, bridge, ...), with links.

Links: unobtrusive, `blob/master/...#L..-L..` into the real proof AND into
`whitepaper/Fragment`, at the point where a definition/theorem is stated.
The link is the phrase itself (`#src("path", a, b)[the phrase]`, label
required), marked by a muted dotted underline — no arrow or other mark;
in HTML the phrase shows the cited lines on hover.

## Process

* The whitepaper lives with the code it cites; lanes work in worktrees
  under `_tmp/` (own `.lake`) and land on the integration branch with a
  merge commit; after every landing run `whitepaper/build.sh` (via
  `nix develop ./whitepaper`) and sync `_out/whitepaper/`.
  `whitepaper/fragment-gate.sh` and `whitepaper/links-gate.sh` run in
  `tests/arena.sh`.
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
* (2026-09-26) "The official kernel" for Lean's, "the checker" for
  con-leche's; never a bare "the kernel". Do not point out that the
  official kernel comes without a proof.
* (2026-09-26) The project is called "con-leche" in prose; "ConLeche"
  exists only in module names and paths.
* (2026-09-26) The omissions are listed in §1 ("This document") and in
  §6, nowhere else: no "not in the fragment" asides in between without
  a specific reason at that spot.
* (2026-09-26) The Lean fragment is mostly a sanity check of the paper.
  The prose links to it but does not explain its mechanics (classes,
  parameters, "every theorem is proved against it", de Bruijn plumbing)
  beyond the two remarks that earn their place: the de Bruijn/named
  variables remark in §2 "Terms", and the library-as-a-class remark in
  §2 "The set theory, with libraries" (the reader is assured nothing
  beyond the stated laws is used). Explanations of the fragment belong
  in its comments.
* (2026-09-26) Not "licenses"/"licensed by": write "justifies", "allows"
  or "permits".
* (2026-09-26) Not "library": the set theory is "the set theory we
  assume" / "the axioms" — an axiomatised, deliberately non-minimal
  theory in Lean's higher-order logic. Said once in §2.

## Rulings of 2026-10-01 (after origin/master's uniform installer landed)

* The inductive story is rewritten upstream: ONE installer for every
  block; the family is the least fixed point of the operator read off
  the constructor types (the real proof calls it the hole operator);
  positivity looks through a container instance such as `List T` by
  walking `List`'s own stored block at that instantiation; recursors
  are GENERATED (the stream's recursor records supply only their types,
  compared up to definitional equality; rule bodies are ignored); the
  recursor's set is the least relation closed under the rules, shown
  single-valued (the real proof's "graph route"); existence of the
  fixed point is by accessibility, not by a container theorem; large
  elimination is refused for nested blocks; mutual blocks are the same
  installer with a tuple of operators.
* Sections: §4 "Adding inductive types" (simple blocks, rewritten to
  the new story), §5 "Nested inductive types" (NEW), §6 extensionality
  (re-cited), §7 what we left out. MUTUAL blocks are skipped: one
  sentence in §7.
* NO pen-and-paper claim without the Lean fragment behind it. The
  nested section is backed by a nested extension of the fragment with
  this scope: a block may have CONTAINER fields, a previously installed
  block `K` applied to the member in one of `K`'s parameter positions
  (`List (Tree α)`); positivity through `K`'s stored constructors at
  that instantiation; the model reads the field through `K`'s own
  fixed-point clause at the given parameters, monotone by `K`'s
  positivity plus leastness; generated `T.rec` and auxiliary `T.rec_1`
  for the outside class with their ι laws, by one graph over both;
  large elimination refused for nested blocks. Left to the real proof,
  listed in §7: nesting at depth ≥ 2, containers with indices, nesting
  through a reflexive field.
* Terminology: the maintainer's current names; NEVER "native route",
  "fixpoint route", "direct route". "Class", "outside class", "frame",
  "hole", "graph route" are jargon: avoid where a plain phrase does the
  job, otherwise gloss at first use.
* Worked example for §5: `Tree α` with `node : α → List (Tree α) →
  Tree α` (the fixture `tests/e2e/src/nested_rec.lean`).
* (2026-10-02) Paper and fragment stay IN SYNC: when the prose says what
  is checked, derived, or assumed, that is what the fragment checks,
  derives, or assumes — change the Lean, not just the words, when a
  ruling moves a condition (e.g. "closedness follows from typing" means
  `DefOk` no longer demands it and a lemma proves it).
* (2026-10-02) "Installer" is jargon too: say "the checker" (and "checks
  … uniformly" for the one-installer point).
* (2026-10-02) Prose about the REAL proof/checker lives in its own
  set-off block (`#real[…]`, labelled "In con-leche", muted, skippable), never
  interleaved with the paper's own argument; inline, only the citation
  links remain. "The input" means the specification in this paper; the
  stream and raw declarations exist only inside `#real` blocks.
* (2026-10-02) Use display style liberally: a formula longer than a few
  symbols (a telescope, a generated type, a rule's right-hand side) is
  set on its own line, not inline.
* (2026-10-03) Always "the type former", never a bare "the former"
  (confusable with "the former/the latter").
* (2026-10-03) No boasting, no line counts ("ten lines", "two lines",
  "costs nothing"): say what follows from what.

## Ruling of 2026-10-03: the fragment follows con-leche's proof

The point of the paper is to expose con-leche's proof. The fragment
may SIMPLIFY it, never replace it by a different proof. For inductive
types this means (con-leche's names in brackets): the universes are
Grothendieck universes (the axiom); an operator on families is
ACCESSIBLE when each element it produces depends on a bounded
subfamily of its input, for one bound fixed in the universe, and an
accessible operator has a closed family in the universe — a THEOREM
proved along well-founded trees [`closed_of_acc`, `SetModel/Access`];
the family is the least fixed point INSIDE the set theory, the
intersection of the closed subfamilies of that closed family
[`lfpFamSet`/`lfpTuple`]; the block's operator is monotone and
accessible BY POSITIVITY [`HoleMono`, `HoleAcc`, `blockAcc_of_run`],
for nested blocks through the container's clause; the recursor by the
graph route [`GraphRecKit`]. The fragment keeps its spec-based operator
(field kinds given by the specification) instead of the hole-and-frame
machinery: what is mirrored is what is proved and from what. The
abstract closure laws for tuples, tags and function spaces stay as
laws; the ad-hoc "inductive closure" law goes.
* (2026-10-03) Never "the member" for the type being defined: that is
  con-leche's word for a member of a mutual block, which this paper
  skips, and "member" already means set membership here. Say "the type being defined" (its occurrence inside a
  container: "the nested occurrence"), "the parameter field" for the
  container's field whose domain is the parameter, and "the
  approximant" for the family the operator is applied to.
* (2026-10-03) Source links attach to a phrase of the sentence, never a
  generic label: the underline style already says where it goes (dashed:
  the fragment, dotted: con-leche). No "(fragment)", "(real checker)",
  "(real proof)" labels; when a sentence cites both, attach each link
  to a different natural phrase (e.g. the name of the thing for one,
  the property claimed for the other).
* (2026-10-03) No separate monotonicity story: accessibility is the
  property; monotonicity, needed only for the fixed-point equation
  (and induction), follows from it on families in the universe
  (`AccFam.mono`). The fragment derives it (`famOp_mono`,
  `ContClause.mono`, `Fam_psK_mono`), for plain and nested blocks and
  in both regimes; the paper says so in one sentence where
  accessibility is defined, and once for the container's clause.
* (2026-10-03) Banned words: "load-bearing", "licenses" (and the other
  rules above). Say "needed", "used", "justifies".
* (2026-10-03) "Our proof" (or "the present proof"), never "this proof"
  — ambiguous after a sentence about another proof.

## Ruling of 2026-10-03 (later): §5 changes tack

§5 (nested inductive types) no longer presents the restricted nested
fragment in detail. It explains con-leche's FULL positivity check
(mutual blocks aside) and the generated recursors, and gives only the
INTUITION of how §4's construction and proofs extend — no proof of its
own, no claim that rests on the fragment. It opens by saying that it
changes tack. Its citations go to con-leche. The nested fragment stays
in the repository (built and gated) and is mentioned once as a
verified restricted case. This is the one exception to "no
pen-and-paper claim without the fragment behind it".

## Rulings of 2026-10-12: the design as it is

* The paper describes the design the fragment proves: terms without
  binder data, the model reading binders off the values, claims silent
  about the point, the certification tax, the cheaper grade, ι with its
  three laws and K, `let` by substitution.
* **Path independence**: describe the design as it is, as if it had
  always been so. No mention of what the design used to have, not even
  in contrast ("no longer", "unlike before"); the same for NOTES.md
  entries. The `#real` blocks and the con-leche citations describe the
  checker and proof as they are in the tree the paper is built from.
* The cheaper grade skips the `let` value check, as `infer_only` does;
  the full grade keeps it.
* Terminology: a ∀-type is a "Π-type" (syntax) and its denotation a
  "(dependent) function space"; never "product", which reads as `Prod`.
  A `let` is a "let-expression" or "let-binding", never a "local
  definition": definitions are entries of the environment.
* Terminology: a λ-expression is "a lambda-expression", or "a lambda" if
  the longer form gets too verbose. Never write the symbol λ as a noun
  in running text ("a $lambda$", "two $lambda$s", "the $lambda$'s
  domain", "$lambda$-telescopes", "$lambda$-congruence"); λ stays where
  it is notation: inside formulas and rules, binder notation such as
  `$lambda x : A. b$`, rule names inside formulas, and code identifiers.

## Rulings of 2026-10-28 (task #375): §7 per module

* No global world, no renaming. Every module uses its own names; what
  identifies a constant across modules is its key (home module, or a
  proof's statement). The theorem is per module: a compatible family
  of models (same key, same value; every proof the point); the
  corollary drops compatibility. The proof glues only over a module's
  imports.
* §7 starts with the abstract view on environment models: what any
  consistency proof must provide, stated before any Lean or fragment
  detail.
* Writing (maintainer, on §7): careful mathematical prose. State what a
  notion is (a definition), then why it is needed; one claim and its
  justification per paragraph; no slogans, no "X is a Y, not a Z"
  constructions, no aphorisms.
