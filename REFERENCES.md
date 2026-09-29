# ConLeche: related work, and how it differs

> **This document was written by an AI agent** (Claude, working with
> the maintainer), in contrast to `README.md`, which is human-written.
> It is not a bibliography: it lists the work that ConLeche most
> resembles and, for each item, says where the similarity ends. It is
> meant for a reader who knows one of these projects and wants to know
> what ConLeche does differently, and for the agents working on
> ConLeche, so that they do not rediscover a known design point. See
> `OVERVIEW.md` for the proof itself.

## 0. The shape being compared

Four features of ConLeche recur in every comparison below.

* **The specification is semantic, not syntactic.** There is no typing
  judgement anywhere in the development. The checker's acceptance is
  proved to imply a semantic invariant (every accepted term denotes,
  hereditarily, in a set-theoretic model), and the consistency theorem
  is a corollary of that. Nothing of the form "accepted ⇒ derivable"
  is stated, so no metatheory of the abstract calculus (confluence,
  subject reduction, normalisation, transitivity of definitional
  equality) is needed or proved.
* **Only the accepting direction is claimed.** The checker may reject
  or decline anything; the theorem says nothing about what it must
  accept. Completeness with respect to the official kernel is measured
  empirically (the kernel arena, Mathlib), not proved.
* **The model is Werner's, mechanised, behind an interface.** The
  target theory is a class `SetTheory V`: ZF-style operators plus a
  tower of Tarski–Grothendieck universes. The consistency proof is
  parametric in an instance; the instance is produced separately, on
  Mathlib's `ZFSet`, from the ω-inaccessibles hypothesis of Carneiro's
  analysis of Lean. Propositions are subsets of a one-point set, so
  proof irrelevance and propositional extensionality are built in.
* **The verified code is the code that runs.** The definitions the
  theorem is about are compiled by Lean's own compiler; performance
  variants are connected to them by proved `@[csimp]` equations, not
  by `implemented_by`. The trust surface is Lean's compiler and
  runtime, the export format, and a short list of documented escapes.

## 1. The set-theoretic model

### Werner, *Sets in types, types in sets* (TACS 1997)

The paper has two halves and both reappear in ConLeche.

*Types in sets* builds a set-theoretic model of the Calculus of
Inductive Constructions in ZFC with, roughly, one inaccessible
cardinal per predicative universe. `Prop` is interpreted
proof-irrelevantly, as subsets of a singleton, so proof irrelevance and
propositional extensionality are validated for free; predicative
universes are stages of the cumulative hierarchy at inaccessibles;
inductive types are least fixed points reached by iteration below the
inaccessible. ConLeche's interpretation is this construction:
propositions are subsets of `{pt}`, a Π whose codomain is a
proposition is a predicate space with a single proof point, sorts are
a chain of Tarski–Grothendieck universes, and an inductive block's
carrier is the least fixed point of its family functor.

*Sets in types* goes the other way: ZF is encoded inside type theory
with universes through Aczel's well-founded-tree encoding, plus
excluded middle, and the two directions together show that the type
theory and the set theory are of comparable strength, with the model's
assumption sitting strictly above the type theory it models. That
direction is ConLeche's bridge: Mathlib's `ZFSet` is the Aczel
encoding, and the bridge turns Carneiro's ω-inaccessibles hypothesis
into an instance of the `SetTheory` interface. The paragraph in
`OVERVIEW.md` on why the theorem does not contradict Gödel is Werner's
conclusion restated.

The difference is where the typing relation sits. Werner interprets
typing derivations: derivable implies true in the model, and
consistency is a statement about the abstract calculus, never about an
algorithm. ConLeche has no derivations. Its invariant is a semantic
predicate on terms, preserved by reduction, and the theorem is stated
directly about what the running checker accepts. That is also why the
checker can afford fuel-bounded reduction and memo-dependent behaviour:
only the accepting direction is claimed, so a run that gives up is
never a counterexample.

### Miquel and Werner, *The not so simple proof-irrelevant model of CC* (TYPES 2002); Lee and Werner, *Proof-irrelevant model of CC with predicative induction and judgmental equality* (LMCS 2011)

Both refine the singleton interpretation of `Prop`. The first shows
that the naive proof-irrelevant model is delicate at the interaction of
impredicative `Prop` with dependent elimination and with substitution
of proofs, and repairs it; the second extends the repaired model to
predicative inductive types and a judgmental-equality presentation.
ConLeche meets the same delicacy in its own terms: the interpretation
is total and term-directed, so it must know at each binder whether
the codomain is a proposition without inferring anything. The
annotated syntax records that sort at every binder (the "Prop-when"
datum of `ConLeche/Kernel/PropWhen.lean`), and elimination out of a
proposition into a type is admitted exactly where the official kernel
admits it (subsingleton elimination), plus one deliberate, name-keyed
exception for `And`.

### Aczel, *On relating type theories and set theories* (TYPES 1998)

The tree encoding of sets in type theory that the "sets in types"
direction uses. ConLeche's own development never mentions it: the
model tier is written against the `SetTheory` interface only, and the
encoding appears solely in the bridge, through Mathlib's `ZFSet`. A
reader who wants a concrete `V` can read the bridge; a reader who
wants to know what the proof assumes reads the class.

### Barras, *Sets in Coq, Coq in Sets* (Journal of Formalized Reasoning 2010)

The closest mechanised precedent for ConLeche's model tier. Barras
axiomatises ZF (optionally with inaccessibles) inside Coq, develops
functions, ordinals and fixpoint theory over it, and builds
set-theoretic models of the Calculus of Constructions, of its
extension with a universe hierarchy, and of an extension with
type-based-termination natural numbers, proving each sound in Coq. The
shape "axiomatise the target set theory as an interface inside the
proof assistant, then model the calculus against the interface" is
exactly ConLeche's `SetTheory` class, and Barras's observation that
replacement in its general form wants a type-level choice principle
has its counterpart in ConLeche's interface: replacement is a
Lean-level scheme over functions `V → V`, and choice is inherited from
the meta-logic rather than being a field.

The differences: Barras models a calculus, given by a typing relation,
and proves the interpretation of derivations sound; ConLeche models
whatever an algorithm accepts, with no relation in between. And
ConLeche's inductive types are one construction for every block,
single, mutual or nested: each block's carrier is the least fixed point
of the operator read off its constructors, with holes for the
recursive positions, and the proof that this operator is monotone and
small enough to have its fixed point inside the universe comes from
the run of the checker's positivity check (see "Inductive types"
below).

### Carneiro, *The Type Theory of Lean* (master's thesis, CMU 2019)

The reference for Lean's type theory and the source of ConLeche's
assumption. The thesis gives a formal presentation of Lean's kernel
theory (as of Lean 3): impredicative proof-irrelevant `Prop`, a
universe hierarchy with level expressions, inductive types with
subsingleton elimination, quotients, and the definitional-equality
rules including η and K. It then builds a set-theoretic model in ZFC
plus a strictly increasing ω-sequence of inaccessible cardinals,
interpreting `Type u` as the hierarchy stage at the `u`-th
inaccessible and `Prop` as `{∅, {∅}}`, and shows the strength
comparison in both directions, in Werner's manner: Lean proves the
consistency of ZFC with any finite number of inaccessibles, and ZFC
with ω many proves Lean consistent.

What ConLeche takes from it, directly: the truth-value universe
`U₀ = {∅, {•}}`; the interpretation of universes as a chain; the
ω-inaccessibles hypothesis itself, which the bridge theorem
`carneiro_implies_conleche` turns into a `SetTheory` instance, so that
the consistency assumption is no stronger than the one already
accepted for Lean; and the general strategy of interpreting an
inductive type as a least fixed point that lives in the universe.

The thesis also contains the negative results that shape ConLeche's
design. It shows that Lean's ideal definitional equality is
undecidable, that the kernel's algorithmic equality is not transitive,
and that subject reduction fails in the presence of proof irrelevance
and the η/K rules. Any verification of the real kernel against a
syntactic judgement has to confront these. ConLeche does not: its
invariant is closed under reduction by construction, definitional
equality is never a relation the proof reasons about, and a conversion
check is certified by the two sides denoting the same set. The
algorithm's failures of transitivity are then invisible to the
theorem.

The differences in coverage: the thesis is a paper proof about the
ideal theory of Lean 3; ConLeche is a mechanised proof about a
particular Lean 4 checker, so it additionally handles structure η,
unit-likeness, nested and mutual blocks (checked directly, without
the kernel's translation of nested blocks into mutual ones), the
kernel's special treatment of `Nat` and `String` literals and the GMP-
backed `Nat` operations (as pinned, certified equations rather than
trusted), and it checks the recursors the input supplies rather than
generating them. The thesis's presentation
of universe levels and of the reduction rules remains the standard
ConLeche's checker is measured against.

### lean4lean-model (Carneiro)

The mechanised counterpart of the thesis's model: a set-theoretic
interpretation of lean4lean's abstract typing judgement on Mathlib's
`ZFSet`, under the `OmegaInaccessibles` hypothesis, with a consistency
theorem stated over well-formed environments of that judgement (at the
revision ConLeche's bridge was written against, the proof of that
statement was still a stub). ConLeche's bridge transcribes the
hypothesis verbatim and proves that it yields an instance of the
`SetTheory` interface, so the two projects assume the same thing. The
routes diverge after that: lean4lean-model validates a judgement,
ConLeche validates an algorithm.

### Felicissimo, Leray, Pujet, Tabareau, Tanter and Winterhalter, *Definitional Proof Irrelevance Made Accessible* (LICS 2026)

Two type theories with a definitionally proof-irrelevant universe of
strict propositions and elimination of the accessibility predicate
into types: one where that elimination computes only propositionally,
keeping conversion decidable, and one with Lean's definitional rule,
which is undecidable but conservative over the first. Two things make
it a neighbour of ConLeche. Its consistency proof is a formalised
set-theoretic model, in intuitionistic ZF with a countable hierarchy
of Grothendieck universes embedded in Rocq, with propositions as
subsets of a singleton, so it is the nearest published relative of
ConLeche's model tier; and its device for injectivity inside the
model, interpreting a type as a set tagged with its head former and
the sets it was built from, is the reference construction should
ConLeche ever need semantic no-confusion, which it does not today.
The paper also documents why Lean makes well-foundedness proofs
opaque; ConLeche goes further and treats every theorem as opaque to
reduction, which is what lets its check phase run in parallel. As with
Barras, the paper models a declarative theory; nothing runs.

### Inductive types: accessibility, and the "bounded" in bounded natural functors (Traytel, Popescu and Blanchette, *Foundational, compositional (co)datatypes for higher-order logic*, LICS 2012)

Isabelle/HOL's datatype package builds every (co)datatype from
*bounded natural functors* (BNFs): type constructors equipped with a
map function, set functions collecting the elements of each type
argument, and a cardinal bound on those sets. The bound is what makes
a least fixed point exist inside HOL's types: iterating the functor up
to a regular cardinal above the bound reaches a fixed point. BNFs are
closed under composition and under (co)fixed points, so nesting a new
datatype through `list` uses the fact, proved once, that `list` is a
BNF.

ConLeche needs the same two facts about an inductive block's operator,
monotonicity and a size bound, and gets them differently.

* **What accessibility is, in set terms.** The operator is
  *accessible* when every element of its least fixed point is built
  from a set of recursive arguments whose size is bounded independently
  of the stage: each constructor takes its recursive arguments from a
  domain that already lies in the universe (a field `f : A → T` takes
  `|A|` of them). Then the iteration closes below the universe's
  inaccessible, so the carrier is a set in the universe. This is the
  counterpart of the "B" in BNF: a support bound, supplied here by the
  universe's inaccessibility rather than by a cardinal stored with the
  functor.
* **How it is deduced.** From the checker's positivity check, not
  from a per-type certificate. The positivity check's successful run
  is inverted once into a declarative derivation of strict positivity,
  and monotonicity and accessibility are both proved by induction over
  that derivation: a strictly positive field is either free of the
  block, or a Π over a block-free domain ending in a recursive
  occurrence, and both shapes preserve monotonicity and the support
  bound.
* **Nesting.** Where Isabelle composes the container's BNF structure
  (proved once per container), ConLeche re-checks the container's
  constructors at the concrete instance each time a block nests
  through it, and derives the facts for that instance. No fact of the
  form "the container is positive in its parameter" is ever stored:
  whether a parameter occurs positively can depend on the other
  arguments (a definition in a constructor type may reduce differently
  at different instances), so the check is made where the instance is
  known. The model uses only each container's recorded least-fixed-point
  clause.
* **Which datatypes each covers.** BNFs cover non-dependent
  (co)datatypes of HOL, including nesting through non-free type
  constructors such as finite sets and multisets, and codatatypes; they
  have no indexed families or universe polymorphism. ConLeche covers
  Lean's inductive families: dependent, indexed, universe-polymorphic,
  impredicative in `Prop`, nested through other inductive types; it has
  no codatatypes and no nesting through quotients or other non-inductive
  type constructors.
* **The mechanism on the common fragment.** For a strictly positive
  nested datatype such as a rose tree, the two constructions agree in
  what they build: a least fixed point reached by transfinite iteration
  of a monotone, bounded operator. They differ in where the
  justification comes from: a BNF's map and bound are proved
  semantically and composed; ConLeche's monotonicity and support bound
  are read off a syntactic check made at the instance.
* **Recursors.** Isabelle and the official Lean kernel generate the
  recursor from the datatype. ConLeche checks the recursors the input
  supplies: the recursor's majors seed the positivity check, each rule
  must be primitive recursion over the constructor's fields, and the
  model interprets the recursor through the least fixed point of its
  rules read as closure conditions (its graph), which exists and is a
  function by induction over the block's least fixed point.

## 2. Verified checkers

### Barras and Werner, *Coq in Coq* (1997); Barras's thesis (1999)

The pure Calculus of Constructions formalised in Coq: confluence,
subject reduction, strong normalisation, decidability of conversion
and of typing, and an extracted type checker that is proved sound and
complete for the typing relation. Barras's thesis extends the kernel
to inductive families, with strong normalisation for that extension
taken as an axiom. Consistency of the object calculus follows from the
syntactic metatheory, essentially from normalisation.

The comparison with ConLeche is a comparison of specifications. Coq in
Coq's checker is correct in both directions with respect to a
judgement, and the judgement is shown consistent by normalisation.
ConLeche proves only that acceptance implies a model, with no
completeness, no confluence and no normalisation; rejection and
decline are always permitted. Strong normalisation of full CIC inside
Coq is impossible by Gödel, which is why the thesis's inductive
extension takes it as an axiom; ConLeche pays the same Gödel price up
front as the one explicit `SetTheory` hypothesis, and covers Lean's
whole kernel theory under it. Coq in Coq's decidability results make
the checker a total function on well-scoped input; ConLeche's
reduction is fuelled and memoised, and its decline and error verdicts
exist because termination is never proved. Both run the verified code:
Coq in Coq through extraction to OCaml, ConLeche through Lean's own
compiler with `@[csimp]` twins connecting the executed definitions to
the verified ones.

### MetaCoq, *Coq Coq Correct!* (Sozeau, Boulier, Forster, Tabareau, Winterhalter, POPL 2020)

The modern successor of Coq in Coq: PCUIC, the calculus underlying
Coq's kernel with universes and inductive families, is formalised in
Coq with its metatheory (confluence, subject reduction, principal
types), and a safe checker is proved sound for it (complete in later
work) and extracted. Strong normalisation is an axiom, for the Gödel reason
above. The relation to ConLeche is the same as for Coq in Coq, at the
scale of a real proof assistant: MetaCoq verifies the checker against
the judgement and takes normalisation on faith; ConLeche verifies the
checker against the model and takes the model's existence on faith.
MetaCoq's checker is complete for its calculus; ConLeche's is measured
against the official kernel and is allowed to fall short.

### McTT (Jang, Gaulin, Hu, Pientka, ICFP 2025)

A verified kernel for a Martin-Löf type theory in Rocq: normalisation
by evaluation over an untyped value domain, with normalisation,
consistency and injectivity of type constructors proved from a
logical relation, and the algorithmic side connected to an extracted
OCaml implementation. It is the most complete published
"verified kernel, end to end" for a dependent type theory, and its
untyped value domain is closer to a set model than MetaCoq's syntactic
metatheory is. The difference is the theory: Martin-Löf type theory
normalises and its conversion is decidable, so McTT can prove
completeness and termination outright. Lean's theory does neither
(§3 below), which is why ConLeche neither normalises nor decides, and
why its value domain is a set model rather than a domain of normal
forms.

### lean4lean (Carneiro, 2024)

A complete typechecker for Lean 4 written in Lean, a faithful
reimplementation of the C++ kernel, together with an abstract
formalisation of Lean's type theory and proofs of parts of the
kernel's correctness against it; the effort found and helped fix a
soundness bug in the C++ kernel. It is the Lean analogue of Coq in
Coq: the specification is a typing judgement, and consistency comes
from a model of the judgement (lean4lean-model, above).

ConLeche deliberately occupies a different point, as `README.md`
says: it adds work to the checker (annotations, certificates, extra
checks, a positivity check whose run doubles as the monotonicity
proof) so that the
consistency proof can go straight from the algorithm to the model,
skipping the judgement and the hard metatheory that a faithful
reimplementation must establish about it. lean4lean aims at the
faithful kernel and at understanding the metatheory; ConLeche aims at
one theorem about one checker. ConLeche borrows lean4lean's and the
official kernel's memoisation style (hash maps keyed on expressions
with precomputed hashes); it does not use `Lean.Expr`.

### Abel, Öhman and Vezzosi, *Decidability of conversion for type theory in type theory* (POPL 2018); Adjedj, Lennon-Bertrand, Maillard, Pédrot and Pujet, *Martin-Löf à la Coq* (CPP 2024)

Mechanised logical-relation proofs that conversion in Martin-Löf type
theory is decidable, in Agda and in Coq, without a normalisation
axiom. They are the metatheory a complete verified checker needs and
that MetaCoq assumes. ConLeche needs none of it: with only the
accepting direction claimed, decidability of conversion is replaced by
"the two sides denote the same set", which the checker certifies on
each accepted conversion.

### Carneiro, Coquand, Frabetti Mathieu, Lennon-Bertrand, Melliès and Weirich, *Definitional Inversion, Without Normalisation* (2026)

A domain-theoretic technique for injectivity and no-confusion of type
constructors, and from them subject reduction, that needs neither
normalisation nor confluence and so applies to non-normalising
theories such as Lean's; mechanised in Agda, Lean and Rocq, and
explicitly aimed at lean4lean, where these inversion properties are
the conjectures a checker-to-judgement soundness proof needs. It is
the live attack on exactly the metatheory ConLeche's route avoids:
ConLeche never states injectivity of Π, because it never needs to
invert a conversion, only to certify that both sides of an accepted
one denote the same set. The technique is semantic, like ConLeche's,
but its model is a Scott domain built to keep the constructors it must
invert apart, not a set model built to be consistent, and it is a
model of a judgement rather than of an algorithm. Its authors list
proof irrelevance with K and inductive types as not yet covered.

### Felicissimo, Bocquet, Maillard, Tabareau, Tanter and Winterhalter, *Consolidating Equality in a Proof Irrelevant Universe* (2026)

Decidability of conversion for a Lean-shaped fragment, an
impredicative proof-irrelevant universe hosting equality with
transport into types, solving a problem left open by Abel and Coquand.
The decision procedure is typed throughout: proofs are never reduced,
only typed; neutral forms carry normal forms of the motive instances;
and the guards are stable only under injective renamings. That is a
machine-checked statement of what ConLeche's design assumes: for
Lean's theory, a complete conversion checker cannot be untyped.
ConLeche's conversion is untyped and incomplete, and stays sound
because every accepted conversion is certified by denotation, not by
the algorithm's verdict. The paper's evaluation-by-erasure theorem is
the first formal justification of a `native_decide`-style mechanism;
ConLeche declines streams that use those axioms.

### HOL: *HOL with definitions: semantics, soundness, and a verified implementation* (Kumar, Arthan, Myreen, Owens, ITP 2014 / JAR 2016); Candle (Abrahamsson, Myreen, Kumar, Sewell, ITP 2022)

The closest match in overall shape, in a much smaller logic. The HOL
inference kernel, including definitional mechanisms, is given a
set-theoretic semantics inside HOL4 (a set theory with an infinite
set suffices), the inference rules are proved sound for it, and a
kernel implementation is verified against the rules and compiled by
the verified CakeML compiler, giving a prover whose executable is
proved to derive only true theorems. Candle is the resulting
interactive system.

Similarities: a semantic soundness statement for the real kernel, the
verified code being the code that runs, and an explicit set-theoretic
assumption that is, as in ConLeche, a parameter: their model of HOL is
stated over an abstract type of sets with a membership relation
satisfying Zermelo's axioms, the same shape as the `SetTheory` class. Differences: HOL is simply typed and its semantics needs
almost no set-theoretic strength, whereas Lean's dependent type theory
with an impredicative `Prop` and a universe hierarchy needs
Werner-style universes; the HOL work still passes through an abstract
inference system (implementation refines rules, rules are sound),
where ConLeche has only the implementation and the model; and the HOL
work verifies all the way to machine code, where ConLeche trusts Lean's
compiler and runtime.

### Milawa (Davis 2009; Myreen and Davis 2011, 2014)

A self-verifying theorem prover: a small trusted checker bootstraps a
tower of increasingly capable provers, each verified by the previous
one, and the runtime it runs on was later verified down to machine
code. It is related to ConLeche only in ambition, not in method: the
trust there is established by bootstrapping and by verifying the
implementation chain; ConLeche's trust is a single theorem about a
single checker relative to a set-theoretic model.

## 3. Why Lean's theory resists the syntactic route

The reason ConLeche's specification is semantic is not taste but a
set of published negative results about Lean's kernel theory, which
any checker-to-judgement verification must carry and a model-only
verification can ignore.

* **Carneiro's thesis, chapter 3.** Ideal definitional equality is
  undecidable (accessibility plus proof irrelevance encodes an
  arbitrary Π⁰₁ statement); the kernel's algorithmic equality is a
  decidable, non-transitive underapproximation of it (a second source
  of non-transitivity is quotients of propositions); subject reduction
  fails for the algorithmic typing; and reduction is not Church-Rosser,
  restored only modulo proof irrelevance and at the price of
  termination.
* **Werner, *On the strength of proof-irrelevant type theories*
  (LMCS 2008).** The untyped K rule for equality admits Klop's
  counterexample and breaks confluence on untyped terms, so the K rule
  must be guarded by convertibility of its endpoints, making reduction
  and conversion mutually defined. Lean's K-like reduction is that
  guarded rule.
* **Gilbert, Cockx, Sozeau and Tabareau, *Definitional
  Proof-Irrelevance without K* (POPL 2019).** Proof irrelevance with
  singleton elimination of accessibility makes conversion undecidable;
  Lean's partial implementation of it breaks subject reduction, with a
  runnable example; and the standard logical-relation route to
  decidability does not apply because conversion cannot be defined
  independently of typing.
* **Abel and Coquand, *Failure of normalization in impredicative type
  theory with proof-irrelevant propositional equality* (LMCS 2020).**
  A closed Lean term, using only `propext`, with no weak head normal
  form; equality of open terms cannot be decided by normalisation.

ConLeche's invariant is closed under the reduction steps the checker
takes, and the checker's verdict never has to agree with an ideal
relation, so none of the four is an obstacle. They are, however, the
reason the checker carries fuel, exits with a distinct verdict when it
runs out, and is measured for completeness rather than proved
complete.

## 4. Unverified Lean checkers and the arena

The official kernel (C++, in the Lean repository), `lean4checker`
(replays a Lean environment through the official kernel),
`lean4export` (the export format ConLeche reads), nanoda (an
independent Lean 4 kernel in Rust), and the further checkers collected
in the Lean kernel arena, where ConLeche is one entry, run verified
and unverified alike on the same exported streams. They provide
ConLeche's empirical completeness measure and its performance
baseline; none of them carries a consistency proof. ConLeche's term
representation, locally nameless with open variables as de Bruijn
levels plus type, is nanoda's.

What none of the above does, and ConLeche does, is put a running
checker on the accepting side of a mechanised set-theoretic model
with nothing in between.
