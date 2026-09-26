#import "../lib.typ": *

= Introduction

ConLeche is a checker for Lean 4. It reads an export of a Lean
environment — the _stream_: every definition, theorem and inductive
type, in the kernel's own terms — and accepts or rejects it, checking
what Lean's kernel checks (on a few features it declines instead; §5).
Unlike the kernel, it comes with a proof, written in Lean itself, of what
an acceptance means: every environment the checker accepts has a model in
set theory
#src("ConLeche/MainTheorem.lean", 96, 99)[(the main theorem)].
Each constant is assigned a set, each type denotes a set, and every stored
constant is a member of the set its type denotes; the constant `False`
denotes the empty set, and `Eq` denotes set equality, so every equation
the checker accepts is an equality of sets
#src("ConLeche/Denotes.lean", 270, 290)[(what a model is)].
So no accepted environment holds a proof of `False`, and every accepted
theorem is true in the model.

The theorem is relative to a model of an
abstract set theory — a structure with membership, extensionality, the
usual set-forming operations and a chain of universes closed under them
#src("ConLeche/SetTheory/Core.lean", 95, 100)[(the interface)]
— and the assumption that such a structure exists is no stronger than
the one already accepted for the consistency of Lean itself: it is
instantiated from the hypothesis of Carneiro's consistency analysis of
Lean
#src("bridge/lean4lean-model/ConLecheBridge/Carneiro.lean", 200, 202)[(the bridge)].
That one hypothesis is where Gödel's theorem is respected: Lean proves
the theorem, but not the existence of the model (the repository's
#overview(7) says more).

The usual way to prove such a statement, given a typing judgement for
the type theory, is in two steps: show that the checker accepts only
derivable judgements, and show that derivable judgements are true in the
model. The first step needs the metatheory of the type theory — that
reduction preserves types (subject reduction), that reduction is
confluent, that a function type determines its domain and codomain
(injectivity of Π). This proof needs none of it.

ConLeche's proof has no typing judgement and none of that metatheory.
In its place is a description of what the checker _does_: three
inductively defined relations (six in the real proof, where premises
about lists get relations of their own; §5) — one for #src("ConLeche/Rules/Rel.lean", 96)[reduction], one for the verdicts of the
#src("ConLeche/Rules/Rel.lean", 334)[definitional-equality test], one for
#src("ConLeche/Rules/Rel.lean", 486)[type inference] — whose rules are exactly the
moves the checker makes, each rule's premises being what the checker
verified at that point. On the model side there is a total,
term-directed #src("ConLeche/Semantics/Interp.lean", 150, 160)[interpretation]: every term denotes a set, well-typed or
not, and the interpretation needs no information beyond what is in the
term itself — in particular no typing information, nothing that would
have to be inferred.
Where a typing judgement would say "this term has that type", there is a
#src("ConLeche/Semantics/WellDenoted.lean", 81, 95)[semantic invariant] on the term's set: hereditarily, every application
applies a function to a member of its domain, every function's values
lie in a bounded set, and so on.
#src("ConLeche/Model/Rules/Sound.lean", 43, 44)[One induction over the three relations] then proves three claims at once:
a reduction step preserves the denotation and the semantic invariant; a
verdict "definitionally equal" means the two sides denote the same set;
and an inferred type contains the term — the term's set is a member of
the type's set.

One thing the interpretation cannot decide from the syntax alone is
how to interpret a `∀` or a `λ`.
In Lean, `∀ x : A, B` is a type of functions when `B` is a type and a
proposition when `B` is a proposition, and in the model these are
different kinds of sets: a function type is a set of graphs, a
proposition is a truth value — a set with at most one element, so that
proof irrelevance is built in. The two cases look the same on the page,
and telling them apart takes the sort of `B`, that is, type inference.
The checker resolves this by #src("ConLeche/Kernel/PropWhen.lean", 413, 415)[storing the answer]. On every `∀` and every
`λ` it records whether the body is a proposition — and, because
declarations are polymorphic in their universe levels, _when_ it is:
#ann[never], or #ann[exactly when these level parameters are all zero].
To choose between the two interpretations of a `∀` or a `λ`, the
interpretation consults this datum and nothing else. Throughout this
document the datum is typeset in this one colour, #ann[like this], in
grammars, rules and terms alike; it is the only thing the checker adds
to Lean's kernel terms, and a reader who ignores the colour sees Lean's
kernel as it is. The annotation is computed when a declaration enters,
by an untrusted pass that infers the sort of every body. Nothing
downstream trusts it: when the checker later infers the type of a `∀`
or a `λ`, it computes the sort of the body again and compares it with
the stored datum, and a mismatch is a rejection. The checker does read
the datum in a few places to save work — a β-step at a #ann[never]
binder, for instance, needs no certificate — and each such use is one
case of the soundness proof.

This document is a pen-and-paper account of that argument on a
simplified fragment of the checker. The fragment has no projections, no
number or string literals, no mutual or nested inductive types, no
quotients, no axioms, no built-in copies of `False`, `Eq`, `Nat` and
their kin (the real checker pins these rather than reading them from
the stream), no `let`, no distinction between a theorem and a
definition, one mode of type inference instead of the full one plus a
cheaper "infer-only" one, and none of the checker's performance devices
(memo tables, fuel, the parallel check phase); §5 lists every
omission with one sentence on what the real proof does about it. The
fragment is verified in Lean in a small development of its own,
`whitepaper/Fragment/`, which imports nothing from the main proof and is
parametric in the same kind of abstract set theory, given as a class;
every theorem there is proved against the class, so nothing beyond the
stated laws is used. The underlined source links are for the reader
who wants to see the real thing; everyone else can ignore them.

The rest is in four parts. §2 presents the fragment without an
environment: terms and their annotations, universe levels, the three
relations, the abstract set theory, the interpretation, the semantic invariant,
the three claims and their proof — "by induction" where nothing happens,
and in full where the annotation carries the argument or a syntactic
proof would fail. §3 adds the environment: definitions, then inductive
types as least fixed points in the model, their recursors and reduction
rules, large elimination, and the consistency corollary: no accepted
environment stores a constant whose type is an inductive proposition
with no constructors. §4 shows that three features of Lean's
definitional equality which the fragment drops — reduction of proofs at
`Eq`-like types, η for structures, and unit-likeness — follow from the
extensionality of the model, at the cost of one proof case each. §5 lists what was left
out, and how the real proof differs from the fragment where they share
a feature.
