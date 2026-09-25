#import "../lib.typ": *

= Introduction

ConLeche is a checker for Lean 4. It reads an export of a Lean
environment — every definition, theorem and inductive type, in the
kernel's own terms — and accepts or rejects it, as Lean's kernel would.
Unlike the kernel, it comes with a proof, written in Lean itself, of what
an acceptance means: every environment the checker accepts has a model in
set theory
#src("ConLeche/MainTheorem.lean", 96, 99)[(the main theorem)].
Each constant is assigned a set, each type denotes a set, and every stored
constant is a member of the set its type denotes; the constant `False`
denotes the empty set
#src("ConLeche/Denotes.lean", 270, 290)[(what a model is)].
So no accepted environment holds a proof of `False`, and every accepted
theorem is true in the model. The theorem is relative to a model of an
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
`OVERVIEW.md`, §7, says more).

The usual way to prove such a statement is in two steps: define a
typing judgement for the type theory, show that the checker accepts only
derivable judgements, and show that derivable judgements are true in the
model. The middle step needs the metatheory of the type theory — that
reduction preserves types (subject reduction), that reduction is
confluent, that a function type determines its domain and codomain
(injectivity of Π). For Lean's type theory, with its proof irrelevance
and its impredicative propositions, these are hard theorems, and some
are open.

ConLeche's proof has no typing judgement and none of that metatheory.
In its place is a description of what the checker _does_: three
inductively defined relations — one for reduction
#src("ConLeche/Rules/Rel.lean", 96), one for the verdicts of the
definitional-equality test
#src("ConLeche/Rules/Rel.lean", 334), one for type inference
#src("ConLeche/Rules/Rel.lean", 486) — whose rules are exactly the
moves the checker makes, each rule's premises being what the checker
verified at that point. On the model side there is a total,
term-directed interpretation: every term denotes a set, well-typed or
not, and the interpretation reads the term's syntax and nothing else —
never a type
#src("ConLeche/Semantics/Interp.lean", 150, 160).
Where a typing judgement would say "this term has that type", there is a
semantic invariant on the term's set: hereditarily, every application
applies a function to a member of its domain, every function's values
lie in a bounded set, and so on
#src("ConLeche/Semantics/WellDenoted.lean", 81, 84).
One induction over the three relations then proves three claims at once
#src("ConLeche/Model/Rules/Sound.lean", 43, 44):
a reduction step preserves the denotation (and the invariant); a
verdict "definitionally equal" means the two sides denote the same set;
and an inferred type contains the term — the term's set is a member of
the type's set.

Equality flows in one direction only: from "the checker said equal" to
"the sets are equal", never back. Nothing about the checker's verdicts
is ever concluded from an equality of sets; what is derivable is decided
by the rules, and the model only has to agree with every rule. This is
also why the familiar obstacles do not arise. Π-injectivity, for
instance, is what an inversion of the typing of `f` in `f a` would need;
here the checker itself reduces the type of `f` to a syntactic `∀`, whose
denotation _is_ a function space, and membership in that space is all
the application rule asks for. (It is also why the equality relation has
no transitivity rule, and cannot have one; §2 explains.)

One thing the interpretation cannot do by syntax alone is read a binder.
In Lean, `∀ x : A, B` is a type of functions when `B` is a type and a
proposition when `B` is a proposition, and in the model these are
different kinds of sets: a function type is a set of graphs, a
proposition is a truth value — a set with at most one element, so that
proof irrelevance is built in. The two cases look the same on the page,
and telling them apart takes the sort of `B`, that is, type inference.
The checker resolves this by storing the answer. On every `∀` and every
`λ` it records whether the body is a proposition — and, because
declarations are polymorphic in their universe levels, _when_ it is:
#ann[never], or #ann[exactly when these level parameters are all zero]
#src("ConLeche/Kernel/PropWhen.lean", 413, 415).
The interpretation reads this datum and nothing else. Throughout this
document the datum is typeset in this one colour, #ann[like this], in
grammars, rules and terms alike; it is the only thing the checker adds
to Lean's kernel terms, and a reader who ignores the colour sees Lean's
kernel as it is. The checker computes the annotation by ordinary type
inference when a declaration enters, and it re-checks every annotation
against its own inference as it type-checks; what it takes from the
annotation is a licence, not a typing it does not redo.

This document is a pen-and-paper account of that argument on a
simplified fragment of the checker. The fragment has no projections, no
number or string literals, no mutual or nested inductive types, no
quotients, no axioms, no built-in pinned declarations, no `let`, one
inference grade instead of two, and none of the checker's performance
devices (memo tables, fuel, the parallel check phase); §5 lists every
omission with one sentence on what the real proof does about it. The
fragment is verified in Lean in a small development of its own,
`whitepaper/Fragment/`, which imports nothing from the main proof and is
parametric in the same kind of abstract set theory, given as a class;
every theorem there is proved against the class, so nothing beyond the
stated laws is used. The small grey arrows #src("ConLeche/Denotes.lean", 132, 135)
link into the real proof on the repository's `master` branch, at the
definition or theorem the text is describing. They are for the reader
who wants to see the real thing; everyone else can ignore them.

The rest is in four parts. §2 presents the fragment without an
environment: terms and their annotations, universe levels, the three
relations, the abstract set theory, the interpretation, the invariant,
the three claims and their proof — "by induction" where nothing happens,
and in full where the annotation carries the argument or a syntactic
proof would fail. §3 adds the environment: definitions, then inductive
types as least fixed points in the model, their recursors and reduction
rules, large elimination, and the consistency corollary: no accepted
environment stores a constant whose type is an inductive proposition
with no constructors. §4 shows that three features of Lean's
definitional equality which the fragment drops — reduction of proofs at
`Eq`-like types, η for structures, and unit-likeness — follow from the
extensionality of the model with no further work. §5 lists what was left
out, and how the real proof differs from the fragment where they share
a feature.
