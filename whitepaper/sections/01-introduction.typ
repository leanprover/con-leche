#import "../lib.typ": *

= Introduction

== What is proved

con-leche is a checker for Lean 4. It reads an export of a Lean
environment, the _stream_: every definition, theorem and inductive
type, in the official kernel's own terms. It accepts or rejects the
stream, checking what the official kernel checks (on a few features
it declines instead; @sec:left-out). It comes with a proof, written in
Lean itself, of what an acceptance means: every environment the
checker accepts
#src("ConLeche/MainTheorem.lean", 96, 99)[has a model in set theory].
#src("ConLeche/Denotes.lean", 248, 268)[Each constant is assigned a set], each type denotes a set, and every stored
constant is a member of the set its type denotes. The constant `False`
denotes the empty set, and `Eq` denotes set equality, so every
equation the checker accepts is an equality of sets. Hence no accepted
environment holds a proof of `False`, and every accepted theorem is
true in the model.

== The shape of the argument

The theorem is relative to a model of an abstract set theory, a
structure with membership, extensionality, the usual set-forming
operations and
#src("ConLeche/SetTheory/Core.lean", 95, 100)[a chain of universes closed under them].
By Gödel's second incompleteness theorem, Lean cannot prove that such
a structure exists. The assumption is standard, though: it follows
from the existence of ω many inaccessible cardinals, the hypothesis of
the Lean development of Carneiro's model of Lean (@sec:related;
#overview(7) says more).

The usual way to prove such a statement, given a typing judgement for
the type theory, has two steps: show that the checker accepts only
derivable judgements, and show that derivable judgements are true in
the model. The first step needs the metatheory of the type theory:
that reduction preserves types (subject reduction), that reduction is
confluent, that a function type determines its domain and codomain
(injectivity of Π), and that a term has one type up to definitional
equality. Our proof needs none of it.

Nor does it have a typing judgement. In its place is a description of
what the checker _does_: three inductively defined relations, one for
#src("ConLeche/Rules/Rel.lean", 101)[reduction], one for the verdicts
of the #src("ConLeche/Rules/Rel.lean", 358)[definitional-equality test]
and one for #src("ConLeche/Rules/Rel.lean", 550)[type inference] (six
in the real proof, where premises about lists get relations of their
own; @sec:left-out). Their rules are exactly the moves the checker
makes, and each rule's premises are what the checker verified at that
point. On the model side there is a total, term-directed
#src("whitepaper/Fragment/Interp.lean", 139, 146)[interpretation]:
every term denotes a set, well-typed or not, and the interpretation
uses nothing beyond what is in the term itself. In particular it uses
no typing information, nothing that would have to be inferred. Where
a typing judgement would say "this term has that type", there is a
#src("whitepaper/Fragment/WellDenoted.lean", 58, 78)[semantic invariant]
on the term's set, imposed at every subterm: every application applies
a function to a member of its domain, every binder's domain is a type,
and so on.
#src("whitepaper/Fragment/Sound.lean", 2322, 2326)[One induction over the three relations]
then proves three claims at once. A reduction step preserves the
denotation and the semantic invariant; a verdict "definitionally
equal" means that the two sides denote the same set; and an inferred
type contains the term, that is, the term's set is a member of the
type's set.

== How to interpret a `∀` or a lambda

At every binder the interpretation has to decide how to interpret a
`∀` or a lambda. In Lean, `∀ x : A, B` is a type of functions when `B`
is a type and a proposition when `B` is a proposition, and in the
model these are different kinds of sets. A function type is a set of
graphs. A proposition is a _truth value_, a set with at most one
element: the model has one distinguished set, _the point_, which every
proof of every proposition denotes, so proof irrelevance is built in.
The two cases look the same on the page, and telling them apart by
the sort of `B` would take type inference. Our interpretation instead
#src("whitepaper/Fragment/Lib.lean", 477, 481)[reads the answer off the values]:
a `∀` denotes a truth value exactly when every one of its fibres (the
set `B` denotes at a member of the domain) is a truth value, and a
lambda denotes the point exactly when every value of its body is the point.
The terms are Lean's own.

Over a non-empty domain this reading agrees with the sort of the body.
Over an empty domain it does not: `fun h => h.elim`, of type
`False → Nat`, denotes the point although its type has sort `Type`
(@sec:interp). This shapes the soundness claims: a reduction or an
equality claims nothing about a term that denotes the point
(@sec:claims). It also costs two checks that the official kernel
never makes (@sec:tax): the checker compares the types of two bodies
at lambda congruence and η, and, in one rare case of ι-reduction, it
compares a constructor application with the recursor's arguments and
type-checks its fields.

== This document

This document is a pen-and-paper account of that argument on a
simplified fragment of the checker. The fragment has no projections,
no number or string literals, no mutual inductive types, nesting only
one container deep and not under a binder (@sec:nested describes the
full check, without proof), no quotients, no axioms, no built-in
copies of `False`, `Eq`, `Nat` and their kin (the real checker pins
these rather than reading them from the stream), no opaques, and
none of the checker's
performance devices (memo tables, fuel, the parallel check phase).
@sec:left-out lists every omission with one sentence on what the real
proof does about it. The fragment is verified in Lean in a small
development of its own, `whitepaper/Fragment/`, which imports nothing
from the main proof and is parametric in the same kind of abstract set
theory. The underlined source links lead into the real proof and into
that development.

The rest is in eight parts. §2 presents the fragment without an
environment: terms and universe levels, the three relations, the
abstract set theory, the interpretation, the semantic invariant, and
the three claims with their proof. The routine cases of the proof are
listed briefly; the cases where the reading of a binder matters, or
where a syntactic proof would fail, are discussed in full. §2 ends
with the checks that other checkers skip and with a cheaper mode of
inference. The claims (@sec:claims) are a good place to start reading.
§3 adds the environment, the constants that refer to it, and its
definitions: what is stored, what is checked, how a definition
unfolds, and the model that grows with it. §4 adds inductive types as
least fixed points in the model, their recursors and reduction rules,
large elimination, and the consistency corollary: no accepted
environment stores a constant whose type is an inductive proposition
with no constructors. §5 changes tack. It describes in full
con-leche's check for nested inductive types, whose constructors
mention the type being defined inside another one, as in
`List (Tree α)`, and their generated recursors, and only sketches how
the model extends to them. §6 shows that two features of Lean's
definitional equality that the fragment drops, η for structures and
unit-likeness, follow from the extensionality of the model, with one
proof case each. §7 checks a development module by module, with
checks that compare each module only with its direct imports, and
builds one model, over names qualified by their home module, in which
every module's environment holds. §8 lists what
was left out, and how the real proof
differs from the fragment where they share a feature. @sec:related
relates the argument to earlier work.
