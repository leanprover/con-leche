#import "../lib.typ": *

= Introduction

== What is proved

con-leche is a checker for Lean 4. It reads an export of a Lean
environment, the _stream_: every definition, theorem and inductive
type, in the official kernel's own terms. It accepts or rejects the
stream, checking what the official kernel checks (on a few features
it declines instead; @sec:left-out). It comes with a proof, written in
Lean itself, of what an acceptance means: every stream the
checker accepts
#src("ConLeche/MainTheorem.lean", 96, 102)[has a model in set theory].
#src("ConLeche/IsModel.lean", 212, 213)[Each constant is assigned a set], each type denotes a set, and every
constant of the stream holds in the model on its own: it is a member
of the set its type denotes, a definition denotes what its value
denotes, and a recursor computes by its rules, read off its own type.
A hole
(an axiom, or a declaration whose value uses `sorry`) is read as an
assumption of its statement. Nothing is fixed by name: the prelude's
`False` denotes the empty set, and its `Eq` denotes equality, by
their declarations' own clauses, so every equation the checker
accepts is an equality of sets. Hence a model of an accepted stream has
no constant of type `False`, since `False` denotes the empty set, and
every accepted theorem is true in the model.

Checked module by module from Lean's `.olean` files, every module of an import closure
#src("ConLeche/MainTheorem.lean", 187, 198)[has a model of its own constants],
and a name a module sees as another module's means there what that
module's model says. A challenge, a module with holes, checked
with a solution that fills them, has a model of its own constants
too, and that statement does not mention the solution.

== The shape of the argument

The theorem is relative to a model of an abstract set theory, a
structure with membership, extensionality, the usual set-forming
operations and
#src("ConLeche/SetTheory/Core.lean", 95, 100)[a chain of universes closed under them].
Such a structure gives a model of Lean, so by Gödel's second
incompleteness theorem Lean cannot prove that one exists, unless Lean
is inconsistent. The assumption is standard, though: it follows
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
#src("ConLeche/Rules/Rel.lean", 106)[reduction], one for the verdicts
of the #src("ConLeche/Rules/Rel.lean", 348)[definitional-equality test]
and one for #src("ConLeche/Rules/Rel.lean", 589)[type inference] (six
in the real proof, where premises about lists get relations of their
own; @sec:left-out). Their rules are exactly the moves the checker
makes, and each rule's premises are what the checker verified at that
point. On the model side there is a total, term-directed
#src("whitepaper/Fragment/Interp.lean", 139, 146)[interpretation]:
every term denotes a set, well-typed or not, and the interpretation
uses nothing beyond what is in the term itself. In particular it uses
no typing information, nothing that would have to be inferred. Where
a typing judgement would say "this term has that type", there is a
#src("whitepaper/Fragment/WellDenoted.lean", 61, 75)[semantic invariant]
on the term's set, imposed at every subterm: every application applies
a function to a member of its domain, every binder's domain is a type,
and so on.
#src("whitepaper/Fragment/Sound.lean", 2293, 2297)[One induction over the three relations]
then proves three claims at once. A reduction step preserves the
denotation and the semantic invariant; a verdict "definitionally
equal" means that the two sides denote the same set; and an inferred
type contains the term, that is, the term's set is a member of the
type's set.

== How to interpret a `∀` or a lambda

At every binder the interpretation has to decide how to interpret a
`∀` or a lambda. In Lean, a Π-type `∀ x : A, B`, with `x` a variable
and `A`, `B` terms, is a type of functions when `B` is a type and a
proposition when `B` is a proposition, and in the model these are
different kinds of sets. A function space is a set of graphs. A proposition is a _truth value_, a set with at most one
element: the model has one distinguished set, _the point_, which every
proof of every proposition denotes, so proof irrelevance is built in.
The two cases look the same on the page, and telling them apart by
the sort of `B` would take type inference. Our interpretation instead
#src("whitepaper/Fragment/Lib.lean", 523, 527)[reads the answer off the values]:
a `∀` denotes a truth value exactly when every one of its fibres (the
set `B` denotes at a member of the domain) is a truth value, and a
lambda denotes the point exactly when every value of its body is the point.
The terms carry no annotation for the choice; they are Lean's own.

Over a non-empty domain this reading agrees with the sort of the body.
Over an empty domain it does not: `fun h => h.elim`, of type
`False → Nat`, denotes the point although its type has sort `Type`
(@sec:interp). This shapes the soundness claims: a reduction or an
equality claims nothing about a term that denotes the point
(@sec:claims). The same mismatch is why the checker makes two checks
that the official kernel never makes (@sec:tax): it compares the types of two bodies
at lambda congruence and η, and, in one rare case of ι-reduction, it
compares a constructor application with the recursor's arguments and
type-checks its fields.

== This document

This document is a pen-and-paper account of that argument on a
simplified fragment of the checker. The fragment keeps the terms, the
three relations, definitions and inductive types with their recursors.
It drops projections, number and string literals, mutual inductive
types, quotients, opaques and axioms (a hole is accepted only with a
solution that fills it, @sec:compare), nests inductive types only one
container deep and not under a binder (@sec:nested describes the full check, without proof),
reads `False`, `Eq` and `Nat` from the input alone (the real checker
also compares them with pinned copies), and has none of the checker's
performance devices (memo tables, fuel, the parallel check phase).
@sec:left-out lists every omission, with a short account of what the
real proof does about it. The fragment is verified in Lean in a small
development of its own, `whitepaper/Fragment/`, which imports nothing
from the main proof and is parametric in the same kind of abstract set
theory. The underlined source links lead into the real proof and into
that development.

@sec:fragment presents the fragment without an environment: terms and
universe levels, the three relations, the set theory, the
interpretation, the semantic invariant, and the three claims with
their proof. Routine proof cases are listed briefly; the cases where
the interpretation of a binder matters, or where a syntactic proof
would fail, are discussed in full. It ends with the checks the
official kernel skips and with a cheaper mode of inference. The claims
(@sec:claims) are a good place to start reading. @sec:env adds the
environment and its definitions, and the model that grows with them.
@sec:ind adds inductive types as least fixed points in the model,
their recursors and ι-reduction, and proves the main theorem: every
accepted input has a model of its constants, so none of them has an
inductive proposition without constructors as its type. @sec:nested
changes tack: it describes con-leche's full check for nested inductive
types, such as `Tree α` with its field of type `List (Tree α)`, and
only sketches how the model extends. @sec:ext derives η for
structures and unit-likeness, which the fragment drops, from the
extensionality of the model. @sec:modular checks a development module
by module, each module against the imported views of its imports, and
gives every module a model of its own constants that agrees with its
imports' models on the names they share. @sec:compare checks an input
with holes against a solution that fills them, and shows that the
input's constants have a model of their own, also module by module.
@sec:left-out lists what
was left out and how the real proof differs from the fragment, and
@sec:related relates the argument to earlier work.
