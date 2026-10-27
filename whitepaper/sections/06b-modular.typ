#import "../lib.typ": *

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is a graph of _modules_, each
importing others. This section checks every module on its own, against
an environment built from constants of earlier modules, with checks
that read the module and the modules its environment draws from, and
nothing else. The result is
one statement about the whole development: a single model, over names
qualified by the module they come from, in which every module's own
environment holds. So no module proves an empty proposition.

The argument uses a few abstract notions: assumptions and the
refinement of one constant by another, qualified names and a module's
resolution of its names to them, and the part of an earlier module's
environment that a module reads as that module does. How Lean's module
system maps onto these notions is described at the end.

== Assumptions, theorems and refinement <sec:mod-refine>

An #src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_] is a stored
constant with level parameters and a type and no value. The rule const
of @sec:env gives it its type. It never unfolds, because $delta$ needs
a value. The only law a model owes an assumption is the typing law of
@def:model: its set is a member of its type.

A _theorem_ is checked like a definition, its statement as the type
and its proof as the value, and its statement must be a proposition.
What is stored is the
#src("whitepaper/Fragment/Decl.lean", 608, 618)[statement alone, as an
assumption]. The checker never unfolds a theorem, so nothing is lost.
Installing a theorem keeps the environment's model:
#src("whitepaper/Fragment/InstallThm.lean", 249, 254)[install the
proof as a definition, then forget the value].

One constant
#src("whitepaper/Fragment/Modular.lean", 23, 26)[_refines_] another
when it is the other, or an assumption with the other's level
parameters and type. A definition seen without its value refines the
definition.

*Proofs denote the point.* A constant whose type is a proposition
denotes the point in every model, because its type is a truth value.
So the set the checker gives a theorem, or a definition the checker
finds to be of a proposition,
#src("whitepaper/Fragment/ModularModel.lean", 59, 79)[is the point], at
every list of levels. This is the semantic face of proof irrelevance,
and it is why two proofs of one statement may be taken as one
constant, whatever their bodies. A module may flag as a proof every
theorem and every definition whose type is a proposition, including
definitions whose value its importers never see.

== Qualified names <sec:mod-names>

Two modules may store the same name with different meanings. In the
proof, every name is therefore _qualified_. An ordinary constant is
named by its home module and its name. A proof is named by its name,
level parameters and statement: two proofs of one statement are one
#src("whitepaper/Fragment/ModularModel.lean", 157, 164)[qualified name].
Each module _resolves_ every name it stores to a qualified name. Its
own constants resolve to its own qualified names. A constant it reads
from an earlier module resolves as that module resolves it. Two constants with
one name that are never read together in one module are two qualified
names, and nothing ever compares them.

The qualified names exist in the proof only. A module's terms keep
their plain names, and the checker never computes a qualified name.

== The local checks <sec:mod-local>

A #src("whitepaper/Fragment/ModularModel.lean", 166, 176)[module] has a
list of declarations. Its _context_ is the environment its
declarations are checked against. For each name of the context, the
module records the earlier module that name is read from, its _home_.
It also records which of its own constants are proofs, and its
resolution. Its
#src("whitepaper/Fragment/ModularModel.lean", 178, 179)[_own
environment_] is its context with its declarations stored. The part of
an earlier module's own environment that a module
#src("whitepaper/Fragment/ModularModel.lean", 185, 189)[_reads as that
module does_], for one of the module's environments, consists of the
constants that environment also stores and that the module resolves as
that module does.

#definition(name: "Reading from earlier modules")[
  An environment of a module
  #src("whitepaper/Fragment/ModularModel.lean", 206, 219)[reads from
  earlier modules] when
  #set enum(numbering: "1.")
  + every name it stores is read from an earlier module of the
    development, its home;
  + every constant it stores refines the constant of its home, and
    #src("whitepaper/Fragment/ModularModel.lean", 191, 204)[lies within]
    the part of the home's own environment the module reads as the
    home does: its type, and where it has them, its value, its rules and
    their constructors, and its inductive block. An assumption brings
    its type only, so a value the module does not see is never
    inspected;
  + the module resolves each of its names as the name's home does;
  + a type former in it comes with its constructors.
] <def:reads>

#definition(name: "Local checks")[
  A module #src("whitepaper/Fragment/ModularModel.lean", 221, 234)[passes its
  local checks] when its context reads from earlier modules, its
  declarations are accepted against its context, every constant it
  flags as a proof is a theorem or a definition of a proposition, and
  its own constants resolve to its own qualified names.
] <def:local>

These checks read the module and the own environments and resolutions
of the modules its context draws from, and nothing else. These are
usually its imports. They need not be: a constant may reach a module's
context from a module it does not import directly. The comparison of
@def:reads is pointwise: a constant of the context is compared with
the constant of the same name in its home, plus the names that
constant's laws read. Hiding a definition's value or a theorem's proof
passes it. So does a context that stores only some of a module's
constants. A definition that typechecks only because it unfolds a
hidden one is never checked again downstream. It is checked once, in
its home module, where the hidden definition has its value.

== Comparing a module <sec:mod-compare>

A module can also be validated without checking its declarations, by
_comparison_. A module is
#src("whitepaper/Fragment/ModularModel.lean", 236, 239)[compared] when
its whole own environment, its declarations included, reads from
earlier modules. Every constant it stores is then an earlier module's
constant, or an assumption of that constant's type. Its assumptions
are its _holes_. Each of its names resolves to the qualified name of a
constant of an earlier module, the _solution_. So the compared module
is the solution's environment with constants left out and some
replaced by assumptions.

This is the shape of a _challenge_. A challenge states what is to be
proved, with holes where the proofs go. Its solution is a module that
fills the holes and is checked. The comparison runs over the
challenge's full environment, definitions with their values. A
definition the challenge spells out must be the solution's, value
included, and only the holes are free. A hole may also be a
definition's value. Then the solution chooses that value, and the
challenge says nothing about it. A reader of a challenge therefore
has to look at its list of holes.

A
#src("whitepaper/Fragment/ModularModel.lean", 241, 242)[_validated_]
module is one that passes its local checks or is compared.

== The theorem <sec:mod-thm>

#theorem(name: "Modular checking")[
  If every module of a development is validated, there is
  #src("whitepaper/Fragment/ModularModel.lean", 563, 575)[one assignment
  of sets to the qualified names], with every proof the point, under
  which every module's own environment has a model. Each module reads
  that assignment through its resolution. Hence for every module:
  #set enum(numbering: "1.")
  + its own environment
    #src("whitepaper/Fragment/ModularModel.lean", 578, 583)[has a model];
  + #src("whitepaper/Fragment/ModularModel.lean", 587, 595)[no closed term
    inhabits an empty proposition] it stores;
  + #src("whitepaper/Fragment/ModularModel.lean", 598, 607)[every
    statement it stores holds] in that model. For a compared module
    this covers every hole: a propositional hole is true there.
] <thm:mod>

#proof[
  By induction along the order of the development, extending the
  assignment one module at a time. Take a module such that every
  earlier module's own environment has a model under the assignment so
  far.

  An environment of the module that reads from earlier modules has a
  model: read the assignment through the module's resolution
  (#src("whitepaper/Fragment/ModularModel.lean", 338, 345)[the
  restricted model]). Each law of one of its constants is the law of
  the home's constant it refines. That law mentions only names the
  module reads as the home does, and on those names the two readings
  give the same sets. An assumption that refines a definition owes
  only the typing law, which the definition satisfies.

  A compared module's own environment reads from earlier modules, so
  this is its model, and it adds no qualified name. A checked module's
  context reads from earlier modules. Its declarations are installed
  on the context's model by the theorems of §3, §4 and @sec:mod-refine
  (#src("whitepaper/Fragment/ModularModel.lean", 98, 104)[installing a
  checked list]). Every stored constant keeps its set, and every proof
  gets the point. The assignment is then extended by the module's own
  ordinary constants
  (#src("whitepaper/Fragment/ModularModel.lean", 540, 550)[one more
  module]). The qualified names of earlier modules are untouched, and a
  proof's qualified name already denotes the point.

  Item 2 is @sec:consistency's argument, at the module's model. Item
  3 is the typing law of the model, which puts every constant in its
  statement.
]

A challenge whose hole states an empty proposition cannot be compared
with any validated solution. The theorem would give it a model, and a
model holds no proof of an empty proposition.

The induction needs an order of the development in which every
module comes after the homes of its names, and it needs every module
to be validated. Nothing else about the development as a whole enters.

*What runs in parallel.* Type checking reads only a module's context,
so all modules can be type-checked at the same time, in any order.
The other checks, and comparisons, compare constants and names with
those of the earlier modules the context draws from, and type-check
nothing.

== Lean's module system in these terms <sec:mod-lean>

A module of Lean's module system has a _private_ view (all its
declarations) and an _exported_ view, in which theorems and the
definitions the module does not expose keep their types only.

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [the environment Lean builds to elaborate a module: each import's
    exported view, its private view under `import all`, and the modules
    imports re-export], [the module's context; each name's home is the
    module that declares it, earlier in the import order, and need not
    be a direct import (check 1)],
  [a module's exported view], [constants that refine its own
    environment's; the context's constants refine their homes' own
    environments through it (check 3)],
  [the merge of two copies of a name on import, which is allowed
    for one theorem or one exported proposition stated twice], [one
    qualified name: a proof's qualified name is its statement],
  [two modules defining one name that Lean never loads together],
  [two qualified names, never compared],
  [an exported term mentions only what an importer loads],
  [check 3: a context constant lies within what the module reads as
    its home does],
  [names of private declarations], [ordinary names; Lean prefixes
    them with their module's name],
  [Comparator's challenge and solution], [a compared module and the
    module it reads from],
  [a hole of the challenge: an axiom, or a constant whose value is
    `sorryAx …`], [an assumption of the compared module],
  [the challenge's private view, with its definitions' values], [the
    compared module's own environment, which the comparison reads in
    full],
  [Comparator's lists of theorems and definitions to compare, and the
    `landrun` sandbox it builds them in], [nothing: the comparison runs
    over the whole environment, read from the built files],
)

The checks are designed not to reject what Lean accepts. That is an
aim, checked by running them on real developments, not a theorem.
Copies Lean merges are proofs of one statement, hence one qualified
name. Constants Lean never loads together are never compared. Check 3
goes further than Lean's merge does: it asks that the names a constant
of the context mentions resolve in the module as they do in the
constant's home. This covers its type and whatever value or rules the
module sees. What the module does not see, such as the value of a
definition it reads as an assumption, is not inspected.

#real[
  Con-leche checks a development as one environment, all its modules
  merged, and the main theorem
  #src("ConLeche/MainTheorem.lean", 96, 99)[is stated] for that
  environment. Checking module by module with the local checks above
  is planned. Its target statement is @thm:mod: one model over
  qualified names, in which every module's own environment holds.
]
