#import "../lib.typ": *

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is a graph of _modules_, each
importing others. This section checks every module on its own, against
an environment built from what its imports provide, with checks that
read the module and its direct imports and nothing else. The result is
one statement about the whole development: a single model, over names
qualified by the module they come from, in which every module's own
environment holds. So no module proves an empty proposition.

The argument uses a few abstract notions: assumptions and the
refinement of one constant by another, qualified names and a module's
resolution of its names to them, and the part of an import's
environment that a module reads as the import does. How Lean's module
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
#src("whitepaper/Fragment/ModularModel.lean", 52, 72)[is the point], at
every list of levels. This is the semantic face of proof irrelevance,
and it is why two proofs of one statement may be taken as one
constant, whatever their bodies.

== Qualified names <sec:mod-names>

Two modules may store the same name with different meanings. In the
proof, every name is therefore _qualified_. An ordinary constant is
named by its home module and its name. A proof is named by its name,
level parameters and statement: two proofs of one statement are one
#src("whitepaper/Fragment/ModularModel.lean", 150, 157)[qualified name].
Each module _resolves_ every name it stores to a qualified name. Its
own constants resolve to its own qualified names. A constant it reads
from an import resolves as the import resolves it. Two constants with
one name that are never read together in one module are two qualified
names, and nothing ever compares them.

The qualified names exist in the proof only. A module's terms keep
their plain names, and the checker never computes a qualified name.

== The local checks <sec:mod-local>

A #src("whitepaper/Fragment/ModularModel.lean", 159, 170)[module] has a
list of imported modules and a list of declarations. Its _context_
is the environment its declarations are checked against. For each
name of the context, the module records the import that name is read
from. It also records which of its own constants are proofs, and its
resolution. Its
#src("whitepaper/Fragment/ModularModel.lean", 172, 173)[_own
environment_] is its context with its declarations stored. The part of
an import's own environment that a module
#src("whitepaper/Fragment/ModularModel.lean", 179, 183)[_reads as the
import does_] consists of the constants that the module's context also
stores and resolves as the import does.

#definition(name: "Local checks")[
  A module #src("whitepaper/Fragment/ModularModel.lean", 200, 228)[passes its
  local checks] when
  #set enum(numbering: "1.")
  + its imports come earlier in the development, and every name of
    its context is read from one of them;
  + its declarations are accepted against its context, and every
    constant it flags as a proof is a theorem or a definition of a
    proposition;
  + every constant of its context refines the constant of the import
    it is read from. That constant
    #src("whitepaper/Fragment/ModularModel.lean", 185, 198)[lies within]
    the part of the import's environment the module reads as the import
    does: its type, its value, its rules and their constructors, and its
    inductive block if it has one;
  + its context resolves each name as the import it is read from does,
    and its own constants to its own qualified names;
  + a type former in its context comes with its constructors.
] <def:local>

Each check reads the module and its direct imports' own environments
and resolutions, and nothing else. Check 3 is pointwise: it compares a
constant of the context with the constant of the same name it is read
from, plus the names that constant's laws read. Hiding a definition's
value or a theorem's proof passes it. So does a context that stores
only some of an import's constants. A definition that typechecks
only because it unfolds a hidden one is never checked again
downstream. It is checked once, in its home module, where the hidden
definition has its value. That module's model is part of the model
the theorem builds.

#theorem(name: "Modular checking")[
  If every module of a development passes its local checks, there is
  #src("whitepaper/Fragment/ModularModel.lean", 525, 537)[one assignment
  of sets to the qualified names], with every proof the point, under
  which every module's own environment has a model. Each module reads
  that assignment through its resolution. Hence every module's own
  environment
  #src("whitepaper/Fragment/ModularModel.lean", 540, 545)[has a model], and
  #src("whitepaper/Fragment/ModularModel.lean", 549, 557)[no closed term
  inhabits an empty proposition] it stores.
] <thm:mod>

#proof[
  By induction along the import order, extending the assignment one
  module at a time. Take a module whose imports all have models of
  their own environments under the assignment so far.

  The module's context then has a model: read the assignment through
  the module's resolution
  (#src("whitepaper/Fragment/ModularModel.lean", 317, 323)[the
  context's model]). Each law of a context constant is the law of the
  import constant it refines. That law mentions only names the module
  reads as the import does, and on those names the two readings give
  the same sets. An assumption that refines a definition owes only the
  typing law, which the definition satisfies.

  The module's declarations are installed on that model by the
  theorems of §3, §4 and @sec:mod-refine
  (#src("whitepaper/Fragment/ModularModel.lean", 91, 97)[installing a
  checked list]). Every stored constant keeps its set, and every proof
  gets the point. The assignment is then extended by the module's own
  ordinary constants
  (#src("whitepaper/Fragment/ModularModel.lean", 479, 489)[one more
  module]). The qualified names of earlier modules are untouched, and a
  proof's qualified name already denotes the point.

  The corollary is @sec:consistency's argument, at the module's model.
]

The induction needs an order in which every module comes after its
imports, and it needs every module to be checked. Nothing else about
the development as a whole enters.

*What runs in parallel.* Check 2, the type checking, reads only the
module's context. So all modules can be type-checked at the same time,
in any order. Checks 1 and 3–5 compare constants and names with the
direct imports' and type-check nothing.

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
    imports re-export], [the module's context, each name read from an
    import (check 1)],
  [a module's exported view], [constants that refine its own
    environment's; the context's constants refine their imports' own
    environments through it (check 3)],
  [the merge of two copies of a name on import, which is allowed
    for one theorem or one exported proposition stated twice], [one
    qualified name: a proof's qualified name is its statement],
  [two modules defining one name that Lean never loads together],
  [two qualified names, never compared],
  [an exported term mentions only what an importer loads],
  [check 3: a context constant lies within what the module reads as
    its import does],
  [names of private declarations], [ordinary names; Lean prefixes
    them with their module's name],
)

The local checks are never stricter than Lean's merge. Copies Lean
merges are proofs of one statement, hence one qualified name.
Constants Lean never loads together are never compared. One check
goes beyond what Lean's merge does: check 3 asks that the names an
imported constant mentions resolve in the importer as they did in the
exporter. Lean's module system guarantees this for the modules it
writes, because an exported term mentions only constants the importer
also loads.

#real[
  Con-leche checks a development as one environment, all its modules
  merged, and the main theorem
  #src("ConLeche/MainTheorem.lean", 96, 99)[is stated] for that
  environment. Checking module by module with the local checks above
  is planned. Its target statement is @thm:mod: one model over
  qualified names, in which every module's own environment holds.
]
