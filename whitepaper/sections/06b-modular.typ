#import "../lib.typ": *

// Notation local to this file.
#let ile = sym.prec.eq

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is a graph of _modules_, each
importing others. This section checks every module on its own: a
module's declarations are checked against an environment built from
what its imports provide, and each module compares its own data only
with that of its direct imports. No table of all the names of the
development is ever formed. The result is per module: the environment a
module's declarations were checked in is part of an environment the
checker accepts declaration by declaration, so §4's consistency
corollary applies to it.

The argument uses three abstract notions: one environment _refining_
another (leaving constants out, or keeping only their types), lists of
declarations being _compatible_ (agreeing where they overlap), and
their _join_. How Lean's module system maps onto these notions is
described separately, at the end.

== Assumptions, theorems and refinement <sec:mod-refine>

An #src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_] is a stored
constant with level parameters and a type and no value. The rule const
of @sec:env gives it its type. It never unfolds, because $delta$ needs
a value.

A _theorem_ is checked like a definition, its statement as the type
and its proof as the value, and its statement must be a proposition.
What is stored is the
#src("whitepaper/Fragment/Decl.lean", 607, 618)[statement alone, as an
assumption]. The checker never unfolds a theorem, so nothing is lost,
and two proofs of one statement store the same constant. Installing a
theorem keeps the environment's model:
#src("whitepaper/Fragment/InstallThm.lean", 248, 252)[install the
proof as a definition], then
#src("whitepaper/Fragment/InstallThm.lean", 180, 181)[forget the
value]. The model is unchanged, because the only law about an
assumption is the typing law of @def:model, and the definition
satisfies it.

#definition(name: "Refinement")[
  An environment $E_1$ #src("whitepaper/Fragment/Modular.lean", 52, 57)[_refines_]
  $E_2$, written $E_1 ile E_2$, when every constant $c$ stored in $E_1$
  is stored in $E_2$ with the same level parameters and type, and with
  the same kind unless $c$ is an assumption in $E_1$.
] <def:refine>

In words, $E_1$ is $E_2$ with some constants left out and some
replaced by assumptions of the same type. Refinement is pointwise: it
compares each constant with the constant of the same name and nothing
else. Hiding a definition's value gives a refinement
(#src("whitepaper/Fragment/Modular.lean", 107, 113)[the hidden view]),
and so does leaving constants out. Refinement is
#src("whitepaper/Fragment/Modular.lean", 86, 91)[transitive].

== Checking is monotone <sec:mod-mono>

A list of declarations is
#src("whitepaper/Fragment/Modular.lean", 494, 498)[checked against an
environment] $E$ as §3 and §4 check a development: each declaration
passes its checks against $E$ and the declarations before it, and is
then stored.

#theorem(name: "Monotonicity")[
  Let $E_1 ile E_2$.
  #set enum(numbering: "1.")
  + Every reduction, definitional equality and inference derivable in
    $E_1$ is
    #src("whitepaper/Fragment/Modular.lean", 176, 296)[derivable in $E_2$].
  + A declaration that passes its checks against $E_1$, and whose names
    are not stored in $E_2$,
    #src("whitepaper/Fragment/Modular.lean", 483, 492)[passes them against $E_2$].
  + A list of declarations checked against $E_1$, whose names are not
    stored in $E_2$, is
    #src("whitepaper/Fragment/Modular.lean", 519, 536)[checked against $E_2$].
] <thm:mod-mono>

#proof[
  *Part 1*, by one induction over the rules of §2–§4. A rule reads
  the environment only by looking up a constant. It reads its type
  and level parameters (rule const, the constructor and the family in
  a rule $iota$), its value (rule $delta$), or its kind (a recursor,
  a constructor of a nested rule, a type former). $E_2$ stores every
  constant of $E_1$ with the same type and level parameters. A constant
  whose value or kind the rule reads is not an assumption in $E_1$,
  so $E_2$ stores it with the same kind and value. Every premise of
  the rule is therefore a premise of the same rule in $E_2$, and the
  induction hypotheses give the derivations among them.

  *Part 2.* The checks of §3, §4 and the theorem check consist of
  three things. Derivations are covered by part 1. Conditions on the
  declaration and the constants it mentions (scope, level parameters,
  positivity, the universe conditions on fields) hold in $E_2$ because
  $E_2$ stores every constant $E_1$ stores. For a nested block there is
  a lookup of the container's type former, which is not an assumption
  and so is stored in $E_2$ as it is
  (#src("whitepaper/Fragment/Modular.lean", 446, 449)[the block check]).
  One check reads an absence: the declaration's names must be fresh.
  That is why freshness in $E_2$ is a hypothesis.

  *Part 3*, along the list. A declaration stores the
  #src("whitepaper/Fragment/Modular.lean", 408, 414)[same entries] in
  front of either environment, so storing it keeps $E_1 ile E_2$; a
  later declaration's names, fresh where it was checked against
  $E_1$, are not among the entries just stored.
]

Three remarks answer what a pointwise relation might seem to miss.
First, part 1 assumes nothing of $E_1$, not even that its constants
are well typed: a derivation against $E_1$ is a derivation against
$E_2$, whatever $E_1$ holds. Second, a definition whose value
typechecks only because it unfolds another definition is checked
once, in the environment where that other definition has its value.
An environment that later refines that one, with the other definition
reduced to an assumption, never checks it again. Third, a theorem is
an assumption everywhere, so hiding it changes nothing.

The checks that could pass _because_ something is missing are the
ones that read an absence or a failure. In the fragment that is
freshness, which part 2 takes as a hypothesis. The inductive checks
(positivity and the universe conditions on fields) are syntactic in
the fragment, and their monotonicity is what part 2 proves. An
implementation that reads them through weak-head normalisation must
keep them monotone in the same sense. A term that is stuck because a
value is hidden may not pass a check that its unfolding would fail.

== The local checks <sec:mod-local>

Two lists of declarations are
#src("whitepaper/Fragment/Modular.lean", 752, 756)[_compatible_] when,
wherever a declaration of the one and a declaration of the other store
a common name, the two store the same entries. Their
#src("whitepaper/Fragment/Modular.lean", 758, 760)[_join_] is the first
list followed by the declarations of the second that store no name
the first stores. Compatibility is what makes the join lose nothing:
every declaration it drops is matched by one with the same entries.

#definition(name: "Development")[
  A #src("whitepaper/Fragment/Modular.lean", 861, 869)[module] has a
  list of imported modules, a list of declarations, a _base_ (the
  environment its declarations are checked against) and a _summary_ (a
  list of declarations: everything it rests on). Its
  #src("whitepaper/Fragment/Modular.lean", 871, 873)[_own environment_]
  is its base with its declarations stored. A _development_ is a
  collection of modules whose imports form a graph without cycles.
] <def:dev>

#definition(name: "Local checks")[
  A module #src("whitepaper/Fragment/Modular.lean", 884, 900)[passes its
  local checks] when
  #set enum(numbering: "1.")
  + its declarations are checked against its base;
  + every constant of its base refines a constant of some import's own
    environment;
  + its declarations and its imports' summaries are pairwise
    compatible;
  + its summary is their join: the imports' summaries joined in order,
    then its declarations.
] <def:local>

Each check reads the module and its direct imports' own environments
and summaries, and nothing else. A summary is computed from the
summaries of the direct imports, so the summaries are passed along the
import edges.

#theorem(name: "Modular checking")[
  If every module of a development passes its local checks, then for
  every module $M$:
  #set enum(numbering: "1.")
  + $M$'s summary
    #src("whitepaper/Fragment/Modular.lean", 942, 990)[is checked] against
    the empty environment, so the environment it stores, $M$'s _world_,
    is #src("whitepaper/Fragment/Modular.lean", 992, 996)[accepted
    declaration by declaration] and
    #src("whitepaper/Fragment/Modular.lean", 1010, 1014)[has a model];
  + $M$'s own environment refines its world;
  + so #src("whitepaper/Fragment/Modular.lean", 1016, 1028)[no closed
    term inhabits an empty proposition] in $M$'s own environment.
] <thm:mod>

#proof[
  By induction along the import graph. For each import, its summary
  is checked and its own environment refines its world (the induction
  hypothesis). The imports' summaries are joined one after another.
  Joining a checked list onto a compatible checked list, when the
  second was checked against an environment the first's environment
  refines, #src("whitepaper/Fragment/Modular.lean", 802, 857)[gives a
  checked list]. The proof goes declaration by declaration: one that
  stores what the first list already stores is dropped, and its
  entries are found where the first list stores them. Any other has
  fresh names, and part 2 of @thm:mod-mono moves its check. Each
  import's world, and hence its own environment, refines the joined
  imports. So $M$'s base refines them (check 2 and transitivity).
  Joining $M$'s declarations, checked against the base (check 1),
  gives a checked summary, and $M$'s own environment refines the
  world it stores. Item 3 is @sec:consistency in the world, carried
  back by part 1 of @thm:mod-mono.
]

The statement is per module, and it has to be. Two modules that never
meet in one summary may store one name with two different meanings.
No module rests on both, and no check compares them.

*What runs in parallel.* Check 1, the type checking, reads only the
module's base, so the type checking of all modules can run at the
same time, in any order. Checks 2–4 compare entries and names. They
follow the import graph, but only to pass the summaries along it, and
they never type-check anything.

== Lean's module system in these terms <sec:mod-lean>

A module of Lean's module system has a _private_ view (all its
declarations) and an _exported_ view, in which theorems and the
definitions the module does not expose keep their types only. In the
terms above:

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [a module's exported view], [an environment that refines its own
    environment, checked once per module],
  [the environment Lean builds to elaborate a module (each import's
    exported view, or its private view under `import all`, and the
    modules imports re-export)], [the module's base: each of its
    constants refines a constant of a direct import's own environment
    (check 2)],
  [a theorem], [its statement as an assumption],
  [the merge of duplicates on import (two copies of one theorem, a
    theorem against its exported view)], [compatibility, and
    refinement for the exported view],
  [names of private declarations], [ordinary names; Lean prefixes
    them with their module's name, so they never collide],
)

The local checks compare more than Lean does in one respect. Lean
compares the constants of the modules it loads, and it does not load
the internals that a module imports without re-exporting them.
Compatibility compares whole summaries, internals included. So two
modules that store one name differently, which Lean never loads
together, are rejected here as soon as some module rests on both. So
are two definitions of one proposition with different values, which
Lean merges when it sees only their exported views. They compare less
in another respect. Two identical non-theorem
declarations in two modules are compatible here, and Lean refuses
them when it loads both. Identical entries cannot make anything
inconsistent, so accepting them is safe.

#real[
  Con-leche checks a development as one environment, all its modules
  merged, and the main theorem
  #src("ConLeche/MainTheorem.lean", 96, 99)[is stated] for that
  environment. Checking module by module with the local checks above
  is planned. Its target statement is @thm:mod: for every module, its
  own environment refines an environment the checker accepts.
]
