#import "../lib.typ": *

// Notation local to this file.
#let ile = sym.prec.eq

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is split into _modules_, and each
module imports others. This section shows that the modules can be
checked one at a time, each against what its imports export, and
that the union of all modules is still an environment of the kind
§4 proves consistent. The argument is that checking is _monotone_: what
the checker accepts against fewer constants, or against a constant
whose value it does not see, it also accepts against more.

== Modules and what they export <sec:mod-export>

A module of Lean's module system records two views of itself. The _private_ view holds
every declaration in full. The _exported_ view is what another module
sees when it imports this one. In it, a theorem keeps its statement
but not its proof, and a definition that its module does not expose
keeps its type but not its value. Both appear to the importer as
assumptions with the same name, universe parameters and type (Lean's
`Lean/AddDecl.lean` stores them as axioms). Inductive types, their
constructors and recursors are exported as they are. A module that
imports another with `import all` sees the private view.

The fragment has no theorems (a theorem is a definition, @sec:left-out),
so hiding a proof and hiding a value are the same operation. An
#src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_] is a stored
constant with level parameters and a type and no value. The rule const
of @sec:env gives it its type; it never unfolds, since $delta$ needs
a value. The
#src("whitepaper/Fragment/Modular.lean", 53, 56)[exported view] of an
environment replaces some of its definitions by assumptions of the
same type.

#definition(name: "Interface")[
  An environment $I$ is an
  #src("whitepaper/Fragment/Modular.lean", 58, 63)[_interface_] of an
  environment $U$, written $I ile U$, when every constant $c$ stored
  in $I$ is stored in $U$ with the same level parameters and type, and
  with the same kind unless $c$ is an assumption in $I$.
] <def:interface>

An environment's exported view is
#src("whitepaper/Fragment/Modular.lean", 141, 153)[an interface of it],
and an interface of an interface is
#src("whitepaper/Fragment/Modular.lean", 92, 97)[an interface] of the
larger environment. Leaving constants out also gives an interface: the
condition speaks only about what $I$ stores. So the exported views of
a module's imports, taken together, form an interface of any
environment that holds the imports' private views.

== Checking is monotone <sec:mod-mono>

A module is
#src("whitepaper/Fragment/Modular.lean", 493, 495)[checked against an
environment] $I$ as §3 and §4 check a development: each declaration
passes its checks against $I$ and the module's earlier declarations,
and is then stored.

#theorem(name: "Monotonicity")[
  Let $I ile U$.
  #set enum(numbering: "1.")
  + Every reduction, definitional equality and inference derivable in
    $I$ is
    #src("whitepaper/Fragment/Modular.lean", 184, 304)[derivable in $U$].
  + A declaration that passes its checks against $I$, and whose names
    are not stored in $U$,
    #src("whitepaper/Fragment/Modular.lean", 485, 489)[passes them against $U$].
  + A module checked against $I$, whose names are not stored in $U$,
    is #src("whitepaper/Fragment/Modular.lean", 518, 531)[checked against $U$].
] <thm:mod-mono>

#proof[
  *Part 1*, by one induction over the rules of §2–§4. A rule reads
  the environment only by looking a constant up: its type and level
  parameters (rule const, the constructor and the family in a rule
  $iota$), its value (rule $delta$) or its kind (a recursor, a
  constructor of a nested rule, a type former). $U$ stores every
  constant of $I$ with the same type and level parameters. A constant
  whose value or kind the rule reads is not an assumption in $I$, so
  $U$ stores it with the same kind and value. Every premise of the
  rule is therefore a premise of the same rule in $U$, and
  the induction hypotheses give the derivations among them. No
  rule asks that a constant be absent.

  *Part 2.* The checks of §3 and §4 consist of derivations, covered
  by part 1; of conditions on the declaration and the constants it
  mentions (scope, level parameters, positivity), which hold in $U$
  because $U$ stores every constant $I$ stores; and, for a nested
  block, a lookup of the container's type former, which is not an
  assumption and so is stored in $U$ as it is. One check reads an
  absence: the declaration's names must be fresh. That is why
  freshness in $U$ is a hypothesis.

  *Part 3*, along the module's declarations. A declaration stores
  the #src("whitepaper/Fragment/Modular.lean", 410, 415)[same entries]
  in front of either environment, so storing it keeps $I ile U$; and a
  later declaration's names, fresh where it was checked against $I$,
  are not among the entries just stored.
]

The theorem says that the exported view can only make the checker
reject more, never accept more. A value it hides could only have been
used by $delta$, and the definition in $U$ still has it.

== The union of the modules <sec:mod-union>

#definition(name: "Modular development")[
  The empty environment is a
  #src("whitepaper/Fragment/Modular.lean", 550, 553)[modular development].
  If $U$ is one, $I ile U$, a module checks against $I$, and none of its
  names is stored in $U$, then $U$ with the module's declarations
  stored is one.
] <def:modular>

Here $U$ is the union of the private views of the modules so far and
$I$ is the interface the next module is checked against: the exported
views of its imports, or their private views where it imports with
`import all`.

#theorem(name: "Modular checking")[
  A modular development is an environment the checker
  #src("whitepaper/Fragment/Modular.lean", 557, 560)[accepts declaration by declaration].
  So it #src("whitepaper/Fragment/Modular.lean", 576, 577)[has a model], and
  no closed term in it
  #src("whitepaper/Fragment/Modular.lean", 581, 584)[inhabits an empty proposition].
] <thm:mod>

#proof[
  By induction on the development. A module checked against
  $I ile U$ is, by @thm:mod-mono, checked against $U$, so storing it
  extends an accepted environment declaration by declaration. The
  model and the consistency statement are those of
  @sec:consistency.
]

*Reading it semantically.* The soundness theorem of §3 holds at every
model of the environment the derivations live in. A model of an
interface interprets an assumption by any member of its type, since
the only law about an assumption is the typing law of
@def:model. So a module's checked declarations hold however the
assumptions it imports are interpreted, in particular at the
definitions' own values, which is what the union's model chooses.

*Independent modules are checked independently.* The premises a
module contributes in @def:modular, its checks and its fresh names,
mention its interface $I$ and nothing about the modules that are
neither its imports nor imported by them. Two modules of which neither
imports the other can therefore be checked at the same time, and a
development is checked along its import graph rather than along one
fixed order of all its declarations. Only the bookkeeping that
assembles $U$ follows an order, and any order that puts every module
after its imports does.

*What the bookkeeping must establish.* The theorem asks two things of
the step that assembles the union: every name is stored by one module
only, and each module's interface is an interface of the union before
it. For an exported view the second is a comparison per constant: the
exported constant is the private one, or an assumption with the
private one's name, level parameters and type.

#real[
  Con-leche checks a development as one environment, all its modules
  merged, and the main theorem
  #src("ConLeche/MainTheorem.lean", 96, 99)[is stated] for that
  environment. Checking module by module, against the imports'
  exported views, is planned. Its target statement is the one above:
  if every module is accepted against its interface, the union of the
  modules' private views has a model.
]
