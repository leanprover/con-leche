#import "../lib.typ": *

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is divided into _modules_. A module
imports earlier modules and adds declarations of its own. This
section checks every module separately, against an environment built
from the modules it imports, and proves that if every module passes
its checks, then the environment of every module has a model. In
particular, no module proves an empty proposition.

The argument is first stated for an arbitrary notion of model
(@sec:mod-iface). It applies to any consistency proof that provides
the constructions listed there. @sec:mod-env and @sec:mod-local
define the environments of a module and the checks it passes.
@sec:mod-thm states and proves the theorem, @sec:mod-par describes
which checks can run in parallel, and @sec:mod-compare treats a module
that is compared with another one instead of being checked.
@sec:mod-lean relates these notions to Lean's module system.

== Environment models in the abstract <sec:mod-iface>

By @def:model and the laws of §4, a model of an environment $E$ is an
assignment $M$ of a set $M(c, arrow(n))$ to every constant $c$ and
every list $arrow(n)$ of level values, subject to one law per stored
constant. We call the function $arrow(n) |-> M(c, arrow(n))$ the
_value_ of $c$ in the model. The argument of this section uses models
only through the constructions below. We state them for an arbitrary
notion of environment, of model and of value, because nothing in the
argument depends on sets.

*Families and assembly.* Let $(E_i)_(i in I)$ be a family of
environments and let $C$ be an environment. For every name $n$ that
$C$ stores, some members of the family are _designated_ as having
$C$'s constant $n$. In the application, the designation compares
which constant the name denotes in $C$ and in $E_i$ (@sec:mod-env).
What it means for $C$ to be _assembled_ from the family under a
designation is defined by each consistency proof for itself
(@def:assembled is the fragment's definition). The argument uses only
one property of it: every constant of an assembled environment has at
least one designated member that stores its name.

A family of models $(m_i)_(i in I)$, with $m_i$ a model of $E_i$, is
_compatible_ for $C$ when for every name $n$ of $C$, all members that
are designated as having $n$ and store it give $n$ the same value.

#definition(name: "What a consistency proof provides")[
  #set enum(numbering: "1.")
  + *Models and values.*
    #src("whitepaper/Fragment/ModularSemantics.lean", 95, 102)[For every
    environment, a type of models], each model giving every name a
    value, and one value $pi$, the value of a proof.
  + *Amalgamation.* If $C$ is assembled from $(E_i)$ and $(m_i)$ is
    compatible for $C$, then $C$
    #src("whitepaper/Fragment/ModularSemantics.lean", 110, 115)[has a
    model] that gives every name $n$ of $C$ the value of $n$ in every
    member designated as having $n$ and storing it.
  + *The conservative step.* If the checker accepts declarations $D$
    over $Gamma$, giving $Gamma'$, then every model of $Gamma$
    #src("whitepaper/Fragment/ModularSemantics.lean", 122, 125)[extends]
    to a model of $Gamma'$ that gives every name of $Gamma$ the same
    value, and gives every name that $D$ flags as a proof the value
    $pi$.
] <def:mod-iface>

A declaration may be _flagged_ as a proof. The checks of
@sec:mod-local accept the flag only on a theorem or on a definition
whose type is a proposition.

*Refinement and restriction.* An environment $Gamma$
#src("whitepaper/Fragment/ModularSemantics.lean", 131, 133)[_refines_]
an environment $E$ when $Gamma$ is assembled from the family whose only
member is $E$, with every name designated. A family with one member is
compatible for any environment. Amalgamation therefore turns every
model of $E$ into a model of $Gamma$ with the same values, the
#src("whitepaper/Fragment/ModularSemantics.lean", 142, 147)[_restriction_]
of the model to $Gamma$. The empty environment is assembled from the
empty family, which is compatible, so amalgamation also gives the
empty environment a model.

*Why the step must extend every model.* The step requires that every
model of $Gamma$ extends to $Gamma'$, and the proof of @sec:mod-thm
applies it to a model of $Gamma$ obtained by amalgamation. The weaker
requirement that $Gamma'$ has a model whenever $Gamma$ has one does
not suffice. Let a module $W$ define $c : "Nat" := 5$. Let a module
$M$ import $c$ from $W$ with its value hidden, so that $M$'s
environment $Gamma$ contains the assumption $c : "Nat"$, and let $M$
add the axiom $h : c = 0$. Then $Gamma$ extended by $h$ has a model,
in which $c$ is $0$, and $W$ has a model. A module that imports both
$W$ and $M$ contains $c := 5$ and $h : c = 0$, and has no model. The
step as stated excludes the axiom $h$: it would have to extend the
model of $Gamma$ in which $c$ is $5$, the restriction of $W$'s model,
and no model of $Gamma$ extended by $h$ gives $c$ the value $5$. The
fragment has no axioms, and the example only concerns the form of the
step.

In the terminology of institutions @goguen1992, environments and
refinements play the role of signatures and their morphisms,
restriction is the reduct of a model along a morphism, and
amalgamation combines models of the parts of a diagram that agree
where the parts overlap.

*A syntactic proof provides the same.* Nothing in @def:mod-iface is
about sets. Consider a type system with constants and a fixed theory
of closed terms, with a
#src("whitepaper/Fragment/ModularSyntactic.lean", 53, 56)[substitution
lemma]: a derivation over an environment remains a derivation in the
fixed theory when a closed term is substituted for every constant,
provided each substituted term has the substituted type and equals
the substituted value of a definition. Take as a model of an
environment such a
#src("whitepaper/Fragment/ModularSyntactic.lean", 76, 84)[_realisation_],
and as the value of a constant its realising term. An environment is
#src("whitepaper/Fragment/ModularSyntactic.lean", 163, 170)[assembled]
when each of its entries is the entry of a designated member, with the
value kept or dropped, and every constant the entry mentions is
designated as that member's. Amalgamation is the
#src("whitepaper/Fragment/ModularSyntactic.lean", 172, 179)[union of
the realisations], and the step
#src("whitepaper/Fragment/ModularSyntactic.lean", 123, 126)[realises a
new definition by its realised value], which has the realised type by
the substitution lemma. This system flags no declaration as a proof. So a proof
by syntax
#src("whitepaper/Fragment/ModularSyntactic.lean", 208, 229)[provides]
@def:mod-iface, and @thm:mod holds for it.

== Environments of modules <sec:mod-env>

*Assumptions and theorems.* An
#src("whitepaper/Fragment/Env.lean", 83, 86)[_assumption_] is a stored
constant with level parameters and a type and no value. The rule const
of @sec:env gives it its type. It never unfolds, because $delta$ needs
a value. The only law a model owes an assumption is the typing law of
@def:model: its value is a member of its type.

A _theorem_ is checked like a definition, with its statement as the
type and its proof as the value, and its statement must be a
proposition. What is stored is the
#src("whitepaper/Fragment/Decl.lean", 608, 618)[statement alone, as an
assumption]. The checker never unfolds a theorem, so nothing is lost.
Installing a theorem keeps the environment's model:
#src("whitepaper/Fragment/InstallThm.lean", 249, 254)[install the
proof as a definition, then forget the value].

*Refinement of constants.* One constant
#src("whitepaper/Fragment/Modular.lean", 23, 26)[_refines_] another
when it is the other, or an assumption with the other's level
parameters and type. A definition seen without its value refines the
definition, and so does a type former seen as an assumption of its
type.

*Proofs denote the point.* If the type of a constant is a
proposition, then in every model its set at every instantiation of its
level parameters is the point, because that set is a member of the
type and the type is a truth value. In particular the value the installation of §3 gives a theorem,
or a definition that the checker finds to be of a proposition,
#src("whitepaper/Fragment/ModularModel.lean", 61, 81)[is the point]
at every list of levels. This is the value $pi$ of @def:mod-iface.

*Modules.* A
#src("whitepaper/Fragment/ModularModel.lean", 391, 402)[module] $M$
consists of
#set enum(numbering: "(i)")
+ the list of modules it _imports_;
+ its _context_ $Gamma_M$, the environment its declarations are
  checked against;
+ its list of declarations $D_M$, some flagged as proofs;
+ its _own environment_ $E_M$, the context with the declarations
  stored;
+ the _views_ it presents to the modules that import it: the
  environments these modules read in place of $E_M$;
+ for every name $n$ it uses, the _key_ $kappa_M (n)$ of the constant
  $n$ denotes in $M$.

A #src("whitepaper/Fragment/ModularSemantics.lean", 78, 84)[key] is
either a module, the _home_ of the constant, which is the module that
declares it, or, for a proof, the proof's statement: its level
parameters and its type. Two modules mean the same constant by a name
$n$ exactly when they give $n$ the same key. Two modules may declare
different constants under one name. Their keys then differ, and no
check compares the two constants. A proof is identified by its
statement rather than by its home because every proof of a statement
denotes the point, whatever its home and its body.

Every module uses its own names. No name is ever renamed, and no
environment holds constants of several modules except a module's own
context. A name that the theory treats specially keeps its meaning in
every module, and nothing in the argument requires the theory to be
invariant under a renaming of constants.

*Assembly in the fragment.* For the models of §3 and §4, assembly is
defined as follows.

#definition(name: "Assembly")[
  Let $(E_i)_(i in I)$ be a family of environments, with a designation
  of members for every name of an environment $C$. Then $C$
  #src("whitepaper/Fragment/ModularModel.lean", 223, 235)[is assembled]
  from the family when, for every constant $c$ that $C$ stores, there
  is a member $E_i$ designated as having $c$ such that
  #set enum(numbering: "1.")
  + $E_i$ stores $c$, and the constant $C$ stores under $c$ refines
    the constant $E_i$ stores;
  + every name that the law of $C$'s constant reads is stored in $C$
    and designated as $E_i$'s: the names in its type, and in its
    value, its rules and their constructors, and its inductive block,
    where $C$ keeps these;
  + if $C$ stores a type former as a type former, $C$ also stores
    its constructors.
] <def:assembled>

An assumption brings only its type into $C$, so a value hidden in $C$
is never inspected. A type former stored as an assumption of its type
brings no constructors and no recursor.

#theorem(name: "Amalgamation")[
  If $C$ is assembled from $(E_i)$ and the models $m_i$ of the $E_i$
  are compatible for $C$, then the assignment that gives every constant
  $c$ of $C$ its value in a member designated as having $c$
  #src("whitepaper/Fragment/ModularModel.lean", 252, 260)[is a model of
  $C$].
] <thm:amalg>

#proof[
  The assignment is well defined because the family is compatible.
  Take a constant $c$ of $C$ and the member $E_i$ of
  @def:assembled. If $C$ stores the constant of $E_i$, its law in $C$
  is its law in $E_i$. If $C$ stores an assumption, its law is the
  typing law, which the constant of $E_i$ satisfies. The law reads the
  assignment only at the names listed in item 2 of @def:assembled,
  because the interpretation of a term
  #src("whitepaper/Fragment/Hygiene.lean", 593, 595)[depends only on
  the constants it mentions], and the block laws of §4 read the
  assignment only through such interpretations. At each such name $d$, $d$ is
  designated as $E_i$'s and stored in both, so by compatibility the
  assignment gives $d$ the value $m_i$ gives it. The law therefore
  holds in $C$ because it holds in $m_i$.
]

The models of §3 and §4 thus
#src("whitepaper/Fragment/ModularInstance.lean", 61, 80)[provide]
@def:mod-iface: the value of a constant is its set at every list of
levels, $pi$ is the point, amalgamation is @thm:amalg, and the step is
the installation of §3 and §4 together with that of a theorem, which
#src("whitepaper/Fragment/ModularModel.lean", 100, 106)[keeps the
values of the context and gives every flagged proof the point].

== The local checks <sec:mod-local>

The checks of a module $M$ fall into three groups, according to the
data they read.

#definition(name: "Local checks")[
  #set enum(numbering: "1.")
  + #src("whitepaper/Fragment/ModularModel.lean", 421, 424)[*Per home.*]
    Every view of $M$ refines $E_M$.
  + #src("whitepaper/Fragment/ModularModel.lean", 426, 431)[*Per importer.*]
    Every module $M$ imports is earlier than $M$, and $Gamma_M$ is
    #src("whitepaper/Fragment/ModularModel.lean", 416, 419)[assembled
    from the views of $M$'s imports], a view of an import $N$ being
    designated as having $M$'s constant $n$ when
    $kappa_M (n) = kappa_N (n)$.
  + *The module's own.* The declarations $D_M$ are accepted against
    $Gamma_M$; a declaration flagged as a proof is a theorem or a
    definition whose type is a proposition; and every name $n$ that
    $D_M$ declares has the key $M$, or its statement if $n$ is
    flagged as a proof
    (#src("whitepaper/Fragment/ModularModel.lean", 407, 410)[the own
    key]).
] <def:local>

A module that passes all three
#src("whitepaper/Fragment/ModularModel.lean", 433, 443)[passes its
local checks]. A module is _validated_ when it passes its local checks
or is compared with another module (@sec:mod-compare).

The check per home reads $M$ alone, and it runs once for $M$, however
many modules import $M$. The check per importer reads $M$'s context
and keys and its imports' views and keys. It never reads the own
environment of an import, and the views may be much smaller. The
check is made constant by constant: a constant of the context is
compared with the constant of the same name in one view, together
with the names its law reads. Hiding a definition's value or a
theorem's proof in a view therefore passes it, and so does a context
that takes only some of a view's constants. A definition that
typechecks only because it unfolds a hidden one is never checked again
by an importer. It is checked once, in its home, where the hidden
definition has its value.

== The theorem <sec:mod-thm>

The theorem gives every module a model, and the models it gives agree
with each other.

#definition(name: "Compatible family")[
  A family of models $(m_M)$, with $m_M$ a model of $E_M$ for every
  module $M$, is
  #src("whitepaper/Fragment/ModularSemantics.lean", 198, 205)[compatible]
  when
  #set enum(numbering: "1.")
  + whenever $E_M$ and $E_N$ both store a name $n$ and
    $kappa_M (n) = kappa_N (n)$, the models $m_M$ and $m_N$ give $n$
    the same value; and
  + every name whose key is a proof's statement has the value $pi$.
] <def:compatible>

Compatibility is needed for the induction to go through. Let a
module $H$ define $c : "Nat" := 0$ and present $c$ in its view with
its value hidden. Let modules $A$ and $B$ import $H$; their contexts
contain the assumption $c : "Nat"$, $A$ defines $a := c$ and $B$
defines $b := c$. The own environment of $A$ has a model in which $c$
is $1$, and that of $B$ one in which $c$ is $0$, since neither sees
$c$'s value. A module that imports $A$ and $B$ has $a := c$ and
$b := c$ in its context, with one $c$, and the two models give no
model of that context: the unfolding laws of $a$ and $b$ would need
$c$ to be $1$ and $0$. The induction therefore builds the models of
$A$ and $B$ from $H$'s model, so that they agree at $c$. The
corollary, which is what a user of the checker relies on, mentions
only the existence of models.

#theorem(name: "Modular checking")[
  If every module of a development is validated, then there is a
  compatible family of models, one model of the own environment of
  every module
  (#src("whitepaper/Fragment/ModularSemantics.lean", 252, 256)[for any
  consistency proof],
  #src("whitepaper/Fragment/ModularInstance.lean", 115, 128)[for the
  fragment's]).
] <thm:mod>

#corollary(name: "Every module has a model")[
  If every module of a development is validated, then for every
  module $M$:
  #set enum(numbering: "1.")
  + $E_M$ #src("whitepaper/Fragment/ModularInstance.lean", 132, 137)[has
    a model];
  + #src("whitepaper/Fragment/ModularInstance.lean", 139, 149)[no closed
    term inhabits an empty proposition] that $E_M$ stores;
  + #src("whitepaper/Fragment/ModularInstance.lean", 151, 160)[every
    statement $E_M$ stores holds] in that model.
] <cor:mod>

Item 2 is @sec:consistency's argument at the model of item 1. Item 3
is the typing law of the model, which puts every constant in its
statement.

#proof[
  By induction along a numbering of the modules in which every module
  comes after the modules it imports. Suppose the models $m_N$ of the
  modules before $M$ form a compatible family. The model of $M$ is
  built in three steps.

  _Restriction to the views._ Every view of an import $N$ refines
  $E_N$, by the check per home, so $m_N$ restricts to a model of the
  view with the same values. Two of these views that are designated
  as having $M$'s constant $n$ give it the same value: their modules
  $N$ and $N'$ satisfy $kappa_N (n) = kappa_M (n) = kappa_(N') (n)$,
  and the family is compatible. So the restricted models are a
  compatible family for $Gamma_M$.

  _Amalgamation and the step._ By the check per importer, $Gamma_M$ is
  assembled from the views, and amalgamation gives a model of
  $Gamma_M$. By the module's own checks, the checker accepts $D_M$
  over $Gamma_M$, and the step extends this model to a model $m_M$ of
  $E_M$ that keeps the values of $Gamma_M$ and gives every flagged
  proof the value $pi$.

  _Compatibility._ Let $E_M$ and an earlier $E_N$ both store $n$ with
  $kappa_M (n) = kappa_N (n)$. If $Gamma_M$ stores $n$, the value of
  $n$ in $m_M$ is its value in a view of an import $N_0$ with
  $kappa_(N_0) (n) = kappa_M (n)$, which is its value in $m_(N_0)$,
  which by compatibility is its value in $m_N$. If $n$ is declared by
  $M$, its key is $M$ or a statement. No earlier module stores a name
  with the key $M$, since
  #src("whitepaper/Fragment/ModularSemantics.lean", 223, 225)[the keys
  of every module name that module or earlier ones]. A statement key
  gives the value $pi$ in both models. The same case analysis shows
  that every name of $E_M$ with a statement key has the value $pi$.

  A compared module's own environment is itself assembled from its
  imports' views, so amalgamation gives its model directly, and the
  step is not used.
]

The induction needs a numbering of the modules in which every module
comes after its imports, and it needs every module to be validated.
Nothing else about the development as a whole enters the argument.

== What runs in parallel <sec:mod-par>

The checks of a module $M$ read $M$ and the views of its imports. A
view of a module is available as soon as its own environment is, so
the checks can proceed along the import graph: a module can be checked
as soon as the views of its imports exist, and modules that do not
depend on each other can be checked at the same time. Each step of the
proof of @thm:mod has the same dependencies. The model of $M$ is made
from the models of its imports, by restriction, amalgamation and one
step, and no part of the argument for $M$ refers to a module that $M$
does not import. The numbering in the induction only fixes one order
in which the modules can be treated.

== Comparing a module <sec:mod-compare>

A module can also be validated without checking its declarations, by
comparison. A module $M$ is
#src("whitepaper/Fragment/ModularModel.lean", 445, 451)[_compared_]
when its views refine its own environment, it imports only earlier
modules, and its whole own environment $E_M$, its declarations
included, is assembled from the views of its imports. Every constant
$M$ stores is then a constant of one of its imports, or an assumption
of that constant's type. The assumptions that replace a constant with
a value are $M$'s _holes_.

This is the situation of a _challenge_ and its _solution_. A
challenge states what is to be proved, with holes where the proofs go.
Its solution is a checked module that declares the same names and
fills the holes. For the comparison, the solution counts among the
challenge's imports, and the challenge's names are the solution's: a
constant of the challenge is keyed like the solution's constant of the
same name. The comparison reads the challenge's own environment in
full, definitions with their values. A definition the challenge states
with a value must be the solution's, value included, and only the
holes are free. A hole may also stand for a definition's value. Then
the solution chooses that value, and the challenge says nothing about
it. A reader of a challenge therefore has to look at its list of
holes.

By @def:compatible, the model @thm:mod gives the challenge agrees with
the solution's model on every constant they share under one key. By @cor:mod, item
3, every statement of the challenge, every hole included, holds in it.
A challenge whose hole states an empty proposition therefore cannot be
compared with any validated solution.

== Lean's module system in these terms <sec:mod-lean>

A module of Lean's module system has an _exported_ level and a
_private_ level. The private level holds all of the module's
declarations. In the exported level, theorems and the definitions the
module does not expose keep their types only. A third level holds data
for the language server.

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [a module's exported level, with the constants of its context that
    the exported constants mention], [a view],
  [the private level, which an importer reads under `import all`],
  [a view equal to the module's own environment],
  [the language server's level], [not used],
  [the modules Lean loads to elaborate a module: its imports, and
    transitively the modules they re-export by `public import`],
  [the module's imports],
  [the environment Lean builds from those modules' levels], [the
    module's context],
  [a theorem, and in the exported level a definition that is not
    exposed], [an assumption of its type; a theorem is flagged as a
    proof],
  [the merge of two copies of one name on import, which Lean allows
    for two theorems with one statement], [one key, since a proof's
    key is its statement],
  [two modules declaring one name that Lean never loads together],
  [two keys, never compared],
  [a private name (`_private.…`)], [an ordinary name, keyed by its
    home],
  [an exported constant whose value mentions a constant that is not
    exported], [an assumption of its type if its type is complete,
    otherwise absent],
  [`backward.privateInPublic`, which exports a private constant], [a
    constant of the view, so that exported values mentioning it stay
    complete],
)

The exported level of a module need not be self-contained: an exported
value may mention a constant that is not exported, such as a private
one. Under @def:assembled, a constant taken from a view can be held in
one of three forms: as stored, if every name its law reads is present
under the same key; as an assumption of its type, if every name in its
type is; or not at all. The context of a module, as con-leche builds
it, takes each constant in the first form that applies, decided for
all constants of the module together until nothing changes. An
inductive block with an incomplete
constructor or recursor type enters as an assumed type former, with no
constructors and no recursor. Nothing from an import's private level is
added to complete an exported constant, and no name is treated
specially because of its spelling.

The checks are designed not to reject what Lean accepts. That is an
aim, checked by running them on real developments, not a theorem.
Copies that Lean merges are proofs of one statement and share a key.
Constants that Lean never loads together are never compared. The check
per importer goes further than Lean's merge: it asks that the names a
constant of the context reads have the same keys in the module as in
the view the constant comes from. This covers the constant's type and
whatever value or rules the module keeps. What the module does not
keep, such as the value of a definition it holds as an assumption, is
not inspected.

#real[
  Con-leche checks a development module by module with local checks of
  the kind above, in two modes. In the first, every module is checked at its
  view of one store of installed constants; in the second
  (`--modular=isolated`), every module is checked in
  #src("ConLeche/Cached/ModIso.lean", 280, 286)[an environment of its
  own], built from its imports' exported levels (private levels under
  `import all`) alone, and the two modes are
  #src("ConLeche/Verify/Modular/IsoCtx.lean", 580, 587)[proved to give
  the same verdicts]. With `--compare CHALLENGE SOLUTION` a challenge
  is compared with its solution as in @sec:mod-compare, as part of the
  challenge's own work, and its holes are listed. The modular theorem
  #src("ConLeche/MainTheorem.lean", 131, 139)[is stated] in the form of
  @sec:mod-thm: if every module passes its local checks, every module's
  own environment has a model, and the models are compatible. Keys are
  home modules or a proof's level parameters and type, and no name is
  renamed. Its proof is
  #src("ConLeche/Modular/Generic.lean", 255, 256)[the theorem over the
  interface] of @sec:mod-iface, the same statement as the fragment's,
  with con-leche's models as the instance: a model is a leaf assignment
  of the module's environment, and amalgamation gives each name the
  leaf of the module it is read from. A constant counts as a proof if it
  is a theorem, or a definition or opaque constant whose type the
  checker infers to be a proposition, decided by the module that
  installs it.
]
