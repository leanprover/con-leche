#import "../lib.typ": *

// Notation local to this file, matching §3 and §4.
#let Sort = $sans("Sort")$
#let Nat = $sans("Nat")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
// The vocabulary of this section.
#let St = $op("St")$
#let Mod = $op("Mod")$
#let Val = $op("Val")$
#let Name = $op("Name")$
#let Asm = $op("Asm")$
#let Acc = $op("Acc")$
#let Fl = $op("Fl")$
#let Sc = $op("Sc")$
#let imp = $op("imp")$
#let names = $op("names")$
#let home = $sans("home")$
#let prf = $sans("proof")$
#let refines = sym.prec.eq

= Checking module by module <sec:modular>

§3 and §4 check a development as one environment, one declaration
after another. A Lean development is divided into _modules_. A module
imports earlier modules and adds declarations of its own. This
section checks every module separately, against an environment built
from the modules it imports. It proves that if every module passes
its checks, then the environment of every module has a model. In
particular, no module proves an empty proposition.

The argument is first stated for an arbitrary notion of model
(@sec:mod-iface). The interface lists the constructions the argument
needs from a consistency proof. The fragment's set-theoretic model
provides them, and so does con-leche's graded model. @sec:mod-env
defines the environments of a module, and @sec:mod-local the checks it
passes. @sec:mod-thm states and proves the theorem. @sec:mod-par
describes which checks can run in parallel, and @sec:mod-compare
treats a module that is compared with another one instead of being
checked. @sec:mod-lean relates these notions to Lean's module system.

== Environment models in the abstract <sec:mod-iface>

The argument of this section uses models only through the
constructions below. We state them for an arbitrary notion of
environment, of model and of value, because nothing in the argument
depends on sets.

*Notation.* For an environment $E$,
#src("whitepaper/Fragment/ModularSemantics.lean", 95, 96)[$St(E)$] is
the set of names that $E$ stores. For $c in St(E)$, $E(c)$ is the
constant stored under $c$: its level parameters, its type and its
kind. A model $m$ of $E$ gives every name $c$ a _value_ $m(c)$. For
the models of §3 and §4, with assignment $M$, the value of $c$ is the
function $arrow(n) |-> M(c, arrow(n))$ from lists of level values to
sets.

*Families and designations.* A _family_ $(E_x)_(x in X)$ is an
environment $E_x$ for every index $x$ of a set $X$. A _designation_ for
an environment $C$ is a relation $sigma subset.eq Name times X$. We
read $sigma(c, x)$ as "the member $x$ counts as having $C$'s constant
$c$". In @sec:mod-local, $sigma(c, x)$ holds when $C$ and $E_x$ come
from modules that give $c$ the same key.

*Assembly.* Each consistency proof defines for itself when $C$ is
_assembled_ from $(E_x)$ under $sigma$, written
$Asm(C, (E_x), sigma)$. @def:assembled is the fragment's definition.
The argument uses one property of assembly: every constant of $C$ has
a designated member that stores its name,
$
  Asm(C, (E_x), sigma) quad ==> quad forall c in St(C). thin exists x in X. thin
    sigma(c, x) and c in St(E_x).
$

#definition(name: "Compatible for an environment")[
  Let $sigma$ be a designation for $C$, and let $m_x$ be a model of
  $E_x$ for every $x in X$. The family $(m_x)_(x in X)$ is
  _compatible for $C$_ when
  $
    forall c in St(C). thin forall x, x' in X. quad
      sigma(c, x) and sigma(c, x') and c in St(E_x) inter St(E_(x')) quad ==> quad
      m_x (c) = m_(x') (c).
  $
] <def:compatible-for>

In words: all members that are designated as having $c$ and store
$c$ give $c$ the same value.

#definition(name: "What a consistency proof provides")[
  #set enum(numbering: "1.")
  + *Models and values.* For every environment $E$
    #src("whitepaper/Fragment/ModularSemantics.lean", 97, 104)[a type
    $Mod(E)$ of models], and for every $m in Mod(E)$ and every name $c$
    a value $m(c) in Val$. One value $pi in Val$ is the _value of a
    proof_.
  + *Assembly.* A relation
    #src("whitepaper/Fragment/ModularSemantics.lean", 105, 111)[$Asm(C, (E_x), sigma)$
    with the property] displayed above.
  + *Amalgamation.* If $Asm(C, (E_x), sigma)$ and $(m_x)$ is
    compatible for $C$, then $C$
    #src("whitepaper/Fragment/ModularSemantics.lean", 112, 117)[has a
    model] with the members' values:
    $
      exists m_C in Mod(C). thin forall c in St(C). thin forall x in X. quad
        sigma(c, x) and c in St(E_x) quad ==> quad m_C (c) = m_x (c).
    $
  + *The conservative step.* For declarations $D$, a set
    $Fl(D)$ of names that $D$ _flags as proofs_, and a relation
    #src("whitepaper/Fragment/ModularSemantics.lean", 118, 123)[$Acc(Gamma, D, Gamma')$],
    "the checker accepts $D$ over $Gamma$, giving $Gamma'$". Every
    model of $Gamma$
    #src("whitepaper/Fragment/ModularSemantics.lean", 124, 127)[extends]
    to $Gamma'$:
    $
      Acc(Gamma, D, Gamma') quad ==> quad
        & forall m in Mod(Gamma). thin exists m' in Mod(Gamma'). \
        & quad (forall c in St(Gamma). thin m'(c) = m(c)) and (forall c in Fl(D). thin m'(c) = pi).
    $
] <def:mod-iface>

The extended model keeps the value of every name of $Gamma$ and gives
every flagged name the value $pi$. The checks of @sec:mod-local accept
a flag only on a theorem or on a definition whose type is a
proposition.

*Refinement and restriction.* Refinement is assembly from a family
with one member.

#definition(name: "Refinement")[
  An environment $Gamma$
  #src("whitepaper/Fragment/ModularSemantics.lean", 133, 135)[_refines_]
  an environment $E$, written $Gamma refines E$, when $Gamma$ is
  assembled from the family $(E)_(x in {*})$ with every name
  designated:
  $
    Gamma refines E quad :<==> quad Asm(Gamma, (E)_(x in {*}), Name times {*}).
  $
] <def:refines>

#lemma(name: "Restriction")[
  If $Gamma refines E$, then
  #src("whitepaper/Fragment/ModularSemantics.lean", 139, 140)[$St(Gamma) subset.eq St(E)$],
  and every model of $E$
  #src("whitepaper/Fragment/ModularSemantics.lean", 144, 147)[restricts]
  to $Gamma$:
  $
    forall m in Mod(E). thin exists m' in Mod(Gamma). thin forall c in St(Gamma). thin m'(c) = m(c).
  $
] <lem:restrict>

#proof[
  The inclusion is the property of assembly. A family with one member
  is compatible for every environment, since $x = x' = *$ in
  @def:compatible-for. Amalgamation of the family $(m)$ gives $m'$.
]

We call $m'$ the _restriction_ of $m$ to $Gamma$. In the same way, the
empty family is compatible for every environment. Amalgamation
therefore gives a model to every environment that is assembled from
the empty family.

*Why the step must extend every model.* The step requires that every
model of $Gamma$ extends to $Gamma'$. The proof of @sec:mod-thm
applies it to a model of $Gamma$ obtained by amalgamation. The weaker
requirement "if $Gamma$ has a model, then $Gamma'$ has one" does not
suffice. Let a module $W$ define $c : Nat := 5$. Let a module $U$
import $c$ from $W$ with its value hidden, so that $U$'s environment
$Gamma$ contains the assumption $c : Nat$. Let $U$ add the axiom
$h : c = 0$. Then $Gamma$ extended by $h$ has a model, in which $c$ is
$0$, and $W$ has a model. A module that imports both $W$ and $U$
contains $c := 5$ and $h : c = 0$, and has no model. The step as
stated excludes the axiom $h$. It would have to extend the model of
$Gamma$ in which $c$ is $5$, the restriction of $W$'s model, and no
model of $Gamma$ extended by $h$ gives $c$ the value $5$. The fragment
has no axioms; the example only concerns the form of the step.

In the terminology of institutions @goguen1992, environments and
refinements play the role of signatures and their morphisms.
Restriction is the reduct of a model along a morphism. Amalgamation
combines models of the parts of a diagram that agree where the parts
overlap.

*An instance by syntax.* Nothing in @def:mod-iface is about sets. The
fragment includes a small syntactic instance of it. Consider a type
system with constants and a fixed theory of closed terms, with a
#src("whitepaper/Fragment/ModularSyntactic.lean", 60, 63)[substitution
lemma]: a derivation over an environment remains a derivation in the
fixed theory when a closed term is substituted for every constant,
provided each substituted term has the substituted type and equals
the substituted value of a definition. A model of an environment is
such a
#src("whitepaper/Fragment/ModularSyntactic.lean", 83, 91)[_realisation_],
and the value of a constant is its realising term. An environment is
#src("whitepaper/Fragment/ModularSyntactic.lean", 170, 177)[assembled]
when each of its entries is the entry of a designated member, with the
value kept or dropped, and every constant the entry mentions is
designated as that member's. Amalgamation is the
#src("whitepaper/Fragment/ModularSyntactic.lean", 179, 186)[union of
the realisations]. The step
#src("whitepaper/Fragment/ModularSyntactic.lean", 130, 133)[realises a
new definition by its realised value], which has the realised type by
the substitution lemma. This system flags no declaration as a proof.
So the syntactic instance
#src("whitepaper/Fragment/ModularSyntactic.lean", 215, 236)[provides]
@def:mod-iface, and @thm:mod holds for it.

The instance illustrates the interface. It does not show that a
syntactic consistency proof of Lean fits it. It handles definitions
only: no axioms, no inductive types, and nothing is flagged a proof.
The interface also gives every proof one shared value $pi$. This suits
set models but not a syntactic proof, where proofs of different
propositions are different terms. Whether the interface suits another
real consistency proof is open until there is such a proof to connect
it to.

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

*Refinement of constants.* An assumption may stand for a constant of
any kind with the same level parameters and type.

#definition(name: "Refinement of constants")[
  For two stored constants $a$ and $b$,
  #src("whitepaper/Fragment/Modular.lean", 23, 26)[$a$ _refines_ $b$]
  when
  $
    a <= b quad :<==> quad a = b quad or quad
      (a "is an assumption" and b "equals" a "except in its kind").
  $
] <def:const-le>

A definition seen without its value refines the definition, and so
does a type former seen as an assumption of its type.

*Proofs denote the point.* Let $(c.\{arrow(p)\} : T) in E$ with
$tack T => S red Sort u$ and $u eq.dot 0$. Then in every model of $E$,
$ M(c, arrow(n)) = pt quad "for every" arrow(n), $
because the typing law puts $M(c, arrow(n))$ into
$lden T rden$, which is a truth value. The same holds for the set that
the installation of §3 gives a theorem, or a definition whose type the
checker finds to be a proposition: its value $v$
#src("whitepaper/Fragment/ModularModel.lean", 61, 66)[denotes the point]
at every list of levels. The function $arrow(n) |-> pt$ is the value
$pi$ of @def:mod-iface.

*Modules.* Modules are numbered $0, 1, 2, dots$, and a module imports
only modules with smaller numbers (@sec:mod-local checks this).

#definition(name: "Development")[
  A #src("whitepaper/Fragment/ModularSemantics.lean", 155, 164)[development]
  gives every module $i$
  #set enum(numbering: "(i)")
  + the list $imp_i$ of modules it _imports_;
  + its _context_ $Gamma_i$, the environment its declarations are
    checked against;
  + its declarations $D_i$, with the set $Fl(D_i)$ of names flagged as
    proofs;
  + its _own environment_ $E_i$. In the fragment,
    #src("whitepaper/Fragment/ModularModel.lean", 404, 405)[$E_i = Gamma_i + D_i$],
    the context with the declarations stored;
  + the list $cal(V)_i$ of _views_ it presents to the modules that
    import it: the environments these modules read in place of $E_i$;
  + for every name $c$, the _key_ $kappa_i (c)$ of the constant that
    $c$ denotes in module $i$,
    $
      kappa_i (c) in {home(j) mid(|) j in NN} union {prf(s) mid(|) s "a statement"}.
    $
] <def:development>

A #src("whitepaper/Fragment/ModularSemantics.lean", 81, 86)[key]
$home(j)$ names the constant's _home_, the module $j$ that declares
it. A key $prf(s)$ is for a proof, and $s$ is the proof's
#src("whitepaper/Fragment/ModularModel.lean", 159, 161)[statement]: its
level parameters and its type, $s = (arrow(p), T)$. Modules $i$ and
$j$ mean the same constant by a name $c$ exactly when
$kappa_i (c) = kappa_j (c)$. Two modules may declare different
constants under one name. Their keys then differ, and no check
compares the two constants. A proof is identified by its statement
rather than by its home, because every proof of a statement denotes
the point, whatever its home and its body.

Every module uses its own names. No name is ever renamed. No
environment holds constants of several modules, except a module's own
context. A name that the theory treats specially keeps its meaning in
every module, and nothing in the argument requires the theory to be
invariant under a renaming of constants.

*Assembly in the fragment.* For the models of §3 and §4, assembly is
defined as follows. Two auxiliary notions come first.

A term $e$ is _closed in $A$ over $arrow(p)$_ when it
#src("whitepaper/Fragment/Decl.lean", 580, 584)[has no free variable,
every constant it mentions is in $St(A)$, and it uses no level
parameter outside $arrow(p)$]. For a family $(E_x)$ and a designation
$sigma$ for $C$,
#src("whitepaper/Fragment/ModularModel.lean", 189, 193)[the part of
$E_x$ that $C$ reads as $E_x$'s] is $E_x$ restricted to the names that
$C$ stores and designates as $E_x$'s:
$
  E_x^C = E_x "restricted to" {c in St(C) mid(|) sigma(c, x)},
  quad "so" quad E_x^C (c) = E_x (c) "for those" c.
$

Let $a$ be a constant with level parameters $arrow(p)$ and type $T$,
and let $A$ and $C$ be environments. Then $Sc(A, C, a)$, "everything the laws of $a$
read is #src("whitepaper/Fragment/ModularModel.lean", 208, 221)[within $A$]",
holds when
#[
#set enum(numbering: "(1)")
+ $T$ is closed in $A$ over $arrow(p)$;
+ if $a$ is a definition with value $v$, then $v$ is closed in $A$ over
  $arrow(p)$;
+ if $a$ is a recursor, then for each of its rules, with right-hand
  side $r$ and constructor $d$: $r$ is closed in $A$ over $arrow(p)$,
  $d in St(A)$, $A(d) = C(d)$, and the type of $A(d)$ is closed in $A$
  over the level parameters of $A(d)$;
+ if $a$ is a type former with a block $B$ that is not nested, then
  the telescopes, fields and index expressions of $B$ are closed in
  $A$, and the type former and the constructors of $B$ are in $St(A)$.
]

#definition(name: "Assembly")[
  Let $(E_x)_(x in X)$ be a family of environments and $sigma$ a
  designation for $C$. Then $C$
  #src("whitepaper/Fragment/ModularModel.lean", 223, 235)[is assembled]
  from the family, $Asm(C, (E_x), sigma)$, when
  #set enum(numbering: "(a)")
  + every constant of $C$ refines a constant of a designated member
    and is within the part of that member that $C$ reads:
    $
      forall c in St(C). thin exists x in X. quad
        sigma(c, x) and c in St(E_x) and C(c) <= E_x (c) and Sc(E_x^C, C, C(c));
    $
  + if $C(c)$ is a type former with a block $B$ that is not nested,
    then $C$ stores the type former and the constructors that $B$
    generates (@sec:ind-checks), under their names.
] <def:assembled>

Item (a) for an assumption reads only its type, so a value hidden in
$C$ is never inspected. A type former stored as an assumption of its
type brings no constructors and no recursor. An assembled environment
is #src("whitepaper/Fragment/ModularModel.lean", 374, 377)[closed]:
every stored term mentions only stored constants.

#theorem(name: "Amalgamation")[
  Let $Asm(C, (E_x), sigma)$, and let $M_x$ be models of the $E_x$
  with
  $
    forall c in St(C). thin forall x, x' in X. quad
      sigma(c, x) and sigma(c, x') and c in St(E_x) inter St(E_(x')) quad ==> quad
      M_x (c, dot.c) = M_(x') (c, dot.c).
  $
  Then the assignment $M$ that gives every $c in St(C)$ its set in a
  member designated as having $c$
  #src("whitepaper/Fragment/ModularModel.lean", 252, 260)[is a model of
  $C$]:
  $
    forall c in St(C). thin forall x in X. quad
      sigma(c, x) and c in St(E_x) quad ==> quad M(c, dot.c) = M_x (c, dot.c).
  $
] <thm:amalg>

#proof[
  The assignment is well defined because the family is compatible.
  Take $c in St(C)$ and the member $E_x$ of item (a). If
  $C(c) = E_x (c)$, the law of $c$ in $C$ is its law in $E_x$. If
  $C(c)$ is an assumption, its law is the typing law, which $E_x (c)$
  satisfies, since it has the same type. The law reads the assignment
  only at names of $E_x^C$, by $Sc(E_x^C, C, C(c))$, because the
  interpretation of a term
  #src("whitepaper/Fragment/Hygiene.lean", 593, 595)[depends only on
  the constants it mentions], and the block laws of §4 read the
  assignment only through such interpretations. At every
  $d in St(E_x^C)$ we have $sigma(d, x)$ and $d in St(C) inter St(E_x)$,
  so $M(d, dot.c) = M_x (d, dot.c)$. The law therefore holds in $C$ because
  it holds in $M_x$. Item (b) puts the block's constructors into $C$,
  where the block law of the type former reads them.
]

The models of §3 and §4 thus
#src("whitepaper/Fragment/ModularInstance.lean", 61, 80)[provide]
@def:mod-iface. The value of a constant is its set at every list of
levels, $pi$ is $arrow(n) |-> pt$, and amalgamation is @thm:amalg.
Declarations are a list $D$ with a flag $p(c) in {"yes", "no"}$ for
every name. The flagged names are
#src("whitepaper/Fragment/ModularInstance.lean", 41, 43)[those that a
declaration of $D$ stores with the flag set]:
$
  Fl(D, p) = {c mid(|) exists d in D. thin c in names(d) and p(c) = "yes"}.
$
#src("whitepaper/Fragment/ModularInstance.lean", 45, 48)[Acceptance]
says that the list is checked, its flags are correct (@def:local,
item 3), and the context is closed:
$
  Acc(Gamma, (D, p), Gamma') quad :<==> quad
    & Gamma' = Gamma + D and D "is checked over" Gamma \
    & and "the flags" p "are correct" and Gamma "is closed".
$
The step is the installation of §3 and §4 together with that of a
theorem. It
#src("whitepaper/Fragment/ModularModel.lean", 100, 107)[keeps the
sets of the context and gives every flagged proof the point]:
$M'(c, dot.c) = M(c, dot.c)$ for $c in St(Gamma)$ and $M'(c, dot.c) = pt$ for
$c in Fl(D, p)$.

== The local checks <sec:mod-local>

*Reading the views.* Module $i$ reads the views of its imports. The
#src("whitepaper/Fragment/ModularSemantics.lean", 170, 171)[index set]
of this family consists of the pairs of an import and one of its views,
and a view is designated as having $c$ when module $i$ and the view's
module give $c$ the same key:
$
  X_i = {(j, V) mid(|) j in imp_i, thin V in cal(V)_j}, quad
  sigma_i (c, (j, V)) quad :<==> quad kappa_i (c) = kappa_j (c).
$
An environment $E$ is
#src("whitepaper/Fragment/ModularSemantics.lean", 173, 176)[assembled
from the imports' views] of module $i$ when
$
  Asm_i (E) quad :<==> quad Asm(E, (V)_((j, V) in X_i), sigma_i).
$

#definition(name: "Valid module")[
  Module $i$ of a development
  #src("whitepaper/Fragment/ModularSemantics.lean", 193, 198)[is _valid_]
  when
  $
    (forall V in cal(V)_i. thin V refines E_i) and
    (forall j in imp_i. thin j < i) and
    ("Checked"_i or "Compared"_i),
  $
  where
  #set enum(numbering: "1.")
  + #src("whitepaper/Fragment/ModularSemantics.lean", 178, 181)[_the new names are keyed by the module, or are flagged proofs_]:
    $
      "NewKeys"_i quad :<==> quad
        & forall c in St(E_i) without St(Gamma_i). \
        & quad kappa_i (c) = home(i) or ((exists s. thin kappa_i (c) = prf(s)) and c in Fl(D_i));
    $
  + #src("whitepaper/Fragment/ModularSemantics.lean", 183, 187)[module $i$ is _checked_]:
    $
      "Checked"_i quad :<==> quad Asm_i (Gamma_i) and Acc(Gamma_i, D_i, E_i) and "NewKeys"_i;
    $
  + #src("whitepaper/Fragment/ModularSemantics.lean", 189, 191)[module $i$ is _compared_]
    (@sec:mod-compare):
    $
      "Compared"_i quad :<==> quad Asm_i (E_i).
    $
] <def:valid>

In the fragment, the checks of a checked module fall into three
groups, according to the data they read.

#definition(name: "Local checks")[
  Module $i$
  #src("whitepaper/Fragment/ModularModel.lean", 433, 443)[passes its
  local checks] when it passes the following three groups of checks.
  #set enum(numbering: "1.")
  + #src("whitepaper/Fragment/ModularModel.lean", 421, 424)[*Per home.*]
    Every view refines the own environment:
    $forall V in cal(V)_i. thin V refines E_i$.
  + #src("whitepaper/Fragment/ModularModel.lean", 426, 431)[*Per importer.*]
    Every import is earlier, and the context is assembled from the
    imports' views:
    $(forall j in imp_i. thin j < i) and Asm_i (Gamma_i)$.
  + *The module's own.* The list $D_i$ is checked over $Gamma_i$: each
    declaration passes its check over $Gamma_i$ extended by the
    declarations before it. The
    #src("whitepaper/Fragment/ModularModel.lean", 85, 90)[flags are
    correct]: a declaration $d$ with a flagged name is a theorem, or
    a definition whose type $T$ has $tack T => S red Sort u$ with
    $u eq.dot 0$ over the environment at $d$. And every name that
    $D_i$ declares has
    #src("whitepaper/Fragment/ModularModel.lean", 407, 410)[the own
    key], with $arrow(p)$ and $T$ the level parameters and type of
    $E_i (c)$:
    $
      forall d in D_i. thin forall c in names(d). quad
        kappa_i (c) = cases(prf(arrow(p), T) & "if" c "is flagged", home(i) & "otherwise.")
    $
] <def:local>

A module is
#src("whitepaper/Fragment/ModularModel.lean", 453, 454)[_validated_]
when it passes its local checks or is
#src("whitepaper/Fragment/ModularModel.lean", 445, 451)[compared]: it
passes the check per home, its imports are earlier, and
$Asm_i (E_i)$. A validated module
#src("whitepaper/Fragment/ModularInstance.lean", 94, 96)[is valid].
The own keys give $"NewKeys"_i$, because every name of $E_i$ that
$Gamma_i$ does not store is declared by $D_i$.

The check per home reads module $i$ alone. It runs once for $i$,
however many modules import $i$. The check per importer reads $i$'s
context and keys and its imports' views and keys. It never reads the
own environment of an import, and the views may be much smaller. The
check is made constant by constant: by item (a) of @def:assembled, a
constant of the context is compared with the constant of the same name
in one view, together with the names its law reads. Hiding a
definition's value or a theorem's proof in a view therefore passes
it, and so does a context that takes only some of a view's constants.
A definition that typechecks only because it unfolds a hidden one is
never checked again by an importer. It is checked once, in its home,
where the hidden definition has its value.

== The theorem <sec:mod-thm>

The theorem gives every module a model, and the models it gives agree
with each other.

#definition(name: "Compatible family of a development")[
  Let $m_i in Mod(E_i)$ for every $i < k$. The family
  $(m_i)_(i < k)$
  #src("whitepaper/Fragment/ModularSemantics.lean", 200, 207)[is
  compatible] when two modules that store a name under one key give it
  one value, and every name with a proof key has the value $pi$:
  $
    & forall i, i' < k. thin forall c in St(E_i) inter St(E_(i')). quad
      kappa_i (c) = kappa_(i') (c) quad ==> quad m_i (c) = m_(i') (c), \
    & forall i < k. thin forall c in St(E_i). thin forall s. quad
      kappa_i (c) = prf(s) quad ==> quad m_i (c) = pi.
  $
] <def:compatible>

Compatibility is needed for the induction to go through. Let a module
$H$ define $c : Nat := 0$ and present $c$ in its view with its value
hidden. Let modules $A$ and $B$ import $H$. Their contexts contain the
assumption $c : Nat$. $A$ defines $a := c$, and $B$ defines $b := c$.
The own environment of $A$ has a model in which $c$ is $1$, and that
of $B$ one in which $c$ is $0$, since neither sees $c$'s value. A
module that imports $A$ and $B$ has $a := c$ and $b := c$ in its
context, with one $c$. The two models give no model of that context:
the unfolding laws of $a$ and $b$ would need $c$ to be both $1$ and
$0$. The induction therefore builds the models of $A$ and $B$ from
$H$'s model, so that they agree at $c$. The corollary, which is what a
user of the checker relies on, mentions only the existence of models.

#lemma(name: "Homes are earlier")[
  If every module $j <= i$ is valid, then
  #src("whitepaper/Fragment/ModularSemantics.lean", 225, 227)[the homes
  in the keys of module $i$ are $i$ or earlier modules]:
  $
    forall c in St(E_i). thin forall h. quad kappa_i (c) = home(h) quad ==> quad h <= i.
  $
] <lem:home-le>

#proof[
  By strong induction on $i$. If $Gamma_i$ stores $c$, or module $i$ is
  compared, then $c$ is stored, under the same key, in a view of an
  import $j < i$, and so in $E_j$ by @lem:restrict. By induction,
  $h <= j < i$. Otherwise $c$ is new, and $"NewKeys"_i$ gives
  $kappa_i (c) = home(i)$ or a proof key.
]

#theorem(name: "Modular checking")[
  If every module below $k$ is valid, then there is a compatible
  family of models, one model of the own environment of every module
  below $k$
  (#src("whitepaper/Fragment/ModularSemantics.lean", 254, 258)[over the
  interface],
  #src("whitepaper/Fragment/ModularInstance.lean", 115, 128)[for the
  fragment's]):
  $
    (forall i < k. thin i "is valid") quad ==> quad
      exists (m_i in Mod(E_i))_(i < k) "compatible".
  $
] <thm:mod>

#proof[
  By induction on $k$. For $k = 0$ the empty family is compatible.
  Let $(m_j)_(j < k)$ be compatible, and let module $k$ be valid. The
  model of module $k$ is built in three steps.

  _Restriction to the views._ Let $(j, V) in X_k$. Then $j < k$, and
  $V refines E_j$ by the check per home. @lem:restrict gives a model
  $m_(j, V)$ of $V$ with $m_(j, V) (c) = m_j (c)$ for every
  $c in St(V)$, and $St(V) subset.eq St(E_j)$. The family
  $(m_(j, V))_((j, V) in X_k)$ is compatible for every environment
  under $sigma_k$: if $sigma_k (c, (j, V))$ and $sigma_k (c, (j', V'))$,
  then $kappa_j (c) = kappa_k (c) = kappa_(j') (c)$, and
  $m_j (c) = m_(j') (c)$ by the first clause of @def:compatible.

  _Amalgamation and the step._ If module $k$ is checked, then
  $Asm_k (Gamma_k)$, and amalgamation gives a model $m_C$ of $Gamma_k$
  with the views' values. From $Acc(Gamma_k, D_k, E_k)$ the step
  gives a model $m_k$ of $E_k$ with $m_k (c) = m_C (c)$ on
  $St(Gamma_k)$ and $m_k (c) = pi$ on $Fl(D_k)$. If module $k$ is
  compared, then $Asm_k (E_k)$, amalgamation gives $m_k$ directly, and
  the step is not used. In both cases every $c in St(E_k)$ satisfies
  one of
  $
    & m_k (c) = m_j (c) "for some" (j, V) in X_k "with" kappa_k (c) = kappa_j (c), thin c in St(V), \
    & kappa_k (c) = home(k), \
    & kappa_k (c) = prf(s) "for some" s, "and" m_k (c) = pi.
  $

  _Compatibility._ Let $c in St(E_k) inter St(E_(i'))$ with $i' < k$
  and $kappa_k (c) = kappa_(i') (c)$. In the first case,
  $m_k (c) = m_j (c) = m_(i') (c)$ by compatibility below $k$. The
  second case is impossible: $kappa_(i') (c) = home(k)$ with $k > i'$
  contradicts @lem:home-le. In the third case, $m_(i') (c) = pi$ by
  the second clause of @def:compatible, and $m_k (c) = pi$. The same
  case analysis shows that $m_k (c) = pi$ for every $c in St(E_k)$
  with a proof key: in the first case by compatibility below $k$, and
  the second case has a home key. So $(m_i)_(i < k + 1)$ is
  compatible.
]

The induction needs a numbering of the modules in which every module
comes after its imports, and it needs every module to be valid.
Nothing else about the development as a whole enters the argument.

#corollary(name: "Every module has a model")[
  Let every module $j <= i$ be valid. Then
  #set enum(numbering: "1.")
  + $E_i$ #src("whitepaper/Fragment/ModularSemantics.lean", 340, 342)[has
    a model]: $Mod(E_i) != emptyset$ (in the fragment,
    #src("whitepaper/Fragment/ModularInstance.lean", 132, 135)[for the
    validated modules]);
  + if $E_i$ stores the recursor of an inductive type $I$ with no
    constructors, parameters, indices or level parameters, then
    #src("whitepaper/Fragment/ModularInstance.lean", 139, 146)[no closed
    term $e$ has] $tack e => I$ over $E_i$;
  + #src("whitepaper/Fragment/ModularInstance.lean", 151, 158)[every
    statement $E_i$ stores holds] in a model $M$ of $E_i$:
    $
      forall (c.\{arrow(p)\} : T) in E_i. thin forall arrow(ell), phi, rho. quad
        lden T[arrow(p) := arrow(ell)] rden_rho != emptyset.
    $
] <cor:mod>

Item 1 reads off the family of @thm:mod at $k = i + 1$. Item 2 is
@cor:consistency's argument at the model of item 1. Item 3 is the
typing law of the model, which puts $M(c, phi(arrow(ell)))$ into the
statement.


== What runs in parallel <sec:mod-par>

The checks of module $i$ read module $i$ and the views of its
imports. A view of a module is available as soon as its own
environment is. The checks can therefore proceed along the import
graph: a module can be checked as soon as the views of its imports
exist, and modules that do not depend on each other can be checked at
the same time. Each step of the proof of @thm:mod has the same
dependencies. The model of module $i$ is made from the models of its
imports, by restriction, amalgamation and one step. No part of the
argument for module $i$ refers to a module that $i$ does not import.
The numbering in the induction only fixes one order in which the
modules can be treated.

== Comparing a module <sec:mod-compare>

A module can also be validated without checking its declarations, by
comparison. Module $i$ is compared when its views refine its own
environment, it imports only earlier modules, and its whole own
environment, its declarations included, is assembled from the views
of its imports: $Asm_i (E_i)$. By item (a) of @def:assembled, every
constant of $E_i$ is then a constant of one of its imports, or an
assumption of that constant's type. The assumptions that replace a
constant with a value are the module's _holes_.

This is the situation of a _challenge_ and its _solution_. A
challenge states what is to be proved, with holes where the proofs go.
Its solution is a checked module that declares the same names and
fills the holes. For the comparison, the solution counts among the
challenge's imports, and the challenge's names are the solution's: a
constant of the challenge is keyed like the solution's constant of the
same name. The comparison reads the challenge's own environment in
full, definitions with their values. A definition that the challenge
states with a value must be the solution's, value included. Only the
holes are free. A hole may also stand for a definition's value. Then
the solution chooses that value, and the challenge says nothing about
it. A reader of a challenge therefore has to look at its list of
holes.

By @def:compatible, the model that @thm:mod gives the challenge agrees
with the solution's model on every constant they share under one key.
By @cor:mod, item 3, every statement of the challenge holds in it,
every hole included. A challenge whose hole states an empty
proposition therefore cannot be compared with any validated solution.

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

The exported level of a module need not be self-contained. An
exported value may mention a constant that is not exported, such as a
private one. Under @def:assembled, a constant taken from a view can be
held in one of three forms: as stored, if every name its law reads is
present under the same key; as an assumption of its type, if every
name in its type is; or not at all. The context of a module, as
con-leche builds it, takes each constant in the first form that
applies. This is decided for all constants of the module together,
until nothing changes. An inductive block with an incomplete
constructor or recursor type enters as an assumed type former, with no
constructors and no recursor. Nothing from an import's private level is
added to complete an exported constant, and no name is treated
specially because of its spelling.

The checks are designed not to reject what Lean accepts. That is an
aim, checked by running them on real developments, not a theorem.
Copies that Lean merges are proofs of one statement and share a key.
Constants that Lean never loads together are never compared. The check
per importer goes further than Lean's merge. It asks that the names a
constant of the context reads have the same keys in the module as in
the view the constant comes from. This covers the constant's type and
whatever value or rules the module keeps. What the module does not
keep, such as the value of a definition it holds as an assumption, is
not inspected.

#real[
  Con-leche checks a development module by module with local checks of
  the kind above, in two modes. In the first, every module is checked at its
  view of one store of installed constants. In the second
  (`--modular=isolated`), every module is checked in
  #src("ConLeche/Cached/ModIso.lean", 280, 286)[an environment of its
  own], built from its imports' exported levels (private levels under
  `import all`) alone. The two modes are
  #src("ConLeche/Verify/Modular/IsoCtx.lean", 580, 587)[proved to give
  the same verdicts]. With `--compare CHALLENGE SOLUTION` a challenge
  is compared with its solution as in @sec:mod-compare, as part of the
  challenge's own work, and its holes are listed. The modular theorem
  #src("ConLeche/MainTheorem.lean", 131, 139)[is stated] in the form of
  @sec:mod-thm: if every module passes its local checks, every module's
  own environment has a model, and the models are compatible. Keys are
  home modules or a proof's level parameters and type, and no name is
  renamed. Its proof is
  #src("ConLeche/Modular/Generic.lean", 256, 257)[the theorem over the
  interface] of @sec:mod-iface, the same statement as the fragment's,
  with con-leche's models as the instance. A model is a leaf assignment
  of the module's environment, and amalgamation gives each name the
  leaf of the module it is read from. A constant counts as a proof if it
  is a theorem, or a definition or opaque constant whose type the
  checker infers to be a proposition, decided by the module that
  installs it.
]
