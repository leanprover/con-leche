#import "../lib.typ": *

#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let Mod = $op("Mod")$
#let Val = $op("Val")$
#let Asm = $op("Asm")$
#let Acc = $op("Acc")$
#let Cmp = $op("Cmp")$
#let Valid = $op("Valid")$
#let Checked = $op("Checked")$
#let Pass = $op("Pass")$
#let Prf = $op("Prf")$
#let By = $op("By")$
#let Side = $op("Pf")$
#let Ag = $op("Ag")$
#let Rd = $op("Rd")$
#let From = $op("src")$
#let rk = $op("rk")$
#let refines = sym.prec.eq
#let agr = $scripts(asymp)$

= Checking module by module <sec:modular>

A module is checked against the views its imports present. These may
hide definition values or theorem proofs, so the environment used to
check an imported declaration can differ from the environment in
which it is used. We show how local checks nevertheless give each
module a model, in which every name a module reads has the value it has
where it is read from. The argument first uses an abstract interface;
we then supply it from the set-theoretic models of §3 and §4.

== Environment models in the abstract <sec:mod-iface>

Let $C$ be the context of the module we are checking, an environment
built from a family of imported views $(E_x)_(x in X)$, environments
indexed by a set $X$. To check the declarations,
we need a model of $C$ that preserves the values already assigned by
the imports' models. This requires agreement wherever two imported
views store a name of $C$.

In general, write
#src("whitepaper/Fragment/ModularSemantics.lean", 112, 113)[$c in E$]
when an environment $E$ stores a name $c$, and $Mod(E)$ for its models.
A model $m in Mod(E)$ assigns each name $c in E$ a value $m(c) in Val$;
all proofs will receive one distinguished value $pi in Val$.
Models $m in Mod(E)$ and $m' in Mod(E')$
#src("whitepaper/Fragment/ModularSemantics.lean", 97, 103)[_agree on_]
an environment $C$ when they give the same value to every name of $C$
that both $E$ and $E'$ store:
$
  m agr_C m' quad :<==> quad
    forall c in C. thin c in E and c in E' ==> m(c) = m'(c).
$
A family of models $(m_x in Mod(E_x))_(x in X)$ is _compatible for
$C$_ when $m_x agr_C m_y$ for all $x,y in X$.

#definition(name: "The model interface")[
  A consistency proof must provide
  #src("whitepaper/Fragment/ModularSemantics.lean", 122, 154)[four laws].
  An _assembly_ relation identifies contexts built from a family of
  environments, with every stored name supplied by a member:
  $
    Asm(C,(E_x)) ==> forall c in C. thin exists x in X. thin c in E_x.
  $
  _Amalgamation_ turns models of the family compatible for $C$ into a model
  of $C$ that agrees on $C$ with each of them:
  $
    Asm(C,(E_x)) and (forall x,y in X. thin m_x agr_C m_y) ==>
    exists m_C in Mod(C). thin forall x in X. thin m_C agr_C m_x.
  $
  _Proofs_ are recognised in two ways. $Prf(C,E,c)$ says that $C$
  shows $E$'s entry at $c$ to be a proof (in the instance: its type is
  inferred over $C$ to be a proposition), and a model of $E$ agreeing on $C$ with a
  model of $C$ gives it $pi$. $By(C,E,E',c)$ says that $E$'s $c$ has the
  statement of a theorem $E'$ stores under $c$, which $C$, $E$ and $E'$
  read alike, and a model of $E$ agreeing on $C$ with a model of $C$
  that agrees on $C$ with a model of $E'$ gives it $pi$:
  $
    Prf(C,E,c) and m_C agr_C m ==> m(c) = pi, quad quad
    By(C,E,E',c) and m_C agr_C m and m_C agr_C m' ==> m(c) = pi,
  $
  for all $m_C in Mod(C)$, $m in Mod(E)$ and $m' in Mod(E')$.
  Finally, for environments $Gamma$, $Gamma'$ and declaration data $D$,
  acceptance of $D$ over $Gamma$, producing $Gamma'$, must give a
  _conservative step_:
  $
    Acc(Gamma,D,Gamma') ==> forall m in Mod(Gamma). thin
      exists m' in Mod(Gamma'). thin
    forall c in Gamma. thin c in Gamma' and m'(c) = m(c).
  $
] <def:mod-iface>

The step must extend _every_ context model. For example, a context
assuming a name $c : sans("Nat")$ can receive $c$'s value $5$ from an import.
Adding an axiom $c = 0$ would leave some model, but none preserving
that imported value. The conservative step excludes this extension.

An environment $V$
#src("whitepaper/Fragment/ModularSemantics.lean", 160, 161)[_refines_]
an environment $E$, written $V refines E$, when it is assembled from $E$ alone.
Amalgamation of the one-member family then
#src("whitepaper/Fragment/ModularSemantics.lean", 170, 175)[restricts]
any model $m in Mod(E)$ to a model of $V$, preserving the value $m(c)$
at every $c in V$
(and assembly ensures $c in E$).
Amalgamation of the empty family supplies a model for any context
assembled from no environments.

== Developments <sec:mod-env>

Number modules by natural numbers. For
#src("whitepaper/Fragment/ModularSemantics.lean", 181, 193)[module $i in NN$],
write $Gamma_i$ for its context, $D_i$ for its declarations and $E_i$
for its own environment, which is to be validated.
Module $i$ reads a list $X_i$ of _imported views_: pairs $(j,V)$ of
an earlier module $j in NN$ and a view $V$ that $j$ presents. A module
may present several views, such as an exported and a private one, and
$X_i$ holds the views $i$ reads of every module whose declarations it
can see, including modules reached through re-exports, not only its
direct imports. In Lean, these are the modules loaded for $i$, each at
the level at which it is loaded (@sec:mod-lean). The context of $i$
is assembled from its imported views. Each must refine the own
environment of the module presenting it, so that the model can be restricted to
what the importer reads.
Module numbers will place imports before importers.

For each name $c in Gamma_i$, module $i$ names the module
$From_i (c)$ it _reads $c$ from_, orders its context names by a rank
$rk_i (c)$, and gives the _part below_ $c$: an environment
$P_i (c)$ of context names of smaller rank. Two modules may hold
copies of one name, and nothing relates copies no module reads
together. What the theory asks is that the copies a module reads
_agree_: get one value in the models.

== Agreement and validity

Module $i$ checks, for each name $c in Gamma_i$ and each imported view
$(j,V) in X_i$ that stores $c$, that $j$'s copy agrees with the one
$i$ reads. A copy is a proof for $i$,
#src("whitepaper/Fragment/ModularSemantics.lean", 205, 209)[$Side_i (c,(j,V))$],
when $i$ proves it one over the part below $c$, or it has the statement
of a theorem an imported view stores, read alike over that part:
$
  Side_i (c,(j,V)) quad :<==> quad Prf(P_i (c), V, c) or
    exists (h,W) in X_i. thin By(P_i (c), V, W, c).
$
One theorem among the copies of a statement is enough: a theorem's
type is a proposition, and every copy of its statement reads that type
alike.
The copy
#src("whitepaper/Fragment/ModularSemantics.lean", 211, 221)[_agrees_],
written $Ag_i (c,(j,V))$, when one of three cases holds:
+ $j = From_i (c)$: it is the module $c$ is read from;
+ $c in Gamma_j$, some $(h,W) in X_j$ stores $c$, and some
  $(h,W') in X_i$ with $h < j$ stores it too: one copy of an earlier
  module $h$, loaded through two paths;
+ $Side_i (c,(j,V))$, and $Side_i (c,(h,W))$ for every
  $(h,W) in X_i$ with $h = From_i (c)$ and $c in W$: two proofs.
Module $i$
#src("whitepaper/Fragment/ModularSemantics.lean", 223, 230)[_reads_ $c$]
when some view of $From_i (c)$ in $X_i$ stores $c$, the part
$P_i (c)$ is assembled from the views in $X_i$, its names are
names of $Gamma_i$ of smaller rank, and every view in $X_i$ storing
$c$ agrees; write $Rd_i (c)$. For an environment $E$, abbreviate
assembly of $E$ from the views in $X_i$ by $Asm_i (E)$.

#definition(name: "Valid module")[
  The #src("whitepaper/Fragment/ModularSemantics.lean", 234, 242)[validity conditions]
  are
  $
    Valid_i & :<==> (forall (j,V) in X_i. thin j < i and V refines E_j)
      and Asm_i (Gamma_i) and (forall c in Gamma_i. thin Rd_i (c)) \
      & quad and Acc(Gamma_i,D_i,E_i).
  $
] <def:valid>

The condition on imported views makes induction and restriction possible.
The rank orders the agreements. Whether a copy's type is a proposition
is inferred over the part below the name, which holds only names of
smaller rank. Their copies agree by the time those of $c$ are
compared, so the part below $c$ has a model amalgamated from the
views' models, and the proof law applies to every copy of $c$.

== Compatible models and the theorem <sec:mod-thm>

The induction must construct models together with their agreement.
For $k in NN$, a family $m_i in Mod(E_i)$, for $i < k$, is
#src("whitepaper/Fragment/ModularSemantics.lean", 244, 251)[_compatible_]
when every module gives each name of its context the value the module
it is read from gives it, and so does every imported view storing it:
$
  Cmp_k ((m_i)) quad :<==> quad
  & forall i < k. thin forall c in Gamma_i. thin (From_i (c) < k
    and m_i (c) = m_(From_i (c)) (c) \
  & quad and forall (j,V) in X_i. thin c in V ==> m_j (c) = m_(From_i (c)) (c)).
$
Two proofs of one statement under one name agree without comparing
their bodies, since both get $pi$.

Compatibility concerns values because hidden bodies can refer to
names that have a different meaning in the importer. Take four
modules $j$, $k$, $l$ and $i$:
$
  j: & quad d := 0, quad c := d, quad "presenting" c : sans("Nat") \
  k: & quad "reads all of" j, quad e : c = 0 "(by unfolding)", quad
    "presenting" c : sans("Nat"), thick e : c = 0 \
  l: & quad d := 1 \
  i: & quad "imports" k "and" l, "reading" c : sans("Nat"), thick
    e : c = 0, thick d := 1.
$
The two copies of $d$ have different values, $0$ and $1$, but never
meet in a context, so nothing asks them to agree. Restoring $c := d$
in $i$ would make $c$ unfold to $1$, contradicting $e$; a model of $i$
instead takes $c$'s value from $j$ and $d$'s from $l$. A module that
did read both copies of $d$ would have to show that they agree: they
come from different modules, are not one copy loaded twice, and are
not proofs, so the check rejects it. There is no combined environment
of bodies and no renaming of names.

#theorem(name: "Modular checking")[
  For every $k in NN$, if the modules $i < k$ are valid, they have a
  #src("whitepaper/Fragment/ModularSemantics.lean", 272, 279)[compatible family of models]:
  $
    (forall i < k. thin Valid_i) ==> \
      exists (m_i in Mod(E_i))_(i < k). thin Cmp_k ((m_i)).
  $
] <thm:mod>

#proof[
  Induct on $k$, starting with the empty family. For each imported
  view $(j,V) in X_k$, restrict the earlier model $m_j$ to $V$. By
  induction on the rank, every view storing a name $c in Gamma_k$
  gives it the value of $m_(From_k (c))$. In the first case of
  agreement this is the restriction. In the second, $j$'s copy is the
  value $m_j$ gives $c$, which by compatibility of the earlier family is
  the value of the view $(h,W)$ that $j$ reads, and so of $(h,W')$, by
  an inner induction on the presenting module, as $h < j$. In the third, the names of
  the part below $c$ have smaller rank, so the restricted models agree
  there and amalgamate to a model of $P_k (c)$, which agrees there with
  every restricted model, a theorem's view's among them; the proof laws
  give $pi$ to $j$'s copy and to the copies of $From_k (c)$.

  The restricted models are thus compatible for $Gamma_k$, and
  amalgamate to a model of $Gamma_k$. The conservative step extends it
  to a model of $E_k$, in which every name of $Gamma_k$ keeps the value
  of the module it is read from, giving $Cmp_(k+1)$.
]

Forgetting compatibility gives the statement one usually needs.

#corollary(name: "Every module has a model")[
  For every $i in NN$,
  #src("whitepaper/Fragment/ModularSemantics.lean", 367, 371)[validity of the modules up to $i$ gives a model of $E_i$]:
  $
    (forall j <= i. thin Valid_j) ==> exists m in Mod(E_i).
  $
] <cor:mod-model>

#proof[
  Apply @thm:mod with $k = i + 1$ and take the member $m_i$ of the
  compatible family.
]

== The set-theoretic instance <sec:mod-instance>

We now supply @def:mod-iface using the models of §3 and §4. Write
$E(c)$ for the entry an environment $E$ stores under a name $c in E$; it has level parameters
$arrow(p)$, a type $T$ and a kind. An
#src("whitepaper/Fragment/Env.lean", 82, 85)[_assumption_]
retains just the parameters and type. Its model obligation is the
typing law of @def:model, with no unfolding law.
The instance's #src("whitepaper/Fragment/ModularInstance.lean", 107, 115)[value $m(c)$]
of a model $m$ at a name $c$ is the function assigning $c$ its set at every list of concrete levels;
$pi$ is the constant function with value $pt$.

*Models.* A model of $E$ is a model in the sense of §3 and §4 in
which
#src("whitepaper/Fragment/ModularModel.lean", 82, 86)[proofs are the point]:
every definition or assumption of $E$ whose type
#src("whitepaper/Fragment/ModularModel.lean", 73, 75)[reads as a truth value]
has the point as its set, at every list of levels, and in which
#src("whitepaper/Fragment/Holds.lean", 39, 40)[every stored constant holds]
in the sense of @def:input-model. Both survive amalgamation, since a
constant's clauses read only the constants its entry mentions, and
the step.

*Proofs.* $Prf(C,E,c)$
#src("whitepaper/Fragment/ModularModel.lean", 710, 716)[holds] when
$E$ stores $c$ as a definition or an assumption whose type, in scope in
both $C$ and $E$, has $tack T => S red Sort u$ over $C$ with
$u eq.dot 0$. In a model of $C$, soundness makes the type a truth
value; a model of $E$ agreeing on $C$ reads the type alike, since
interpretation depends only on the mentioned constants; so the copy
#src("whitepaper/Fragment/ModularModel.lean", 718, 731)[gets $pi$].
The fragment's theorems are the statements their own environment
infers to be propositions:
#src("whitepaper/Fragment/ModularModel.lean", 733, 739)[$By(C,E,E',c)$]
holds when $E$ stores $c$ as a definition or an assumption of the type
of $E'$'s $c$, in scope in $C$ and $E$, and $Prf(E',E',c)$. A model of
$E'$ reads the type as a truth value, and the agreeing models of $C$
and $E$ read it alike, so the copy
#src("whitepaper/Fragment/ModularModel.lean", 741, 758)[gets $pi$] too.

*Assembly.* An entry's laws transfer when everything they read is
read alike. Accordingly,
#src("whitepaper/Fragment/ModularModel.lean", 426, 439)[assembly]
requires each $C(c)$, for $c in C$, to come from some member $E_x$ of the family at the same name,
either unchanged or as an assumption of the same parameters and type
(#src("whitepaper/Fragment/Modular.lean", 26, 29)[entry refinement]).
An assumption stands for statements only: every member's copy of its
name is a definition or an assumption.
The #src("whitepaper/Fragment/ModularModel.lean", 392, 396)[common part]
$E_x^C$ consists of $E_x$'s entries at names also stored by $C$.

The retained entry must be
#src("whitepaper/Fragment/ModularModel.lean", 411, 424)[in scope in this common part]:
its type and any retained value or rule body are closed, mention only
constants in the common part and use only the entry's declared level
parameters, as in §3 and §4. A recursor's rules must also read the same constructor
entries in $E_x$ and $C$, with their types in scope. Hiding a
value removes its unfolding law and therefore its value dependencies;
an assumption needs only its type's dependencies.

For a retained plain type former (one without nesting), assembly also
requires the block's
#src("whitepaper/Fragment/Decl.lean", 699, 710)[specification scope]
from @sec:ind-checks in the common part, with the type former
and its constructors present there, and their exact generated entries
in $C$. The models
#src("whitepaper/Fragment/BlockModel.lean", 46, 66)[retain the block facts]
from @sec:ind-model: scope, generated entries, the constructed family
and constructor sets, and the
#src("whitepaper/Fragment/IndSem.lean", 601, 622)[field universe bound]
at every fitting parameter list, for every family in the result
universe. These facts are needed when a later block uses this one
as a container.

*Amalgamation.* Choose each name's value from any member storing it,
and use $pi$ if no member does. On names of $C$, compatibility makes
this assignment agree with every such member. Interpretation
#src("whitepaper/Fragment/Hygiene.lean", 585, 587)[depends only on mentioned constants],
so scope in the common part transfers the typing, unfolding and
recursor laws. The block facts transfer for the same reason, with
assembly supplying the generated entries in $C$. This
#src("whitepaper/Fragment/ModularModel.lean", 452, 459)[proves amalgamation].
Proofs stay the point: a definition or an assumption of $C$ is a
definition or an assumption of a member, of the same type, read alike
(#src("whitepaper/Fragment/ModularModel.lean", 573, 577)[the amalgam keeps proofs the point]).
Assembly also #src("whitepaper/Fragment/ModularModel.lean", 693, 695)[makes $C$ closed]:
its stored terms are in scope and its rules name stored constructors,
because each common part is contained in $C$.

*The conservative step.* Definitions and blocks use the installation
results of §3 and §4. A
#src("whitepaper/Fragment/Decl.lean", 608, 618)[theorem $c : T := v$]
passes the definition check and additionally has a propositional type:
$tack T => S red Sort u$ for some type $S$ and level $u$ with $u eq.dot 0$. It is stored as an
assumption of $T$. Installing the checked definition and then
forgetting its value
#src("whitepaper/Fragment/InstallThm.lean", 249, 255)[extends every model],
assigning the theorem the set of its proof.

Declaration data are a sequential list.
#src("whitepaper/Fragment/ModularInstance.lean", 54, 56)[Acceptance]
requires a closed context and the checks of §3 and §4 (or the theorem
check) at each successive declaration. A definition's or theorem's
set is its value's,
#src("whitepaper/Fragment/ModularModel.lean", 110, 113)[at every list of levels],
even those of the wrong length; the typing law alone constrains only
correctly sized lists. Where its type reads as a truth value, the
value lies in it, so the set is the point. Sequential installation
therefore gives
#src("whitepaper/Fragment/ModularModel.lean", 261, 265)[the conservative step],
preserving old values and keeping proofs the point.

#remark(name: "A syntactic illustration")[
  The #src("whitepaper/Fragment/ModularSyntactic.lean", 89, 92)[models]
  may instead be realisations by terms of a fixed ground theory:
  each constant is assigned a term of its realised type, equal to
  its realised value when a definition. Compatible realisations
  #src("whitepaper/Fragment/ModularSyntactic.lean", 188, 195)[amalgamate]
  by choosing, for each name, the term of a member storing it. The
  #src("whitepaper/Fragment/ModularSyntactic.lean", 131, 134)[step]
  realises a fresh definition by its value under the old realisation;
  a substitution lemma gives its typing. This
  #src("whitepaper/Fragment/ModularSyntactic.lean", 223, 249)[instance]
  handles definitions only, and recognises no proofs, so copies agree
  only by being read from one module. It illustrates
  the interface; connecting a syntactic consistency proof of Lean
  would require a separate argument, including the shared proof value.
]

== The local checks <sec:mod-local>

For this instance,
#src("whitepaper/Fragment/ModularModel.lean", 776, 777)[$E_i = Gamma_i + D_i$],
the context extended by the declaration list. Each module $i$ presents
a set of views $cal(V)_i$, imports earlier modules, and names for each
context name the module it is read from, its rank and the part below it;
its imported views are
#src("whitepaper/Fragment/ModularModel.lean", 779, 782)[every view of every import],
paired with the module presenting it. The
#src("whitepaper/Fragment/ModularModel.lean", 829, 847)[checks divide by who runs them]:

- At the presenting module, check that each view refines its own
  environment. This runs once, however many modules import it.
- At the importer, check that imports are earlier, that the context is
  assembled from their views, and that every context name is
  #src("whitepaper/Fragment/ModularModel.lean", 812, 820)[read],
  with every copy agreeing. This uses the context, the views and how
  the imports read their own context names; it needs no import's own
  environment.
- For the declarations, check sequential acceptance.

Write $Pass_i$ for the three checks together. These concrete
checks #src("whitepaper/Fragment/ModularInstance.lean", 148, 159)[imply abstract validity]:
$
  (forall j <= i. thin Pass_j) ==> Valid_i.
$
The imports' view checks supply the refinement of imported views, and
context assembly supplies closure. Thus @def:valid applies, and
@thm:mod #src("whitepaper/Fragment/ModularInstance.lean", 178, 181)[gives compatible models]:
every module gives each context name the set of the module it is read
from, and every proof the point.

The theorem is stated over the input, as @thm:accepted-model is. A
module $j$ _sees_ a name $c$ as module $j'$'s when
#src("whitepaper/Fragment/ModularInstance.lean", 170, 171)[$c$ is a context name of $j$ and a view of $j'$ that $j$ imports stores $c$]:
$
  c in Gamma_j and exists V. thin (j', V) in X_j and c in V.
$
The fragment has no import rules: $X_j$ is given, and the local checks
say what it must satisfy. So seeing is read off the imported views,
which are the parts of other modules that $j$ loads, and it covers
both agreements a module's reading needs: the module $From_j (c)$ a
name is read from is seen, and so is every other module whose view
holds a copy of it.

#theorem(name: "Every module has a model of its constants")[
  For every $k in NN$, assume $Pass_j$ for every module $j < k$. Then
  there are assignments $M_j$, for $j < k$, such that
  #src("whitepaper/Fragment/ModularInstance.lean", 204, 207)[$M_j$ is a model of the constants of $D_j$]
  (@def:input-model), and every name $c$ that $j$ sees as $j'$'s, for
  $j, j' < k$, has one value in both:
  $
    c in Gamma_j and (exists V. thin (j', V) in X_j and c in V)
      ==> M_j (c) = M_(j') (c).
  $
] <thm:mod-input>

#proof[
  Take the compatible family of @thm:mod and let $M_j$ be the
  assignment of $m_j$. The step installs $D_j$ as §3 and §4 do, and
  #src("whitepaper/Fragment/ModularInstance.lean", 178, 181)[its models carry the clauses of @def:input-model]
  for every stored constant, amalgamation and restriction included,
  so every constant of $D_j$, stored in $E_j$ as declared, holds in
  $M_j$. Compatibility gives $m_j (c) = m_(From_j (c)) (c)$, and the
  same value at every imported view storing $c$.
]

Let $B$ be the empty Prop block of @cor:consistency, with no level
parameters, parameters, indices or constructors, and with large
elimination. Let the modules up to $i$ pass their checks, so that
@thm:mod-input with $k = i + 1$ gives the constants of $D_i$ a model.
If they include $B$'s recursor, then,
by the argument of @cor:consistency over
#src("whitepaper/Fragment/Main.lean", 59, 62)[any model of such constants],
none of them has type $I_B$: no theorem of $D_i$ proves the empty
proposition.

A context need not be everything a module loads. Let $Gamma'$ store
some of $Gamma_i$'s entries, each as $Gamma_i$ does, and let what the
laws of each read lie in $Gamma'$ itself. Then $Gamma'$
#src("whitepaper/Fragment/ModularModel.lean", 648, 651)[is assembled from the same views],
and its names are read as $Gamma_i$'s are; so
#src("whitepaper/Fragment/ModularModel.lean", 851, 854)[a closed part of the context]
may stand for the context in $Pass_i$. A checker may therefore check a
module over the part of its context its own declarations reach,
following types, the values a view retains and the rules of reached
recursors, and stopping at every assumption.


== What runs in parallel

The local checks read a module, its imports' views and how they read
their context names, so modules can be checked together once those
data are available. Acceptance still requires every relevant module to
pass. The
#src("whitepaper/Fragment/ModularSemantics.lean", 280, 344)[model construction]
has the same dependencies: restrict the imports' models, amalgamate,
and extend for checked declarations. Its compatibility proof uses
the earlier family too, but the numbering adds no inputs to the
construction of a module's model.

== Lean's module system in these terms <sec:mod-lean>

The table maps Lean's module system to the notions above. An exported
level need not be self-contained; a view used in assembly must
satisfy the scope conditions.

#table(
  columns: (1fr, 1fr),
  stroke: none,
  table.header[*Lean*][*Here*],
  [An exported level, with the imported dependencies of retained
    types and values],
  [A view retaining entries whose laws have the required dependencies;
    a value may be hidden while its type is kept],
  [The private level, available under `import all`],
  [Full own declarations; with their context, they can supply the own
    environment as a view],
  [The language server's level], [No role in the argument],
  [Imports and modules reached through `public import` re-exports],
  [The modules supplying the imported views],
  [The environment built from the loaded levels], [The context $Gamma_i$],
  [An unavailable theorem proof or hidden definition value],
  [An assumption of the same type],
  [A module loaded through two imports], [One copy, read through two paths],
  [Copies merged on import, allowed for theorems of the same statement],
  [Copies that agree as proofs of one statement],
  [Declarations of one name never loaded together],
  [Copies no module reads together; nothing asks them to agree],
  [A private name `_private.…`], [An ordinary name, read from the module
    that declares it],
  [An exported entry mentioning a constant that neither its module's exported level nor a
    module of that module's `public import` closure holds],
  [The export completed where it was made: the importer reads, in addition, the view of
    the module the exporting module loads first holding that constant, as an assumption (an
    inductive type with its block), and that copy is read like a loaded one],
  [`backward.privateInPublic`, which exports private constants with their values],
  [Entries like any other],
)

#real[
  The checks are stated over con-leche's own records
  (#src("ConLeche/Modular.lean", 209, 229)[the local checks]): a context is a
  list of records each of which an earlier module
  #src("ConLeche/Modular.lean", 82, 92)[presents], as itself or as its
  statement, so an inductive type reaches an importer with its whole block;
  every context name is read from one module; what a context record reads
  is stored in the context. A record of module $h$ means by a name it reads
  the copy $h$'s export holds: $h$'s own, or that of a module of $h$'s
  `public import` closure exporting it; a name neither holds is completed
  from $h$'s view, on demand, for the names the context reads and every copy
  of every clashing name it stores. The importer's check is that rule: a read
  passes when the context's copy is that one, and otherwise the copy $h$'s
  view locates must agree with the context's. So the copy $h$'s view locates
  for each such name
  #src("ConLeche/Modular.lean", 168, 192)[agrees] with the context's: it is
  the copy of the module the name is read from, or one record loaded through two paths, or both are proofs
  of one statement whose names agree: an earlier module's copy of it, its
  names agreeing too, is a theorem, or else its type is inferred to be a
  proposition over the records before the name's; every record reads only itself and earlier
  records; and the module's own records are accepted from the context by the
  declaration fold's own step.
  The theorem over the interface,
  #src("ConLeche/Modular/Generic.lean", 278, 279)[for any instance], is
  @thm:mod.
]
