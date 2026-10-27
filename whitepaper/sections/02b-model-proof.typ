#import "../lib.typ": *

// Notation local to this file, matching the first half of the section.
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let red = sym.arrow.r.squiggly
#let elet = $sans("let")$
#let eqlam = $scripts(equiv)_lambda$
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
#let PiV = $Pi^sans("v")$
#let LamV = $Lambda$
#let TyU = $cal(T)$
// The denotation brackets ⟦ ⟧, used in math as `lden e rden_rho`.
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

== The set theory we assume <sec:lib>

The other side of the argument is a set theory. We do not construct
one. The reader is given an axiomatised theory, a type of sets with
the operations and laws listed below, and is promised that nothing
beyond these laws is used. The theory is stated in Lean's own logic,
so it is higher-order: separation takes any predicate of that logic,
and graphs and function spaces are formed from any function of it.
It is deliberately not minimal: graphs, dependent function spaces and
the universe chain, which a minimal axiom system would construct, are
assumed outright with their laws, because how they are built does not
matter to the argument. The promise is literal: in the Lean fragment
the structure is a class,
#src("whitepaper/Fragment/Lib.lean", 56, 126)[#lean[SetLib]], and every theorem of the
fragment is proved against that class.

#real[
  The real proof is parametric in
  #src("ConLeche/SetTheory/Core.lean", 95, 100)[a smaller interface],
  ZF without infinity plus a chain of Grothendieck universes (sets
  closed under all the set-forming operations), from which it derives
  the operators below.
]

The laws come in four groups.

*Sets, membership, extensionality, separation.* A type $V$ of sets
with a membership relation $x in y$;
#src("whitepaper/Fragment/Lib.lean", 64, 65)[extensionality]: two sets with the same members are equal; and
#src("whitepaper/Fragment/Lib.lean", 66, 69)[separation]: for every set $A$ and every property $P$ of sets, a set
${x in A | P(x)}$ whose members are the members of $A$ that satisfy
$P$. A property here is any predicate on sets expressible in Lean's
type theory, the logic the theory is stated in, not only a
first-order formula.

*The point and the truth values.* A distinguished set $pt$, _the
point_, and
#src("whitepaper/Fragment/Lib.lean", 73, 76)[its singleton ${pt}$]. The point will be the one proof of every true
proposition. For a proposition $P$ of the ambient logic we write
$tv(P)$ for the separation ${x in {pt} | P}$ and call it
#src("whitepaper/Fragment/Lib.lean", 142, 144)[the _truth value_ of $P$]. Its only possible member is the
point, which it has exactly when $P$ holds, so $tv(P) = {pt}$ when
$P$ is true and $tv(P) = emptyset$ when it is false. This is an
abbreviation, not an axiom. The point itself obeys
#src("whitepaper/Fragment/Lib.lean", 120, 126)[three laws]: it is not a
truth value (it has a member other than itself), it has at most one
member, and no graph (below) is a member of it.

#real[
  The point is
  #src("ConLeche/SetTheory/Derive/Pt.lean", 68, 69)[the singleton]
  of #src("ConLeche/SetTheory/Derive/Pt.lean", 44, 46)[the set $\{emptyset, \{\{emptyset\}\}\}$],
  chosen so that no encoding of a value of a data type produces it;
  the three laws are theorems there.
]

*The universes.* A #src("whitepaper/Fragment/Lib.lean", 77, 85)[chain of sets] $cal(U)_0, cal(U)_1, cal(U)_2, dots$,
with $cal(U)_0$ the set of truth values, the subsets of ${pt}$. Each
$cal(U)_n$ is a member of $cal(U)_(n+1)$. The chain is cumulative (a
member of $cal(U)_m$ is a member of every later $cal(U)_n$), and every
universe is
#src("whitepaper/Fragment/Lib.lean", 118, 119)[closed under separation].

*Graphs, function spaces, application.* For a function $F$ from sets
to sets (a function of the meta-theory, not a set) and a set $A$, a
set $graph(F, A)$; for a set $A$ and a family $B$ of sets indexed by
sets, again a function of the meta-theory, a set $Pi(A, B)$, the
_dependent function space_; and for two sets $f$ and $a$ a set
$f dot.op a$, #src("whitepaper/Fragment/Lib.lean", 86, 93)[the
_application_]. Their laws:

- $pt dot.op a = pt$: #src("whitepaper/Fragment/Lib.lean", 94, 95)[a proof applied to anything is the proof].
- #src("whitepaper/Fragment/Lib.lean", 96, 97)[β]: if $a in A$ then $graph(F, A) dot.op a = F(a)$.
- $graph(F, A) != pt$: #src("whitepaper/Fragment/Lib.lean", 98, 99)[a graph is never the point].
- #src("whitepaper/Fragment/Lib.lean", 100, 103)[Congruence]: $graph(F, A)$ depends only on the values of $F$ on $A$,
  and $Pi(A, B)$ only on the values of $B$ on $A$.
- #src("whitepaper/Fragment/Lib.lean", 104, 106)[Introduction]: if $F(x) in B(x)$ for every $x in A$, then
  $graph(F, A) in Pi(A, B)$.
- #src("whitepaper/Fragment/Lib.lean", 107, 108)[Elimination]: if $f in Pi(A, B)$ and $a in A$, then $f dot.op a in B(a)$.
- #src("whitepaper/Fragment/Lib.lean", 109, 110)[η]: if $f in Pi(A, B)$, then $graph(x |-> f dot.op x, A) = f$.
- #src("whitepaper/Fragment/Lib.lean", 111, 113)[Domain uniqueness]: if $f in Pi(A, B)$ and $f in Pi(A', B')$, then
  $A = A'$.
- #src("whitepaper/Fragment/Lib.lean", 114, 117)[Closure]: for $n != 0$, if $A in cal(U)_n$ and $B(x) in cal(U)_n$ for
  every $x in A$, then $Pi(A, B) in cal(U)_n$.

This is all this section needs. When inductive types arrive, §4
extends the theory.

Two of these laws are design choices. The first is that _application
of the point is the point_. In the model a proof of a proposition is
the point, and a proof of $forall x : A. thin P$ is again the point,
not a function. The law makes application one operation that does the
right thing on both kinds of value, so the interpretation of
$f thick a$ need not know which kind it is applying. The second is
that _a graph is never the point_: a function and a proof are never
the same set. A value that is known to be in a function space, or
merely known not to be the point, is therefore a graph, and by domain
uniqueness a graph carries its own domain. This is what lets β fire
with no premise at all.

One law is deliberately restricted: closure of a universe under
function spaces is stated for $cal(U)_1, cal(U)_2, dots$ and not for
$cal(U)_0$. A proposition $forall x : A. thin P$ has no function space
in the model. It has a truth value, and a truth value is in
$cal(U)_0$ whatever $A$ is. This is
#src("whitepaper/Fragment/Lib.lean", 275, 278)[the model's impredicativity].

== The interpretation <sec:interp>

Every term denotes a set. The interpretation is _total_, defined on
every term, well-typed or not, and _term-directed_: it is a structural
recursion on the term, consulting no derivation and no type. It takes
two parameters:

- a valuation $phi$ of the level parameters (@sec:levels);
- a _variable environment_ $rho$, assigning a set to every variable in
  scope.

We write $lden e rden_rho$ for the set the term $e$ denotes under $rho$
($phi$ stays implicit), and $rho, x |-> v$ for $rho$ extended
with the value $v$ for the variable $x$. #src("whitepaper/Fragment/Interp.lean", 138, 146)[The clauses]:

$
  lden x rden_rho & = rho(x) \
  lden Sort u rden_rho & = TyU_(phi(u)) \
  lden f thick a rden_rho & = lden f rden_rho dot.op lden a rden_rho \
  lden lambda x : A. thin b rden_rho & = LamV(lden A rden_rho, med v |-> lden b rden_(rho, x |-> v)) \
  lden forall x : A. thin B rden_rho & = PiV(lden A rden_rho, med v |-> lden B rden_(rho, x |-> v)) \
  lden elet x : T := v; thin b rden_rho & = lden b rden_(rho, x |-> lden v rden_rho)
$

with $phi(u)$ the value of the level $u$ at the valuation, and $TyU_n$
the sets a sort denotes, below. The two binder clauses
#src("whitepaper/Fragment/Lib.lean", 469, 481)[choose between two readings by the values]:

$
  PiV(A, B) & = cases(
    Pi_0(A, B) & "if" B(v) "is a truth value for every" v in A\,,
    Pi(A, B) & "otherwise;") \
  LamV(A, F) & = cases(
    pt & "if" F(v) = pt "for every" v in A\,,
    graph(F, A) & "otherwise.")
$

Here $Pi_0(A, B)$ is
#src("whitepaper/Fragment/Lib.lean", 185, 191)[the _propositional function space_],
$tv(forall v in A. thin B(v) = {pt})$. When the fibres $B(v)$ are
truth values it is their intersection $inter.big_(v in A) B(v)$ (the
empty intersection being ${pt}$), which is ${pt}$ exactly when every
fibre is and $emptyset$ otherwise: the function space of subsets of a
singleton.
A `let` reads its body at the value's value, and its type is not read,
as no type is read anywhere.

So a binder has two readings. When the body is not a proposition, a
lambda is a graph and a $forall$ is a set of such graphs, a function
space. When it is, a lambda is a proof, hence the point, and a
$forall$ is a proposition, true when every _fibre_ (the set
$lden B rden_(rho, x |-> v)$ at a $v in lden A rden_rho$) is ${pt}$.
Which reading applies is decided by the values the body takes over the
domain, and by nothing else. The interpretation does not know the sort
of $B$, and does not compute it.

*The empty domain.* Over a non-empty domain the values choose the
reading the sort of the body would choose. Over an _empty_ domain
there are no values, and both clauses take their first case: a
function space over an empty domain
#src("whitepaper/Fragment/Lib.lean", 625, 631)[is ${pt}$], and an abstraction over one
#src("whitepaper/Fragment/Lib.lean", 633, 635)[is the point], whatever
the sort of the body. So `False → Nat`, a type of sort `Type`, denotes
${pt}$, and its inhabitant `fun h => h.elim` denotes the point. A
function space over an inhabited domain can do the same:
`Nat → False → Nat` has ${pt}$ as every fibre and is
#src("whitepaper/Fragment/Probe.lean", 52, 54)[itself ${pt}$], and
`fun n h => h.elim` is the point. No other reading over the empty
domain does better. Whether the codomain is a proposition there is a
fact about the syntax, not about any value, and reading an empty
Π-type as a function space instead would make the proposition
`False → False` denote a one-element set of graphs, which no truth
value is.

*What a sort denotes.* A set is a
#src("whitepaper/Fragment/Lib.lean", 298, 302)[_type_] when it is a truth value or
_strict_, that is, neither the point nor a set holding the point. The
members of a type are
#src("whitepaper/Fragment/Lib.lean", 359, 364)[all the point or none of it],
and this is the one fact about types the soundness proof reads. A sort
denotes
#src("whitepaper/Fragment/Lib.lean", 304, 306)[the types of its universe]:
$TyU_0 = cal(U)_0$, the truth values, and $TyU_n$ for $n >= 1$ the
members of $cal(U)_n$ that are types. These are cumulative, and
$TyU_(n+1)$ holds the truth values too. It must, since a function
space over an empty domain is ${pt}$,
#src("whitepaper/Fragment/ValueReading.lean", 58, 63)[which is no strict set].
The point is no type, so no sort holds it.

#real[
  Con-leche's sorts denote the same sets:
  #src("ConLeche/SetTheory/Derive/Univ.lean", 34, 35)[a sort's universe]
  is #src("ConLeche/SetTheory/Derive/TypeU.lean", 214, 216)[the universe of types],
  read off the same notions of a
  #src("ConLeche/SetTheory/Derive/TypeU.lean", 57, 58)[strict set] and a
  #src("ConLeche/SetTheory/Derive/TypeU.lean", 60, 61)[type].
]

This is the whole of the interpretation. Nothing had to be
well-typed, no typing judgement was consulted, and there is no
partiality to discharge. The next subsection says what replaces
typing. Three lemmas about the interpretation are needed later, each
proved by induction on the term.
#src("whitepaper/Fragment/Interp.lean", 242, 246)[Substituting a term for a variable] is extending
the environment with the term's value,
$lden b[x := a] rden_rho = lden b rden_(rho, x |-> lden a rden_rho)$;
hence #src("whitepaper/Fragment/Interp.lean", 248, 253)[a `let` denotes what its $zeta$-reduct denotes],
at every environment; and #src("whitepaper/Fragment/Hygiene.lean", 464, 467)[a term does not
see a variable it does not mention].

== The semantic invariant <sec:inv>

There is no typing judgement in the proof. In its place is a predicate
on terms, the _semantic invariant_: a term is #src("whitepaper/Fragment/WellDenoted.lean", 55, 78)[_well-denoted_] when its
applications and binders respect domains. It is stated under a
valuation $phi$ and an environment $rho$, like the interpretation, by
recursion on the term: it holds of a term when it holds of the
subterms and one condition on the term's own shape is met. We write
$rho models e$ for "$e$ is well-denoted under $rho$" ($phi$ is fixed
throughout). Variables and sorts are always well-denoted, and

#rules(
  rule(name: "app",
    $rho models f$, $rho models a$,
    $lden f rden_rho in P$,
    $lden a rden_rho in A'$,
    $rho models f thick a$),
  rule(name: "let",
    $rho models v$, $rho, x |-> lden v rden_rho models b$,
    $rho models elet x : T := v; thin b$),
)
#rules(
  rule(name: "lam",
    $rho models A$, $lden A rden_rho "a type"$,
    $forall v in lden A rden_rho. thin rho, x |-> v models b \
     forall v in lden A rden_rho. thin lden b rden_(rho, x |-> v) in B(v) "a type"$,
    $rho models lambda x : A. thin b$),
  rule(name: "pi",
    $rho models A$, $lden A rden_rho "a type"$,
    $forall v in lden A rden_rho. thin rho, x |-> v models B \
     forall v in lden A rden_rho. thin lden B rden_(rho, x |-> v) "a type"$,
    $rho models forall x : A. thin B$),
)

In app, $P$ is either a function space $Pi(A', B')$ whose domain $A'$
is a type, or a propositional function space $Pi_0(A', B')$ whose
fibres are truth values. In lam, $B$ is some family of types bounding
the body's values, its _codomain_. In words: an application applies a
function, or a proof of a propositional $forall$, to a member of its
domain; a binder's domain is a type; a lambda's values lie in a
bounded family of types, and a $forall$'s fibres are types. The
invariant records which sets are types, and that is what makes the
choice between the two readings agree with membership. An abstraction
is #src("whitepaper/Fragment/Lib.lean", 552, 558)[a member of the function space]
of a family of types bounding its values: if every fibre is a truth
value, every value is the point and so is the abstraction; if one
fibre is not, it is strict, the body's value there is not the point,
and the abstraction is the graph.

The semantic invariant is #src("whitepaper/Fragment/WellDenoted.lean", 196, 199)[transported by substitution]: $b[x := a]$ is
well-denoted under $rho$ exactly when $b$ is well-denoted under
$rho, x |-> lden a rden_rho$, provided $a$ itself is. The proof is by
induction on the term, using the interpretation's substitution
lemma; no typing derivation is involved.

A context $Gamma$, the list of the types of the variables in scope,
is #src("whitepaper/Fragment/WellDenoted.lean", 252, 259)[_satisfied_] by $rho$ when every entry is well-denoted under the
environment beyond it, denotes a type there, and has the variable's
value as a member.
This is the semantic reading of "$Gamma$ is a well-formed context", and
it is the only thing the claims below assume about the context.

The first non-routine step is β. Take a well-denoted redex
$(lambda x : A. thin b) thick a$. From the application rule we know
that the lambda's value lies in some $P$ whose domain $A'$ contains
$lden a rden_rho$; from the lambda rule we know that the body is
bounded over $lden A rden_rho$. For the β law we need
$lden a rden_rho in lden A rden_rho$, the argument in _the lambda's own_
domain, and the semantic invariant has given us $A'$, not $A$.

#lemma(name: [β where the redex is not the point])[
  If $(lambda x : A. thin b) thick a$ is well-denoted under $rho$ and
  does not denote the point, then
  $lden (lambda x : A. thin b) thick a rden_rho = lden b[x := a] rden_rho$
  and $b[x := a]$ #src("whitepaper/Fragment/Sound.lean", 107, 132)[is well-denoted under $rho$].
] <lem:beta>

#proof[
  The application is not the point, so neither is the lambda, since
  $pt dot.op a = pt$. An abstraction that is not the point is
  a graph, $graph(v |-> lden b rden_(rho, x |-> v), lden A rden_rho)$.
  A graph is never the point, so the application's $P$ is a
  function space $Pi(A', B')$, not a propositional function space. The
  lambda's own rule puts the same graph into
  $Pi(lden A rden_rho, B)$ by introduction, and domain
  uniqueness gives $A' = lden A rden_rho$; so $lden a rden_rho in lden A rden_rho$,
  and the β law computes the application to
  $lden b rden_(rho, x |-> lden a rden_rho)$, which is $lden b[x := a] rden_rho$ by
  the substitution lemma. The semantic invariant of the reduct is the
  substitution transport.
]

For a redex that does denote the point there is no such lemma. Its
lambda may be the point, which carries no domain, and its argument
may lie anywhere. Such a redex is well-denoted, and its reduct need
not be:
#src("whitepaper/Fragment/EtaIota.lean", 707, 724)[$(lambda x : A. thin g thick (k thick x)) thick a$],
with a lambda that is the point and an argument $a$ outside the
domain $A$ of the graph $k$, reduces to $g thick (k thick a)$, which
is not well-denoted. So the reduction claim below says nothing about
a term that denotes the point, and β needs no premise. @sec:claims
shows that the other rules need no more than such a claim.

*Why no sort holds the point.* The claims below rely on one fact: an
inferred type is a type, so it is never the point. It also keeps β
sound on stored values. A stored constant $c : Sort 1$ whose value is
the ill-typed redex
$(lambda h : (forall P : sans("Prop"). thin P). thin h) thick sans("Prop")$
reduces by δ and β to $sans("Prop")$. The redex denotes the point
(its lambda is an abstraction over an empty domain), and
$sans("Prop")$ does not. Such an environment
#src("whitepaper/Fragment/UniformBeta.lean", 76, 80)[has no model]: the
constant's set would have to be the point and a member of
$TyU_1$, which holds no point.

== The three claims and their proof <sec:claims>

#theorem(name: "Soundness of the three relations")[
  Fix a valuation $phi$ and let $rho$ satisfy $Gamma$. Then:
  + reduction preserves the denotation and the semantic invariant of
    a term that is not the point: if $Gamma tack e red e'$, $e$ is
    well-denoted and $lden e rden_rho != pt$, then $e'$ is
    well-denoted and $lden e rden_rho = lden e' rden_rho$;
  + equality means equal sets where neither side is the point: if
    $Gamma tack a equiv b$, both $a$ and $b$ are well-denoted and
    neither denotes the point, then $lden a rden_rho = lden b rden_rho$;
  + inference establishes the semantic invariant and a membership: if
    $Gamma tack e => T$, then $e$ and $T$ are well-denoted, $lden T
    rden_rho$ is a type, and $lden e rden_rho in lden T rden_rho$.
  (The theorem is #src("whitepaper/Fragment/Sound.lean", 2322, 2326)[`soundness`], with
  #src("whitepaper/Fragment/Motive.lean", 51, 84)[the three claims stated].)
] <thm:sound>

Reduction and equality assume the semantic invariant; inference
establishes it. The inference rules are the ones that check a term's
shape, so their soundness proves that the term's applications and
binders respect domains; the other two relations are handed
well-denoted terms and pass the semantic invariant along. The first
two claims are also conditional on the point: they say nothing about
a term that denotes it.

*Why the claims may say nothing about the point.* A claim that is
silent about the point is only useful if every rule that uses a
premise's claim has that premise not the point, or does not need the
claim there. Every rule falls into one of four cases.

+ _The subject is a type, never the point._ The reductions of an
  inferred type to a sort or a $forall$ (in the binder rules, in app,
  in $eta$, in proof irrelevance), the comparisons of two types (an
  argument's type with a domain in app, a domain with a domain in
  the congruences, the checker's type comparisons in $iota$), the
  fibres compared in $forall$-congruence. The third claim made each
  subject a type, so the conditional claim applies outright.
+ _The subject is not the point by hypothesis._ trans passes the
  first claim's denotation on to the second; head reduces the head of
  an application that is not the point, which is therefore not the
  point either; red-l reduces a side of an equality that is not the
  point; app compares the heads of two applications that are not the
  point.
+ _The two sides share a type, so they are both the point or
  neither._ app's arguments: the heads are one graph, whose domain is
  a type and holds both arguments. ι's comparisons and its major
  premise (@sec:ind) are of the same kind. The bodies of
  lambda congruence and $eta$ are the one place where nothing else
  supplies a common type, and that is why those rules compare the
  bodies' types (@sec:tax).
+ _The step is an identity everywhere._ β on a redex that is not the
  point (@lem:beta), $zeta$ and δ (@sec:env) claim nothing beyond what
  holds at every environment.

#corollary[
  If the checker infers $tack e => T$ in the empty context, then $lden e rden_rho in lden T rden_rho$ #src("whitepaper/Fragment/Sound.lean", 2330, 2333)[at every valuation]
  and every $rho$.
] <cor:closed>

This is the statement the environment section builds on: a
declaration is accepted when its value's inferred type is
definitionally equal to its declared type, and the corollary, with the
second claim, puts the value's set into the declared type's set.

*Proofs that are not proofs.* The proof asks whether a term's value is
the point, never whether the term is a proof in Lean's sense (except
in the proof-irrelevance rule, whose claim turns out to be empty), and
it learns that only through a type the term lies in. So a term whose
value is the point is treated like a proof whatever the sort of its
type, also when its value is the point
#src("whitepaper/Fragment/Probe.lean", 65, 72)[only at some values of a variable].

The three claims are proved together, by #src("whitepaper/Fragment/Sound.lean", 2202, 2311)[one structural induction] over
the three mutually inductive relations (#src("ConLeche/Model/Rules/Sound.lean", 51, 52)[as in con-leche]).
Every rule is one case, and every case is a lemma about that rule
alone, with the induction hypothesis for each premise as an assumption.
The routine cases are listed at the end; the others follow.

#proof[
  *#src("whitepaper/Fragment/Sound.lean", 111, 132)[Rule beta]*, $(lambda x : A. thin b) thick a red b[x :=
  a]$: \
  This is @lem:beta. The rule has no premise, and the lemma needs
  none, because the claim is asked only where the redex is not the
  point.

  *#src("whitepaper/Fragment/Sound.lean", 134, 142)[Rule zeta]*, $elet x : T := v; thin b red b[x := v]$: \
  The two sides denote the same set at every environment, the point
  included, and the reduct's semantic invariant is the `let`'s,
  through the substitution transport.

  *#src("whitepaper/Fragment/Sound.lean", 165, 171)[Rule red-l]*, $Gamma tack a equiv b$ from $Gamma tack a red a'$ and
  $Gamma tack a' equiv b$: \
  $a$ is not the point, so by the first claim $a'$ is well-denoted
  and $lden a rden_rho = lden a' rden_rho$. Now $a'$ and $b$ are both
  well-denoted and neither is the point, so the second claim applies
  to the continuation, and the two equalities chain. This is the one
  sound way to chain in the equality relation, because a reduction
  step _produces_ the semantic invariant of its result; see the
  discussion of transitivity below.

  *#src("whitepaper/Fragment/Sound.lean", 173, 175)[Rule sort]*, $Sort u equiv Sort v$ when $u eq.dot v$: \
  The oracle is assumed correct: it answers yes only if the levels
  agree at every valuation (@sec:levels), so the two sorts denote the
  same set.

  *#src("whitepaper/Fragment/Sound.lean", 181, 198)[Rule pi]*, $forall x : A_1. thin B_1 equiv forall x : A_2. thin B_2$ from
  $Gamma tack A_1 equiv A_2$ and $Gamma, x : A_2 tack B_1 equiv B_2$: \
  Both $forall$s are well-denoted, so their domains are types, never
  the point, and the second claim on the domains gives
  $lden A_1 rden_rho = lden A_2 rden_rho$. At every $v$ in that domain
  the fibres are types too, so the claim on the bodies makes them
  equal. A $forall$'s set is a function of its domain's set and its
  fibres, the choice of reading included, since that is read off the
  fibres; so the two $forall$s are equal. No comparison of the two
  sides' sorts is needed.

  *#src("whitepaper/Fragment/Sound.lean", 200, 220)[Rule lam]*, $lambda x : A_1. thin b_1 eqlam lambda x : A_2. thin b_2$ from
  the domains, the bodies, and the bodies' types $t_1 equiv t_2$: \
  The domains are equal as for $forall$. Fix $v$ in the domain. The
  third claim puts $lden b_1 rden$ in $lden t_1 rden$ and $lden b_2
  rden$ in $lden t_2 rden$ (at $rho, x |-> v$), both types, and the
  second claim on the types, which are not the point, makes them one
  type. Its members are all the point or none, so either both bodies
  are the point, or neither is and the claim on the bodies makes them
  equal. Either way they are equal at every $v$, and so are the two
  abstractions, whether or not either of them is the point. The claim
  is therefore unconditional; lam-outer passes such a claim outwards
  (@sec:tax), and lams weakens it to the second claim. Without the
  type premises the argument breaks at "both or neither": a body may
  be the point at some $v$ and not at others, and the claim on the
  bodies says nothing at such a $v$.

  *#src("whitepaper/Fragment/Sound.lean", 233, 254)[Rule app]*, $f_1 thick a_1 equiv f_2 thick a_2$: \
  Neither application is the point, so neither head is, and the claim
  on the heads makes them one graph. Each application's rule puts its
  head in some $P$, with its argument in $P$'s domain. A graph is in
  no propositional function space, so each $P$ is a function space,
  and domain uniqueness puts both arguments in one domain, a type.
  They are both the point, or neither is and the claim on the
  arguments makes them equal.

  *#src("whitepaper/Fragment/Sound.lean", 391, 436)[Rule fun-eta]*, $lambda x : A_1. thin b_1 equiv b$ when
  $Gamma tack b => T red forall x : A_2. thin B$,
  $Gamma tack A_2 equiv A_1$, $Gamma, x : A_1 tack b_1 equiv b thick x$,
  and the body's type agrees with $B$: \
  $b$ is not the point, so the third claim, then the first, put
  $lden b rden_rho$ in the denotation of the $forall$, which is
  well-denoted; the domains are equal as before. Fix $v$ in the
  domain. The lambda's body lies in its inferred type, which the
  type premise makes the fibre $lden B rden_(rho, x |-> v)$; the term
  $b thick x$ lies there by elimination. In one type, they are both
  the point or neither, and in the second case the claim on the bodies
  makes them equal. So the lambda denotes the abstraction of
  $v |-> lden b rden_rho dot.op v$, and a
  #src("whitepaper/Fragment/Lib.lean", 574, 577)[member of a function space of types is the abstraction of its applications].

  *#src("whitepaper/Fragment/Sound.lean", 579, 589)[Rule proof-irrel]*, $a equiv b$ when $Gamma tack a => T_a => S_a red Sort u$
  with $u eq.dot 0$, and likewise for $b$: \
  By the third claim twice and the first once, $lden a rden_rho in
  lden T_a rden_rho in TyU_0$, a truth value, whose only possible
  member is the point. So $a$ denotes the point, and the claim, which
  is about sides that are not the point, holds vacuously. The two
  types $T_a$ and $T_b$ were never compared, and the semantic
  invariants of $a$ and $b$ were not used.

  *#src("whitepaper/Fragment/Sound.lean", 292, 306)[Rule pi, inference]*, $Gamma tack forall x : A. thin B => Sort (imax(u,
  v))$ when $Gamma tack A => S red Sort u$ and $Gamma, x : A tack B => T
  red Sort v$: \
  The third claim for $A$ and the first for $S$ put $lden A rden_rho$ in
  $TyU_(phi(u))$, so it is a type, and for every $v' in lden A rden_rho$
  the environment $rho, x |-> v'$ satisfies $Gamma, x : A$; the same
  claims for $B$ put every fibre in $TyU_(phi(v))$. That is the
  $forall$ rule of the semantic invariant, and $PiV(A, B)$
  #src("whitepaper/Fragment/Lib.lean", 595, 601)[lies in $TyU_(phi(imax(u, v)))$].
  If $phi(v) = 0$, every fibre is a truth value, so is $PiV(A, B)$,
  and $phi(imax(u, v)) = 0$. Otherwise $PiV(A, B)$ is a truth value
  or a function space in $cal(U)_(max(phi(u), phi(v)))$ by
  cumulativity and closure, a type either way. $PiV(A, B)$ need not
  be a function space when $phi(v) != 0$: over an empty domain it is
  ${pt}$, and $TyU$ admits it.

  *#src("whitepaper/Fragment/Sound.lean", 308, 329)[Rule lam, inference]*, $Gamma tack lambda x : A. thin b => forall x : A
  . thin B$ when $Gamma tack A => S red Sort u$ and
  $Gamma, x : A tack b => B$: \
  The same argument one level down. The domain is a type, and for
  every $v'$ in it the third claim for $b$ gives $b$ and $B$
  well-denoted, $lden B rden$ a type and $lden b rden in lden B rden$.
  So the family of the $lden B rden$ is a bounded codomain of types,
  which is the lambda rule, and the $forall$ rule of the inferred
  type is met too; and the introduction law for values puts the
  abstraction into $PiV(A, B)$. Nothing about the sort of $B$ is
  needed, so the rule computes none.

  *#src("whitepaper/Fragment/Sound.lean", 331, 349)[Rule app, inference]*, $Gamma tack f thick a => B[x := a]$ when
  $Gamma tack f => T red forall x : A. thin B$,
  $Gamma tack a => T_a$ and $Gamma tack T_a equiv A$: \
  By the third claim, $f$ and $T$ are well-denoted and $lden f rden_rho in lden T rden_rho$;
  $T$ is a type, so by the first claim the $forall$ is well-denoted and
  $lden T rden_rho = lden forall x : A. thin B rden_rho$. By the
  third claim for $a$, $a$ and $T_a$ are well-denoted, $lden T_a rden$ is
  a type and $lden a rden_rho in lden T_a rden_rho$; $A$ is a type by
  the $forall$ rule, so the second claim gives $lden T_a rden_rho =
  lden A rden_rho$ and $lden a rden_rho in lden A rden_rho$. Now $f thick a$ is well-denoted by the
  application rule of @sec:inv, with the $forall$'s denotation as
  $PiV(A, B)$; $B[x := a]$ is well-denoted by the
  substitution transport; and the elimination law puts
  $lden f rden_rho dot.op lden a rden_rho$ into the fibre at $lden a rden_rho$, which
  is $lden B[x := a] rden_rho$ by the substitution lemma.

  A syntactic proof would here invert a derivation of $f : T$ to
  learn the domain and the codomain, using the injectivity of
  $forall$ that @sec:rules discussed. Our proof inverts nothing. The
  checker itself reduced $T$ to a syntactic $forall$, the first claim
  says that the reduction did not change the set, and that set _is_
  $PiV(A, B)$ by the interpretation's rule.

  *#src("whitepaper/Fragment/Sound.lean", 351, 367)[Rule let, inference]*, $Gamma tack elet x : T := v; thin b => B$
  when $Gamma tack b[x := v] => B$ and the checks on the value: \
  The claim for the substituted body is the claim for the `let`: the
  two denote the same set, and the `let`'s semantic invariant is the
  substituted body's, by the transport. The two checks on the value
  are not used. They would be if the body were inferred at a variable
  of type $T$ instead: then the value must
  #src("whitepaper/Fragment/Sound.lean", 369, 385)[lie in the type] to extend a
  satisfying environment, and the checks give that.

  *The rest*, by induction on the derivation.

  - #src("whitepaper/Fragment/Sound.lean", 87, 105)[Reduction]: the no-step reduction is $lden e rden_rho = lden e rden_rho$;
    trans chains two reductions, passing the semantic invariant along;
    head reduces the head of an application that is not the point,
    which is not the point either, and keeps the application's rule,
    because the head's set did not change.
  - #src("whitepaper/Fragment/Sound.lean", 158, 163)[Equality]: refl is again $lden e rden_rho = lden e rden_rho$, and
    sym swaps the two sides.
  - #src("whitepaper/Fragment/Sound.lean", 262, 274)[Inference]: a variable's type is read off the satisfied context; a
    sort's type is the next sort, which contains it.
]

*Why there is no transitivity.* The proof above shows why the rule
"$a equiv b$ and $b equiv c$ give $a equiv c$" cannot be added. The
second claim assumes both sides well-denoted. In a transitivity case
the induction would have to apply the hypothesis to $a equiv b$, and
for that it needs $b$ well-denoted. But $b$ is neither a subterm of
$a$ or $c$ nor produced by a premise, so nothing supplies its
semantic invariant.
#src("whitepaper/Fragment/Rules.lean", 529, 546)[Every other rule] keeps one discipline: each term of an equality
premise is either a subterm of the conclusion (the congruences, the
$eta$ body) or a term that another premise produced, a reduct (red-l)
or an inferred type (lam, $eta$), and the corresponding claim delivers
the semantic invariant of every produced term. The one way to chain
is therefore "reduce, then continue", and that is how the checker's
equality test is structured: it head-normalises a side and compares
again.

== The certification tax <sec:tax>

The checker makes two kinds of check that other checkers for Lean
(the official kernel, Lean4Lean, nanoda) skip. Both come from one
fact: the semantic invariant admits terms that are well-denoted but
not well-typed. A typing judgement would exclude them, and with them
the need for the checks. The semantic proof has no typing judgement,
so the checker verifies the one property the proof would otherwise
take from typing. The two kinds are:

+ *The bodies' types at lambda congruence and $eta$*: inferred by full
  inference and compared, at the innermost level of two
  lambda telescopes only. This subsection explains them.
+ *The constructor application in one case of ι-reduction*: when the
  family of the major premise may be a proposition at the instance
  and the rule is not K-like (one constructor, no fields, in `Prop`;
  @sec:iota-cases), the checker
  #tax[compares the constructor's levels, parameters and index
  expressions with the recursor's], and
  #tax[type-checks every parameter and field of the constructor
  application against the constructor's type]. The official kernel
  makes none of these checks at an ι step; @sec:iota and
  @sec:iota-cases explain them.

#real[
  The checks are the checker's
  #src("ConLeche/Kernel/Core.lean", 1333, 1339)[innermost lambda level],
  #src("ConLeche/Kernel/Core.lean", 483, 488)[its $eta$] and
  #src("ConLeche/Kernel/Core.lean", 851, 865)[the case of ι]. On real
  input neither kind ever fails: they never change a verdict on a
  stream the official kernel accepts. Both run at `--verified` only;
  `--trusted` skips them.
]

*Why lambda congruence needs the bodies' types.* The claim on the bodies
says nothing where a body is the point, and whether a body is the
point can vary with the variable. Without a common type of the two
bodies the rule is unsound in the model. Take
#src("whitepaper/Fragment/ValueReading.lean", 177, 184)[the two lambdas]
$
  lambda (x : sans("Prop")). thin (lambda (h : E thick x). thin h) thick n
  quad "and" quad
  lambda (x : sans("Prop")). thin n,
$
with $E$ sending `True` to `Prop` and `False` to `False`, and $n$
denoting `True`. They have equal domains, and their bodies are equal
by β then refl; both premises are derivations of the checker. Yet at
$x := sans("False")$ the left body is an abstraction over an empty
domain, applied, hence the point, while the right body is `True`. The
two lambdas are well-denoted, neither is the point, and they differ. The
left body is ill-typed ($n$ is no member of $E thick x$), but it is
well-denoted, because the abstraction over $E thick sans("False")$ is
the point and constrains nothing.

*Why other checkers do without it.* Their argument only ever compares
two terms of one type: the caller compared the types, or knows them,
and lambda inversion gives the two bodies a common type, by subject
reduction and uniqueness of types. The model has neither, and the
semantic invariant is satisfied by terms no typing judgement derives,
so the common type is recomputed.

*Innermost only.* The checker compares
#src("whitepaper/Fragment/Rules.lean", 670, 714)[two lambda telescopes level by level], and
infers and compares the bodies' types only at the innermost level,
where the descent through two syntactic lambdas stops (the next
comparison is $eta$, or a reduction, or any other rule). At the outer
levels the domains are compared and nothing else. This is sound
because the type comparison makes the claim at the innermost level
_unconditional_: two bodies in one type are equal at every value of
the variable, the point included. An unconditional equality of the
bodies at every value is an equality of the abstractions, with no
type at all, so #src("whitepaper/Fragment/Sound.lean", 722, 739)[the claim propagates outwards] through
any number of levels. A δ step or a reduction between two levels ends
the telescope, and the level below it is an innermost level again.

*Full inference.* The bodies' types are inferred by full inference
(@sec:infer), not by `infer_only` (@sec:io). With `infer_only` there
is a typed definition at which
#src("whitepaper/Fragment/IOWitness.lean", 444, 456)[every premise of lambda congruence holds]
while the two lambdas differ. Every premise is a derivation of the
relations, so the rule itself is unsound, whatever claim `infer_only`
makes.

== The cheaper mode of inference <sec:io>

The official kernel infers the type of a term it has already checked
by a cheaper mode, `infer_only`. The fragment has
#src("whitepaper/Fragment/IOGrade.lean", 60, 95)[that mode]: the rules
of @sec:infer without app's comparison of the argument's type with
the domain, without the lambda's check of its domain, and without
the check of a let-binding's value against its type.

Its result is not always a type of the term:
$(lambda h : sans("False"). thin (h.sans("elim") : sans("Nat"))) thick 0$
gets the type `Nat`, is well-denoted, and denotes the point (the
lambda is an abstraction over an empty domain), which is no member
of the set `Nat` denotes. What holds is
#src("whitepaper/Fragment/IOGrade.lean", 148, 172)[a hereditary claim]:
the value is the point, or a member of the type, or, when the type is
a $forall$, a graph over its domain whose applications satisfy the
claim at the $forall$'s body. It is
#src("whitepaper/Fragment/IOGrade.lean", 368, 369)[proved for every rule]
of `infer_only`.

The claim serves two consumers. One is proof irrelevance with both
types inferred by `infer_only`
(#src("whitepaper/Fragment/IOGrade.lean", 425, 428)[the rule's case]):
a value whose type has sort `Prop` is the point, the hereditary case
included, because the body of a $forall$ of sort `Prop` has sort
`Prop`. The other is $eta$ against a term whose head is a variable or
a constant, whose claim is
#src("whitepaper/Fragment/IOGrade.lean", 446, 449)[never the hereditary one]
(#src("whitepaper/Fragment/IOGrade.lean", 479, 482)[the rule's case]).
The bodies' types at lambda congruence and $eta$ are not among them, as
@sec:tax showed, so the checker infers those by full inference and
keeps the results of the two modes apart.

#real[
  The checker's cheaper mode is
  #src("ConLeche/Kernel/Core.lean", 1188, 1193)[`infer_only` exactly]. Like it,
  the mode does not check a let-binding's value against its type
  (full inference does, @sec:infer); the soundness proof needs no
  such check, since the value is substituted.
]

== The argument in brief <sec:brief>

Three points of this section run through the rest of the paper. The claims of reduction and
equality are conditional: they say nothing about a term that denotes
the point. The checks of the certification tax are exactly what a
typing judgement would otherwise supply: a common type for the two
sides of a comparison where nothing else gives one. And the proof uses
no subject reduction, no confluence, no injectivity of Π-types and no
unique typing; it needs only the laws of the set theory and the
derivations of the checker's three relations.
