#import "../lib.typ": *

// Notation local to this file, matching the first half of the section.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let always = $sans("always")$
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let zn = $sans("zeroness")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
// The denotation brackets ⟦ ⟧, used in math as `lden e rden_rho`.
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

== The set theory we assume <sec:lib>

The other side of the argument is a set theory. We do not construct
one: the reader is given an axiomatised theory — a type of sets with
the operations and laws listed below — and is promised that nothing
beyond these laws is used. The theory is stated in Lean's own logic,
so it is higher-order: separation takes any predicate of that logic,
and graphs and function spaces are formed from any function of it.
And it is deliberately not minimal: graphs, dependent function spaces
and the universe chain, which a lean axiom system would construct,
are assumed outright with their laws, because how they are built does
not matter to the argument. The promise is literal: in the Lean
fragment the structure is a class,
#src("whitepaper/Fragment/Lib.lean", 44, 99)[#lean[SetLib]], and every theorem of the
fragment is proved against that class.

#real[
  The real proof is parametric in
  #src("ConLeche/SetTheory/Core.lean", 95, 100)[a smaller interface] —
  ZF without infinity plus a chain of Grothendieck universes, sets
  closed under all the set-forming operations — from which it derives
  the operators below.
]

Here are the laws, in four groups.

*Sets, membership, extensionality, separation.* A type $V$ of sets
with a membership relation $x in y$;
#src("whitepaper/Fragment/Lib.lean", 46, 48)[extensionality]: two sets with the same members are equal; and
#src("whitepaper/Fragment/Lib.lean", 49, 52)[separation]: for every set $A$ and every property $P$ of sets, a set
${x in A | P(x)}$ whose members are the members of $A$ that satisfy
$P$. A property here is any predicate on sets expressible in the logic
the theory is stated in — Lean's type theory — not only a first-order
formula.

*The point and the truth values.* A distinguished set $pt$, _the
point_ — any set would do — and
#src("whitepaper/Fragment/Lib.lean", 53, 59)[its singleton ${pt}$]. The point will be the one proof of every true
proposition. For a proposition $P$ — a proposition of the ambient
logic, in which this theory is stated — we write $tv(P)$ for the
separation ${x in {pt} | P}$ and call it
#src("whitepaper/Fragment/Lib.lean", 115, 121)[the _truth value_ of $P$]: a set whose only possible member is the
point, which it has exactly when $P$ holds, so $tv(P) = {pt}$ when
$P$ is true and $tv(P) = emptyset$ when it is false. This is an
abbreviation, not an axiom.

*The universes.* A #src("whitepaper/Fragment/Lib.lean", 61, 67)[chain of sets] $cal(U)_0, cal(U)_1, cal(U)_2, dots$.
$cal(U)_0 = {emptyset, {pt}}$, the two truth values. Each $cal(U)_n$ is a member of
$cal(U)_(n+1)$, and the chain is cumulative: a member of $cal(U)_m$ is
a member of every later $cal(U)_n$.

*Graphs, function spaces, application.* For a function $F$ from sets to
sets and a set $A$, a set $graph(F, A)$; for a set $A$ and a family
$B$ of sets indexed by sets, a set $Pi(A, B)$, the _dependent function
space_; and for two sets $f$ and $a$ a set $f dot.op a$, #src("whitepaper/Fragment/Lib.lean", 69, 75)[the
_application_]. Their laws:

- $pt dot.op a = pt$: #src("whitepaper/Fragment/Lib.lean", 77)[a proof applied to anything is the proof].
- #src("whitepaper/Fragment/Lib.lean", 79)[β]: if $a in A$ then $graph(F, A) dot.op a = F(a)$.
- $graph(F, A) != pt$: #src("whitepaper/Fragment/Lib.lean", 81)[a graph is never the point].
- #src("whitepaper/Fragment/Lib.lean", 83, 85)[Congruence]: $graph(F, A)$ depends only on the values of $F$ on $A$,
  and $Pi(A, B)$ only on the values of $B$ on $A$.
- #src("whitepaper/Fragment/Lib.lean", 87, 88)[Introduction]: if $F(x) in B(x)$ for every $x in A$, then
  $graph(F, A) in Pi(A, B)$.
- #src("whitepaper/Fragment/Lib.lean", 90)[Elimination]: if $f in Pi(A, B)$ and $a in A$, then $f dot.op a in B(a)$.
- #src("whitepaper/Fragment/Lib.lean", 92)[η]: if $f in Pi(A, B)$, then $graph(x |-> f dot.op x, A) = f$.
- #src("whitepaper/Fragment/Lib.lean", 94, 95)[Domain uniqueness]: if $f in Pi(A, B)$ and $f in Pi(A', B')$, then
  $A = A'$.
- #src("whitepaper/Fragment/Lib.lean", 98, 99)[Closure]: for $n != 0$, if $A in cal(U)_n$ and $B(x) in cal(U)_n$ for
  every $x in A$, then $Pi(A, B) in cal(U)_n$.

This is all this section needs. When inductive types arrive, §4
extends the theory.

Two of these laws are design choices, and each earns a sentence. The
first is that _application of the point is the point_. In the model a
proof of a proposition is the point, and a proof of $forall x : A. thin P$
is again the point, not a function; the law makes application a single
operation that does the right thing on both kinds of value, so the
interpretation of $f thick a$ will not need to know which kind it is
applying. The second is that _a graph is never the point_: a function
and a proof are never the same set. A value that is known to be in a
function space is therefore a graph, and by domain uniqueness a graph
carries its own domain. This is what will let β fire, at a binder
annotated $ann(never)$, with no certificate at all.

One law is deliberately restricted: closure of a universe under function
spaces is stated for $cal(U)_1, cal(U)_2, dots$ and not for $cal(U)_0$. A
proposition $forall x : A. thin P$ has no function space in the model. It
has a truth value, and a truth value is in $cal(U)_0$ whatever $A$ is —
#src("whitepaper/Fragment/Lib.lean", 249, 250)[the model's impredicativity]. The interpretation is where the two readings are told apart.

== The interpretation <sec:interp>

Every term denotes a set. The interpretation is _total_ — it is defined
on every term, well-typed or not — and _term-directed_: it is a
structural recursion on the term, consulting no derivation and no
type. It takes two parameters:

- a valuation $phi$ of the level parameters (@sec:levels);
- a _variable environment_ $rho$, assigning a set to every variable in
  scope.

We write $lden e rden_rho$ for the set the term $e$ denotes under $rho$
($phi$ stays implicit), and $rho, x |-> v$ for $rho$ extended
with the value $v$ for the variable $x$. #src("whitepaper/Fragment/Interp.lean", 124, 130)[The clauses]:

$
  lden x rden_rho & = rho(x) \
  lden Sort u rden_rho & = cal(U)_(phi(u)) \
  lden f thick a rden_rho & = lden f rden_rho dot.op lden a rden_rho \
  lden lambda x : A thin ann(PW). thin b rden_rho & = cases(
    graph(v |-> lden b rden_(rho, x |-> v), med lden A rden_rho) & "if" ann(PW) "does not hold at" phi\,,
    pt & "if" ann(PW) "holds at" phi\;) \
  lden forall x : A thin ann(PW). thin B rden_rho & = cases(
    Pi(lden A rden_rho, med v |-> lden B rden_(rho, x |-> v)) & "if" ann(PW) "does not hold at" phi\,,
    Pi_0(lden A rden_rho, med v |-> lden B rden_(rho, x |-> v)) & "if" ann(PW) "holds at" phi.)
$

Here $phi(u)$ is the value of the level $u$ at the valuation;
"$ann(PW)$ holds at $phi$" is
#src("whitepaper/Fragment/PropWhen.lean", 191, 194)[the readout] of @sec:annotation: $ann(never)$ never holds, and
$ann(sans("whenZero") \{p_1\, ...\, p_k\})$ holds exactly when $phi$
sends each $p_i$ to $0$. $Pi_0(A, B)$ is
#src("whitepaper/Fragment/Lib.lean", 157, 163)[the _propositional product_],
$tv(forall v in A. thin B(v) = {pt})$: when the fibres $B(v)$ are
truth values it is their intersection $inter.big_(v in A) B(v)$ (the
empty intersection being ${pt}$), which is ${pt}$ exactly when every
fibre is and $emptyset$ otherwise — the product of subsets of a
singleton. (The two binder clauses, each with its two
cases: #src("whitepaper/Fragment/Lib.lean", 167, 172)[fragment],
#src("ConLeche/SetModel/Ops.lean", 56, 62)[real proof].)

A binder has two regimes. When the body is not a proposition, a
$lambda$ is a graph and a $forall$ is a set of such graphs, a
function space. When the body is a proposition, a $lambda$ is a
proof of one, hence the point, and a $forall$ is a proposition — it
is true when every _fibre_, the set $lden B rden_(rho, x |-> v)$ at
each $v in lden A rden_rho$, is the singleton ${pt}$, the truth value
of a true proposition. We call the two shapes a $forall$ can denote a
_function space_ $Pi$ and a _propositional product_ $Pi_0$. Which regime applies is decided by the annotation's readout at
$phi$, and by nothing else: the interpretation does not know the sort
of $B$, and does not compute it. A sort denotes its universe.

This is the whole of the interpretation. Nothing had to be well-typed;
no typing judgement was consulted; there is no partiality to discharge.
What replaces typing is the subject of the next subsection. Two
lemmas about the interpretation are needed later, both proved by
induction on the term: #src("whitepaper/Fragment/Interp.lean", 210, 212)[substituting a term for a variable] is extending
the environment with the term's value,
$lden b[x := a] rden_rho = lden b rden_(rho, x |-> lden a rden_rho)$\; and #src("whitepaper/Fragment/Interp.lean", 151, 153)[a term does not
see a variable it does not mention]. (#src("ConLeche/Semantics/Interp.lean", 150, 156)[The real proof's
interpretation].)

== The semantic invariant <sec:inv>

There is no typing judgement in the proof. In its place is a predicate
on terms, the _semantic invariant_: a term is #src("whitepaper/Fragment/WellDenoted.lean", 62, 119)[_well-denoted_] when its
set is put together honestly
(#src("ConLeche/Semantics/WellDenoted.lean", 56, 70)[the real proof's version]). It is stated under a valuation $phi$ and an environment
$rho$, like the interpretation, and it is an inductively defined
judgement: it holds of a term when it holds of the subterms and one
condition on the term's own shape is met. We write $rho models e$
for "$e$ is well-denoted under $rho$" ($phi$ is fixed throughout), and
$cal(U)_0$ for the set of truth values:

#rules(
  rule(name: "var", $rho models x$),
  rule(name: "sort", $rho models Sort u$),
  rule(name: "app-fun",
    $rho models f$, $rho models a$,
    $lden f rden_rho in Pi(A', B')$,
    $lden a rden_rho in A'$,
    $rho models f thick a$),
)
#rules(
  rule(name: "app-prop",
    $rho models f$, $rho models a$,
    $lden f rden_rho in Pi_0(A', B') \
     forall v in A'. thin B'(v) in cal(U)_0$,
    $lden a rden_rho in A'$,
    $rho models f thick a$),
)
#rules(
  rule(name: "lam-fun",
    $ann(PW "does not hold")$,
    $rho models A$,
    $forall v in lden A rden_rho. thin rho, x |-> v models b \
     forall v in lden A rden_rho. thin lden b rden_(rho, x |-> v) in B(v)$,
    $rho models lambda x : A thin ann(PW). thin b$),
)
#rules(
  rule(name: "lam-prop",
    $ann(PW "holds")$,
    $rho models A$,
    $forall v in lden A rden_rho. thin rho, x |-> v models b \
     forall v in lden A rden_rho. thin lden b rden_(rho, x |-> v) in B(v)$,
    $ann(forall v in lden A rden_rho. thin B(v) in cal(U)_0)$,
    $rho models lambda x : A thin ann(PW). thin b$),
)
#rules(
  rule(name: "pi-fun",
    $ann(PW "does not hold")$,
    $rho models A$,
    $forall v in lden A rden_rho. thin rho, x |-> v models B$,
    $rho models forall x : A thin ann(PW). thin B$),
  rule(name: "pi-prop",
    $ann(PW "holds")$,
    $rho models A$,
    $forall v in lden A rden_rho. thin rho, x |-> v models B$,
    $ann(forall v in lden A rden_rho. thin lden B rden_(rho, x |-> v) in cal(U)_0)$,
    $rho models forall x : A thin ann(PW). thin B$),
)

In app-fun, $A'$ and $B'$ are some domain and family, and a graph
determines its domain. In app-prop they are some domain and family
that the value of $f$ — the point — does not determine, which is the
reason the β step there needs a certificate (@lem:beta-graph,
@lem:beta-cert). In the rules for $lambda$, $B$ is some family
bounding the body's values, its _codomain_. In words: an application
applies a function, or a proof of a propositional $forall$, to a
member of its domain; a $lambda$'s values lie in a bounded codomain;
the annotation decides the regime of a binder, and it may claim
"proposition" only where the fibres really are truth values.

The rules lam-prop and pi-prop are where the annotation is held to
account: the datum may claim "the body is a proposition" only if the
body really denotes a truth value. For example, a $forall$ whose
annotation is $ann(sans("whenZero") \{\})$ — "always a proposition" —
but whose body denotes a two-element set is not well-denoted.

The semantic invariant is #src("whitepaper/Fragment/WellDenoted.lean", 425, 429)[transported by substitution]: $b[x := a]$ is
well-denoted under $rho$ exactly when $b$ is well-denoted under
$rho, x |-> lden a rden_rho$, provided $a$ itself is. The proof is by
induction on the derivation, using the interpretation's substitution
lemma; no typing derivation is involved.

A context $Gamma$ — the list of the types of the variables in scope —
is #src("whitepaper/Fragment/WellDenoted.lean", 529, 534)[_satisfied_] by $rho$ when every entry is well-denoted under the
environment beyond it and the variable's value is a member of what the
entry denotes.
This is the semantic reading of "$Gamma$ is a well-formed context", and
it is the only thing the claims below assume about the context.

Now the first interesting point of the whole development: what a β step
needs. Take a redex $(lambda x : A thin ann(PW). thin b) thick a$ that is
well-denoted. From the application rule we know the $lambda$'s value
lies in some space whose domain $A'$ contains $lden a rden_rho$; from the
$lambda$ rule we know the body is bounded over $lden A rden_rho$. To make
the β law fire we need $lden a rden_rho in lden A rden_rho$ — the argument
in _the λ's own_ domain — and the semantic invariant has given us $A'$, not $A$.

#lemma(name: [β at a $ann(never)$ binder])[
  If $(lambda x : A thin ann(never). thin b) thick a$ is well-denoted
  under $rho$, then
  $lden (lambda x : A thin ann(never). thin b) thick a rden_rho = lden b[x := a] rden_rho$
  and $b[x := a]$ is well-denoted under $rho$
  (#src("whitepaper/Fragment/WellDenoted.lean", 469, 489)[fragment],
  #src("ConLeche/Semantics/WellDenoted.lean", 256, 260)[real proof]).
] <lem:beta-graph>

#proof[
  The annotation $ann(never)$ holds at no valuation, so the $lambda$
  denotes a graph. A graph is never the point, so the application's
  rule is app-fun: the space is a function space $Pi(A', B')$. The
  $lambda$'s own rule, lam-fun, puts the same graph into
  $Pi(lden A rden_rho, B)$ by introduction. Domain
  uniqueness gives $A' = lden A rden_rho$, so $lden a rden_rho in lden A rden_rho$,
  and the β law computes the application to
  $lden b rden_(rho, x |-> lden a rden_rho)$, which is $lden b[x := a] rden_rho$ by
  the substitution lemma. The semantic invariant of the reduct is the
  substitution transport.
]

#lemma(name: "β at any binder, given the membership")[
  If $(lambda x : A thin ann(PW). thin b) thick a$ is well-denoted under
  $rho$ and $lden a rden_rho in lden A rden_rho$, then the same two conclusions
  hold (#src("whitepaper/Fragment/WellDenoted.lean", 495, 505)[fragment],
  #src("ConLeche/Semantics/WellDenoted.lean", 290, 294)[real proof]).
] <lem:beta-cert>

#proof[
  If $ann(PW)$ does not hold at $phi$, the $lambda$ is a graph and the
  membership is exactly what β needs. If it does, the $lambda$ is the
  point, so the left side is $pt dot.op lden a rden_rho = pt$; the right
  side is a member of $B(lden a rden_rho)$, which lam-prop says
  is a truth value, so it too is the point. Transport as before.
]

The difference between the two lemmas is the whole reason the annotation
exists. At a $ann(never)$ binder the semantic invariant alone suffices, because
the value is a graph and a graph remembers its domain. At a binder that
may be a proposition it does not: the value is the point, every domain
has collapsed into it, and no semantic fact about the point can recover
$lden A rden_rho$. A syntactic proof would at this point want subject
reduction — that the argument has the domain's type, and that this
survives the reductions and substitutions that brought the redex here.
This proof wants a certificate from the checker instead: at such a redex
the checker infers the argument's type and compares it with the domain
(rule beta-cert of @sec:rules), and the soundness of that comparison —
the second and third claims below — supplies precisely the premise of
@lem:beta-cert. The checker pays an inference and an equality test per
possibly-propositional redex, and the proof pays nothing.

== The three claims and their proof <sec:claims>

#theorem(name: "Soundness of the three relations")[
  Fix a valuation $phi$ and let $rho$ satisfy $Gamma$. Then:
  + reduction preserves the denotation and the semantic invariant: if
    $Gamma tack e red e'$ and $e$ is well-denoted, then $e'$ is
    well-denoted and $lden e rden_rho = lden e' rden_rho$;
  + equality means equal sets: if $Gamma tack a equiv b$ and both $a$
    and $b$ are well-denoted, then $lden a rden_rho = lden b rden_rho$;
  + inference establishes the semantic invariant and a membership: if
    $Gamma tack e => T$, then $e$ and $T$ are well-denoted and
    $lden e rden_rho in lden T rden_rho$.
  (#src("whitepaper/Fragment/Sound.lean", 817, 821)[fragment], with
  #src("whitepaper/Fragment/Motive.lean", 40, 53)[the three claims stated]\; #src("ConLeche/Model/Rules/Motive.lean", 70, 104)[real
  proof], whose claims also carry the erased reading of the term, @sec:left-out.)
] <thm:sound>

Look at where the semantic invariant sits in the three statements. Reduction and
equality _consume_ it: they are stated for well-denoted subjects, and
say nothing about others. Inference _establishes_ it: the third claim
has no premise about $e$ at all. That is the division of labour. The
checker's inference rules are the ones that check a term's shape, so
their soundness is what proves the term put together honestly; the
other two relations are handed well-denoted terms and pass the
invariant along.

#corollary[
  If the checker infers $tack e => T$ in the empty context, then $lden e rden_rho in lden T rden_rho$ #src("whitepaper/Fragment/Sound.lean", 825, 828)[at every valuation]
  and every $rho$.
] <cor:closed>

This is the statement the environment section builds on: a
declaration is accepted when its value's inferred type is
definitionally equal to its declared type, and the corollary, with the
second claim, puts the value's set into the declared type's set.

The three claims are proved together, by #src("whitepaper/Fragment/Sound.lean", 754, 807)[one structural induction] over
the three mutually inductive relations (#src("ConLeche/Model/Rules/Sound.lean", 43, 44)[the real proof's
master induction]).
Every rule is one case, and every case is a lemma about that rule
alone, with the induction hypothesis for each premise as an assumption.
Most cases are routine and are listed at the end; the ones below are
where the argument lives.

#proof[
  *#src("whitepaper/Fragment/Sound.lean", 166, 170)[Rule beta-gate]* — $(lambda x : A thin ann(never). thin b) thick a red b[x :=
  a]$: \
  This is @lem:beta-graph, verbatim: the rule has no premise, and
  the lemma needs none
  (#src("ConLeche/Model/Rules/RedSound.lean", 180, 182)[real proof]).

  *#src("whitepaper/Fragment/Sound.lean", 180, 190)[Rule beta-cert]* — $(lambda x : A thin ann(PW). thin b) thick a red b[x := a]$
  from $ann(Gamma tack a => T)$ and $ann(Gamma tack T equiv A)$: \
  The
  redex is well-denoted, so by the application rule the $lambda$ is,
  and by the $lambda$ rule $A$ is. The induction
  hypothesis for the inference gives $T$ well-denoted and
  $lden a rden_rho in lden T rden_rho$. Now both $T$ and $A$ are well-denoted,
  so the hypothesis for the equality applies and gives
  $lden T rden_rho = lden A rden_rho$; hence $lden a rden_rho in lden A rden_rho$, and
  @lem:beta-cert finishes (#src("ConLeche/Model/Rules/RedSound.lean", 197, 200)[real proof]). Note how the second claim was used: with both sides'
  semantic invariants in hand, one from the redex and one from the inference —
  and never without.

  *#src("whitepaper/Fragment/Sound.lean", 501, 505)[Rule red-l]* — $Gamma tack a equiv b$ from $Gamma tack a red a'$ and
  $Gamma tack a' equiv b$: \
  By the first claim, $a'$ is well-denoted
  and $lden a rden_rho = lden a' rden_rho$; now both $a'$ and $b$ are
  well-denoted, so the second claim applies to the continuation, and
  the two equalities chain (#src("ConLeche/Model/Rules/DefEqSound.lean", 47, 49)[real proof]). This is the one sound way to chain in the equality relation,
  because a reduction step _produces_ the semantic invariant of its result; see
  the discussion of transitivity below.

  *#src("whitepaper/Fragment/Sound.lean", 507, 509)[Rule sort]* — $Sort u equiv Sort v$ when $u eq.dot v$: \
    The oracle is assumed correct: it
  answers yes only if the levels agree at every valuation
  (@sec:levels), so the two universes are the same universe
  (#src("ConLeche/Model/Rules/DefEqSound.lean", 56, 58)[real proof]).

  *#src("whitepaper/Fragment/Sound.lean", 556, 590)[Rule fun-eta]* — $lambda x : A_1 thin ann(PW). thin b_1 equiv b$ when
  $Gamma tack b => T red forall x : A_2 thin ann(PW). thin B$,
  $Gamma tack A_2 equiv A_1$, and $Gamma, x : A_1 tack b_1 equiv b thick x$: \
    The third claim, then the first, put $lden b rden_rho$ in the denotation
  of the $forall$, which is well-denoted; the $lambda$ is well-denoted
  by assumption. The second claim on the domains, both well-denoted by
  the two binder rules, gives $lden A_2 rden_rho = lden A_1 rden_rho$. Under
  $x |-> v$ for any $v in lden A_1 rden_rho$, the term $b thick x$ is
  well-denoted — $b$ and $x$ are, the $forall$'s space contains
  $lden b rden_rho$ with $v$ in its domain (by the domains' equality),
  and the $forall$'s own rule supplies the truth-value condition when
  $ann(PW)$ holds — so the second claim on the bodies gives $lden b_1 rden_(rho, x |-> v) = lden b rden_rho dot.op v$. The
  $lambda$ therefore denotes, by congruence, the abstraction over
  $lden A_2 rden_rho$ of $v |-> lden b rden_rho dot.op v$; and that is
  $lden b rden_rho$ by the η law when $ann(PW)$ does not hold at
  $phi$, and because both are the point when it does — $lden b rden_rho$ is
  then a member of a truth value (#src("ConLeche/Model/Rules/DefEqSound.lean", 193, 200)[real proof]). The rule requires the annotation on the $forall$ and on
  the $lambda$ to be the same datum; that is what makes the two sides
  fall into the same regime at every $phi$.

  *#src("whitepaper/Fragment/Sound.lean", 593, 613)[Rule proof-irrel]* — $a equiv b$ when $Gamma tack a => T_a => S_a red Sort u$
  with $u eq.dot 0$, and likewise for $b$: \
  By the third claim twice
  and the first once, $lden a rden_rho in lden T_a rden_rho$ and
  $lden T_a rden_rho in cal(U)_(phi(u))$, and $phi(u) = 0$ because the
  oracle said $u eq.dot 0$ (@sec:levels). A member of $cal(U)_0$ has
  only the point as a member, so
  $lden a rden_rho = pt$; likewise $lden b rden_rho = pt$
  (#src("ConLeche/Model/Rules/DefEqSound.lean", 309, 316)[real proof]). The two
  types $T_a$ and $T_b$ were never compared, and the semantic invariants of $a$
  and $b$ were not even used: there is only one proof in the whole
  model, so any two proofs of anything are equal in it.

  *#src("whitepaper/Fragment/Sound.lean", 646, 680)[Rule pi]* — $Gamma tack forall x : A thin ann(PW). thin B => Sort (imax(u,
  v))$ when $Gamma tack A => S red Sort u$, $Gamma, x : A tack B => T
  red Sort v$, and $ann(zn(v) = PW)$: \
  This is where the annotation is
  _established_. The third claim for $A$ gives $A$ well-denoted and
  $lden A rden_rho in lden S rden_rho$, and the first turns $lden S rden_rho$ into
  $cal(U)_(phi(u))$. For any $v' in lden A rden_rho$ the environment
  $rho, x |-> v'$ satisfies $Gamma, x : A$, so the third claim for $B$
  gives $B$ well-denoted there and, with the first,
  $lden B rden_(rho, x |-> v') in cal(U)_(phi(v))$. Now #src("whitepaper/Fragment/Sound.lean", 46, 48)[the exactness lemma]
  (@lem:zeroness): $ann(zn(v))$ holds at $phi$ if and only if
  $phi(v) = 0$. So
  when $ann(PW)$ does not hold at $phi$, $phi(v) != 0$ and the
  $forall$ denotes a function space; cumulativity lifts
  $lden A rden_rho$ and every fibre into
  $cal(U)_(max(phi(u), phi(v)))$, which is not $cal(U)_0$, so the
  closure law puts the space there — and that is
  $cal(U)_(phi(imax(u, v)))$. When it holds, every fibre lies in
  $cal(U)_0$ and is a truth value — the $forall$ rule of the semantic
  invariant is met — and the $forall$ denotes a truth value, which is
  in $cal(U)_0 = cal(U)_(phi(imax(u, v)))$ since $phi(v) = 0$
  (#src("ConLeche/Model/Rules/InferSound.lean", 267, 273)[real proof]). The sort $Sort (imax(u, v))$ is well-denoted, as every
  sort is.

  *#src("whitepaper/Fragment/Sound.lean", 688, 722)[Rule lam]* — $Gamma tack lambda x : A thin ann(PW). thin b => forall x : A
  thin ann(PW). thin B$ when $Gamma tack A => S red Sort u$,
  $Gamma, x : A tack b => B ann(=> T red Sort v)$, and $ann(zn(v) = PW)$: \
    The same argument one level down. Under $x |-> v'$ for $v' in
  lden A rden_rho$, the third claim for $b$ gives $b$ and $B$ well-denoted
  and $lden b rden_(rho, x |-> v') in lden B rden_(rho, x |-> v')$; the coloured
  premises and the first claim give $lden B rden_(rho, x |-> v') in
  cal(U)_(phi(v))$. So the family $v' |-> lden B rden_(rho, x |-> v')$ is a
  bounded codomain for the body, with truth values as fibres when
  $ann(PW)$ holds at $phi$ — then $phi(v) = 0$ by exactness, so every
  $lden B rden_(rho, x |-> v')$ lies in $cal(U)_0$. That is the
  $lambda$ rule; the $forall$ rule of the inferred type is met the
  same way; and the introduction law puts the abstraction into the
  space (#src("ConLeche/Model/Rules/InferSound.lean", 356, 367)[real proof]): a graph into the function space, or, when $ann(PW)$
  holds, the point into the truth value — whose proposition holds
  because each fibre is a truth value containing the body's value,
  hence ${pt}$. This is where the proof uses that the fibres are
  truth values. The premise that the domain's type reduces to a sort is not
  used: it is the checker's, and the model needs only that $A$ is
  well-denoted, which the inference of $A$ supplies.

  *#src("whitepaper/Fragment/Sound.lean", 732, 748)[Rule app]* — $Gamma tack f thick a => B[x := a]$ when
  $Gamma tack f => T red forall x : A thin ann(PW). thin B$,
  $Gamma tack a => T_a$ and $Gamma tack T_a equiv A$: \
  By the third
  claim, $f$ and $T$ are well-denoted and $lden f rden_rho in lden T rden_rho$;
  by the first, the $forall$ is well-denoted and
  $lden T rden_rho = lden forall x : A thin ann(PW). thin B rden_rho$. By the
  third claim for $a$, $a$ and $T_a$ are well-denoted and
  $lden a rden_rho in lden T_a rden_rho$; $A$ is well-denoted by the $forall$
  rule, so the second claim gives $lden T_a rden_rho = lden A rden_rho$ and
  $lden a rden_rho in lden A rden_rho$. Now $f thick a$ is well-denoted by the
  establishing lemma of @sec:inv; $B[x := a]$ is well-denoted by the
  substitution transport, since $B$ is well-denoted under
  $x |-> lden a rden_rho$; and the elimination law puts
  $lden f rden_rho dot.op lden a rden_rho$ into the fibre at $lden a rden_rho$, which
  is $lden B[x := a] rden_rho$ by the substitution lemma
  (#src("ConLeche/Model/Rules/InferSound.lean", 511, 515)[real proof]). When
  $ann(PW)$ holds, "elimination" reads: the $forall$ is a truth value
  containing $lden f rden_rho$, so $lden f rden_rho$ is the point and every fibre
  is ${pt}$; the application is the point, which is in the fibre at
  $lden a rden_rho$. The $forall$ rule of the semantic invariant is not
  consulted.

  A syntactic proof would here invert a derivation of $f : T$ to
  learn the domain and the codomain — the injectivity of $forall$
  that @sec:rules discussed. Nothing is inverted here: the checker
  itself reduced $T$ to a syntactic $forall$, the first claim says
  the reduction did not change the set, and that set _is_ a function
  space or a truth value by the interpretation's rule.

  _The rest_, by induction on the derivation.

  - #src("whitepaper/Fragment/Sound.lean", 138, 156)[Reduction]: the no-step reduction is $lden e rden_rho = lden e rden_rho$;
    trans chains two reductions, passing the semantic invariant along; head
    reduces the function of a well-denoted application and keeps the
    application's rule, because the function's set did not change.
  - #src("whitepaper/Fragment/Sound.lean", 490, 495)[Equality]: refl is again $lden e rden_rho = lden e rden_rho$, and
    sym swaps the two semantic invariants. #src("whitepaper/Fragment/Sound.lean", 515, 547)[The congruences]
    for $forall$ and $lambda$ apply the hypothesis to the domains, then
    to the bodies at every value of the domain, and finish with
    the congruence laws; the congruence for applications
    applies the hypothesis to both parts (real proof:
    #src("ConLeche/Model/Rules/DefEqSound.lean", 111, 117)[∀],
    #src("ConLeche/Model/Rules/DefEqSound.lean", 135, 141)[λ],
    #src("ConLeche/Model/Rules/DefEqSound.lean", 159, 161)[app]).
  - #src("whitepaper/Fragment/Sound.lean", 621, 631)[Inference]: a variable's type is read off the satisfied context; a
    sort's type is the next universe, which contains it (real proof:
    #src("ConLeche/Model/Rules/InferSound.lean", 135, 136)[sort],
    #src("ConLeche/Model/Rules/InferSound.lean", 151, 152)[variable]).

  In every one of these cases the semantic invariant of every term the induction
  hypothesis is applied to is either a subterm's, or was produced by
  another claim.
]

*Why there is no transitivity.* The proof above shows why the rule
"$a equiv b$ and $b equiv c$ give $a equiv c$" cannot be added. The
second claim assumes both sides well-denoted. In a transitivity case
the induction would have to apply the hypothesis to $a equiv b$, and
for that it needs $b$ well-denoted — but $b$ is neither a subterm of
$a$ or $c$ nor produced by a premise, so nothing supplies its semantic
invariant. #src("whitepaper/Fragment/Rules.lean", 222, 236)[Every other rule] keeps the discipline of @sec:rules, and the
corresponding claim delivers the semantic invariant of every produced term. The
one way to chain is therefore "reduce, then continue", and that is how
the checker's equality test is structured: it head-normalises a side
and compares again.

The absence is not a restriction on the checker: its equality test
never chains through an arbitrary middle term; every comparison it
makes is one of the rules. Transitivity is a property one would want of
a _type theory_; the relation here describes a _checker_, and the
model only has to agree with what the checker does.
