#import "../lib.typ": *

// Notation local to this file, matching the first half of the section.
#let PW = $italic("pw")$
#let never = $sans("never")$
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

== The set theory, with libraries <sec:lib>

The other side of the argument is a set theory. We do not construct
one. The reader is given one abstract structure — a type of sets with
the operations and laws listed below, which we call the _library_ —
and is promised that nothing
beyond these laws is used. The promise is literal: in the Lean fragment
the structure is a class, #lean[SetLib]
#src("whitepaper/Fragment/Lib.lean", 36, 87), and every theorem of the
fragment is proved against that class. (The real proof is parametric in
a smaller interface — ZF without infinity plus a chain of Grothendieck
universes #src("ConLeche/SetTheory/Core.lean", 95, 100) — from which it
derives the operators below; that interface is instantiated on
Mathlib's `ZFSet` from the hypothesis of ω many inaccessible cardinals
#src("bridge/lean4lean-model/ConLecheBridge/Carneiro.lean", 200, 202).)

Here are the laws, in four groups.

*Sets.* A type $V$ of sets with a membership relation $x in y$, and
extensionality: two sets with the same members are equal
#src("whitepaper/Fragment/Lib.lean", 38, 40).

*The point and the truth values.* A distinguished set $pt$, _the
point_, which will be the one proof of every true proposition. For
every proposition $P$ a set $tv(P)$, its _truth value_, whose only
possible member is the point, and which has it exactly when $P$ holds:
$tv(P) = {pt}$ when $P$ is true and $tv(P) = emptyset$ when it is
false #src("whitepaper/Fragment/Lib.lean", 42, 47).

*The universes.* A chain of sets $cal(U)_0, cal(U)_1, cal(U)_2, dots$.
The members of $cal(U)_0$ are exactly the sets all of whose members are
the point — the truth values. Each $cal(U)_n$ is a member of
$cal(U)_(n+1)$, and the chain is cumulative: a member of $cal(U)_m$ is
a member of every later $cal(U)_n$
#src("whitepaper/Fragment/Lib.lean", 49, 55).

*Graphs, function spaces, application.* For a function $F$ from sets to
sets and a set $A$, a set $graph(F, A)$; for a set $A$ and a family
$B$ of sets indexed by sets, a set $Pi(A, B)$, the _dependent function
space_; and for two sets $f$ and $a$ a set $f dot.op a$, the
_application_ #src("whitepaper/Fragment/Lib.lean", 57, 63). Their laws:

- $pt dot.op a = pt$: a proof applied to anything is the proof
  #src("whitepaper/Fragment/Lib.lean", 65).
- β: if $a in A$ then $graph(F, A) dot.op a = F(a)$
  #src("whitepaper/Fragment/Lib.lean", 67).
- $graph(F, A) != pt$: a graph is never the point
  #src("whitepaper/Fragment/Lib.lean", 69).
- Congruence: $graph(F, A)$ depends only on the values of $F$ on $A$,
  and $Pi(A, B)$ only on the values of $B$ on $A$
  #src("whitepaper/Fragment/Lib.lean", 71, 73).
- Introduction: if $F(x) in B(x)$ for every $x in A$, then
  $graph(F, A) in Pi(A, B)$
  #src("whitepaper/Fragment/Lib.lean", 75, 76).
- Elimination: if $f in Pi(A, B)$ and $a in A$, then $f dot.op a in B(a)$
  #src("whitepaper/Fragment/Lib.lean", 78).
- η: if $f in Pi(A, B)$, then $graph(x |-> f dot.op x, A) = f$
  #src("whitepaper/Fragment/Lib.lean", 80).
- Domain uniqueness: if $f in Pi(A, B)$ and $f in Pi(A', B')$, then
  $A = A'$ #src("whitepaper/Fragment/Lib.lean", 82, 83).
- Closure: for $n != 0$, if $A in cal(U)_n$ and $B(x) in cal(U)_n$ for
  every $x in A$, then $Pi(A, B) in cal(U)_n$
  #src("whitepaper/Fragment/Lib.lean", 86, 87).

That is the whole library. Note what is absent: no pairing, no union,
no power set, no choice, no fixed points. None of those is needed
before the environment section, and the fragment's proof cannot use
what its class does not state.

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
the model's impredicativity #src("whitepaper/Fragment/Lib.lean", 208,
209). The interpretation is where the two readings are told apart.

== The interpretation <sec:interp>

Every term denotes a set. The interpretation is _total_ — it is defined
on every term, well-typed or not — and _term-directed_: it is a
structural recursion on the term, consulting no derivation, no
environment lookup, and no type. It takes three parameters:

- a valuation $phi$ of the level parameters (@sec:levels);
- an _assignment_ $M$ of a set to every constant at every list of
  concrete levels — the environment's contribution (§3 says where it
  comes from; here it is a parameter);
- a _variable environment_ $rho$, assigning a set to every variable in
  scope.

We write $lden e rden_rho$ for the set the term $e$ denotes under $rho$
($phi$ and $M$ stay implicit), and $rho, x |-> v$ for $rho$ extended
with the value $v$ for the variable $x$. The clauses
#src("whitepaper/Fragment/Interp.lean", 124, 130):

$
  lden x rden_rho & = rho(x) \
  lden Sort u rden_rho & = cal(U)_(phi(u)) \
  lden c.\{arrow(ell)\} rden_rho & = M(c, phi(arrow(ell))) \
  lden f thick a rden_rho & = lden f rden_rho dot.op lden a rden_rho \
  lden lambda x : A thin ann(italic("pw")). thin b rden_rho & = cases(
    pt & "if" ann(italic("pw")) "holds at" phi\,,
    graph(v |-> lden b rden_(rho, x |-> v), med lden A rden_rho) & "otherwise;") \
  lden forall x : A thin ann(italic("pw")). thin B rden_rho & = cases(
    tv(forall v in lden A rden_rho\, thick lden B rden_(rho, x |-> v) "is inhabited") & "if" ann(italic("pw")) "holds at" phi\,,
    Pi(lden A rden_rho, med v |-> lden B rden_(rho, x |-> v)) & "otherwise.")
$

Here $phi(u)$ is the value of the level $u$ at the valuation, and
$phi(arrow(ell))$ the list of values; "$ann(PW)$ holds at $phi$" is
the readout of @sec:terms: $ann(never)$ never holds, and
$ann(sans("whenZero") \{p_1\, ...\, p_k\})$ holds exactly when $phi$
sends each $p_i$ to $0$ #src("whitepaper/Fragment/PropWhen.lean", 191,
194). The Lean fragment packs each binder clause's two cases into one
operator that takes the readout as a Boolean, #lean[piR] and
#lean[lamR] #src("whitepaper/Fragment/Lib.lean", 125, 130), as the real
proof does #src("ConLeche/SetModel/Ops.lean", 60, 66)\; and it uses de
Bruijn indices, so $rho, x |-> v$ is "cons $v$ onto $rho$" there.

Read the two regimes of a binder. When the body is not a proposition, a
$forall$ is a set of functions and a $lambda$ is one of them: a graph.
When the body is a proposition, a $forall$ is a proposition — it is true
when every _fibre_, the set $lden B rden_(rho, x |-> v)$ at each
$v in lden A rden_rho$, is inhabited, which is the usual reading of a
universal quantifier over a set — and a $lambda$ is a proof of one,
hence the point. We call the two shapes a $forall$ can denote a
_function space_ and a _propositional_ $forall$. Which regime applies is decided by the annotation's readout at
$phi$, and by nothing else: the interpretation does not know the sort
of $B$, and does not compute it. A sort denotes its universe, and a
constant denotes what the assignment says.

This is the whole of the interpretation. Nothing had to be well-typed;
no typing judgement was consulted; there is no partiality to discharge.
What replaces typing is the subject of the next subsection. Three
lemmas about the interpretation are needed later, all proved by
induction on the term: substituting a term for a variable is extending
the environment with the term's value,
$lden b[x := a] rden_rho = lden b rden_(rho, x |-> lden a rden_rho)$
#src("whitepaper/Fragment/Interp.lean", 210, 212)\; instantiating
level parameters is changing the valuation
#src("whitepaper/Fragment/Interp.lean", 215, 217)\; and a term does not
see a variable it does not mention
#src("whitepaper/Fragment/Interp.lean", 151, 153). (The real proof's
interpretation: #src("ConLeche/Semantics/Interp.lean", 150, 156).)

== The invariant <sec:inv>

There is no typing judgement in the proof. In its place is a predicate
on terms, _well-denoted_, which says that the term's set is put
together honestly #src("whitepaper/Fragment/WellDenoted.lean", 50, 68)
(the real proof's version: #src("ConLeche/Semantics/WellDenoted.lean",
81, 95)). It is stated under a valuation $phi$ and an environment
$rho$, like the interpretation, and it is hereditary: it holds of a
term when it holds of the subterms and one condition on the term's own
shape is met. In words:

- A variable, a sort or a constant is always well-denoted.
- An application $f thick a$ is well-denoted when $f$ and $a$ are, and
  the value of $f$ lies in some function space $Pi(A', B')$ or some
  propositional $forall$ over a domain $A'$ with fibres $B'$, with
  $lden a rden_rho in A'$; in the second case every $B'(v)$ for
  $v in A'$ must be a truth value.
- A $lambda x : A thin ann(PW). thin b$ is well-denoted when $A$ is,
  when $b$ is under every value $v in lden A rden_rho$ of the variable, and
  when the body has a _bounded codomain_: some family $B$ with
  $lden b rden_(rho, x |-> v) in B(v)$ for every such $v$ — and, if
  $ann(PW)$ holds at $phi$, each $B(v)$ is a truth value.
- A $forall x : A thin ann(PW). thin B$ is well-denoted when $A$ is,
  when $B$ is under every value $v in lden A rden_rho$ — and, if $ann(PW)$
  holds at $phi$, $lden B rden_(rho, x |-> v)$ _is_ a truth value for every
  such $v$.

The two binder clauses are where the annotation is held to account. The
datum may say "the body is a proposition" only where the body really
denotes a truth value; a $forall$ annotated $ann(sans("whenZero") \{\})$
whose body denotes a set with two members is not well-denoted, and
neither is an application whose function is the point applied outside
a truth value. A reader who wants one sentence for the whole predicate:
the invariant is the semantic content of a typing derivation, with the
types forgotten and only the memberships kept.

The invariant is transported by substitution, without any lemma about
derivations: $b[x := a]$ is well-denoted under $rho$ exactly when $b$
is well-denoted under $rho, x |-> lden a rden_rho$, provided $a$ itself is
#src("whitepaper/Fragment/WellDenoted.lean", 183, 187). This follows
from the interpretation's substitution lemma by induction on $b$.

A context $Gamma$ — the list of the types of the variables in scope —
is _satisfied_ by $rho$ when every entry is well-denoted under the
environment beyond it and the variable's value is a member of what the
entry denotes #src("whitepaper/Fragment/WellDenoted.lean", 287, 292).
This is the semantic reading of "$Gamma$ is a well-formed context", and
it is the only thing the claims below assume about the context.

Now the first interesting point of the whole development: what a β step
needs. Take a redex $(lambda x : A thin ann(PW). thin b) thick a$ that is
well-denoted. From the application clause we know the $lambda$'s value
lies in some space whose domain $A'$ contains $lden a rden_rho$; from the
$lambda$ clause we know the body is bounded over $lden A rden_rho$. To make
the library's β fire we need $lden a rden_rho in lden A rden_rho$ — the argument
in _the λ's own_ domain — and the invariant has given us $A'$, not $A$.

#lemma(name: [β at a $ann(never)$ binder])[
  If $(lambda x : A thin ann(never). thin b) thick a$ is well-denoted
  under $rho$, then
  $lden (lambda x : A thin ann(never). thin b) thick a rden_rho = lden b[x := a] rden_rho$
  and $b[x := a]$ is well-denoted under $rho$
  #src("whitepaper/Fragment/WellDenoted.lean", 227, 247)
  (real proof: #src("ConLeche/Semantics/WellDenoted.lean", 281, 285)).
] <lem:beta-graph>

#proof[
  The annotation $ann(never)$ holds at no valuation, so the $lambda$
  denotes a graph. A graph is never the point, so the space the
  application clause supplies is not a propositional $forall$ — it is
  a function space $Pi(A', B')$. The $lambda$'s own clause puts the
  same graph into $Pi(lden A rden_rho, B)$ by introduction. Domain
  uniqueness gives $A' = lden A rden_rho$, so $lden a rden_rho in lden A rden_rho$,
  and the library's β computes the application to
  $lden b rden_(rho, x |-> lden a rden_rho)$, which is $lden b[x := a] rden_rho$ by
  the substitution lemma. The invariant of the reduct is the
  substitution transport.
]

#lemma(name: "β at any binder, given the membership")[
  If $(lambda x : A thin ann(PW). thin b) thick a$ is well-denoted under
  $rho$ and $lden a rden_rho in lden A rden_rho$, then the same two conclusions
  hold #src("whitepaper/Fragment/WellDenoted.lean", 253, 263)
  (real proof: #src("ConLeche/Semantics/WellDenoted.lean", 315, 319)).
] <lem:beta-cert>

#proof[
  If $ann(PW)$ does not hold at $phi$, the $lambda$ is a graph and the
  membership is exactly what β needs. If it does, the $lambda$ is the
  point, so the left side is $pt dot.op lden a rden_rho = pt$; the right
  side is a member of $B(lden a rden_rho)$, which the $lambda$ clause says
  is a truth value, so it too is the point. Transport as before.
]

The difference between the two lemmas is the whole reason the annotation
exists. At a $ann(never)$ binder the invariant alone suffices, because
the value is a graph and a graph remembers its domain. At a binder that
may be a proposition it does not: the value is the point, every domain
has collapsed into it, and no semantic fact about the point can recover
$lden A rden_rho$. A syntactic proof would at this point want subject
reduction — that the argument has the domain's type, and that this
survives the reductions and substitutions that brought the redex here.
This proof wants a certificate from the checker instead: at such a redex
the checker infers the argument's type and compares it with the domain
(rule β-cert of @sec:rules), and the soundness of that comparison —
the second and third claims below — supplies precisely the premise of
@lem:beta-cert. The checker pays an inference and an equality test per
possibly-propositional redex, and the proof pays nothing.

One more lemma establishes the application clause rather than consuming
it: if $f$ and $a$ are well-denoted, $forall x : A thin ann(PW). thin B$
is well-denoted, $lden f rden_rho$ is a member of its denotation and
$lden a rden_rho$ a member of $lden A rden_rho$, then $f thick a$ is well-denoted
#src("whitepaper/Fragment/WellDenoted.lean", 271, 280). The $forall$'s
own annotation clause is what supplies the truth-value condition when
$ann(PW)$ holds. This is the lemma the application rule of inference
will use.

== The three claims and their proof <sec:claims>

Fix an environment with a _model_: an assignment $M$ and three laws
about the stored constants #src("whitepaper/Fragment/EnvModel.lean",
92, 117). Every stored constant's declared type is well-denoted and
contains the constant's set, at every level instantiation
#src("whitepaper/Fragment/EnvModel.lean", 99, 102)\; a definition's
value denotes the constant's set and is well-denoted
#src("whitepaper/Fragment/EnvModel.lean", 105, 109)\; and every
recursor rule's reduction holds in the model
#src("whitepaper/Fragment/EnvModel.lean", 110, 117). §3 constructs a
model for every accepted environment; here the three laws are assumed.
The third is used only by the rule $iota$, which belongs to §3 too.

#theorem(name: "Soundness of the three relations")[
  Fix a model of the environment and a valuation $phi$, and let $rho$
  satisfy $Gamma$. Then:
  + if $Gamma tack e red e'$ and $e$ is well-denoted, then $e'$ is
    well-denoted and $lden e rden_rho = lden e' rden_rho$;
  + if $Gamma tack a equiv b$ and both $a$ and $b$ are well-denoted,
    then $lden a rden_rho = lden b rden_rho$;
  + if $Gamma tack e => T$, then $e$ and $T$ are well-denoted and
    $lden e rden_rho in lden T rden_rho$.
  (#src("whitepaper/Fragment/Sound.lean", 571, 575)[fragment], with
  the three claims stated at #src("whitepaper/Fragment/Motive.lean",
  40, 53)\; #src("ConLeche/Model/Rules/Motive.lean", 71, 105)[real
  proof], whose claims also carry the reading of the term and its
  free-variable frame, which the fragment has no need of.)
] <thm:sound>

Look at where the invariant sits in the three statements. Reduction and
equality _consume_ it: they are stated for well-denoted subjects, and
say nothing about others. Inference _establishes_ it: the third claim
has no premise about $e$ at all. That is the division of labour. The
checker's inference rules are the ones that check a term's shape, so
their soundness is what proves the term put together honestly; the
other two relations are handed well-denoted terms and pass the
invariant along.

#corollary[
  If the checker infers $tack e => T$ in the empty context, then $lden e rden_rho in lden T rden_rho$ under every model,
  every valuation and every $rho$
  #src("whitepaper/Fragment/Sound.lean", 579, 582).
] <cor:closed>

This is the statement the environment section builds on: a
declaration is accepted when its value's inferred type is
definitionally equal to its declared type, and the corollary, with the
second claim, puts the value's set into the declared type's set.

The three claims are proved together, by one structural induction over
the three mutually inductive relations
#src("whitepaper/Fragment/Sound.lean", 516, 561) (the real proof's
master induction: #src("ConLeche/Model/Rules/Sound.lean", 43, 44)).
Every rule is one case, and every case is a lemma about that rule
alone, with the induction hypothesis for each premise as an assumption.
Most cases are routine and are listed at the end; the ones below are
where the argument lives.

#proof[
  _β-gate_ ($(lambda x : A thin ann(never). thin b) thick a red b[x :=
  a]$). This is @lem:beta-graph, verbatim: the rule has no premise, and
  the lemma needs none #src("whitepaper/Fragment/Sound.lean", 144, 148)
  (real proof: #src("ConLeche/Model/Rules/RedSound.lean", 186, 188)).

  _β-cert_ ($(lambda x : A thin ann(PW). thin b) thick a red b[x := a]$
  from $ann(Gamma tack a => T)$ and $ann(Gamma tack T equiv A)$). The
  redex is well-denoted, so by the application clause the $lambda$ is,
  and by the $lambda$ clause $A$ is. The induction
  hypothesis for the inference gives $T$ well-denoted and
  $lden a rden_rho in lden T rden_rho$. Now both $T$ and $A$ are well-denoted,
  so the hypothesis for the equality applies and gives
  $lden T rden_rho = lden A rden_rho$; hence $lden a rden_rho in lden A rden_rho$, and
  @lem:beta-cert finishes #src("whitepaper/Fragment/Sound.lean", 158,
  168) (real proof: #src("ConLeche/Model/Rules/RedSound.lean", 204,
  207)). Note how the second claim was used: with both sides'
  invariants in hand, one from the redex and one from the inference —
  and never without.

  _δ_ ($c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$ for a
  definition $c$ with parameters $arrow(p)$ and value $v$, at
  $|arrow(ell)| = |arrow(p)|$ levels — the rule @sec:rules deferred
  because it reads the environment). The
  environment's unfolding law says the instantiated value is
  well-denoted and denotes $M(c, phi(arrow(ell)))$, which is what the
  constant denotes #src("whitepaper/Fragment/Sound.lean", 171, 177)
  (real proof: #src("ConLeche/Model/Rules/RedSound.lean", 247, 248)).
  The redex's invariant is not even needed. §3 shows the law holds when
  a definition is added.

  _red-l_ ($Gamma tack a equiv b$ from $Gamma tack a red a'$ and
  $Gamma tack a' equiv b$). By the first claim, $a'$ is well-denoted
  and $lden a rden_rho = lden a' rden_rho$; now both $a'$ and $b$ are
  well-denoted, so the second claim applies to the continuation, and
  the two equalities chain #src("whitepaper/Fragment/Sound.lean", 265,
  269) (real proof: #src("ConLeche/Model/Rules/DefEqSound.lean", 50,
  52)). This is the one sound way to chain in the equality relation,
  because a reduction step _produces_ the invariant of its result; see
  the discussion of transitivity below.

  _sort, const_ ($Sort u equiv Sort v$ when $u eq.dot v$;
  $c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$ when
  $arrow(ell) eq.dot arrow(ell)'$ pointwise). The oracle is assumed correct: it
  answers yes only if the levels agree at every valuation
  (@sec:levels). So the two universes are the same universe, and the
  two constants read the same entry of $M$
  #src("whitepaper/Fragment/Sound.lean", 271, 277) (real proof:
  #src("ConLeche/Model/Rules/DefEqSound.lean", 59, 61),
  #src("ConLeche/Model/Rules/DefEqSound.lean", 79, 81)).

  _η_ ($lambda x : A_1 thin ann(PW). thin b_1 equiv b$ when
  $Gamma tack b => T red forall x : A_2 thin ann(PW). thin B$,
  $Gamma tack A_2 equiv A_1$, and $Gamma, x : A_1 tack b_1 equiv b thick x$).
  The third claim, then the first, put $lden b rden_rho$ in the denotation
  of the $forall$, which is well-denoted; the $lambda$ is well-denoted
  by assumption. The second claim on the domains, both well-denoted by
  the two binder clauses, gives $lden A_2 rden_rho = lden A_1 rden_rho$. Under
  $x |-> v$ for any $v in lden A_1 rden_rho$, the term $b thick x$ is
  well-denoted — $b$ and $x$ are, the $forall$'s space contains
  $lden b rden_rho$ with $v$ in its domain (by the domains' equality),
  and the $forall$'s own clause supplies the truth-value condition when
  $ann(PW)$ holds — so the second claim on the bodies gives $lden b_1 rden_(rho, x |-> v) = lden b rden_rho dot.op v$. The
  $lambda$ therefore denotes, by congruence, the abstraction over
  $lden A_2 rden_rho$ of $v |-> lden b rden_rho dot.op v$; and that is
  $lden b rden_rho$ by the library's η when $ann(PW)$ does not hold at
  $phi$, and because both are the point when it does — $lden b rden_rho$ is
  then a member of a truth value #src("whitepaper/Fragment/Sound.lean",
  320, 354) (real proof: #src("ConLeche/Model/Rules/DefEqSound.lean",
  197, 204)). The rule requires the annotation on the $forall$ and on
  the $lambda$ to be the same datum; that is what makes the two sides
  fall into the same regime at every $phi$.

  _proof-irrel_ ($a equiv b$ when $Gamma tack a => T_a => S_a red Sort u$
  with $u eq.dot 0$, and likewise for $b$). By the third claim twice
  and the first once, $lden a rden_rho in lden T_a rden_rho$ and
  $lden T_a rden_rho in cal(U)_(phi(u))$, and $phi(u) = 0$ because the
  oracle said $u eq.dot 0$ (@sec:levels). A member of $cal(U)_0$ has
  only the point as a member, so
  $lden a rden_rho = pt$; likewise $lden b rden_rho = pt$
  #src("whitepaper/Fragment/Sound.lean", 357, 377) (real proof:
  #src("ConLeche/Model/Rules/DefEqSound.lean", 313, 320)). The two
  types $T_a$ and $T_b$ were never compared, and the invariants of $a$
  and $b$ were not even used: there is only one proof in the whole
  model, so any two proofs of anything are equal in it.

  _∀_ ($Gamma tack forall x : A thin ann(PW). thin B => Sort (imax(u,
  v))$ when $Gamma tack A => S red Sort u$, $Gamma, x : A tack B => T
  red Sort v$, and $ann(zn(v) = PW)$). This is where the annotation is
  _established_. The third claim for $A$ gives $A$ well-denoted and
  $lden A rden_rho in lden S rden_rho$, and the first turns $lden S rden_rho$ into
  $cal(U)_(phi(u))$. For any $v' in lden A rden_rho$ the environment
  $rho, x |-> v'$ satisfies $Gamma, x : A$, so the third claim for $B$
  gives $B$ well-denoted there and, with the first,
  $lden B rden_(rho, x |-> v') in cal(U)_(phi(v))$. Now the exactness lemma
  (@lem:zeroness): $ann(zn(v))$ holds at $phi$ if and only if
  $phi(v) = 0$ #src("whitepaper/Fragment/Sound.lean", 45, 47). So
  when $ann(PW)$ holds at $phi$, every fibre lies in $cal(U)_0$ and is
  a truth value — the $forall$ clause of the invariant is met — and
  the $forall$ denotes a truth value, which is in
  $cal(U)_0 = cal(U)_(phi(imax(u, v)))$ since $phi(v) = 0$. When it
  does not hold, $phi(v) != 0$ and the $forall$ denotes a function
  space; cumulativity lifts $lden A rden_rho$ and every fibre into
  $cal(U)_(max(phi(u), phi(v)))$, which is not $cal(U)_0$, so the
  closure law puts the space there — and that is
  $cal(U)_(phi(imax(u, v)))$ #src("whitepaper/Fragment/Sound.lean",
  410, 444) (real proof: #src("ConLeche/Model/Rules/InferSound.lean",
  269, 275)). The sort $Sort (imax(u, v))$ is well-denoted, as every
  sort is.

  _λ_ ($Gamma tack lambda x : A thin ann(PW). thin b => forall x : A
  thin ann(PW). thin B$ when $Gamma tack A => S red Sort u$,
  $Gamma, x : A tack b => B ann(=> T red Sort v)$, and $ann(zn(v) = PW)$).
  The same argument one level down. Under $x |-> v'$ for $v' in
  lden A rden_rho$, the third claim for $b$ gives $b$ and $B$ well-denoted
  and $lden b rden_(rho, x |-> v') in lden B rden_(rho, x |-> v')$; the coloured
  premises and the first claim give $lden B rden_(rho, x |-> v') in
  cal(U)_(phi(v))$. So the family $v' |-> lden B rden_(rho, x |-> v')$ is a
  bounded codomain for the body, with truth values as fibres when
  $ann(PW)$ holds at $phi$ — then $phi(v) = 0$ by exactness, so every
  $lden B rden_(rho, x |-> v')$ lies in $cal(U)_0$. That is the
  $lambda$ clause; the $forall$ clause of the inferred type is met the
  same way; and the introduction law puts the abstraction into the
  space, in either regime #src("whitepaper/Fragment/Sound.lean", 452,
  484) (real proof: #src("ConLeche/Model/Rules/InferSound.lean", 359,
  370)). The premise that the domain's type reduces to a sort is not
  used: it is the checker's, and the model needs only that $A$ is
  well-denoted, which the inference of $A$ supplies.

  _app_ ($Gamma tack f thick a => B[x := a]$ when
  $Gamma tack f => T red forall x : A thin ann(PW). thin B$,
  $Gamma tack a => T_a$ and $Gamma tack T_a equiv A$). By the third
  claim, $f$ and $T$ are well-denoted and $lden f rden_rho in lden T rden_rho$;
  by the first, the $forall$ is well-denoted and
  $lden T rden_rho = lden forall x : A thin ann(PW). thin B rden_rho$. By the
  third claim for $a$, $a$ and $T_a$ are well-denoted and
  $lden a rden_rho in lden T_a rden_rho$; $A$ is well-denoted by the $forall$
  clause, so the second claim gives $lden T_a rden_rho = lden A rden_rho$ and
  $lden a rden_rho in lden A rden_rho$. Now $f thick a$ is well-denoted by the
  establishing lemma of @sec:inv; $B[x := a]$ is well-denoted by the
  substitution transport, since $B$ is well-denoted under
  $x |-> lden a rden_rho$; and the elimination law puts
  $lden f rden_rho dot.op lden a rden_rho$ into the fibre at $lden a rden_rho$, which
  is $lden B[x := a] rden_rho$ by the substitution lemma
  #src("whitepaper/Fragment/Sound.lean", 494, 510) (real proof:
  #src("ConLeche/Model/Rules/InferSound.lean", 515, 519)). When
  $ann(PW)$ holds, "elimination" reads: the $forall$ is a truth value
  containing $lden f rden_rho$, so $lden f rden_rho$ is the point and every fibre
  is inhabited; the application is the point; and the fibre at
  $lden a rden_rho$ is a truth value — the $forall$ clause again — that is
  inhabited, hence contains the point.

  Compare this with a syntactic proof. There, one has a derivation of
  $f : T$ and must invert it to learn that $T$ is a $forall$ with a
  particular domain and codomain; since $T$ is only given up to
  definitional equality, that inversion is the injectivity of
  $forall$ — which, as @sec:rules noted, the model does not even
  validate. Here nothing is inverted. The checker itself reduced $T$ to a syntactic $forall$, the
  first claim says the reduction did not change the set, and that set
  _is_ a function space or a truth value by the interpretation's
  clause. Membership in it is all that is asked.

  _The rest_, by induction on the derivation ($iota$ waits for the
  environment section).

  - Reduction: the no-step reduction is $lden e rden_rho = lden e rden_rho$;
    trans chains two reductions, passing the invariant along; head
    reduces the function of a well-denoted application and keeps the
    application's clause, because the function's set did not change
    #src("whitepaper/Fragment/Sound.lean", 116, 134).
  - Equality: refl is again $lden e rden_rho = lden e rden_rho$, and
    sym swaps the two invariants
    #src("whitepaper/Fragment/Sound.lean", 254, 259). The congruences
    for $forall$ and $lambda$ apply the hypothesis to the domains, then
    to the bodies at every value of the right-hand domain — which the
    domains' equality makes the left-hand domain too — and finish with
    the library's congruence laws; the congruence for applications
    applies the hypothesis to both parts
    #src("whitepaper/Fragment/Sound.lean", 279, 311) (real proof:
    #src("ConLeche/Model/Rules/DefEqSound.lean", 114, 120),
    #src("ConLeche/Model/Rules/DefEqSound.lean", 138, 144),
    #src("ConLeche/Model/Rules/DefEqSound.lean", 162, 164)).
  - Inference: a variable's type is read off the satisfied context; a
    sort's type is the next universe, which contains it; a constant's
    type is the environment's first law
    #src("whitepaper/Fragment/Sound.lean", 385, 402) (real proof:
    #src("ConLeche/Model/Rules/InferSound.lean", 136, 137),
    #src("ConLeche/Model/Rules/InferSound.lean", 152, 153),
    #src("ConLeche/Model/Rules/InferSound.lean", 173, 178)).

  In every one of these cases the invariant of every term the induction
  hypothesis is applied to is either a subterm's, or was produced by
  another claim.
]

*Why there is no transitivity.* The equality relation has rules for
reflexivity and symmetry, but none saying that $a equiv b$ and
$b equiv c$ give $a equiv c$, and @sec:rules said none can be added.
The proof above shows exactly why. The second claim assumes both sides
well-denoted. In a transitivity case the induction would have to apply
the hypothesis to $a equiv b$, and for that it needs $b$ well-denoted
— but $b$ is not a subterm of $a$ or $c$, and no premise produced it.
It comes from nowhere, and nothing supplies its invariant. The other
rules never have this problem, and that is by design: in every rule,
the subject of an equality premise is a subterm of the conclusion, or a
term that a reduction premise or an inference premise produced — a
reduct, an inferred type — whose invariant the corresponding claim
delivers #src("whitepaper/Fragment/Rules.lean", 137, 151). The one way
to chain is therefore "reduce, then continue", and that is how the
checker's equality test is structured: it head-normalises a side and
compares again. (In the real checker a transitivity rule would be not
merely unprovable but false, for the reason @sec:rules gave
#src("ConLeche/Rules/Rel.lean", 310, 333).)

The absence is not a restriction on the checker. Its equality test
never chains through an arbitrary middle term; every comparison it
makes is one of the rules. Transitivity is a property one would want of
a _type theory_; the relation here describes a _checker_, and the
model only has to agree with what the checker does.
