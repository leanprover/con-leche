#import "../lib.typ": *

// Notation local to this file, matching §2.
#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let Nat = $sans("Nat")$

= Adding definitions <sec:env>

§2 fixed an environment and assumed a model of it: an assignment $M$
of a set to every constant at every list of levels, and three laws
about the stored constants. This section and the next are about where
that model comes from. The environment grows one declaration at a time
— a definition, or an inductive block with its constructors and
recursor — and each step is checked by the relations of §2. We say
what the checker checks at each step, what the checker stores, and how
the model grows with the environment so that the three laws keep
holding. This section does it for definitions and states the reduction
rule $delta$, which §2 deferred because it reads the environment;
inductive types, the rule $iota$ and the consistency corollary follow
in @sec:ind.

== Definitions <sec:defs>

*The environment* is a list of the constants accepted so far, most
recent first
(#src("whitepaper/Fragment/Env.lean", 88, 104)[fragment],
#src("ConLeche/Kernel/Env.lean", 677)[real checker]). A stored
constant has its level parameters $arrow(p)$, its type — a closed
term over $arrow(p)$ — and its _kind_
(#src("whitepaper/Fragment/Env.lean", 45, 79)[fragment],
#src("ConLeche/Kernel/Env.lean", 461, 475)[real checker]): a
_definition_ carries a value; an _inductive type former_ carries its
parameter and index counts and the names of its constructors; a
_constructor_ names its type and carries its parameter and field
counts; a _recursor_ carries the shape of its argument list — how
many parameters, motives, minor premises and indices precede the
major premise (the recursor's argument groups; @ex:nat shows them on
$Nat$) — and its reduction rules, one per constructor, each a closed
right-hand side over the recursor's level parameters
(#src("whitepaper/Fragment/Env.lean", 30, 43)[fragment],
#src("ConLeche/Kernel/Env.lean", 249, 262)[real checker]). A name is
stored at most once. The fragment has no axioms, no theorems as
distinct from definitions, and no quotients (§6).

*The $delta$ rule.* A definition unfolds to its value at the levels
it is used at
(#src("whitepaper/Fragment/Rules.lean", 77, 83)[fragment],
#src("ConLeche/Rules/Rel.lean", 129, 133)[real checker]). With the
head rule of @sec:rules, an applied definition unfolds at its head.

#rules(
  rule(name: "δ",
    $c "stored as a definition with parameters" arrow(p) "and value" v$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$),
)

*What a definition must satisfy.* Before the checker stores a
definition $c$ with parameters $arrow(p)$, type $T$ and value $v$, it
checks four things
(#src("whitepaper/Fragment/Decl.lean", 415, 425)[fragment],
#src("ConLeche/Kernel/CheckerBase.lean", 99, 119)[real checker, the common checks]
and #src("ConLeche/Kernel/Checker.lean", 36, 52)[the value check]): the
name is fresh; the type has a sort, $tack T => S red Sort u$; the
value's inferred type is definitionally equal to the declared type,
$tack v => T' $ and $tack T' equiv T$; and both terms are _in scope_
— closed, mentioning only stored constants, using only the level
parameters $arrow(p)$
(#src("whitepaper/Fragment/Decl.lean", 403, 407)[fragment]). All
in the empty context: stored terms are closed. The scope check is
what lets the model read a stored term without looking at anything
that is added later: the interpretation of a term depends only on
the constants and the free variables it mentions and the level
parameters it uses
(#src("whitepaper/Fragment/Hygiene.lean", 498, 500)[constants],
#src("whitepaper/Fragment/Hygiene.lean", 387, 389)[variables],
#src("whitepaper/Fragment/Hygiene.lean", 554, 556)[parameters]).

*The contract between §2 and §3–§4.* Here, once more and in full, is
what §2 assumed of the environment: #src("whitepaper/Fragment/EnvModel.lean", 163, 189)[a _model_]
is an assignment $M(c, arrow(n))$ of a set to every constant $c$ and
every list of natural numbers $arrow(n)$ — the values of its level
parameters — such that

+ #src("whitepaper/Fragment/EnvModel.lean", 167, 174)[every stored constant is a member of its type]: for every
  stored $c$ with parameters $arrow(p)$ and type $T$, at every list
  of levels $arrow(ell)$ of the right length and every valuation
  $phi$, the instantiated type $T[arrow(p) := arrow(ell)]$ is
  well-denoted and $M(c, phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden$;
+ #src("whitepaper/Fragment/EnvModel.lean", 175, 181)[a definition's value denotes the constant]: for a stored
  definition $c$ with value $v$, the instantiated value is
  well-denoted and $lden v[arrow(p) := arrow(ell)] rden = M(c, phi(arrow(ell)))$;
+ #src("whitepaper/Fragment/EnvModel.lean", 182, 189)[every recursor rule satisfies its $iota$ law], a statement
  about sets that @sec:ind-model spells out.

The real proof's carrier has the same three laws among others
(#src("ConLeche/Model/Annot/EnvModelM.lean", 71, 100)[the carrier's invariant],
#src("ConLeche/Model/Annot/Laws.lean", 436, 439)[the $iota$ law]).
The laws mention the model only at the _stored_ terms — the types,
the values, the rules' right-hand sides — and quantify over sets
where a use site would have terms. That is deliberate: when a fresh
constant is added, no stored term mentions it, so every old law is
read off the extended assignment exactly as off the old one, and
nothing has to be re-proved. The empty environment has a model
trivially: any assignment, and three laws with nothing to say
(#src("whitepaper/Fragment/EnvModel.lean", 191, 196)[fragment]).

#theorem(name: "Installing a definition")[
  If the environment has a model and the definition $c$ passes the
  checks above, then the environment extended with $c$ has a model.
  (#src("whitepaper/Fragment/InstallDef.lean", 281, 286)[fragment],
  #src("ConLeche/Model/Install.lean", 446, 448)[real proof].)
] <thm:install-def>

#proof[
  Let $M$ be the model. Define $M'$ as $M$ on every old constant and,
  at $c$ and a list $arrow(n)$, as the set $lden v rden$ read at the
  valuation that sends $arrow(p)$ to $arrow(n)$ — $v$ is closed and
  uses no other parameter, so no $rho$ and no other part of $phi$
  enters. The old laws hold for $M'$ because no stored term mentions
  $c$ (#src("whitepaper/Fragment/InstallDef.lean", 158, 161)[fragment]). For the new constant, @cor:closed and the second claim of
  @thm:sound do the work: from $tack v => T'$ the value and $T'$ are
  well-denoted and $lden v rden in lden T' rden$; from $tack T => S$
  the type is well-denoted; so the second claim applies to
  $tack T' equiv T$ and gives $lden v rden in lden T rden$. This holds
  at every valuation, and instantiating the level parameters is the
  same as changing the valuation (@sec:interp), so it holds at every
  $arrow(ell)$; and $v$ and $T$ mention no constant but old ones, so
  the two sets are the same under $M'$ as under $M$ (the scope check,
  above). That is law 1, and law 2 is the definition of $M'$ at $c$.
  Law 3 has no new instance.
]

The proof is two lines because everything difficult was done in §2:
the checks a definition passes are exactly the premises of the
corollary, and the corollary's conclusion is exactly law 1. The same
shape recurs for inductive blocks, with two new pieces of work:
showing that the constructed sets — the family, the constructors, the
recursor — are members of their generated types (law 1), and the
$iota$ law (law 3).

