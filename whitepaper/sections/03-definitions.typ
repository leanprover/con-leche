#import "../lib.typ": *

// Notation local to this file, matching §2.
#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let zn = $sans("zeroness")$

= Adding definitions <sec:env>

§2 had no environment. This section adds one, and with it the
constants that refer to its entries, the reduction rule $delta$ that
unfolds a definition, and the _model_ of the environment that the
interpretation reads a constant off. The environment grows one
declaration at a time, and each step is checked by the relations
of §2, extended by the rules below. We say what the checker checks at
each step, what the checker stores, and how the model grows with the
environment so that its laws keep holding. This section does it for
definitions; inductive types, the rule $iota$ and the consistency
corollary follow in @sec:ind.

== Definitions <sec:defs>

*The environment* is a list of the constants accepted so far, most
recent first
(#src("whitepaper/Fragment/Env.lean", 88, 104)[fragment],
#src("ConLeche/Kernel/Env.lean", 677)[real checker]). A stored
constant has its level parameters $arrow(p)$, its type — a closed
term over $arrow(p)$ — and its _kind_
(#src("whitepaper/Fragment/Env.lean", 45, 79)[fragment],
#src("ConLeche/Kernel/Env.lean", 461, 475)[real checker]): a
_definition_ carries a value; the other kinds — type former,
constructor, recursor — are what an inductive block stores, and
@sec:ind-checks introduces them. A name is
stored at most once. The fragment has no axioms, no theorems as
distinct from definitions, and no quotients (§6).

*Constants.* The grammar of @sec:terms gains one form: a constant $c$
of the environment, used at a list of levels $arrow(ell)$, one per
level parameter of its declaration
(#src("whitepaper/Fragment/Syntax.lean", 36, 37)[fragment],
#src("ConLeche/Kernel/Expr.lean", 344, 354)[real checker]).

$
  e & colon.double.eq dots | c.\{arrow(ell)\}
$

_Level instantiation_ $e[arrow(p) := arrow(ell)]$, used when a constant
declared with level parameters $arrow(p)$ is taken at the levels
$arrow(ell)$, replaces the parameters in sorts, in the level lists of
constants, and in the annotations.  There "all of $q_1, ..., q_k$ zero"
becomes "each of the substitutes of $q_1, ..., q_k$ is zero", computed
with the $zn$ function of @sec:levels and the intersection of
data
(#src("whitepaper/Fragment/Syntax.lean", 104, 112)[fragment],
#src("whitepaper/Fragment/PropWhen.lean", 322, 329)[its datum part]\;
#src("ConLeche/Kernel/Level.lean", 234, 245)[real checker],
#src("ConLeche/Kernel/Level.lean", 205, 207)[datum part]).

*The rules for constants.* A constant has its declared type at the
levels it is used at, and two constants of the same name are compared
through the level oracle
(#src("whitepaper/Fragment/Rules.lean", 242, 246)[fragment, inference]
and #src("whitepaper/Fragment/Rules.lean", 191, 195)[equality]\;
#src("ConLeche/Rules/Rel.lean", 494, 502)[real checker, inference]
and #src("ConLeche/Rules/Rel.lean", 357, 362)[equality]).

#rules(
  rule(name: "const",
    $c "stored with parameters" arrow(p) "and type" T$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$),
  rule(name: "const", $arrow(ell) eq.dot arrow(ell)'$,
    $Gamma tack c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$),
)

*The $delta$ rule.* A definition unfolds to its value at the levels
it is used at
(#src("whitepaper/Fragment/Rules.lean", 77, 83)[fragment],
#src("ConLeche/Rules/Rel.lean", 129, 133)[real checker]). With the
head rule of @sec:rules, an applied definition unfolds at its head.

#rules(
  rule(name: "delta",
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

*The interpretation, extended.* The interpretation of @sec:interp
gains one parameter, an _assignment_ $M$ of a set to every constant
at every list of concrete levels, and one clause: a constant denotes
what the assignment says,

$
  lden c.\{arrow(ell)\} rden_rho & = M(c, phi(arrow(ell)))
$

with $phi(arrow(ell))$ the list of the levels' values
(#src("whitepaper/Fragment/Interp.lean", 124, 130)[fragment]). It
stays term-directed: no environment lookup, no derivation, no type.
A third lemma joins the two of @sec:interp, by the same induction:
#src("whitepaper/Fragment/Interp.lean", 215, 217)[instantiating
level parameters] is changing the valuation. And the semantic
invariant gains the clause that a constant, like a variable or a
sort, is always well-denoted.

*The three-law contract.* What the soundness theorem, extended below,
assumes of the environment: #src("whitepaper/Fragment/EnvModel.lean", 163, 189)[a _model_]
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
+ every rule of a stored recursor satisfies its $iota$ law — a law
  about the declarations of @sec:ind, stated and used there.

The real proof's carrier has the same three laws among others
(#src("ConLeche/Model/Annot/EnvModelM.lean", 71, 100)[the carrier's invariant]).
The laws mention the model only at the _stored_ terms — the types,
the values, and in @sec:ind the rules' right-hand sides — and quantify over sets
where a use site would have terms. That is deliberate: when a fresh
constant is added, no stored term mentions it, so every old law is
read off the extended assignment exactly as off the old one, and
nothing has to be re-proved. The empty environment has a model
trivially: any assignment, and three laws with nothing to say
(#src("whitepaper/Fragment/EnvModel.lean", 191, 196)[fragment]).

*Soundness, extended.* @thm:sound holds for the relations extended by
the three rules above, with one more hypothesis: fix a model of the
environment, a valuation $phi$, and let $rho$ satisfy $Gamma$; then
the three claims hold as stated
(#src("whitepaper/Fragment/Sound.lean", 679, 683)[fragment]), and
@cor:closed holds under every model. The induction of @sec:claims
gains three cases, one per rule.

#proof[
  #src("whitepaper/Fragment/Sound.lean", 193, 199)[_δ_] ($c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$ for a
  definition $c$ with parameters $arrow(p)$ and value $v$, at
  $|arrow(ell)| = |arrow(p)|$ levels). Law 2 says the instantiated
  value is well-denoted and denotes $M(c, phi(arrow(ell)))$, which is
  what the constant denotes
  (#src("ConLeche/Model/Rules/RedSound.lean", 247, 248)[real proof]).
  The redex's semantic invariant is not even needed.
  @thm:install-def shows the law holds when a definition is added.

  #src("whitepaper/Fragment/Sound.lean", 379, 381)[_const_, equality]
  ($c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$ when
  $arrow(ell) eq.dot arrow(ell)'$ pointwise). The oracle answers yes
  only if the levels agree at every valuation (@sec:levels), so the
  two constants read the same entry of $M$
  (#src("ConLeche/Model/Rules/DefEqSound.lean", 79, 81)[real proof]).

  #src("whitepaper/Fragment/Sound.lean", 501, 506)[_const_, inference]
  ($c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$). The constant is
  well-denoted, and law 1 says its instantiated type is well-denoted
  and contains the constant's set
  (#src("ConLeche/Model/Rules/InferSound.lean", 173, 178)[real proof]).
]

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
  same as changing the valuation (above), so it holds at every
  $arrow(ell)$; and $v$ and $T$ mention no constant but old ones, so
  the two sets are the same under $M'$ as under $M$ (the scope check,
  above). That is law 1, and law 2 is the definition of $M'$ at $c$.
  Law 3 has no new instance.
]

The proof is two lines because everything difficult was done in §2:
the checks a definition passes are exactly the premises of the
corollary, and the corollary's conclusion is exactly law 1.

