#import "../lib.typ": *

// Notation local to this file, matching §2.
#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let zn = $sans("zeroness")$

= Adding definitions <sec:env>

§2 had no environment. This section adds one, together with the
constants that refer to its entries, the reduction rule $delta$ that
unfolds a definition, and the _model_ of the environment, from which
the interpretation reads a constant. The environment grows one
declaration at a time, and each step is checked by the relations
of §2, extended by the rules below. We say what the checker checks at
each step, what it stores, and how the model grows with the
environment so that its laws keep holding. This section covers
definitions; inductive types, the rule $iota$ and the consistency
corollary follow in @sec:ind.

*The environment* $E$, fixed throughout like the valuation, is a
#src("whitepaper/Fragment/Env.lean", 109, 125)[list of the constants] accepted so far,
#src("ConLeche/Kernel/Env.lean", 536)[most recent first]. A
#src("whitepaper/Fragment/Env.lean", 63, 100)[stored constant] has its level parameters $arrow(p)$, its type (a closed
term over $arrow(p)$) and #src("ConLeche/Kernel/Env.lean", 354, 368)[its _kind_]. We write
$(c.\{arrow(p)\} : T) in E$ for "$c$ is stored with parameters
$arrow(p)$ and type $T$", and $(c.\{arrow(p)\} : T := v) in E$ when
it is a definition with value $v$. A
_definition_ carries a value. The other kinds (type former,
constructor, recursor) are what an inductive block stores, and
@sec:ind-checks introduces them. A name is
stored at most once.

*Constants.* The grammar of @sec:terms gains one form: a #src("whitepaper/Fragment/Syntax.lean", 35, 36)[constant $c$]
of the environment, used at a list of levels $arrow(ell)$,
#src("ConLeche/Kernel/Expr.lean", 315, 325)[one per level parameter] of its declaration.

$
  e & colon.double.eq dots | c.\{arrow(ell)\}
$

#src("whitepaper/Fragment/Syntax.lean", 112, 121)[_Level instantiation_] $e[arrow(p) := arrow(ell)]$, used when a constant
declared with level parameters $arrow(p)$ is taken at the levels
$arrow(ell)$, replaces the parameters in sorts and in the level lists
of constants
(#src("ConLeche/Kernel/Level.lean", 218, 231)[as in con-leche]).

*The rules for constants.* A constant
#src("whitepaper/Fragment/Rules.lean", 749, 753)[has its declared type] at the
levels it is used at, and two constants of the same name
#src("whitepaper/Fragment/Rules.lean", 563, 566)[are compared] through the level oracle
(in con-leche: #src("ConLeche/Rules/Rel.lean", 560, 566)[inference]
and #src("ConLeche/Rules/Rel.lean", 381, 386)[equality]).

#rules(
  rule(name: "const",
    $(c.\{arrow(p)\} : T) in E$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$),
  rule(name: "const", $arrow(ell) eq.dot arrow(ell)'$,
    $Gamma tack c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$),
)

*The $delta$ rule.* A definition #src("whitepaper/Fragment/Rules.lean", 88, 94)[unfolds to its value] at the levels
it is used at
(#src("ConLeche/Rules/Rel.lean", 137, 141)[as in con-leche]). With the
head rule of @sec:rules, an applied definition unfolds at its head.

#rules(
  rule(name: "delta",
    $(c.\{arrow(p)\} : T := v) in E$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$),
)

*What a definition must satisfy.* Before the checker stores a
definition $c$ with parameters $arrow(p)$, type $T$ and value $v$, it
#src("whitepaper/Fragment/Decl.lean", 591, 605)[checks four things]
(in con-leche: #src("ConLeche/Kernel/CheckerBase.lean", 105, 121)[the common checks]
and #src("ConLeche/Kernel/Checker.lean", 34, 47)[the value check]):

- the name $c$ is fresh;
- the type has a sort: $tack T => S red Sort u$;
- the value's inferred type is definitionally equal to the declared
  type: $tack v => T'$ and $tack T' equiv T$;
- both terms #src("whitepaper/Fragment/Decl.lean", 604, 605)[use only the level parameters] $arrow(p)$.

A stored term is thus closed, mentions only stored constants and
uses only the declared level parameters. These three facts
let the model read a stored term without looking at anything
that is added later, because the interpretation of a term depends only on
the constants and the free variables it mentions and the level
parameters it uses
(#src("whitepaper/Fragment/Hygiene.lean", 593, 595)[constants],
#src("whitepaper/Fragment/Hygiene.lean", 466, 468)[variables],
#src("whitepaper/Fragment/Hygiene.lean", 656, 658)[parameters]).

*The interpretation, extended.* The interpretation of @sec:interp
gains one parameter, an _assignment_ $M$ of a set to every constant
at every list of concrete levels, and one clause: a constant
#src("whitepaper/Fragment/Interp.lean", 142)[denotes what the assignment says],

$
  lden c.\{arrow(ell)\} rden_rho & = M(c, phi(arrow(ell)))
$

with $phi(arrow(ell))$ the list of the levels' values. It
stays term-directed. $M$ is a parameter like $rho$, consulted at a
constant the way $rho$ is at a variable. The environment $E$ itself,
with its stored types and values, is never read, and no derivation and
no type is needed.
A fourth lemma joins those of @sec:interp, by the same induction:
#src("whitepaper/Fragment/Interp.lean", 256, 258)[instantiating
level parameters] is changing the valuation. And the semantic
invariant gains the clause that a constant, like a variable or a
sort, is always well-denoted.

*The contract.* What the soundness theorem, extended below,
assumes of the environment is #src("whitepaper/Fragment/EnvModel.lean", 298, 362)[a _model_]: an
assignment $M(c, arrow(n))$ of a set to every constant $c$ and every
list of natural numbers $arrow(n)$ (the values of its level
parameters), satisfying two laws (four more, for inductive types,
join in @sec:ind). Throughout, $arrow(ell)$ ranges
over level lists with $|arrow(ell)| = |arrow(p)|$, $phi$ over
valuations and $rho$ over variable environments, and $rho models e$ is
the semantic invariant of @sec:inv.

#definition(name: "Model of an environment")[
  #set enum(numbering: "1.")
  + #src("whitepaper/Fragment/EnvModel.lean", 302, 310)[Typing]: for every $(c.\{arrow(p)\} : T) in E$,
    $ rho models T[arrow(p) := arrow(ell)], quad lden T[arrow(p) := arrow(ell)] rden_rho "is a type", quad "and" quad
      M(c, phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden_rho. $
  + #src("whitepaper/Fragment/EnvModel.lean", 311, 317)[Unfolding]: for every $(c.\{arrow(p)\} : T := v) in E$,
    $ rho models v[arrow(p) := arrow(ell)] quad "and" quad
      lden v[arrow(p) := arrow(ell)] rden_rho = M(c, phi(arrow(ell))). $
] <def:model>

In words: every stored constant is a member of its type, which is a
type in the sense of @sec:interp, and a
definition's value denotes the constant, at every instantiation of
the declared level parameters.

#real[
  The real proof's model carries the same two laws among others
  (#src("ConLeche/Model/Env/EnvModelM.lean", 229, 252)[the carrier's invariant]).
]

The empty environment #src("whitepaper/Fragment/EnvModel.lean", 364, 373)[has a model
trivially]: any assignment, and laws with nothing to say.

*Soundness, extended.* @thm:sound holds for the relations extended by
the three rules above, with one more hypothesis: fix a model of the
environment, a valuation $phi$, and let $rho$ satisfy $Gamma$; then
the three claims #src("whitepaper/Fragment/Sound.lean", 2322, 2326)[hold as stated], and
@cor:closed holds under every model. The induction of @sec:claims
gains three cases, one per rule.

#proof[
  *#src("whitepaper/Fragment/Sound.lean", 144, 150)[Rule delta]*, $c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$ for a
  definition $c$ with parameters $arrow(p)$ and value $v$, at
  $|arrow(ell)| = |arrow(p)|$ levels: \
  Law 2 says the instantiated
  value is well-denoted and denotes $M(c, phi(arrow(ell)))$, which is
  #src("ConLeche/Model/Rules/RedSound.lean", 211, 212)[what the constant denotes].
  The redex's semantic invariant is not used.
  @thm:install-def shows the law holds when a definition is added.

  *#src("whitepaper/Fragment/Sound.lean", 177, 179)[Rule const, equality]*,
  $c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$ when
  $arrow(ell) eq.dot arrow(ell)'$ pointwise: \
  The oracle answers yes
  only if the levels agree at every valuation (@sec:levels), so the
  two constants #src("ConLeche/Model/Rules/DefEqSound.lean", 69, 71)[read the same entry of $M$].

  *#src("whitepaper/Fragment/Sound.lean", 276, 281)[Rule const, inference]*,
  $c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$: \
  The constant is
  well-denoted, and law 1 says its instantiated type is well-denoted,
  a type, and #src("ConLeche/Model/Rules/InferSound.lean", 210, 215)[contains the constant's set].
]

#theorem(name: "Installing a definition")[
  If the environment has a model and the definition $c$ passes the
  checks above, then the environment
  #src("whitepaper/Fragment/InstallDef.lean", 345, 350)[extended with $c$ has a model]
  (#src("ConLeche/Model/Install.lean", 337, 340)[as in con-leche]).
] <thm:install-def>

#proof[
  Let $M$ be the model. Define $M'$ as $M$ on every old constant and,
  at $c$ and a list $arrow(n)$, as the set $lden v rden$ read at the
  valuation that sends $arrow(p)$ to $arrow(n)$. Since $v$ is closed and
  uses no other parameter, no $rho$ and no other part of $phi$
  enters. The old laws hold for $M'$ because
  #src("whitepaper/Fragment/InstallDef.lean", 158, 161)[no stored term mentions $c$]. For the new constant we use @cor:closed and the second claim of
  @thm:sound. From $tack v => T'$ the value and $T'$ are
  well-denoted and $lden v rden in lden T' rden$, a type; from
  $tack T => S red Sort u$ the type $T$ is well-denoted and a type;
  two types are never the point, so the second claim applies to
  $tack T' equiv T$ and gives $lden v rden in lden T rden$. This holds
  at every valuation, and instantiating the level parameters is the
  same as changing the valuation (above), so it holds at every
  $arrow(ell)$. Finally, $v$ and $T$ are closed and mention no constant but
  old ones, because the derivations are in the empty context, where
  #src("whitepaper/Fragment/ScopeOfInfer.lean", 37, 38)[no rule types a variable] and
  #src("whitepaper/Fragment/ScopeOfInfer.lean", 60, 61)[the constant rule requires the constant stored]. So
  the two sets are the same under $M'$ as under $M$. That is law 1,
  and law 2 is the definition of $M'$ at $c$.
]

The proof is short because §2 did the work. The checks a definition
passes are the premises of the corollary, and the corollary's
conclusion is law 1.

