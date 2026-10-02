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

*The environment* $E$ — fixed throughout, like the valuation — is a
list of the constants accepted so far, most recent first
(#src("whitepaper/Fragment/Env.lean", 101, 117)[fragment],
#src("ConLeche/Kernel/Env.lean", 674)[real checker]). A stored
constant has its level parameters $arrow(p)$, its type — a closed
term over $arrow(p)$ — and its _kind_; we write
$(c.\{arrow(p)\} : T) in E$ for "$c$ is stored with parameters
$arrow(p)$ and type $T$", and $(c.\{arrow(p)\} : T := v) in E$ when
it is a definition with value $v$
(#src("whitepaper/Fragment/Env.lean", 55, 92)[fragment],
#src("ConLeche/Kernel/Env.lean", 468, 482)[real checker]): a
_definition_ carries a value; the other kinds — type former,
constructor, recursor — are what an inductive block stores, and
@sec:ind-checks introduces them. A name is
stored at most once.

*Constants.* The grammar of @sec:terms gains one form: a constant $c$
of the environment, used at a list of levels $arrow(ell)$, one per
level parameter of its declaration
(#src("whitepaper/Fragment/Syntax.lean", 36, 37)[fragment],
#src("ConLeche/Kernel/Expr.lean", 328, 338)[real checker]).

$
  e & colon.double.eq dots | c.\{arrow(ell)\}
$

_Level instantiation_ $e[arrow(p) := arrow(ell)]$, used when a constant
declared with level parameters $arrow(p)$ is taken at the levels
$arrow(ell)$, replaces the parameters in sorts, in the level lists of
constants — and in the annotations, so that the instantiated term is
annotated for the levels it is now used at
(#src("whitepaper/Fragment/Syntax.lean", 104, 112)[fragment],
#src("whitepaper/Fragment/PropWhen.lean", 322, 329)[its datum part]\;
#src("ConLeche/Kernel/Level.lean", 230, 241)[real checker],
#src("ConLeche/Kernel/Level.lean", 206, 208)[datum part]).

*The rules for constants.* A constant has its declared type at the
levels it is used at, and two constants of the same name are compared
through the level oracle
(#src("whitepaper/Fragment/Rules.lean", 303, 307)[fragment, inference]
and #src("whitepaper/Fragment/Rules.lean", 252, 256)[equality]\;
#src("ConLeche/Rules/Rel.lean", 489, 495)[real checker, inference]
and #src("ConLeche/Rules/Rel.lean", 356, 361)[equality]).

#rules(
  rule(name: "const",
    $(c.\{arrow(p)\} : T) in E$,
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
    $(c.\{arrow(p)\} : T := v) in E$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$),
)

*What a definition must satisfy.* Before the checker stores a
definition $c$ with parameters $arrow(p)$, type $T$ and value $v$, it
checks four things
(#src("whitepaper/Fragment/Decl.lean", 592, 606)[fragment],
#src("ConLeche/Kernel/CheckerBase.lean", 96, 116)[real checker, the common checks]
and #src("ConLeche/Kernel/Checker.lean", 34, 50)[the value check]):

- the name $c$ is fresh;
- the type has a sort: $tack T => S red Sort u$;
- the value's inferred type is definitionally equal to the declared
  type: $tack v => T'$ and $tack T' equiv T$;
- both terms use only the level parameters $arrow(p)$
  (#src("whitepaper/Fragment/Decl.lean", 605, 606)[fragment]) — the
  one condition the typing derivations do not give, since the rules
  accept $Sort u$ for any level $u$. That both terms are closed and
  mention only stored constants follows from the two derivations
  being in the empty context: no rule types a variable there
  (#src("whitepaper/Fragment/ScopeOfInfer.lean", 36, 37)[fragment]),
  and the constant rule requires the constant to be stored
  (#src("whitepaper/Fragment/ScopeOfInfer.lean", 55, 56)[fragment]).

These three facts are
what let the model read a stored term without looking at anything
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
stays term-directed: $M$ is a parameter like $rho$, consulted at a
constant the way $rho$ is at a variable; the environment $E$ itself —
the stored types and values — is never read, and no derivation and
no type is needed.
A third lemma joins the two of @sec:interp, by the same induction:
#src("whitepaper/Fragment/Interp.lean", 215, 217)[instantiating
level parameters] is changing the valuation. And the semantic
invariant gains the clause that a constant, like a variable or a
sort, is always well-denoted.

*The contract.* What the soundness theorem, extended below,
assumes of the environment is #src("whitepaper/Fragment/EnvModel.lean", 192, 229)[a _model_]: an
assignment $M(c, arrow(n))$ of a set to every constant $c$ and every
list of natural numbers $arrow(n)$ — the values of its level
parameters — satisfying two laws (a third, for recursors, joins in
@sec:ind). Throughout, $arrow(ell)$ ranges
over level lists with $|arrow(ell)| = |arrow(p)|$, $phi$ over
valuations and $rho$ over variable environments, and $rho models e$ is
the semantic invariant of @sec:inv.

#definition(name: "Model of an environment")[
  #set enum(numbering: "1.")
  + #src("whitepaper/Fragment/EnvModel.lean", 196, 203)[Typing]: for every $(c.\{arrow(p)\} : T) in E$,
    $ rho models T[arrow(p) := arrow(ell)] quad "and" quad
      M(c, phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden_rho. $
  + #src("whitepaper/Fragment/EnvModel.lean", 204, 210)[Unfolding]: for every $(c.\{arrow(p)\} : T := v) in E$,
    $ rho models v[arrow(p) := arrow(ell)] quad "and" quad
      lden v[arrow(p) := arrow(ell)] rden_rho = M(c, phi(arrow(ell))). $
] <def:model>

In words: every stored constant is a member of its type, and a
definition's value denotes the constant, at every instantiation of
the declared level parameters.

The real proof's carrier has the same laws among others
(#src("ConLeche/Model/Annot/EnvModelM.lean", 159, 185)[the carrier's invariant]).
The laws mention the model only at the _stored_ terms — the types,
the values, and in @sec:ind the rules' right-hand sides — and quantify over sets
where a use site would have terms. That is deliberate: when a fresh
constant is added, no stored term mentions it, so every old law is
read off the extended assignment exactly as off the old one, and
nothing has to be re-proved. The empty environment has a model
trivially: any assignment, and laws with nothing to say
(#src("whitepaper/Fragment/EnvModel.lean", 231, 237)[fragment]).

*Soundness, extended.* @thm:sound holds for the relations extended by
the three rules above, with one more hypothesis: fix a model of the
environment, a valuation $phi$, and let $rho$ satisfy $Gamma$; then
the three claims hold as stated
(#src("whitepaper/Fragment/Sound.lean", 817, 821)[fragment]), and
@cor:closed holds under every model. The induction of @sec:claims
gains three cases, one per rule.

#proof[
  *#src("whitepaper/Fragment/Sound.lean", 193, 199)[Rule delta]* — $c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$ for a
  definition $c$ with parameters $arrow(p)$ and value $v$, at
  $|arrow(ell)| = |arrow(p)|$ levels: \
  Law 2 says the instantiated
  value is well-denoted and denotes $M(c, phi(arrow(ell)))$, which is
  what the constant denotes
  (#src("ConLeche/Model/Rules/RedSound.lean", 240, 241)[real proof]).
  The redex's semantic invariant is not even needed.
  @thm:install-def shows the law holds when a definition is added.

  *#src("whitepaper/Fragment/Sound.lean", 511, 513)[Rule const, equality]*
  — $c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$ when
  $arrow(ell) eq.dot arrow(ell)'$ pointwise: \
  The oracle answers yes
  only if the levels agree at every valuation (@sec:levels), so the
  two constants read the same entry of $M$
  (#src("ConLeche/Model/Rules/DefEqSound.lean", 76, 78)[real proof]).

  *#src("whitepaper/Fragment/Sound.lean", 633, 638)[Rule const, inference]*
  — $c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$: \
  The constant is
  well-denoted, and law 1 says its instantiated type is well-denoted
  and contains the constant's set
  (#src("ConLeche/Model/Rules/InferSound.lean", 172, 177)[real proof]).
]

#theorem(name: "Installing a definition")[
  If the environment has a model and the definition $c$ passes the
  checks above, then the environment extended with $c$ has a model.
  (#src("whitepaper/Fragment/InstallDef.lean", 305, 310)[fragment],
  #src("ConLeche/Model/Install.lean", 271, 273)[real proof].)
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
]

The proof is two lines because everything difficult was done in §2:
the checks a definition passes are exactly the premises of the
corollary, and the corollary's conclusion is exactly law 1.

