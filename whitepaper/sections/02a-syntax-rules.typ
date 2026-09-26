#import "../lib.typ": *

// Notation local to this file.  Everything a rule mentions is spelled
// here once, so the rules below read the same in the PDF and the HTML.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let whenZero = $sans("whenZero")$
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let zn = $sans("zeroness")$
#let red = sym.arrow.r.squiggly

== Terms and the annotation <sec:terms>

The terms of the fragment are Lean's kernel terms, minus what §6
leaves out.  The grammar, with the annotation in colour:

$
  e & colon.double.eq x | Sort u | c.\{arrow(ell)\} | e thick e
      | lambda x : A thin ann(PW). thin e | forall x : A thin ann(PW). thin e \
  PW & colon.double.eq never | whenZero \{p_1, ..., p_k\}
$

A term is a variable $x$; a sort $Sort u$ at a universe level $u$
(@sec:levels), with $sans("Prop") = Sort 0$; a constant $c$ of the
environment, used at a list of levels $arrow(ell)$, one per level
parameter of its declaration; an application $f thick a$; a function
$lambda x : A thin ann(PW). thin b$; or a dependent function type
$forall x : A thin ann(PW). thin B$, written $A -> B$ when $x$ does not
occur in $B$.  Types are terms; there is no separate class.
(#src("whitepaper/Fragment/Syntax.lean", 30, 46)[fragment],
#src("ConLeche/Kernel/Expr.lean", 344, 354)[real checker].)

The paper writes named variables, with the usual conventions: terms
are taken up to renaming of bound variables, and $B[x := a]$ is the
capture-avoiding substitution of $a$ for $x$.  The Lean fragment uses
de Bruijn indices instead (a variable is the number of binders
between its occurrence and its own), and a rule that mentions the types of the
variables in scope carries a _context_ $Gamma$, a list of those types.
The real checker does neither: it opens a binder with a fresh free
variable that carries its own type, so the checker keeps no context
at all — a performance device that changes nothing below.  No rule in
this paper needs index arithmetic in its named form.

*The annotation.*  Every binder carries, after its domain, one datum
$ann(PW)$.  It answers a single question: _when is the body a
proposition?_  The answer is one of two shapes:

- $ann(never)$: the body is not a proposition, whatever the level
  parameters are;
- $ann(whenZero \{p_1\, ...\, p_k\})$: the body is a proposition exactly
  when the level parameters $p_1, ..., p_k$ are all zero.
  $ann(whenZero \{\})$ means "always".

A _valuation_ $phi$ assigns a natural number to every level parameter.
A datum is _read_ at a valuation: $ann(never)$ reads false, and
$ann(whenZero \{p_1\, ...\, p_k\})$ reads true exactly when
$phi(p_1) = ... = phi(p_k) = 0$.
(#src("whitepaper/Fragment/PropWhen.lean", 176, 194)[fragment],
#src("ConLeche/Kernel/PropWhen.lean", 413, 415)[real checker], with its
#src("ConLeche/Kernel/PropWhen.lean", 694, 700)[readout].)

The datum is _canonical_: the parameter set is stored as a strictly
ascending list, and every operation that produces a datum normalises.
The payoff is that two data are equal — plain equality, `=`, the thing
a checker can compare in constant time — exactly when they hold at the
same valuations
(#src("whitepaper/Fragment/PropWhen.lean", 232, 235)[fragment],
#src("ConLeche/Kernel/PropWhen.lean", 833, 834)[real checker]).
So wherever a rule below compares two annotations with `=`, the
comparison is semantic, and no separate notion of "equivalent
annotations" exists.

*Where it comes from.*  The datum is determined by type checking,
so inference could output the annotated term.  As said in §1, the
paper and the checker take the annotations as given from the start
and only check them: the inference rules for $forall$ and $lambda$
(@sec:rules) compute the body's sort and compare it with the stored
datum, so a wrong annotation makes the term rejected, never accepted
wrongly.  The real checker writes the annotation into the binder's
metadata; the fragment makes it a field of the binder.

*What it is for.*  The interpretation (@sec:interp) assigns a set to
every term by a plain recursion over the term, and at a binder it
must choose: for a $forall$, a dependent function space or a truth
value; for a $lambda$, a function or the one canonical proof.  It may
never _infer a type_ to find out — running the checker inside the
semantics is exactly what this design avoids — so it reads the
coloured datum, and that is the only use the semantics makes of the
annotation.

*Substitution and instantiation.*  $B[x := a]$ replaces $x$ by $a$ and
leaves every annotation as it is, since a datum mentions level
parameters only
(#src("whitepaper/Fragment/Syntax.lean", 62, 71)[fragment],
#src("ConLeche/Kernel/ExprOps.lean", 33, 45)[real checker]).
_Level instantiation_ $e[arrow(p) := arrow(ell)]$, used when a constant
declared with level parameters $arrow(p)$ is taken at the levels
$arrow(ell)$, replaces the parameters in sorts, in the level lists of
constants, and in the annotations.  There "all of $q_1, ..., q_k$ zero"
becomes "each of the substitutes of $q_1, ..., q_k$ is zero", computed
with the $zn$ function of the next subsection and the intersection of
data
(#src("whitepaper/Fragment/Syntax.lean", 104, 112)[fragment],
#src("whitepaper/Fragment/PropWhen.lean", 322, 329)[its datum part];
#src("ConLeche/Kernel/Level.lean", 234, 245)[real checker],
#src("ConLeche/Kernel/Level.lean", 205, 207)[datum part]).

== Levels <sec:levels>

Universe levels are Lean's, without metavariables:

$
  u colon.double.eq 0 | u + 1 | max(u, v) | imax(u, v) | p
$

with $p$ a level parameter of the enclosing declaration
(#src("whitepaper/Fragment/Level.lean", 32, 46)[fragment],
#src("ConLeche/Kernel/Expr.lean", 41, 46)[real checker]).  A level
means a natural number once a valuation $phi$ fixes the parameters:
$0$, successor, maximum, and $imax(u, v)$ is $0$ when $v$ is $0$ and
$max(u, v)$ otherwise
(#src("whitepaper/Fragment/Level.lean", 53, 59)[fragment],
#src("ConLeche/Verify/Level.lean", 26, 31)[real proof]).
The impredicative maximum is what makes $forall x : A. thin B$ a
proposition whenever $B$ is one, whatever the level of $A$: its sort
is $Sort (imax(u, v))$ (rule $forall$ in @sec:rules).

*The level oracle.*  The checker decides $u <= v$ and $u = v$ between
levels with an algorithm.  This paper does not present that algorithm
and does not verify it.  It _assumes_ two Boolean functions with a
specification: $u <= v$ is answered yes exactly when the value of $u$
is at most the value of $v$ at every valuation, and $u = v$ exactly
when the values agree at every valuation — correct and complete, in
both directions.  In the Lean fragment this is literal: the oracle is
a class with the two functions and the two equivalences, a parameter
of the whole development, and every theorem is proved against it
(#src("whitepaper/Fragment/Level.lean", 117, 130)[fragment]).  The
real checker implements the two
(#src("ConLeche/Kernel/Level.lean", 138, 140)[$<=$],
#src("ConLeche/Kernel/Level.lean", 158, 161)[$=$]) and proves them
sound
(#src("ConLeche/Verify/Level.lean", 173, 174)[$<=$],
#src("ConLeche/Verify/Level.lean", 339, 341)[$=$]).  We write
$u eq.dot v$ for "the oracle says $u = v$"; the environment-free part
of the proof uses only that half.

*Zero-ness.*  One function on levels _is_ defined, because the
annotation design needs it and it is small: $zn$ turns a level into
the datum that says when the level is zero.

$
  zn(0) & = whenZero \{\} & quad zn(u + 1) & = never \
  zn(p) & = whenZero \{p\} & quad zn(max(u, v)) & = zn(u) inter zn(v) \
  zn(imax(u, v)) & = zn(v)
$

Here $inter$ is the intersection of two data: it holds where both hold,
so $never inter PW = never$ and $whenZero S inter whenZero T =
whenZero (S union T)$
(#src("whitepaper/Fragment/PropWhen.lean", 208, 212)[fragment],
#src("ConLeche/Kernel/PropWhen.lean", 866)[real checker]).
The function is exact:

#lemma(name: "exactness")[
  For every level $u$ and valuation $phi$, the datum $zn(u)$ holds at
  $phi$ if and only if $u$ evaluates to $0$ at $phi$.
  (#src("whitepaper/Fragment/PropWhen.lean", 279, 302)[fragment],
  #src("ConLeche/Kernel/Level.lean", 190, 195)[real checker] and its
  #src("ConLeche/Verify/PropWhen.lean", 52, 53)[proof].)
] <lem:zeroness>

Why can a datum of two shapes be exact for every level?  Because the
set of valuations at which a level is zero is always one of three
things: empty (a successor is never zero), everything (the level $0$),
or "these parameters are all zero".  $max$ is zero when both sides
are, which intersects two such sets and gives another; and $imax$ is
zero exactly when its second argument is, so it stays in the family
where a plain maximum would have introduced a union.

== The three relations <sec:rules>

The checker is described by three relations over terms, defined
together by inference rules: _reduction_ $Gamma tack e red e'$,
_definitional equality_ $Gamma tack a equiv b$, and _inference_
$Gamma tack e => T$.  The environment is a fixed parameter of all
three; a context $Gamma$ lists the variables in scope with their
types.  The whole set of rules is at
#src("whitepaper/Fragment/Rules.lean", 46, 278)[fragment] and
#src("ConLeche/Rules/Rel.lean", 92, 96)[real checker]; the rules that
unfold definitions and fire recursors ($delta$ and $iota$) are left
out here, because the environment enters in §3 and §4.

*How to read them.*  The three relations describe _what the checker
does_, not what is true.  $Gamma tack a equiv b$ means: on the terms
$a$ and $b$, the checker's equality test answers yes.  $Gamma tack e
=> T$ means: asked for the type of $e$, the checker returns $T$ —
we write $=>$ rather than the customary colon so that it is not read
as a typing judgement, which this paper does not have.  Every relation
is stated in the accepting direction only; nothing says what the
checker rejects.  A rule's premises are exactly what the checker did at that
site: the recursive calls it made, and the tests whose outcome fixes
the shape of the conclusion.  We call these the checker's
_certificates_.  What is _not_ a premise anywhere is
well-formedness of the terms — that the terms make sense together.
The checker never establishes that; it is a semantic fact, the
semantic invariant of @sec:inv, and it enters only the
soundness theorems, which assume it of the conclusion's terms and
conclude it of every term a rule produces.

A convention: a chain
such as $Gamma tack a => T red e$ abbreviates consecutive premises in
the same context, one per arrow, the right end of each arrow being the
subject of the next — here $Gamma tack a => T$ and $Gamma tack T red
e$.  Chains of any length are read the same way.

=== Reduction

Reduction chains the head steps the checker makes when it normalises
a term.  It is reflexive and transitive, and it reaches inside the
head of an application
(#src("whitepaper/Fragment/Rules.lean", 48, 59)[fragment],
#src("ConLeche/Rules/Rel.lean", 96, 112)[real checker]).

#rules(
  rule(name: "refl", $Gamma tack e red e$),
  rule(name: "trans", $Gamma tack e_1 red e_2$, $Gamma tack e_2 red e_3$,
    $Gamma tack e_1 red e_3$),
  rule(name: "head", $Gamma tack f red f'$, $Gamma tack f thick a red f' thick a$),
)

There are two $beta$ rules.  The first fires only at a binder whose
annotation is $ann(never)$ and needs nothing else — the annotation
acts as a _gate_ that opens plain $beta$, hence the rule's name; the
second fires at
any binder, but only after the argument's type has been inferred and
found equal to the domain
(#src("whitepaper/Fragment/Rules.lean", 60, 76)[fragment],
#src("ConLeche/Rules/Rel.lean", 121, 128)[real checker]).

#rules(
  rule(name: "β-gate",
    $Gamma tack (lambda x : A thin ann(never). thin b) thick a red b[x := a]$),
  rule(name: "β-cert",
    $ann(Gamma tack a => T)$, $ann(Gamma tack T equiv A)$,
    $Gamma tack (lambda x : A thin ann(PW). thin b) thick a red b[x := a]$),
)

*Why two $beta$s.*  A textbook kernel reduces every $beta$-redex it
meets.  This checker may do so only where the body is certainly not a
proposition; elsewhere it first runs a certificate — an inference and
an equality test — which a textbook kernel would not.  The reason is
in the model (@sec:inv gives it in full).  The soundness of a $beta$
step needs the argument to lie in the domain of the $lambda$.  Where
the $lambda$ denotes a genuine function — a set of pairs — that fact
is recoverable, because a function determines its domain.  Where the
body is a proposition, the $lambda$ denotes a single point, the same
point for every domain, and the domain cannot be read off it.  A
syntactic proof would take the fact from subject reduction; this
proof has no typing judgement and takes it from the certificate.
Reduction never rejects: where the certificate fails the term is
simply not reduced, and an unreduced term can only make the checker
reject more, never accept more.

=== Definitional equality

The checker's equality test is reflexive and symmetric (the checker never
takes a symmetry step; the rule is there so that each one-sided rule
below — red-l, $eta$ — need be written once and its mirror image
follows), and it interleaves with
reduction in one way: reduce the left side, then continue.  Sorts and
constants are compared through the level oracle
(#src("whitepaper/Fragment/Rules.lean", 176, 195)[fragment],
#src("ConLeche/Rules/Rel.lean", 334, 362)[real checker]).

#rules(
  rule(name: "refl", $Gamma tack a equiv a$),
  rule(name: "sym", $Gamma tack a equiv b$, $Gamma tack b equiv a$),
  rule(name: "red-l", $Gamma tack a red a'$, $Gamma tack a' equiv b$,
    $Gamma tack a equiv b$),
  rule(name: "sort", $u eq.dot v$, $Gamma tack Sort u equiv Sort v$),
  rule(name: "const", $arrow(ell) eq.dot arrow(ell)'$,
    $Gamma tack c.\{arrow(ell)\} equiv c.\{arrow(ell)'\}$),
)

The congruences descend into the two binders and into applications.
Domains are compared first, then the bodies, under the right-hand
domain; the two annotations must be the same datum
(#src("whitepaper/Fragment/Rules.lean", 196, 209)[fragment],
#src("ConLeche/Rules/Rel.lean", 373, 392)[real checker]).

#rules(
  rule(name: "∀",
    $Gamma tack A_1 equiv A_2$, $Gamma\, x : A_2 tack B_1 equiv B_2$,
    $Gamma tack forall x : A_1 thin ann(PW). thin B_1 equiv forall x : A_2 thin ann(PW). thin B_2$),
  rule(name: "λ",
    $Gamma tack A_1 equiv A_2$, $Gamma\, x : A_2 tack b_1 equiv b_2$,
    $Gamma tack lambda x : A_1 thin ann(PW). thin b_1 equiv lambda x : A_2 thin ann(PW). thin b_2$),
  rule(name: "app",
    $Gamma tack f_1 equiv f_2$, $Gamma tack a_1 equiv a_2$,
    $Gamma tack f_1 thick a_1 equiv f_2 thick a_2$),
)

A $lambda$ against a term $b$ that is not one is tried by $eta$: the
type of $b$ is inferred and reduced to a $forall$, its domain is
compared with the $lambda$'s, and the body is compared with $b$
applied to the bound variable.  Two terms are equal by proof
irrelevance when both are proofs: each one's type has type
$Sort u$ with $u$ oracle-equal to $0$
(#src("whitepaper/Fragment/Rules.lean", 210, 230)[fragment],
#src("ConLeche/Rules/Rel.lean", 400, 422)[real checker]).

#rules(
  rule(name: "η",
    $Gamma tack b => T red forall x : A_2 thin ann(PW). thin B$,
    $Gamma tack A_2 equiv A_1$,
    $Gamma\, x : A_1 tack b_1 equiv b thick x$,
    $Gamma tack lambda x : A_1 thin ann(PW). thin b_1 equiv b$),
)
#rules(
  rule(name: "proof-irrel",
    $Gamma tack a => T_a => S_a red Sort u$, $u eq.dot 0$,
    $Gamma tack b => T_b => S_b red Sort v$, $v eq.dot 0$,
    $Gamma tack a equiv b$),
)

*No transitivity.*  The list has no rule "$a equiv b$ and $b equiv c$
give $a equiv c$", and none can be added
(#src("whitepaper/Fragment/Rules.lean", 158, 175)[fragment],
#src("ConLeche/Rules/Rel.lean", 310, 333)[real checker]).  Look at the shape of the
rules above: the two terms of every equality premise are each either a
subterm of the conclusion (the congruences, the $eta$ body) or a
term that another premise _produced_ — a reduct (red-l) or an
inferred type ($eta$, $beta$-cert).  The soundness proof lives on
that discipline, and a transitivity rule is the one rule whose middle
term comes from nowhere; @sec:claims says why, once the proof is on
the table.  In the fragment, adding the rule would leave the
soundness theorem without a proof — not because the rule is false
there, but because the induction cannot reach its middle term.  In
the real checker it would make the theorem
false.  The relation there has two further rules, one that compares
free variables by index alone and one that reads a variable's
annotation to decide "this is a proof", and each is sound on its own
only because, when the terms are well-formed, a variable's annotation
agrees with the type the context gives it.  A transitivity rule lets
the two meet on a middle term that is not well-formed — a variable
wearing a wrong annotation — and derives $x equiv y$ for any two
variables, which no model satisfies.  The fragment, having no free
variables, has no such counterexample, but the discipline is the
same.  What the checker does instead of
chaining equalities is chain reductions: reduce, then continue, which
is red-l.

*Proof irrelevance.*  The rule compares the two _sorts_ of the two
types and never the two types.  Lean's own kernel demands more: it
also compares $T_a$ with $T_b$, so that $a$ and $b$ are proofs of the
same proposition.  This checker never compares them, and so accepts
strictly more than Lean at this one site — the one place where a
reader who ignores the colour does not see Lean as it is.  The model
licenses it: every proof denotes the one canonical point, so two
proofs of two propositions denote the same set outright.

*$eta$.*  The annotation of the $forall$ that $b$'s type reduces to
must be the $lambda$'s own.  The rule is sound because in the model a
member of a function space is the abstraction of its applications;
and where the datum says "proposition", both sides are the one point.

=== Inference

A variable's type is read off the context; a sort has the next sort; a
constant has its declared type at the levels it is used at
(#src("whitepaper/Fragment/Rules.lean", 233, 246)[fragment],
#src("ConLeche/Rules/Rel.lean", 486, 502)[real checker]).

#rules(
  rule(name: "var", $(x : A) in Gamma$, $Gamma tack x => A$),
  rule(name: "sort", $Gamma tack Sort u => Sort (u + 1)$),
  rule(name: "const",
    $c "declared with parameters" arrow(p) "and type" T$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} => T[arrow(p) := arrow(ell)]$),
)

The two binder rules are where the annotation is checked.  For a
$forall$, the domain's type must reduce to a sort $Sort u$ and the
body's type, under the domain, to a sort $Sort v$; the result is
$Sort (imax(u, v))$, and the stored datum must be the zero-ness of
$v$.  For a $lambda$, the body's type $B$ is inferred; then the type
of $B$ is inferred and reduced to a sort $Sort v$, and the stored
datum must be the zero-ness of $v$
(#src("whitepaper/Fragment/Rules.lean", 247, 266)[fragment],
#src("ConLeche/Rules/Rel.lean", 515, 539)[real checker]).

#rules(
  rule(name: "∀",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack B => T red Sort v$,
    $ann(zn(v) = PW)$,
    $Gamma tack forall x : A thin ann(PW). thin B => Sort (imax(u, v))$),
)
#rules(
  rule(name: "λ",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack b => B ann(=> T red Sort v)$,
    $ann(zn(v) = PW)$,
    $Gamma tack lambda x : A thin ann(PW). thin b => forall x : A thin ann(PW). thin B$),
)

The coloured premises are the price of the annotation.  A kernel with
a typing judgement infers a $lambda$'s type without ever computing the
sort of its body's type; this one does, in order to check the datum.
By the exactness lemma (@lem:zeroness) the check $ann(zn(v) = PW)$ is
a semantic statement: the datum holds at a valuation exactly when $v$
is $0$ there, which is exactly when the body is a proposition.  The
real checker validates the datum once per chain of $lambda$s; the
fragment does it at every $lambda$.

An application infers the head's type, reduces it to a $forall$,
infers the argument's type and compares it with the domain
(#src("whitepaper/Fragment/Rules.lean", 267, 276)[fragment],
#src("ConLeche/Rules/Rel.lean", 544, 547)[real checker]).

#rules(
  rule(name: "app",
    $Gamma tack f => T red forall x : A thin ann(PW). thin B$,
    $Gamma tack a => T_a$, $Gamma tack T_a equiv A$,
    $Gamma tack f thick a => B[x := a]$),
)

*Reducing to a $forall$.*  Note what the rule does not do.  It does not
know a type of $f$ that is a $forall$ "up to definitional equality"
and then argue that its domain is the right one; it reduces the
inferred type until a $forall$ is syntactically there.  This is the
site where a syntactic soundness proof needs injectivity of $forall$
— that $forall x : A. B equiv forall x : A'. B'$ forces $A equiv A'$
— a property this proof never needs, and one that the
model does not even validate: $forall x : A. thin sans("True")$ and
$forall x : A'. thin sans("True")$ denote the same truth value whatever
$A$ and $A'$ are.  The semantic proof never needs it.  The $forall$ the head's type reduces to denotes a
function space; the head denotes a member of it, because reduction
preserves denotations; the argument denotes a member of the domain,
by the certificate; and applying a member of a function space to a
member of its domain lands in the codomain.  The second half of this
section carries this out.
