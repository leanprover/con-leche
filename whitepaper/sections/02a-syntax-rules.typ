#import "../lib.typ": *

// Notation local to this file.  Everything a rule mentions is spelled
// here once, so the rules below read the same in the PDF and the HTML.
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let red = sym.arrow.r.squiggly
#let elet = $sans("let")$
#let eqlam = $scripts(equiv)_lambda$

== Terms <sec:terms>

The terms of the fragment are the official kernel's terms, minus what @sec:left-out
leaves out:

$
  e & colon.double.eq x | Sort u | e thick e
      | lambda x : A. thin e | forall x : A. thin e
      | elet x : T := v; thin e
$

A #src("whitepaper/Fragment/Syntax.lean", 29, 48)[term] is a variable $x$; a sort $Sort u$ at a universe level $u$
(@sec:levels), with $sans("Prop") = Sort 0$; an application
$f thick a$; a function
$lambda x : A. thin b$; a dependent function type, or Π-type,
$forall x : A. thin B$, written $A -> B$ when $x$ does not
occur in $B$; or a let-expression $elet x : T := v; thin b$.
Types are terms; there is no separate class. A sequence of binders,
such as the lambdas of $lambda x : A. thin lambda y : B. thin e$,
is a _telescope_.

The paper writes named variables, with the usual conventions: terms
are taken up to renaming of bound variables, and $B[x := a]$ is the
capture-avoiding #src("whitepaper/Fragment/Syntax.lean", 65, 75)[substitution] of $a$ for $x$.  The Lean fragment uses
de Bruijn indices instead (a variable is the number of binders
between its occurrence and its own), and a rule that mentions the types of the
variables in scope carries a _context_ $Gamma$, a list of those types.
No rule in this paper needs index arithmetic in its named form.

#real[
  The checker uses neither device. It opens a binder with a fresh
  free variable that carries its own type, so it keeps no context at
  all. This is a performance device and changes nothing below.
]

== Levels <sec:levels>

#src("whitepaper/Fragment/Level.lean", 29, 43)[Universe levels] are Lean's,
#src("ConLeche/Kernel/Expr.lean", 39, 44)[without metavariables]:

$
  u colon.double.eq 0 | u + 1 | max(u, v) | imax(u, v) | p
$

with $p$ a level parameter of the enclosing declaration.  A level
#src("whitepaper/Fragment/Level.lean", 50, 56)[means a natural number] once a _valuation_ $phi$ fixes the parameters:
$0$, successor, maximum, and $imax(u, v)$ is $0$ when $v$ is $0$ and
$max(u, v)$ otherwise
(#src("ConLeche/Verify/Level.lean", 26, 31)[as in con-leche]).
The impredicative maximum is what makes $forall x : A. thin B$ a
proposition whenever $B$ is one, whatever the level of $A$: its sort
is $Sort (imax(u, v))$ (rule pi in @sec:rules).

*The level oracle.*  The checker decides $u <= v$ and $u = v$ between
levels with an algorithm.  This paper does not present that algorithm
and does not verify it.  It #src("whitepaper/Fragment/Level.lean", 130, 145)[_assumes_ two Boolean functions] with a
specification: $u <= v$ is answered yes exactly when the value of $u$
is at most the value of $v$ at every valuation, and $u = v$ exactly
when the values agree at every valuation
(#src("ConLeche/Kernel/Level.lean", 144, 146)[the real $<=$],
#src("ConLeche/Kernel/Level.lean", 164, 167)[the real $=$] and their
#src("ConLeche/Verify/Level.lean", 173, 174)[soundness]
#src("ConLeche/Verify/Level.lean", 201, 202)[proofs]).  We write
$u eq.dot v$ for "the oracle says $u = v$".

== The three relations <sec:rules>

The checker is described by three relations over terms, defined
together by inference rules: _reduction_ $Gamma tack e red e'$,
_definitional equality_ $Gamma tack a equiv b$, and _inference_
$Gamma tack e => T$.  A context $Gamma$ lists the variables in scope
with their types.  The complete rule sets are
#src("whitepaper/Fragment/Rules.lean", 56, 798)[one mutual inductive definition],
#src("ConLeche/Rules/Rel.lean", 97, 101)[as in con-leche].

*How to read them.*  The three relations describe what the checker
does. $Gamma tack a equiv b$ means that on the terms $a$ and $b$ the
checker's equality test answers yes. $Gamma tack e => T$ means that,
asked for the type of $e$, the checker returns $T$. We write $=>$
rather than the customary colon so that it is not read as a typing
judgement, which this paper does not have. Every relation is stated
in the accepting direction only; nothing says what the checker
rejects. A rule's premises are exactly what the checker did at that
site: the recursive calls it made, and the tests whose outcome fixes
the shape of the conclusion.

A convention: a chain
such as $Gamma tack a => T red e$ abbreviates consecutive premises in
the same context, one per arrow, the right end of each arrow being the
subject of the next; here $Gamma tack a => T$ and $Gamma tack T red
e$.  Chains of any length are read the same way.

=== Reduction <sec:red>

Reduction chains the head steps the checker makes when it normalises
a term.  It is #src("whitepaper/Fragment/Rules.lean", 58, 69)[reflexive and transitive], and it
#src("ConLeche/Rules/Rel.lean", 101, 117)[reaches inside the head] of an application.

#rules(
  rule(name: "refl", $Gamma tack e red e$),
  rule(name: "trans", $Gamma tack e_1 red e_2$, $Gamma tack e_2 red e_3$,
    $Gamma tack e_1 red e_3$),
  rule(name: "head", $Gamma tack f red f'$, $Gamma tack f thick a red f' thick a$),
)

#src("whitepaper/Fragment/Rules.lean", 70, 80)[$beta$] fires at every redex, and
#src("whitepaper/Fragment/Rules.lean", 81, 87)[$zeta$] substitutes a
let-binding's value into its body; neither has a premise.

#rules(
  rule(name: "beta",
    $Gamma tack (lambda x : A. thin b) thick a red b[x := a]$),
  rule(name: "zeta",
    $Gamma tack (elet x : T := v; thin b) red b[x := v]$),
)

As in the official kernel, $beta$ has no premise, although its
soundness needs the argument to lie in the domain of the lambda;
@sec:inv shows where that comes from. $zeta$ is simpler: a
let-expression always denotes what its body with the value
substituted denotes.

=== Definitional equality

The checker's #src("whitepaper/Fragment/Rules.lean", 547, 566)[equality test] is reflexive and symmetric. The checker
never takes a symmetry step; the rule is there so that each one-sided
rule below (red-l, $eta$) need be written once, and its mirror image
follows. The test interleaves with reduction in one way: reduce the
left side, then continue.  Sorts
are #src("ConLeche/Rules/Rel.lean", 392, 394)[compared through the level oracle].

#rules(
  rule(name: "refl", $Gamma tack a equiv a$),
  rule(name: "sym", $Gamma tack a equiv b$, $Gamma tack b equiv a$),
  rule(name: "red-l", $Gamma tack a red a'$, $Gamma tack a' equiv b$,
    $Gamma tack a equiv b$),
  rule(name: "sort", $u eq.dot v$, $Gamma tack Sort u equiv Sort v$),
)

The congruences descend into the two binders and into applications.
Domains are compared first, then the bodies, under the right-hand
domain.  #src("whitepaper/Fragment/Rules.lean", 567, 575)[For $forall$] that is all.

#rules(
  rule(name: "pi",
    $Gamma tack A_1 equiv A_2$, $Gamma\, x : A_2 tack B_1 equiv B_2$,
    $Gamma tack forall x : A_1. thin B_1 equiv forall x : A_2. thin B_2$),
  rule(name: "app",
    $Gamma tack f_1 equiv f_2$, $Gamma tack a_1 equiv a_2$,
    $Gamma tack f_1 thick a_1 equiv f_2 thick a_2$),
)

Two lambdas are compared as two lambda telescopes, by an auxiliary
relation $Gamma tack a eqlam b$. The checker
#src("whitepaper/Fragment/Rules.lean", 701, 714)[descends level by level]
while both bodies are lambdas, comparing the domains at each level
(lam-outer). At the innermost level, where the descent stops,
#src("whitepaper/Fragment/Rules.lean", 704, 709)[it also infers the types of the two bodies]
under the binder and compares them (lam). That comparison is a check
the official kernel does not make. Such checks are typeset in one
colour, #tax[like this], throughout the paper; a reader who ignores
the coloured premises sees the official kernel's rule. @sec:tax
explains why they are there, and why the outer levels need none.

#rules(
  rule(name: "lam",
    $Gamma tack A_1 equiv A_2 \ Gamma\, x : A_2 tack b_1 equiv b_2$,
    tax($Gamma\, x : A_2 tack b_1 => t_1 quad Gamma\, x : A_2 tack b_2 => t_2 \ Gamma\, x : A_2 tack t_1 equiv t_2$),
    $Gamma tack lambda x : A_1. thin b_1 eqlam lambda x : A_2. thin b_2$),
)
#rules(
  rule(name: "lam-outer",
    $Gamma tack A_1 equiv A_2$, $Gamma\, x : A_2 tack b_1 eqlam b_2$,
    $Gamma tack lambda x : A_1. thin b_1 eqlam lambda x : A_2. thin b_2$),
  rule(name: "lams", $Gamma tack a eqlam b$, $Gamma tack a equiv b$),
)

(Two syntactically equal terms are also related by $eqlam$.)
A lambda against a term $b$ that is not a lambda is #src("whitepaper/Fragment/Rules.lean", 640, 653)[tried by $eta$]. The
type of $b$ is inferred and reduced to a $forall$, its domain is
compared with the lambda's, and the body is compared with $b$
applied to the bound variable. As at the innermost level of
lambda congruence, the type of the lambda's body is inferred and compared
with the $forall$'s body.  Two terms are
#src("whitepaper/Fragment/Rules.lean", 654, 663)[equal by proof irrelevance] when both are proofs: each one's type has type
$Sort u$ with $u$ oracle-equal to $0$.

#rules(
  rule(name: "fun-eta",
    $Gamma tack b => T red forall x : A_2. thin B \ Gamma tack A_2 equiv A_1$,
    $Gamma\, x : A_1 tack b_1 equiv b thick x$,
    tax($Gamma\, x : A_1 tack b_1 => t_1 \ Gamma\, x : A_1 tack t_1 equiv B$),
    $Gamma tack lambda x : A_1. thin b_1 equiv b$),
)
#rules(
  rule(name: "proof-irrel",
    $Gamma tack a => T_a => S_a red Sort u$, $u eq.dot 0$,
    $Gamma tack b => T_b => S_b red Sort v$, $v eq.dot 0$,
    $Gamma tack a equiv b$),
)

*Proof irrelevance.*  The rule compares the sorts of the two types,
and never the two types. The official kernel also compares $T_a$ with
$T_b$, so that $a$ and $b$ are proofs of the same proposition. This
checker does not, and so accepts strictly more than Lean at this one
site. The model justifies it: every proof denotes the point, so two
proofs of two propositions denote the same set.

The list has #src("whitepaper/Fragment/Rules.lean", 529, 546)[no transitivity rule], and
#src("ConLeche/Rules/Rel.lean", 354, 377)[none can be added]\; @sec:claims
explains why. Instead of chaining equalities, the checker chains
reductions: it reduces a side, then continues (red-l).

#real[
  In con-leche a transitivity rule would also combine two rules that
  are each sound alone into an unsound one. Free variables are
  #src("ConLeche/Rules/Rel.lean", 395, 401)[compared by index], not by
  the types they carry, and a
  #src("ConLeche/Rules/Rel.lean", 459, 465)[fast path] equates two
  terms whose heads' declared types say they are proofs. Chained, the
  two would equate any two variables: give each the type of a
  proposition, then compare the two proofs.
]

=== Inference <sec:infer>

A variable's type is #src("whitepaper/Fragment/Rules.lean", 740, 748)[read off the context], and a sort
#src("ConLeche/Rules/Rel.lean", 570, 586)[has the next sort]. The rules
of this subsection are the checker's _full inference_. The checker
also has a cheaper mode, `infer_only`, which skips some of their
checks; @sec:io presents it.

#rules(
  rule(name: "var", $(x : A) in Gamma$, $Gamma tack x => A$),
  rule(name: "sort", $Gamma tack Sort u => Sort (u + 1)$),
)

The two #src("whitepaper/Fragment/Rules.lean", 754, 771)[binder rules] are Lean's own.  For a
$forall$, the domain's type must reduce to a sort $Sort u$ and the
body's type, under the domain, to a sort $Sort v$; the result is
$Sort (imax(u, v))$.  For a lambda, the domain's type must reduce to
a sort, and the result is the $forall$ of the body's inferred type;
the sort of that type is not computed.

#rules(
  rule(name: "pi",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack B => T red Sort v$,
    $Gamma tack forall x : A. thin B => Sort (imax(u, v))$),
  rule(name: "lam",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack b => B$,
    $Gamma tack lambda x : A. thin b => forall x : A. thin B$),
)

An #src("whitepaper/Fragment/Rules.lean", 772, 781)[application infers the head's type], reduces it to a $forall$,
infers the argument's type and #src("ConLeche/Rules/Rel.lean", 638, 642)[compares it with the domain].
A #src("whitepaper/Fragment/Rules.lean", 782, 796)[let-expression] checks that its type has a
sort and that its value's type agrees with it, as Lean does, and then
infers the type of the body with the value substituted.

#rules(
  rule(name: "app",
    $Gamma tack f => T red forall x : A. thin B$,
    $Gamma tack a => T_a$, $Gamma tack T_a equiv A$,
    $Gamma tack f thick a => B[x := a]$),
)
#rules(
  rule(name: "let",
    $Gamma tack T => S red Sort u$,
    $Gamma tack v => T_v$, $Gamma tack T_v equiv T$,
    $Gamma tack b[x := v] => B$,
    $Gamma tack (elet x : T := v; thin b) => B$),
)

*Reducing to a $forall$.*  The application rule reduces the inferred
type of $f$ until a $forall$ is syntactically there. It does not take
a type of $f$ that is a $forall$ up to definitional equality and argue
that its domain is the right one. That argument is where a syntactic
soundness proof needs injectivity of $forall$, the property that
$forall x : A. thin B equiv forall x : A'. thin B'$ forces
$A equiv A'$. Our proof never needs it, and the model does not
validate it: $forall x : A. thin sans("True")$ and
$forall x : A'. thin sans("True")$ denote the same truth value whatever
$A$ and $A'$ are. Our proof argues instead that the head denotes a
member of what the $forall$ denotes, because reduction preserves
denotations; that the argument denotes a member of the domain, by the
comparison premise; and that applying a member of a function space to
a member of its domain lands in the fibre. The second half of this
section carries this out.

*The let-expression.*  The two checks on the value are what Lean
runs, and they decide verdicts: they reject a let-expression whose
value does not have the stated type even where the body ignores it.
The soundness proof does not use them (@sec:claims): the
interpretation reads no type, and the body is inferred with the value
itself in place of the variable.

#real[
  The checker substitutes the value in the same way, both when it
  #src("ConLeche/Kernel/Core.lean", 979, 981)[reduces] and when it
  #src("ConLeche/Kernel/Core.lean", 1179, 1184)[infers]\; it keeps no
  variables bound to values.
  The official kernel opens the body at such a variable instead, which
  avoids copying the value when the body uses it many times; for
  con-leche that case is a known performance gap, not a soundness
  question.
]
