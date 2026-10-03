#import "../lib.typ": *

= Related work <sec:related>

This section compares our proof with a small selection of the most
closely related work. It is not a survey and makes no claim to be
comprehensive.

*Lean's type theory.* Carneiro's thesis @carneiro2019 presents Lean's
type theory by a typing judgement and builds a set-theoretic model of
it, from which Lean's consistency follows relative to ZFC together
with, for each $n$, the axiom that there are $n$ inaccessible
cardinals. A Lean development of that model, lean4lean-model
@lean4lean-model, assumes $omega$ inaccessible cardinals, and the set
theory con-leche assumes
#src("bridge/lean4lean-model/ConLecheBridge/Carneiro.lean", 200, 202)[follows from that hypothesis].
Lean4Lean @carneiro2025lean4lean is a checker for Lean 4 written in
Lean, parts of which are verified against a typing judgement that
formalises the thesis's presentation. All three reason about a typing
judgement; our proof has none, and connects what the checker accepts
to the model directly.

*Set-theoretic models with an impredicative `Prop`.* Werner
@werner1997 interprets the Calculus of Inductive Constructions in set
theory with inaccessible cardinals, interpreting propositions proof
irrelevantly; Barras @barras2010 states ZF, possibly with inaccessible
cardinals, as axioms inside Coq and proves set-theoretic models of the
Calculus of Constructions and of some of its extensions sound. The
interpretation of @sec:interp is of this kind, and the set theory of
@sec:lib is likewise given by axioms. The difference is what is shown
true in the model: there, the derivable judgements of a calculus given
by typing rules; here, the verdicts of the checker on annotated terms.

*Inductive types.* Dybjer @dybjer1994 gives a general scheme for
inductive families with strictly positive constructors, in which the
elimination and equality rules are derived from the formation and
introduction rules, as the checker (like the official kernel)
generates the recursor from the constructors (@sec:ind). Aczel
@aczel1977 calls a monotone operator $kappa$-based when every element
it produces from a set $X$ it already produces from a subset of $X$ of
cardinality less than $kappa$, and shows that for regular $kappa$ such
an operator's iteration closes by stage $kappa$. Accessibility
(@sec:ind-model) is a variant of that condition in which the support
is indexed by a subset of one set $A$ instead of being bounded by a
cardinal, and @thm:closed-of-acc indexes its stages by well-founded
trees instead of ordinals. Abbott, Altenkirch and Ghani @abbott2005
represent strictly positive types, nested ones included, as
containers — a set of shapes and, for each shape, a set of positions
holding data — and construct them from W-types. In these terms an
element's support is a set of positions with the occurrences that fill
them, and the bound $A$ is one set that holds every shape's positions;
here the fixed point exists by accessibility instead.
