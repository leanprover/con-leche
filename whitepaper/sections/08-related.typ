#import "../lib.typ": *

#let pt = $sans("pt")$

= Related work <sec:related>

This section compares our proof with a small selection of the most
closely related work. It is not a survey and makes no claim to be
comprehensive.

*Carneiro, "The Type Theory of Lean".* The thesis @carneiro2019
presents Lean's type theory in full by a typing judgement, studies its
metatheory, and builds a set-theoretic model, from which Lean's
consistency follows relative to ZFC together with, for each $n$, the
existence of $n$ inaccessible cardinals. It is the starting point of
our model, whose interpretation follows the thesis's: a proof is one
point, a proposition $forall x : alpha. thin
beta$ is the intersection of its fibres with the singleton of that
point — our propositional product $Pi_0$ (@sec:interp) — and a $forall$
into a higher universe is the full dependent function space. To decide
which reading applies, the thesis first translates every well-typed
term into a language in which the propositional and the
non-propositional $forall$ and $lambda$ are separate constructs, using
the sort of each body, which is well defined given the thesis's
unique typing theorem. Our proof records that sort in the annotation and the
checker's inference rules check it (@sec:annotation), so the
interpretation consults no typing information and our proof does not
need unique typing. The thesis models a fixed basis of eight inductive
types, the W-type among them, to which it reduces the others (parts of
the reduction left as future work); here every
inductive block the checker accepts is interpreted by its own least
fixed point (@sec:ind-model). And the statements differ in form: there,
each derivation of a formal typing judgement is sound in the model
once a number of inaccessible cardinals depending on the derivation is
assumed; here the theorem is about the verdicts of the checker's own
rules, and assumes the whole
chain of universes $cal(U)_0, cal(U)_1, dots$ at once (@sec:lib).

*Lean4Lean.* Lean4Lean @carneiro2025lean4lean is a checker for Lean 4
written in Lean, closely following the official kernel and able to
check all of Mathlib. The paper also formalises a typing judgement, a
slight variation of the thesis's, and proves the main body of the
checker correct against it: an equality test that answers yes yields a
definitional equality of the judgement, an inferred type a typing;
inductive types and additions to the environment are listed as
unfinished. The paper notes that this correctness proof needs, in some
form, unique typing and the inversion of definitional equality on
sorts and $forall$-types for its judgement. Our proof relates the
checker's verdicts to the model directly, with no typing judgement in
between, and uses no such property (@sec:claims). The Lean development
lean4lean-model @lean4lean-model, built on Lean4Lean's judgement,
states as its target theorem the consistency of that judgement
assuming $omega$ inaccessible cardinals, a proof still to be supplied
at the time of writing; the set theory con-leche assumes
#src("bridge/lean4lean-model/ConLecheBridge/Carneiro.lean", 200, 202)[follows from that hypothesis].

*Werner, "Sets in types, types in sets".* Werner @werner1997
interprets the Calculus of Inductive Constructions in ZFC with an
increasing sequence of inaccessible cardinals, one for each universe,
and conversely encodes ZFC in the type theory, so that the two
hierarchies interleave in strength. The interpretation is proof
irrelevant: a proposition denotes $0$ or $1 = {0}$, a proof denotes
$0$, a $forall$ into propositions denotes $1$ exactly when every fibre
does, and a function type of the predicative levels denotes the full
set of set-theoretic functions — the two readings of a $forall$ in
@sec:interp. It is defined on a term in its context, by structural
induction on the term, and partially:
whether the clause for proofs or for propositions applies to a term is
a matter of its type. It is shown defined and sound on every derivable
judgement by induction on the derivation, and the case of the
conversion rule uses subject reduction and confluence of
reduction. Our interpretation is total and term-directed, takes
the choice from the annotation, and @thm:sound is an induction over
the checker's three relations that uses neither. Werner interprets an
inductive type of a universe as the least fixed point, in that
universe, of the monotone operator that strict positivity provides,
and his calculus has no inductive propositions; here proposition-valued families
are least fixed points too, in $cal(U)_0$ (@sec:ind-model).

*Barras, "Sets in Coq, Coq in Sets".* Barras @barras2010 axiomatises
intuitionistic ZF, possibly with inaccessible cardinals, inside Coq,
develops functions, ordinals and fixpoint theory over the axioms, and
proves set-theoretic models of the Calculus of Constructions sound, as
well as its extension with a hierarchy of universes (interpreted by
Grothendieck universes) and an extension with the natural numbers. The
set theory is given by axioms, as ours is (@sec:lib). Products are
interpreted by one clause: with Aczel's encoding of a function as the
set of pairs $(x, y)$ with $y$ in its value at $x$, a function into
propositions collapses to a proposition, so the interpretation, like
ours, consults no typing information and, unlike ours, needs no
annotation. In our set
theory a graph is never the point (@sec:lib), so that a graph
determines its domain; the two readings of a $forall$ or a $lambda$
are then different sets, and the annotation chooses between them.
Soundness there is stated for semantic judgements $Gamma ⊨ M
: T$ and $Gamma ⊨ M = M'$ over valuations, close to our
three claims, and the typing derivations of the calculus, in a
presentation with judgemental equality, are shown to imply them; our claims are proved of the checker's verdicts instead.
Barras observes that set-theoretic $beta$ holds only for arguments in
the function's domain, so his semantic $beta$ rule has a typing
premise; in our proof the same condition is checked by the checker
itself, which before a $beta$ step whose function may be a proof
infers the argument's type and compares it with the domain
(@sec:red).

*Dybjer, "Inductive families".* Dybjer @dybjer1994 gives a general
scheme for inductive definitions of families of sets in Martin-Löf's
type theory: formal criteria for the formation and introduction rules
of a new set former — parameters, indices, non-recursive premises and
recursive premises — and an inversion principle that derives the
elimination and equality rules from them. A recursive premise may be a
function over a sequence of types that does not mention the set former
being defined: strictly positive, generalised induction. Our blocks
follow this scheme (@sec:ind-checks): ordinary fields are his
non-recursive premises, reflexive fields his recursive premises with
the field's telescope as that sequence, and recursive fields the case
of an empty one. His order, non-recursive premises before recursive
ones, appears here as the condition that nothing after a reflexive
field depends on its value. The recursor's type and its $iota$ laws are
generated from the constructors as his elimination and equality rules
are; in our proof they are not rules of a calculus but statements
about the model, where the recursor's set is constructed and the
$iota$ law proved (@thm:iota). Proposition-valued families, and the
subsingleton criterion for their large elimination, belong to the
impredicative setting, which his scheme, for a predicative theory, does
not have.

*Abbott, Altenkirch and Ghani, "Containers".* Abbott, Altenkirch and
Ghani @abbott2005 represent strictly positive types as containers: a
set of shapes and, for each shape, a set of positions, an element
being a shape with an element of the argument at each of its
positions. They show that nested strictly positive inductive and
coinductive types exist in any Martin-Löf category — locally cartesian
closed, with disjoint coproducts and W-types — by representing them as
containers and constructing them from W-types. In these terms an
element's support (@sec:ind-model) is the set of its positions with the
occurrences that fill them, and the bound $A$ is one set that holds
the positions of every shape. Our proof represents no operator as a
container: the support and the bound are read off the block's fields,
and a nested occurrence is handled by checking the container's own
constructors at the given instantiation (@sec:nest-checks) rather
than by composing containers. Coinductive types are outside our proof,
and indexed families outside the paper's containers.

*Traytel, Popescu and Blanchette, "Foundational, compositional
(co)datatypes for higher-order logic".* Traytel, Popescu and Blanchette
@traytel2012 build datatypes and codatatypes in Isabelle/HOL, with
mutual and nested recursion and corecursion, from _bounded natural
functors_: type constructors equipped with a map function, set
functions returning the elements an argument holds, and an infinite
cardinal bounding those sets, subject to conditions including
naturality and the bound. The class of these functors is closed under
composition, initial algebras and final coalgebras, so a datatype
nested through `list` uses the fact, proved once, that `list` is a
bounded natural functor; it includes non-free type constructors such
as finite sets. The bound is what lets the initial algebra be
constructed inside HOL. Our proof uses no map function and records
nothing per type former: the operator's accessibility, a support bound
in the same role, is read off the checker's positivity check for each
block, and a container's positivity in its parameter is decided at
each instantiation by walking its constructors (@sec:nest-checks),
never stored. Coverage differs as well: their framework has
codatatypes and nesting through non-free type constructors; ours has
indexed, universe-polymorphic families and proposition-valued ones,
and no codatatypes.

*Aczel, "An introduction to inductive definitions".* Aczel's chapter
@aczel1977 treats inductive definitions by rule sets and by monotone
operators on the subsets of a set: the set inductively defined is the
least set closed under the rules, which is the least fixed point of
the operator and is reached by iterating it. It calls an operator
$kappa$-based when every element it produces from a set $X$ it already
produces from a subset of $X$ of cardinality less than $kappa$ — as
when every rule has fewer than $kappa$ premises — and shows that for
regular $kappa$ such an operator's iteration closes by stage $kappa$.
Accessibility (@sec:ind-model) is this idea of rules with a bound on
their premises, the bound being a set $A$ indexing the support rather
than a cardinal. What is specific to our proof is where the bound comes
from: it is not stated with a rule set or a type former but read off
the checker's positivity check, for each block — one occurrence per
reflexive field and tuple of its telescope — and, for a nested block,
at each instantiation of a container (@sec:nest-checks).
