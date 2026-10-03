#import "../lib.typ": *

// Notation local to this file, matching §4.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let always = $sans("always")$
#let Sort = $sans("Sort")$
#let Prop = $sans("Prop")$
#let zn = $sans("zeroness")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let tag = $op("tag")$
#let tuple = $op("tuple")$
#let lfp = $op("lfp")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let Tree = $sans("Tree")$
#let List = $sans("List")$
#let node = $sans("node")$
#let nil = $sans("nil")$
#let cons = $sans("cons")$
#let TreeRec = $sans("Tree.rec")$
#let TreeRec1 = $sans("Tree.rec")_1$
#let TRec = $sans("T.rec")$
#let TRec1 = $sans("T.rec")_1$
#let ts = $italic("ts")$

= Nested inductive types <sec:nested>

A block of @sec:ind mentions the family it defines only directly: a
recursive field's domain _is_ the family, a reflexive field's domain
a function type into it. A _nested_ block mentions it inside another type,
as in a tree whose children are a _list_ of trees. The checks and
the model of §4 carry over with one addition each — the positivity
check looks through the other type, and the model reads that type's
own least fixed point — and the recursor gains a companion. This
section does the same work as §4 for that addition, on the
fragment's nested extension, and says what the real proof does
beyond it.

== A nested block <sec:nest-what>

#example(name: [$Tree$])[
  The block $Tree$ has one parameter $(alpha : Sort 1)$, no index, sort
  $Sort 1$, and one constructor
  $ node : forall (alpha : Sort 1) thin ann(never). thin forall (a : alpha) thin ann(never). thin forall (ts : List thick (Tree thick alpha)) thin ann(never). thin Tree thick alpha. $
  The second field's domain is $List thick (Tree thick alpha)$: the
  block $List$, installed earlier, applied to the family being
  defined (#src("tests/e2e/src/nested_rec.lean", 17, 18)[the fixture]).
] <ex:tree>

Such a field is a _container field_, the fourth kind of field after
the three of @sec:ind-checks
(#src("whitepaper/Fragment/Spec.lean", 43, 49)[fragment]). Its
domain is a previously installed block $K$ — the _container_ — at
some levels, applied to arguments one of which is the _nested
occurrence_ $I thick arrow(x) thick arrow(e)$: the type being
defined at the block's own parameters and some index expressions.
That domain is the block's _class_, a type the recursion has to
pass through; here it is $List thick (Tree thick alpha)$. The fragment's specification of a
block gains this one datum
(#src("whitepaper/Fragment/Spec.lean", 105, 136)[the class]): the
container's stored data, its levels and other arguments, the _nested
position_ $p$ — the position of the type being defined among the
container's parameters — the index expressions of the nested
occurrence, and the name of the companion recursor $TRec1$
introduced in @sec:nest-rec.

#real[
  The container is found by reducing the field's domain to an
  application of a stored inductive type, and the instantiation —
  the levels and the arguments with the type being defined in place
  — is recorded
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1406, 1415)[the container case]).
]

What the fragment admits is nesting at depth one — the type being
defined is an argument of the container directly, not of a container
inside a container — through one container instance per block, where
the container has parameters and no indices and the type being
defined fills one parameter position; the container's own fields are ordinary or
recursive — reflexive only with the empty telescope — and never
themselves container fields. What
the real checker accepts beyond this is @sec:nest-beyond.

== What is checked <sec:nest-checks>

*Positivity through the container.* A recursive field is positive
because the family occurs as the whole domain; a container field
puts the family _inside_ $K$, and whether that is positive depends
on how $K$ uses its parameter. The checker answers by reading $K$'s
own stored constructors with the type being defined in the
parameter's place. For @ex:tree it fetches $List$'s constructors,
$nil$ and
$ cons : forall (h : alpha) thin ann(never). thin forall (t : List thick alpha) thin ann(never). thin List thick alpha, $
and reads them at $alpha := Tree thick alpha$. The condition is that
every field of every constructor of the container is one of three
things: the _parameter field_ — the parameter at the nested position
itself, as $h$ is; a _recursive field_ of the container, as $t$ is;
or an ordinary field whose domain mentions neither that parameter
nor an earlier parameter field. So the parameter never occurs to the
left of an arrow, under a binder or inside yet another type, and
nothing after a parameter field reads its value. The fragment also
asks that the container's constructors have no index expressions,
that the domain of the parameter at the nested position is a sort
and that no later parameter depends on it
(#src("whitepaper/Fragment/Spec.lean", 182, 208)[strict positivity at the nested position]).

#real[
  This happens inside the one positivity walk of @sec:ind-checks: at
  an application of a stored inductive type the walk descends into
  that type's stored constructors at the instantiation, with the
  container instance being walked — like the family itself —
  replaced by a variable standing for the whole application
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 260, 279)[the cases],
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1442, 1453)[the walk]).
]

*The other checks.* A nested block passes the checks of
@sec:ind-checks for its type former and its constructors — a container
field's domain, the class, is type-checked like any other domain —
and then four more
(#src("whitepaper/Fragment/Decl.lean", 760, 803)[fragment]). The
container is stored, with no container field of its own, and is
positive at the nested position. Its sort at the instantiation is
the block's sort, and so is the sort of the parameter's domain at
the nested position, so that a fibre of the family can be the
parameter's value.
The class has a type at the block's parameters, which is what puts
the class's arguments in the container's parameter domains. And the
two recursors' types and every rule's type have types in the
environment holding the type former and the constructors. One rule of
@sec:ind-checks tightens: _large elimination is refused for a nested
block unless its sort is never zero_
(#src("whitepaper/Fragment/Decl.lean", 800)[fragment],
#src("ConLeche/Kernel/Inductives/BlockRec.lean", 82, 84)[the real checker's guard]),
as in the official kernel. The subsingleton criterion is therefore
never asked of a nested block, and the model never needs the
agreement of decodings that @thm:iota's proof draws from it: wherever the
recursion equation has content, the family is type-valued and
every major carries its fields.

== The generated recursors <sec:nest-rec>

A recursion over a tree has to pass through the list of its
children, so the recursor has two motives and two kinds of minor
premise, and there are two recursors sharing one prefix. In the
fragment, where the class is one container instance, they are
$TRec$, whose major is a member of the family, and
$TRec1$, whose major is a member of the class.

#example(name: [$Tree$'s recursors])[
  With $C$ the motive for $Tree thick alpha$ and $C_1$ the motive for
  $List thick (Tree thick alpha)$ — the class's motive takes no index
  and a member of the class — the shared prefix is the parameter,
  the two motives, a minor premise for $node$ and one for each of
  $List$'s constructors at the instantiation:

  $
    TreeRec.\{ell\} : & forall (alpha : Sort 1) thin ann(q). thin forall (C : forall (t : Tree thick alpha) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (C_1 : forall (ts : List thick (Tree thick alpha)) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (s : forall (a : alpha) thin ann(q). thin forall (ts : List thick (Tree thick alpha)) thin ann(q). thin forall (h : C_1 thick ts) thin ann(q). thin C thick (node thick a thick ts)) thin ann(q). \
    & forall (n : C_1 thick nil) thin ann(q). \
    & forall (c : forall (t : Tree thick alpha) thin ann(q). thin forall (ts : List thick (Tree thick alpha)) thin ann(q). \
    & quad quad forall (h : C thick t) thin ann(q). thin forall (h_1 : C_1 thick ts) thin ann(q). thin C_1 thick (cons thick t thick ts)) thin ann(q). \
    & forall (t : Tree thick alpha) thin ann(q). thin C thick t \
    TreeRec1.\{ell\} : & dots.c thin forall (ts : List thick (Tree thick alpha)) thin ann(q). thin C_1 thick ts
  $

  (the $dots.c$ is the same prefix, and the constructors' own
  parameter arguments are left implicit). The minor for $node$ has
  one inductive hypothesis, the _class's_ motive at the container
  field; the minor for $cons$ has two, the block's motive at the
  parameter field $t$ and the class's at the recursive field $ts$ —
  so the container's constructors are read as if they were
  constructors of the block: the parameter field becomes a recursive
  field, the
  container's recursive field a container field
  (#src("whitepaper/Fragment/Decl.lean", 349, 356)[the translation],
  #src("whitepaper/Fragment/Decl.lean", 381, 383)[a translated constructor]).
  There are three rules, one per constructor of the block and of
  the container; $arrow(r)$ abbreviates the shared prefix
  $alpha thick C thick C_1 thick s thick n thick c$:

  $
    TreeRec thick arrow(r) thick (node thick a thick ts) & red s thick a thick ts thick (TreeRec1 thick arrow(r) thick ts) \
    TreeRec1 thick arrow(r) thick nil & red n \
    TreeRec1 thick arrow(r) thick (cons thick t thick ts) & red c thick t thick ts thick (TreeRec thick arrow(r) thick t) thick (TreeRec1 thick arrow(r) thick ts).
  $
] <ex:tree-rec>

In general the prefix is the parameters, the block's motive, the
class's motive, the block's minors and the class's minors; a minor
is generated as in @sec:ind-checks from the constructor's fields,
with the inductive hypothesis at a container field being the class's
motive at the field, and the rules' right-hand sides call
$TRec$ at a reflexive field (under its telescope, as in §4) and
$TRec1$ at a container field. (Generated:
#src("whitepaper/Fragment/Decl.lean", 389, 391)[the class's motive],
#src("whitepaper/Fragment/Decl.lean", 404, 416)[a class minor],
#src("whitepaper/Fragment/Decl.lean", 438, 450)[the two types],
#src("whitepaper/Fragment/Decl.lean", 452, 466)[an inductive hypothesis' value]
and #src("whitepaper/Fragment/Decl.lean", 502, 509)[a rule of $TRec1$]\;
real checker: #src("ConLeche/Kernel/Inductives/GenRec.lean", 180, 187)[the type],
#src("ConLeche/Kernel/Inductives/GenRec.lean", 189, 212)[a rule],
one recursor per class.)

*Where a rule of $TRec1$ fires.* The $iota$ rule of
@sec:ind-model compares the constructor's parameters with the
recursor's. For a rule of $TRec1$ that comparison is wrong:
the constructor is $cons$, whose parameter — left implicit in
@ex:tree-rec — is $Tree thick alpha$, while the recursor's is
$alpha$. So each stored rule of
$TRec1$ carries its _instantiation_ — the container's
levels and the class's arguments, terms under the recursor's
parameter binders
(#src("whitepaper/Fragment/Env.lean", 43, 52)[fragment],
#src("ConLeche/Kernel/Env.lean", 196, 206)[real checker]) — and
fires by a second $iota$ rule that compares the constructor's levels
and parameters with the stored instantiation at the recursor's
levels and parameter arguments
(#src("whitepaper/Fragment/Rules.lean", 160, 172)[fragment],
#src("ConLeche/Kernel/Inductives/RecCheck.lean", 587, 597)[the stored rules, firing at their instantiation]).
The plain $iota$ rule applies only to a rule without a stored
instantiation, and not just because of the comparison: it finds the
constructor's fields by dropping the _recursor's_ parameter count
from the constructor's spine, the wrong count when the container has
more parameters than the block; the second rule drops the
constructor's own. The model's $iota$ law for such a rule assumes
neither comparison against the instantiation, and its proof uses no
comparison at all (@sec:nest-model), for the same reason the plain
law needs none in the type-valued regime: the major is a tagged tuple
and carries its fields.

== The model <sec:nest-model>

Fix a nested block, a valuation $phi$ and parameter values
$arrow(X)$. The block's operator $Phi$ is the operator of
@sec:ind-model with one more case, the set a container field ranges
over. The story of @sec:ind-model then repeats with that case added:
$Phi$ is monotone and accessible, so it has a closed family
(@thm:closed-of-acc) and its least fixed point is the family. What is
new is why the clause is monotone and accessible. The reason is not a
fact recorded about the container when it was installed. It follows
from two things the model already knows: the container is positive
at the nested position, which the checker verified, and its family is
a _least_ fixed point.

*A container field's set.* The container $K$ was installed before,
so the model already assigns it a set: by the law recorded when $K$
was installed — a fact about its set, not about monotonicity or
accessibility — the graph over $K$'s parameters of $K$'s family. For a set $Y$
write $arrow(d)[Y]$ for the class's arguments read at $arrow(X)$, with
$Y$ at the nested position $p$, and $Phi_K^(arrow(d)[Y])$ for $K$'s
operator at those parameter values. The _class at $Y$_ is $K$'s set
applied to $arrow(d)[Y]$
(#src("whitepaper/Fragment/IndCommon.lean", 201, 204)[fragment]). By
$beta$ it is $K$'s family at those parameters, a single set because
$K$ has no indices
(#src("whitepaper/Fragment/NestSem.lean", 311, 315)[the class is the container's family]):
$ cal(C)(Y) = lden K rden dot.op arrow(d)[Y] = lfp(Phi_K^(arrow(d)[Y])). $
Let $W$ be the family $Phi$ is applied to, the _approximant_. A
container field ranges over the class at $W$'s fibre at the nested
occurrence's index expressions $arrow(e)$:
$ cal(C)(W(arrow(e))) $
(#src("whitepaper/Fragment/IndSem.lean", 274, 294)[a field's set],
#src("whitepaper/Fragment/IndSem.lean", 296, 299)[the container clause]).
For @ex:tree, relative to the approximant $W$, the children of a node
range over the lists whose entries all lie in $W$. Nothing new is
constructed. The container's least fixed point is reused, at every
approximant.

*What the operator asks of the class.* The proofs of @sec:ind-model
go field kind by field kind, and at a container field they ask of
$cal(C)$ what they ask of a reflexive field's product. It must grow
with its argument. A member of $cal(C)(Y)$ must have a support in $Y$,
coded inside one bound fixed in advance. And $cal(C)(Y)$ must lie in
the universe whenever $Y$ does. These facts are the _container's
clause_
(#src("whitepaper/Fragment/IndSem.lean", 452, 471)[fragment]).
Given the clause, the proofs of @sec:ind-model go through unchanged
(#src("whitepaper/Fragment/IndSem.lean", 596, 609)[a field's set grows, the container case last],
#src("whitepaper/Fragment/IndSem.lean", 1193, 1200)[the operator is accessible]),
and the bound gains, per container field, the class's bound $A_K$ of
@lem:class-acc with each of its paths prefixed by the field's position
(#src("whitepaper/Fragment/IndSem.lean", 973, 990)[fragment]).

One observation about $K$ proves the clause. Recall from
@sec:nest-checks that positivity sorts $K$'s fields into three kinds.
A constructor of $K$ reads the parameter at the nested position only
through its parameter fields. It reads $K$'s own family only through
its recursive fields. An ordinary field reads neither, nor the value
of an earlier parameter field; and by the second shape condition of
@sec:ind-checks, which $K$ passed when it was installed, nothing reads
the value of an earlier recursive field. So a list of
fields that fits a constructor of $K$, at the parameter $Y$ and
relative to a family $L$, still fits in a changed setting: at another
parameter $Y'$ and relative to another family $L'$, provided the
parameter fields are replaced by members of $Y'$, the recursive
fields by members of $L'$, and the ordinary fields are kept
(#src("whitepaper/Fragment/NestSem.lean", 385, 399)[fragment]).
This is where positivity is used: were the parameter to occur to the
left of an arrow, say in a field of type $Y -> B$, a function on $Y$
would not be a function on a larger $Y'$, and neither lemma below
would hold.

#lemma(name: "the class grows with the approximant")[
  Let $Y subset.eq Y'$ be members of $cal(U)_(phi(u))$, the
  universe of the block's sort. Then $cal(C)(Y) subset.eq cal(C)(Y')$
  (#src("whitepaper/Fragment/NestSem.lean", 504, 515)[fragment]).
] <lem:class-mono>

#proof[
  Write $L_Y$ for $lfp(Phi_K^(arrow(d)[Y]))$. The family $L_(Y')$ is
  closed under the operator at $Y$. Take a constructor value whose
  fields fit at $Y$ relative to $L_(Y')$. Its parameter fields lie in
  $Y subset.eq Y'$, its recursive fields in $L_(Y')$, and its
  ordinary fields are unchanged. By the observation, the fields fit
  at $Y'$ relative to $L_(Y')$, and $L_(Y')$ is a fixed point of the
  operator at $Y'$. Now $L_Y$ is the _least_ closed family of the
  operator at $Y$ (@sec:ind-model), so $L_Y subset.eq L_(Y')$.
]

#lemma(name: "the class is accessible in the approximant")[
  In the type-valued regime, every member $v$ of $cal(C)(Y)$, for $Y in cal(U)_(phi(u))$, has a support in $Y$. That is, there are a subset
  $B$ of the _class's bound_ $A_K$ and an element $g(b) in Y$ for each
  $b in B$, such that $v in cal(C)(Y')$ for every $Y'$ in the universe
  holding every $g(b)$. The bound $A_K$, the finite paths over the
  numerals below the length of $K$'s longest field list, is computed
  from the specification alone and is a member of the universe
  (#src("whitepaper/Fragment/NestSem.lean", 700, 710)[fragment],
  #src("whitepaper/Fragment/IndSem.lean", 431, 439)[the bound]).
] <lem:class-acc>

#proof[
  Read $K$'s operator as a function of two arguments, the parameter
  $Y$ and its own family $L$
  (#src("whitepaper/Fragment/NestSem.lean", 532, 536)[fragment]).
  As such it is accessible with one code per field position. A
  constructor value's support is its parameter fields, which are
  occurrences in $Y$, and its recursive fields, which are occurrences
  in $L$. By the observation, the value is produced from every pair
  holding them
  (#src("whitepaper/Fragment/NestSem.lean", 546, 554)[fragment]).
  The _nested case of accessibility_ turns this into accessibility
  of $Y |-> L_Y$
  (#src("whitepaper/Fragment/Access.lean", 411, 423)[fragment]).
  The argument is an induction over $L_Y$. A member produced by the
  operator has a support of occurrences, each either in $Y$ or in
  $L_Y$. An occurrence in $L_Y$ has a support in $Y$ by the induction
  hypothesis. Prefix each of these supports with the position it
  came from, and the member's support becomes a set of paths. If
  $Y'$ holds all of them then $L_(Y')$ holds every occurrence, and
  $L_(Y')$ produces the member: it is a fixed point, because $K$'s
  operator with the parameter held at $Y'$ is still accessible and so
  has a closed family (@thm:closed-of-acc).
]

At a proposition the support is $Y$ itself: $Y subset.eq {pt}$, its
one possible element is coded by the point, a member of $A_K$, and
@lem:class-mono carries $v$ to every $Y'$ holding it. One more fact enters the clause, for the bound of
@sec:ind-model. That bound reads the telescopes at the one-fibre
family, where a container field needs a stand-in value. So the class
at ${pt}$ must be inhabited whenever the class at some $Y$ is. This is
an induction over $L_Y$ that replaces the parameter fields by the
point, using the observation once more
(#src("whitepaper/Fragment/NestSem.lean", 725, 733)[fragment]). The
clause is assembled from these lemmas, from the class's membership in
the universe — a fibre of $K$'s family lies in the universe $K$'s
sort names, which the checker compared with the block's — and from
what is known about the container
(#src("whitepaper/Fragment/NestSem.lean", 789, 798)[the clause],
#src("whitepaper/Fragment/NestSem.lean", 195, 223)[what is known]).
That knowledge is the container's law, its shape condition of
@sec:ind-checks, and the nested block's checks of @sec:nest-checks.
So the model of an environment remembers, for every plain block it
holds, that the block's type former denotes the graph of its family,
its constructors their tagged tuples, and that the universe bound on
its fields holds at every fitting parameter list
(#src("whitepaper/Fragment/BlockModel.lean", 46, 57)[the block's law],
#src("whitepaper/Fragment/BlockModel.lean", 61, 66)[a model that remembers its blocks]).
A nested block is never a container in the fragment, so it stores no
such law.

*The family and the constructors.* With the clause in hand, the rest
of @sec:ind-model applies as stated: the theorems there take the
clause as a premise and are the same theorems. The operator is
monotone, maps the universe to itself and is accessible, so it has a
closed family (@thm:closed-of-acc), and the block's family is its
least fixed point
(#src("whitepaper/Fragment/IndSem.lean", 1296, 1314)[the closed family and the family]).
The fixed-point equation, the constructors' values and law, and
induction over the family are as in @sec:ind-model
(#src("whitepaper/Fragment/IndSem.lean", 1324, 1359)[fragment]).

#real[
  Monotonicity and accessibility are read off the positivity check's
  run, case by case, as in @sec:ind-model. At a container instance,
  monotonicity compares the container's least fixed point at two
  parameter instantiations
  (#src("ConLeche/Semantics/Inductives/HoleMono.lean", 23)[the container row],
  #src("ConLeche/Model/Annot/BlockLfpMono.lean", 113, 125)[the container case]).
  Its set-level half is leastness, exactly as in @lem:class-mono
  (#src("ConLeche/SetModel/HoleClose.lean", 61, 70)[the least tuple lies below]).
  Accessibility in the holes has no container row
  (#src("ConLeche/Semantics/Inductives/HoleAcc.lean", 41, 45)[the cases]).
  A container instance is accessible once the container's
  constructors are, at the instantiation
  (#src("ConLeche/Model/Inductives/ContAccFrame.lean", 486, 491)[one constructor of a frame],
  #src("ConLeche/Model/Inductives/ContAcc.lean", 131, 137)[the instance]),
  by the same nested case of accessibility
  (#src("ConLeche/SetModel/Access.lean", 506, 515)[the least tuple is accessible in its parameter]).
  No monotonicity or accessibility fact about the container is
  recorded when it is installed. The fragment replaces the walk of
  the container's constructors at the instantiation by the
  observation about its fields.
]

*The two recursors.* Both recursors are read off one _graph_, the
least relation closed under the rules of both. At a tagged tuple
fitting a constructor of the block, the value at the family is the
block's minor at the fields and the inductive hypotheses; at a
tagged tuple fitting a constructor of the container at the
instantiation, the value at the class is the class's minor at the
fields and the hypotheses. A hypothesis at a reflexive field is the
graph's value at the family (under the field's telescope), at a
container field its value at the class
(#src("whitepaper/Fragment/NestRec.lean", 181, 196)[the step],
#src("whitepaper/Fragment/NestRec.lean", 202, 205)[the graph]).
The graph is single-valued because tagged tuples are injective,
the block's constructors being tagged after the container's so that
no block value is a class value
(#src("whitepaper/Fragment/NestRec.lean", 450, 454)[fragment]). It
is total on the family and on the class by an induction over the
family with an inner induction over the class, the two
_interleaved_. The outer induction runs over the family's separation
by "the graph has a value here", so a container field's value lies in
the class at a subset $Y$ of the family's fibre on which the graph is
already total; the inner induction over $cal(C)(Y)$ then supplies the
values at its members, its parameter fields being in $Y$
(#src("whitepaper/Fragment/NestRec.lean", 598, 606)[totality],
#src("whitepaper/Fragment/NestRec.lean", 555, 560)[the inner induction]).
The inner induction is the container's own: the class's inversion,
introduction and induction principles are $K$'s fixed-point laws at
the instantiation, read in the block's terms
(#src("whitepaper/Fragment/NestClass.lean", 359, 367)[the class's laws]).
Both recursion equations follow
(#src("whitepaper/Fragment/NestRec.lean", 686, 694)[$TRec$],
#src("whitepaper/Fragment/NestRec.lean", 702, 712)[$TRec1$]),
and each recursor's set is a member of its type
(#src("whitepaper/Fragment/NestIota.lean", 1451, 1455)[$TRec$],
#src("whitepaper/Fragment/NestIota.lean", 1481, 1485)[$TRec1$]).

#real[
  The graph is the one of @sec:ind-model over the recursor's
  classes, and the induction over the majors is proved from the
  classes' own fixed-point clauses by a strengthened predicate,
  without a joint operator
  (#src("ConLeche/SetModel/NestRec.lean", 9, 19)[the nested graph kit],
  #src("ConLeche/Model/Inductives/TargetNestKit.lean", 8, 19)[the classes as clauses]).
]

#theorem(name: [the $iota$ laws of a nested block])[
  Every rule of $TRec$ satisfies the $iota$ law of
  @def:iota-law, and every rule of $TRec1$ satisfies the
  $iota$ law of the second $iota$ rule — the same statement at the
  container's parameter count, with the index comparison as its
  only comparison premise: the comparisons against the stored
  instantiation, which the rule checks, are not part of the law
  (#src("whitepaper/Fragment/EnvModel.lean", 163, 190)[the law]).
  (#src("whitepaper/Fragment/NestIota.lean", 2281, 2288)[$TRec$],
  #src("whitepaper/Fragment/NestIota.lean", 2924, 2929)[$TRec1$]\;
  real proof: #src("ConLeche/Model/Annot/Laws.lean", 294, 297)[the stored instantiation's clause of the law].)
] <thm:iota-nested>

#proof[
  As for @thm:iota in the type-valued regime, which is the only regime
  with content: by the elimination guard, the elimination level of a
  nested block whose family may be a proposition is zero, and then
  both sides are the point. For a rule of $TRec1$ the
  major is the container's constructor applied, and the recursor's
  fit puts it in the class at the recursor's parameters; the class's
  inversion says it is a tagged tuple of fields fitting that
  constructor at the instantiation, and injectivity of tags and
  tuples identifies constructor and fields with the rule's. Neither
  the index comparison nor the stored instantiation is used
  (#src("whitepaper/Fragment/NestIota.lean", 2611, 2619)[the core]).
]

#theorem(name: "Installing a nested block")[
  If the environment has a model that remembers its blocks and the
  nested block passes the checks of @sec:nest-checks, then the
  extended environment has one, with every old constant's set
  unchanged
  (#src("whitepaper/Fragment/NestInstall.lean", 194, 199)[fragment]).
  With the plain block step of @sec:ind-model this gives
  #src("whitepaper/Fragment/NestInstall.lean", 203, 206)[one installation theorem for any accepted block],
  which is what the proof of @thm:accepted-model runs at a block
  step — the acceptance relation's block step is stated over any
  block, plain or nested
  (#src("whitepaper/Fragment/Consistency.lean", 46, 47)[fragment]) —
  and @cor:consistency holds as stated.
] <thm:install-nest>

== Beyond the fragment <sec:nest-beyond>

The real checker's positivity walk carries a stack of _frames_ — a
frame is one type whose constructors are being checked, the block
itself or a container instance met in a field. So it accepts a
container inside a container
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 1359, 1364)[a new frame],
#src("tests/e2e/src/nested_p03.lean", 5, 6)[a block nested at depth two]),
containers with indices
(#src("tests/e2e/src/nested_p25.lean", 7, 8)[a block nested through an indexed container]),
containers from a mutual block, whose types are walked together
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 1285, 1291)[a frame's group-mates]),
and nesting through a reflexive field
(#src("tests/e2e/src/ind_nest_via_refl.lean", 9, 14)[a field of type `W1 ViaRefl`]).
The recursors then come one per class, the classes read off the
stream's recursor types
(#src("ConLeche/Kernel/Inductives/GenRec.lean", 18, 27)[the classes]).
The real proof covers these accepts; the account of them is
#overview(5), and this document leaves them there (@sec:left-out).
