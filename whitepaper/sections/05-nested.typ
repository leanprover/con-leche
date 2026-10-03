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
recursive field _is_ a member of the family, a reflexive field is a
function into it. A _nested_ block mentions it inside another type,
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
some levels, applied to arguments one of which is the _member_
$I thick arrow(x) thick arrow(e)$: the family at the block's own
parameters and some index expressions. That domain is the block's
_class_, a type the recursion has to pass through; here it is
$List thick (Tree thick alpha)$. The fragment's specification of a
block gains this one datum
(#src("whitepaper/Fragment/Spec.lean", 105, 136)[the class]): the
container's stored data, its levels and other arguments, the position
$p$ of the member among its parameters, the member's index
expressions, and the name of the companion recursor $TRec1$
introduced in @sec:nest-rec.

#real[
  The container is found by reducing the field's domain to an
  application of a stored inductive type, and the instantiation —
  the levels and the arguments with the member in place — is
  recorded
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1406, 1415)[the container case]).
]

What the fragment admits is nesting at depth one — the member is an
argument of the container directly, not of a container inside a
container — through one container instance per block, where the
container has parameters and no indices and the member fills one
parameter position; the container's own fields are ordinary or
recursive — reflexive only with the empty telescope — and never
themselves container fields. What
the real checker accepts beyond this is @sec:nest-beyond.

== What is checked <sec:nest-checks>

*Positivity through the container.* A recursive field is positive
because the family occurs as the whole domain; a container field
puts the family _inside_ $K$, and whether that is positive depends
on how $K$ uses its parameter. The checker answers by reading $K$'s
own stored constructors with the member in the parameter's place.
For @ex:tree it fetches $List$'s constructors, $nil$ and
$cons : forall (h : alpha) thin ann(never). thin forall (t : List thick alpha) thin ann(never). thin List thick alpha$,
and reads them at $alpha := Tree thick alpha$. The condition is that
every field of every constructor of the container is one of three
things: the _member field_ — the parameter itself, as $h$ is; a
_recursive field_ of the container, as $t$ is; or an ordinary field
whose domain mentions neither the member parameter nor an earlier
member field. So the member never occurs to the left of an arrow,
under a binder or inside yet another type, and nothing after a
member field reads its value. The fragment also asks that the
container's constructors have no index expressions, that the
member's parameter domain is a sort and that no later parameter
depends on it
(#src("whitepaper/Fragment/Spec.lean", 182, 208)[strict positivity in the member's position]).

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
positive in the member's position. Its sort at the instantiation is
the block's sort, and so is the sort of the member parameter's
domain, so that a fibre of the family can be the parameter's value.
The class has a type at the block's parameters, which is what puts
the class's arguments in the container's parameter domains. And the
two recursors' types and every rule's type have types in the
environment holding the type former and the constructors. One rule of
@sec:ind-checks tightens: _large elimination is refused for a nested
block unless its sort is never zero_
(#src("whitepaper/Fragment/Decl.lean", 800)[fragment],
#src("ConLeche/Kernel/Inductives/BlockRec.lean", 82, 84)[the real checker's guard]),
as in the official kernel. The subsingleton criterion is therefore
never asked of a nested block, and the model never needs the witness
device of @thm:iota's proof for a nested block: wherever the
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
  member field $t$ and the class's at the recursive field $ts$ — so
  the container's constructors are read as if they were constructors
  of the block: the member field becomes a recursive field, the
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

Fix a nested block, a valuation and parameter values $arrow(X)$.
The operator $Phi$ of @sec:ind-model acts on predicates $Z$ over
(index values, a set), and "fit" reads each field's domain with the
family that $Z$ describes. The one new clause is the set a container
field ranges over, and the one new idea is where that set comes
from.

*A container field's set.* The container $K$ was installed before,
so the model already assigns it a set — the graph, over $K$'s
parameters, of $K$'s own fibres. The class at a member set $Y$ is
that set applied to the class's arguments with $Y$ at the member's
position
(#src("whitepaper/Fragment/IndSem.lean", 291, 294)[fragment]), and by
$beta$ it is $K$'s family at those parameters
(#src("whitepaper/Fragment/NestSem.lean", 300, 304)[the class is the container's family]).
A container field ranges over the class at the fibre of the
_approximant_ $Z$ — the stage of the fixed point reached so far —
at the member's index expressions
(#src("whitepaper/Fragment/IndSem.lean", 321, 333)[the field's set]):
for $Tree$, the children of a node at stage $Z$ are the lists of
trees already in $Z$. Nothing is constructed: the container's least
fixed point is reused at every stage of the block's.

For $Phi$ to have a least fixed point it must be monotone, so the
class must grow with its member set. This is the one fact about the
container the model needs, and it is not a fact about $K$ "in its
parameter" — nothing was recorded about that when $K$ was installed
— but a consequence of two things the model does know: that $K$ is
positive in the member's position, which the checker verified, and
that $K$'s family is the _least_ fixed point of its operator.

#lemma(name: "the class grows with the member set")[
  Let $Y subset.eq Y'$ be two member sets in $cal(U)_(phi(u))$, the
  universe the block's sort names (its _result universe_). Then every
  member of the class at $Y$ is a member of the class at $Y'$, and
  the class at $Y$ is in the result universe
  (#src("whitepaper/Fragment/NestSem.lean", 401, 404)[fragment]\;
  real proof: #src("ConLeche/Model/Inductives/ContLeaf.lean", 180, 183)[a container instance grows along a relation],
  from #src("ConLeche/Model/Annot/BlockLfpMono.lean", 28, 34)[the container case of monotonicity]).
] <lem:class-mono>

#proof[
  By induction over $K$'s family at $Y$ — leastness — show that
  every member is in $K$'s family at $Y'$
  (#src("whitepaper/Fragment/NestSem.lean", 364, 374)[fragment]).
  A member is a tagged tuple fitting a constructor of $K$ at the
  parameters with $Y$. By positivity each field is the member field,
  whose value is in $Y$ and hence in $Y'$; a recursive field, whose
  value is in the family at $Y$ and in the family at $Y'$ by the
  induction hypothesis; or an ordinary field, whose domain mentions
  neither and is the same set at $Y$ and at $Y'$
  (#src("whitepaper/Fragment/NestSem.lean", 315, 331)[the three cases]).
  So the tuple fits the same constructor at $Y'$, and is a member of
  the family there. The class at $Y$ is a fibre of $K$'s family, and
  a fibre lies in the universe $K$'s sort names, which at the
  instantiation is the block's: the checker compared the two.
]

With the lemma, $Phi$ is monotone and the family is its least fixed
point as in §4
(#src("whitepaper/Fragment/IndSem.lean", 300, 312)[the lemma's two conclusions, as the fragment states them]);
the lemma itself is proved from what the container's installation
left in the model and what the block's own checks add
(#src("whitepaper/Fragment/NestSem.lean", 196, 225)[what is known about the container]).
For this the model of an environment remembers, for every plain
block it holds, that the block's type former denotes the graph of its
family and its constructors their tagged tuples
(#src("whitepaper/Fragment/BlockModel.lean", 46, 57)[the block's law],
#src("whitepaper/Fragment/BlockModel.lean", 61, 66)[a model that remembers its blocks]);
a nested block, never being a container in the fragment, stores no
such law.

*The bound.* The fibre must again be separated from a member of the
universe closed under the constructors. The fragment applies the
inductive closure law of @sec:ind-model once to the block's
constructors _and_ the container's at the instantiation, over a
joint index — the family's fibres and the class — with the member
field read as a recursive field at the family's bound
(#src("whitepaper/Fragment/IndSem.lean", 366, 370)[the joint index],
#src("whitepaper/Fragment/IndSem.lean", 392, 408)[the container's constructors at the instantiation]);
by one more induction over $K$'s family, the class at the family's
fibre lies inside its part of that bound
(#src("whitepaper/Fragment/NestSem.lean", 579, 584)[fragment]).

#real[
  The bound comes from accessibility as in §4, read off the
  positivity walk's run case by case
  (#src("ConLeche/Semantics/Inductives/HoleAcc.lean", 8, 19)[accessibility in the holes]),
  with a container instance accessible as soon as the container's
  constructors are, at the instantiation
  (#src("ConLeche/Model/Inductives/ContAcc.lean", 15, 29)[the container case]);
  monotonicity is inverted from the same run, one lemma per case of
  the walk
  (#src("ConLeche/Semantics/Inductives/HoleMono.lean", 9, 23)[monotonicity in the holes]),
  the container case reading the container's least fixed point at
  two parameter instantiations and asking nothing of the container
  in its parameter
  (#src("ConLeche/SetModel/HoleClose.lean", 7, 15)[the set-level half]).
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
(#src("whitepaper/Fragment/NestRec.lean", 172, 186)[the step],
#src("whitepaper/Fragment/NestRec.lean", 193, 196)[the graph]).
The graph is single-valued because tags and tuples are injective,
the block's constructors being tagged after the container's so that
no block value is a class value
(#src("whitepaper/Fragment/NestRec.lean", 472, 476)[fragment]). It
is total on the family and on the class by an induction over the
family with an inner induction over the class, the two
_interleaved_: at a container field — whose value is in the class at
the approximant — the inner induction over the class at that
approximant supplies the values at its members, the member fields
being in the approximant
(#src("whitepaper/Fragment/NestRec.lean", 584, 591)[totality],
#src("whitepaper/Fragment/NestRec.lean", 571, 576)[the inner induction]).
The inner induction is the container's own: the class's inversion,
introduction and induction principles are $K$'s fixed-point laws at
the instantiation, read in the block's terms
(#src("whitepaper/Fragment/NestClass.lean", 406, 414)[the class's laws]).
Both recursion equations follow
(#src("whitepaper/Fragment/NestRec.lean", 678, 686)[$TRec$],
#src("whitepaper/Fragment/NestRec.lean", 693, 700)[$TRec1$]),
and each recursor's set is a member of its type
(#src("whitepaper/Fragment/NestIota.lean", 1481, 1485)[$TRec$],
#src("whitepaper/Fragment/NestIota.lean", 1511, 1515)[$TRec1$]).

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
  (#src("whitepaper/Fragment/NestIota.lean", 2315, 2322)[$TRec$],
  #src("whitepaper/Fragment/NestIota.lean", 2966, 2971)[$TRec1$]\;
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
  (#src("whitepaper/Fragment/NestIota.lean", 2648, 2656)[the core]).
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
containers from a mutual block, whose members are walked together
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 1285, 1291)[a frame's group-mates]),
and nesting through a reflexive field
(#src("tests/e2e/src/ind_nest_via_refl.lean", 9, 14)[a field of type `W1 ViaRefl`]).
The recursors then come one per class, the classes read off the
stream's recursor types
(#src("ConLeche/Kernel/Inductives/GenRec.lean", 18, 27)[the classes]).
The real proof covers these accepts; the account of them is
#overview(5), and this document leaves them there (@sec:left-out).
