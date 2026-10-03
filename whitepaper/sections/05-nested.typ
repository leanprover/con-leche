#import "../lib.typ": *

// Notation local to this file, matching §4.
#let never = $sans("never")$
#let Sort = $sans("Sort")$
#let Nat = $sans("Nat")$
#let red = sym.arrow.r.squiggly
#let Tree = $sans("Tree")$
#let List = $sans("List")$
#let node = $sans("node")$
#let nil = $sans("nil")$
#let cons = $sans("cons")$
#let mk = $sans("mk")$
#let leaf = $sans("leaf")$
#let TreeNode = $sans("Tree.node")$
#let ListNil = $sans("List.nil")$
#let ListCons = $sans("List.cons")$
#let PMk = $sans("P.mk")$
#let TMk = $sans("T.mk")$
#let RNode = $sans("R.node")$
#let LCons = $sans("L.cons")$
#let P = $sans("P")$
#let L = $sans("L")$
#let R = $sans("R")$
#let T = $sans("T")$
#let TreeRec = $sans("Tree.rec")$
#let TreeRec1 = $sans("Tree.rec")_1$
#let ts = $italic("ts")$

= Nested inductive types <sec:nested>

This section changes tack. The previous sections present a fragment of
the checker and prove it sound; this one describes con-leche's check
for _nested_ blocks, which mention the type being defined inside
another inductive type, in full (mutual blocks aside), and then only
sketches how the construction and the proofs of @sec:ind-model extend
to them. Nothing is proved here, and the citations go to con-leche. A
restricted case — one container instantiation, at depth one, not under
a binder — is verified in the paper's Lean fragment:
#src("whitepaper/Fragment/NestInstall.lean", 197, 201)[installing such a block keeps a model of the environment].

== Nested blocks <sec:nest-what>

A block of @sec:ind mentions the type being defined only directly: a
recursive field's domain is the family itself, a reflexive field's a
function type into it. The standard example of such a nested block is
#src("tests/e2e/src/nested_rec.lean", 17, 18)[a tree whose children form a _list_ of trees]:
```lean
inductive Tree (α : Type) where
  | node : α → List (Tree α) → Tree α
```
The domain of the field `List (Tree α)` is the block `List`, installed
earlier — the _container_ — applied to the type being defined. The
type `Tree α` there is the _nested occurrence_, and `List (Tree α)`,
the container at given levels and parameters, is an _instantiation_ of
the container.

The container may also sit under a binder,
#src("tests/e2e/src/nested_p01.lean", 4, 5)[as in]
```lean
inductive P where
  | mk : (Nat → List P) → P
```
and nesting may go deeper. With
#src("tests/e2e/src/nest_rose_tree.lean", 15, 24)[lists, rose trees and]
```lean
inductive L (α : Type) where
  | nil : L α
  | cons : α → L α → L α
inductive R (α : Type) where
  | node : α → L (R α) → R α
inductive T where
  | leaf : T
  | mk : R T → T
```
the block `T` is nested through `R`, a container that is itself
nested: inside `R T`, the constructor `R.node` holds an `L (R T)`, so
`T` occurs at depth two. Containers with indices are allowed too,
#src("tests/e2e/src/indexed_nested_aux.lean", 13, 18)[as in]
```lean
inductive TV (α : Type) where
  | node : α → {n : Nat} → Vec (TV α) n → TV α
```
with `Vec α n` the vectors of length `n`.

== The positivity check <sec:nest-checks>

@sec:ind-checks classifies each field by the shape of its domain as
ordinary or reflexive. The checker does this with
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1453, 1496)[one walk over the constructors],
the same for every block, which also looks through containers. On a
block of §4's shape only the first three cases below apply, and they
give exactly §4's classification.

*Holes and frames.* The walk works on variables in place of types.
Before a constructor is examined, every application of the type being
defined to the block's parameters, $I thick arrow(x)$, is replaced by a
variable $X$ — a _hole_ — standing for that whole application, a family
over the indices. For this to catch every occurrence, the walk is
preceded by a
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1555, 1569)[uniformity check]:
the type being defined occurs in a constructor only applied to exactly
the block's parameters, at the block's own levels, and in no
parameter's domain. A _frame_ is one type whose constructors are being
walked, at one instantiation: the block itself, the _root_ frame, or a
container instantiation met in a field, such as $List$ at
$Tree thick alpha$. A container's frame has holes of its own: in
$List$'s constructors the application $List thick alpha$ of the
container to its own parameter is replaced by a hole $Y$
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1110, 1116)[_before_ $alpha$ is instantiated],
so it is not confused with an application at another instantiation.
Frames nest: walking one may meet another container, whose frame is
walked inside it. At any point the _types in progress_ are the type
being defined and every instantiation whose frame is open, each
present as its hole.

*The cases.* The walk first puts a field's domain in
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1458)[weak head normal form]
$w$, and every case reads $w$, never the domain's syntax — so a
container reached only by unfolding a definition counts as one. Inside
the current frame:

+ _Ordinary._ If $w$ mentions no type in progress, the field is
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1461, 1462)[_ordinary_].
+ _A $forall$._ If $w$ is $forall (z : A). thin B$, the domain $A$ must
  not mention a type in progress — otherwise the block is rejected,
  "non positive occurrence" — and
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1464, 1471)[the walk continues with $B$],
  $z$ a new variable. The binders passed form the field's telescope.
+ _A hole._ If $w$ is a hole applied to arguments, the arguments — the
  indices of the type the hole stands for — must all be present and
  must not mention a type in progress; otherwise "non valid
  occurrence". The root frame's hole makes the field _recursive_
  (_reflexive_ when a $forall$ was passed); the hole of a container
  frame, this one or an enclosing one, stands for an instantiation in
  progress — the tail of a $ListCons$, for instance — and
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1475, 1489)[is accepted].
+ _A container._ If $w$ is a stored inductive type $C$ — not one of the
  block's, and not the quotient type — at levels $arrow(u)$ applied to
  arguments, the first $k_C$ of them ($C$'s parameter count) are its
  parameters $arrow(D)$, the rest its indices.
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1415, 1440)[It is required]
  that
  - the indices mention no type in progress — they may mention earlier
    fields, as the $n$ of $sans("Vec") thick (T thick alpha) thick n$
    does;
  - the parameters mention no variable but the block's parameters and
    the holes — no field, no variable bound by a $forall$ of the field
    ("parameters cannot contain local variables");
  - $arrow(u)$ has $C$'s number of levels, and every index of $C$ is
    supplied;
  - #src("ConLeche/Kernel/Inductives/Positivity.lean", 1124, 1158)[$C$'s index telescope at $arrow(D)$]
    mentions no type in progress, and $C$'s sort is equivalent to the
    block's ("must live in the same universe").
  The parameters may mention the types in progress anywhere — in
  $List thick (Nat -> Tree thick alpha)$, say; the frame decides whether
  that is positive. Then
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1395, 1404)[the instantiation $C.\{arrow(u)\} thick arrow(D)$ is looked up]:
  if it is in progress, it is rejected — its syntactic occurrences
  have become its hole, so meeting it as a type here means reduction
  produced it; otherwise its frame is walked, as described next
  (unless the same instantiation was accepted before). The field is
  then _nested_, under the $forall$s it passed.
+ _Anything else_ — the type being defined at other levels, a variable
  that is not a hole, a quotient — is
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1488, 1496)[rejected as a "non valid occurrence"].

*Walking a frame.* At an instantiation $C.\{arrow(u)\} thick arrow(D)$,
the walk checks that $C.\{arrow(u)\} thick arrow(D)$ has a type, and
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1333, 1351)[introduces a hole for it]:
a variable standing for the container's type former applied at this
instantiation. It then
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1213, 1262)[takes each of $C$'s constructors in turn]:

- its stored type at $arrow(u)$, the frame's applications replaced by
  the holes and the parameters instantiated at $arrow(D)$, must be a
  type;
- every field is classified by the cases above, inside this frame;
- no later field and no result index may depend on a field that is not
  ordinary (§4's second shape condition, at the instantiation);
- the result's indices mention no type in progress;
- the constructor's walked type is recorded, every hole read back as
  the application it stands for, for the recursors below.

#src("ConLeche/Kernel/Inductives/Positivity.lean", 1592, 1600)[The root frame]
is the same loop over the block's own constructors.

On $Tree$, the field $ts$ meets the container case at $List$ with the
parameter $X$. In $List$'s frame, $ListNil$ has no field, and $ListCons$ has
the fields $h : X$, the root's hole — recursive — and $t : Y$, the
frame's own hole — accepted. In $PMk : (Nat -> List thick P) -> P$ the
walk passes a $forall$ over $Nat$ and meets $List$ at $X$ the same
way. For the rose trees, $TMk$'s field meets $R$ at $X$; in $R$'s
frame, with its hole $Y_R$, $RNode$'s fields are $X$ and $L thick Y_R$,
so $L$'s frame opens inside $R$'s, with its hole $Y_L$, and there
$LCons$'s fields are $Y_R$ and $Y_L$, both accepted. A container that
uses its parameter to the left of an arrow, such as $C thick alpha$
with a constructor of type $(alpha -> Nat) -> C thick alpha$, fails at
the instantiation: in its frame that field's domain is $X -> Nat$, a
$forall$ whose domain mentions the hole. Whether a container is
positive in its parameter is thus decided at the instantiation, by
walking it; nothing about it is recorded when the container is
installed.

#real[
  The official kernel translates a nested block into an auxiliary
  mutual block, with a copy of the container per instantiation, and
  checks that; con-leche builds no auxiliary type and walks the
  container at the instantiation (#overview(5)). It keeps
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 658, 664)[a record of the instantiations it accepted, beside the set of open ones],
  and an accepted instantiation is not walked again — unless its
  parameters mention a container frame's hole, since one hole variable
  stands for different instantiations in different frames
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1364, 1382)[a new frame]).
  An instantiation whose parameters mention no such hole is
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1356, 1357)[walked outside the enclosing frames],
  as it reads nothing of them. The walk runs on fuel derived from the
  constructor's size, and running out declines.
]

== Classes and their recursors <sec:nest-rec>

A recursion over a tree has to pass through the list of its children.
So a nested block's recursors eliminate several types, its _classes_:
the type being defined and the container instantiations the recursion
passes through — every instantiation at which a field of the block or
of a walked container lands, read with its holes back as the types
they stand for, needs one. For $Tree$ the classes are
$Tree thick alpha$ and $List thick (Tree thick alpha)$; for the rose
trees, $T$, $R thick T$ and $L thick (R thick T)$. Each class gets a
motive and a recursor — $T.sans("rec")$ for the type being defined,
$T.sans("rec")_1, T.sans("rec")_2, dots$ for the others — and each
constructor of each class a minor premise; all recursors share one
prefix: the parameters, the motives and the minor premises.
#src("ConLeche/Kernel/Inductives/GenRec.lean", 143, 163)[A minor premise]
is generated as in @sec:ind-checks from the constructor's fields at
the instantiation, with one inductive hypothesis per recursive or
nested field: the motive of the class where the field lands, under the
field's $forall$s, read off the walk's recorded type
(#src("ConLeche/Kernel/Inductives/GenRec.lean", 180, 187)[a recursor's type],
#src("ConLeche/Kernel/Inductives/GenRec.lean", 189, 212)[a rule]).

#example(name: [$Tree$'s recursors])[
  With $C$ the motive for $Tree thick alpha$ and $C_1$ the motive for
  $List thick (Tree thick alpha)$, and $ann(q)$ as in @ex:nat, the
  shared prefix is the parameter, the two motives, a minor premise for
  $TreeNode$ and one for each of $List$'s constructors at the
  instantiation:

  $
    TreeRec.\{ell\} : & forall (alpha : Sort 1) thin ann(q). thin forall (C : forall (t : Tree thick alpha) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (C_1 : forall (ts : List thick (Tree thick alpha)) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (s : forall (a : alpha) thin ann(q). thin forall (ts : List thick (Tree thick alpha)) thin ann(q). thin forall (h : C_1 thick ts) thin ann(q). thin C thick (TreeNode thick a thick ts)) thin ann(q). \
    & forall (n : C_1 thick ListNil) thin ann(q). \
    & forall (c : forall (t : Tree thick alpha) thin ann(q). thin forall (ts : List thick (Tree thick alpha)) thin ann(q). \
    & quad quad forall (h : C thick t) thin ann(q). thin forall (h_1 : C_1 thick ts) thin ann(q). thin C_1 thick (ListCons thick t thick ts)) thin ann(q). \
    & forall (t : Tree thick alpha) thin ann(q). thin C thick t \
    TreeRec1.\{ell\} : & dots.c thin forall (ts : List thick (Tree thick alpha)) thin ann(q). thin C_1 thick ts
  $

  (the $dots.c$ is the same prefix; the constructors' own parameter
  arguments are left implicit). The minor for $TreeNode$ has one inductive
  hypothesis, $C_1$ at the nested field; the minor for $ListCons$ has two,
  $C$ at the field that held the hole $X$ and $C_1$ at the one that
  held $Y$. With $arrow(r)$ for the prefix
  $alpha thick C thick C_1 thick s thick n thick c$, the three rules are

  $
    TreeRec thick arrow(r) thick (TreeNode thick a thick ts) & red s thick a thick ts thick (TreeRec1 thick arrow(r) thick ts) \
    TreeRec1 thick arrow(r) thick ListNil & red n \
    TreeRec1 thick arrow(r) thick (ListCons thick t thick ts) & red c thick t thick ts thick (TreeRec thick arrow(r) thick t) thick (TreeRec1 thick arrow(r) thick ts).
  $
] <ex:tree-rec>

A nested field under binders gets its hypothesis under the same
binders: for $PMk : (Nat -> List thick P) -> P$ the minor premise is
$ forall (f : Nat -> List thick P) thin ann(q). thin forall (h : forall (n : Nat) thin ann(q). thin C_1 thick (f thick n)) thin ann(q). thin C thick (PMk thick f). $

*Where a rule of $T.sans("rec")_1$ fires.* A rule of @sec:ind-model
takes the constructor's levels and parameters to be the recursor's
own. At a container class they are not: $ListCons$ in the class
$List thick (Tree thick alpha)$ has the parameter $Tree thick alpha$,
not the recursor's $alpha$, and $List$'s level names, not $Tree$'s. So
#src("ConLeche/Kernel/Env.lean", 196, 206)[each rule of a recursor at a container class stores the instantiation]
— the container's levels and parameters, as terms in the recursor's
level parameters and parameters — and fires only on a constructor
application whose levels and parameters equal
#src("ConLeche/Kernel/CoreDefs.lean", 884, 891)[the stored ones, instantiated at the recursor's levels and parameter arguments]
(#src("ConLeche/Rules/Rel.lean", 197, 204)[the levels by the level oracle, the parameters definitionally]);
the constructor's fields are what follows its own parameters, and the
index comparison is as before
(#src("ConLeche/Kernel/Inductives/RecCheck.lean", 592, 597)[the stored rules at a container class]).

*Large elimination.* A nested block may eliminate into every sort only
if #src("ConLeche/Kernel/Inductives/BlockRec.lean", 82, 84)[its sort is never zero]
(#src("ConLeche/Kernel/Inductives/GenRec.lean", 569, 573)[the guard, applied]),
as in the official kernel. A nested proposition eliminates only into
$sans("Prop")$, and the subsingleton criterion is never asked of a
nested block.

#real[
  As for a simple block (@sec:ind-checks), the classes and the layout
  of the prefix are read off the stream's recursor types by
  #src("ConLeche/Kernel/Inductives/ClassRead.lean", 15, 32)[an unverified pre-pass],
  and each class is then checked: the type being defined at the
  block's levels and parameters, or
  #src("ConLeche/Kernel/Inductives/RecCheck.lean", 400, 437)[a stored inductive type, not the quotient, whose parameters mention the type being defined and nothing but the block's parameters, in the block's sort].
  #src("ConLeche/Kernel/Inductives/Positivity.lean", 1646, 1654)[Every outside class is walked]
  as a container met at the root, so every class is an instantiation
  the walk visited; a field landing at a class the stream gives
  #src("ConLeche/Kernel/Inductives/GenRec.lean", 453, 456)[no recursor] for
  is rejected. One class may be visited at several places: in
  #src("tests/e2e/src/corner_nestind_f13_listrose.lean", 12, 15)[a block with a field of type $List thick (sans("RL") thick sans("TL"))$],
  with $sans("RL") thick alpha$ a rose tree over lists, that
  instantiation is met at the block's field and again inside
  $sans("RL") thick sans("TL")$; the generator checks that
  #src("ConLeche/Kernel/Inductives/GenRec.lean", 256, 271)[every visit gives each field the same inductive hypothesis].
]

== The model, as a sketch <sec:nest-model>

What follows is intuition for how the construction of @sec:ind-model
carries over; con-leche's proof is linked, and no step here is proved.

*The operator.* Fix the parameters, and let $W$ be the _approximant_,
the family the operator is applied to, as in @sec:ind-model. A
container field ranges over the container's own family at the
instantiation, with $W$ in place of the type being defined: the
children of a node range over the lists whose entries all lie in $W$.
That family is known, because every installed block leaves
#src("ConLeche/Model/Annot/BlockLfp.lean", 32, 43)[a clause in the model]:
its type former denotes, at all parameter values, the least fixed
point of its operator. So the container's least fixed point is
reused, at each approximant, and nothing new is constructed for it. At
depth two the same holds one level down: an element of $R thick W$
holds a list from $L$'s family at the parameter $R thick W$.

*Accessibility.* The block's operator stays accessible, because the
walk that checked positivity also bounds the support. An element of
the container's family at $W$ depends on $W$ only through the
positions the walk found: the fields that held the root's hole, such
as the entries of a list, and, through the fields that held the
frame's own hole, the same positions of its sub-values. Read as an
operator of two arguments — the approximant and the container's own
family — the container's operator at the instantiation is accessible
by
#src("ConLeche/Semantics/Inductives/HoleAcc.lean", 39, 45)[the same case-by-case argument as §4's],
#src("ConLeche/Model/Inductives/ContAcc.lean", 15, 35)[run on the frame];
and
#src("ConLeche/SetModel/Access.lean", 506, 516)[the least fixed point of such an operator is accessible in its first argument],
the supports of an element's sub-values collected along paths into
one support. Monotonicity follows from accessibility as in §4;
con-leche proves it case by case too, the container's row
#src("ConLeche/Semantics/Inductives/HoleMono.lean", 17, 23)[comparing its least fixed points at two instantiations]
#src("ConLeche/SetModel/HoleClose.lean", 17, 22)[by leastness].
Nothing about the container's parameter is recorded at its install:
the walk at the instantiation is what makes the argument go through.

*The family.* The container lives in the block's sort (case 4), so its
family at an approximant in the universe is in the universe, and the
operator maps the universe to itself. With accessibility,
@thm:closed-of-acc gives a closed family, and the block's family is
the least fixed point as in @sec:ind-model, with its fixed-point
equation and its induction.

*The recursors.* All recursors of the block are read off one graph: the
least relation between a class, an element of it and a value that is
closed under the rules of every recursor — at a constructor of a class,
the class's minor applied to the fields and to the graph's values at
the fields' landing classes. It is single-valued as in @sec:ind-model,
since tagged tuples are injective and, at the elimination level zero,
both sides are the point; the guard spares the model the agreement of
decodings that a large eliminator out of a proposition needs. It is
total by one induction over all the classes together: the family's
induction, entering at each nested field the container's own induction
at the instantiation, as deep as the walk went
(#src("ConLeche/SetModel/NestRec.lean", 8, 46)[the induction over the classes],
#src("ConLeche/SetModel/NestRecCls.lean", 6, 29)[read at the recursors' classes]).
The $iota$ laws follow as in @sec:ind-model: for a rule of
$T.sans("rec")_1$ the major is a container's constructor applied; the
recursor's fit puts its value in the class at the recursor's
parameters, and the container's fixed-point equation there identifies
the constructor and the fields with the rule's
(#src("ConLeche/Model/Inductives/BlockRecLaw.lean", 448, 456)[the graph's equation, lifted to the law]).
