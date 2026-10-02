#import "../lib.typ": *

// Notation local to this file, matching §2 and §3.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let whenZero = $sans("whenZero")$
#let Sort = $sans("Sort")$
#let Prop = $sans("Prop")$
#let zn = $sans("zeroness")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
#let tag = $op("tag")$
#let tuple = $op("tuple")$
#let lfp = $op("lfp")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked
#let Nat = $sans("Nat")$
#let zero = $sans("zero")$
#let succ = $sans("succ")$
#let mk = $sans("mk")$
#let NatRec = $sans("Nat.rec")$
#let PRec = $sans("P.rec")$

= Adding inductive types <sec:ind>

The second kind of declaration is an inductive block: a type former
with its constructors and its recursor. It is checked and installed by
the same shape of argument as a definition (@sec:defs), and its
reduction rule $iota$ reads the environment as $delta$ does; the two
new pieces of work are showing that the constructed sets — the
family, the constructors, the recursor — are members of their
generated types (law 1), and the $iota$ law — a third law that
joins the contract of @sec:defs here (law 3) — which this section
states and proves. This
section says what the checker checks for
a block and what it stores, how the model grows by a least fixed point
so that the three laws keep holding, and then the consistency
corollary, which is two lines.

== Inductive types: what is checked <sec:ind-checks>

An inductive block declares an _indexed family_ by its constructors:
one type, or one proposition, per choice of indices — _type-valued_
or _proposition-valued_, the two regimes of §2 for a whole family at
once. The fragment takes a block with one type former, neither mutual
nor nested; nesting is added in @sec:nested. The block is given by a
_specification_
(#src("whitepaper/Fragment/Spec.lean", 80, 103)[fragment],
#src("ConLeche/Kernel/Inductives/BlockParts.lean", 104, 122)[real checker]):

- a name $I$ and level parameters $arrow(p)$;
- a _parameter_ telescope $(x_1 : P_1) dots (x_k : P_k)$ and, under
  it, an _index_ telescope $(y_1 : J_1) dots (y_m : J_m)$; the
  parameters are the same for every constructor and every field, the
  indices vary;
- a result sort $Sort u$: the family has type
  $ forall arrow(x) : arrow(P) thin ann(never). thin forall arrow(y) : arrow(J) thin ann(never). thin Sort u; $
  a binder whose body is the family — a member of $Sort u$ — carries
  the datum
  #src("whitepaper/Fragment/Decl.lean", 145, 148)[$ann(PW) = zn(u)$],
  "a proposition exactly when $u$ is zero", and the generated types
  below use it;
- constructors $c_1, dots, c_n$, each with a list of _fields_ and,
  under the parameters and the fields, the index expressions
  $arrow(e)_j$ of its result $I thick arrow(x) thick arrow(e)_j$.

A field is one of two kinds
(#src("whitepaper/Fragment/Spec.lean", 28, 42)[fragment],
#src("ConLeche/Kernel/Inductives/Positivity.lean", 598, 608)[real checker]):
_ordinary_, with a domain that does not mention $I$; or _reflexive_,
with domain
$ forall arrow(z) : arrow(A) thin ann(PW). thin I thick arrow(x) thick arrow(e) $
— a function, under a telescope of binders $arrow(z)$ whose domains
do not mention $I$, into the family being defined at the block's own
parameters and some index expressions (the binders carry $ann(PW)$,
since the body is the family). The
telescope may be empty: then the domain is $I thick arrow(x) thick arrow(e)$,
a member of the family itself, and the field is simply _recursive_ —
the common case, and the name this document uses for it; one kind
covers both, since the generated terms and the model treat them
alike. This is the strictly positive shape, and the only one the
fragment admits: no
field's domain mentions $I$ anywhere else (in the fragment, the
specification's pieces — the domains $arrow(P)$, $arrow(J)$ and
$arrow(A)$, an ordinary field's domain and the index expressions —
are scope-checked in the environment _before_ $I$ is added, so none
of them mentions $I$; a reflexive field's $I$ is given by its kind,
not written in a term —
#src("whitepaper/Fragment/Decl.lean", 622, 636)[the scope of a field]).
One more condition of shape: nothing after a reflexive field may
depend on its value
(#src("whitepaper/Fragment/Decl.lean", 639, 644)[fragment],
#src("ConLeche/Kernel/Inductives/Positivity.lean", 1246, 1249)[real checker], as in the
official kernel) — the model will read a constructor's domains without knowing
the values of its reflexive fields.

#real(label: "In the real checker")[
  Simple, mutual and nested blocks are checked uniformly
  (#overview(5)); this section describes that check on a block of
  the fragment's shape. Its positivity check classifies each field's
  domain after weak head normal form, with $I$ at the block's
  parameters replaced by a variable standing for the family being
  defined; @sec:nested uses the same check
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1453, 1454)[positivity]).
]

Reflexive fields matter to the model. A tree type with a constructor
$sans("node") : (Nat -> sans("Tree")) -> sans("Tree")$ has nodes with
countably many children, so a node may have children of every finite
depth and the set of all trees is not the union of the "trees of
depth $k$": it is not reached by iterating the constructors $omega$
times, as $Nat$'s is, and a model must obtain the least fixed point
some other way (@sec:ind-model).

*The generated declarations.* From the specification the checker
generates the types of the former, the constructors and the
recursor, and the recursor's rules. The former's type is the one
displayed above; a constructor's type is
$ forall arrow(x) : arrow(P) thin ann(PW). thin forall arrow(f) : arrow(F) thin ann(PW). thin I thick arrow(x) thick arrow(e)_j $
with $ann(PW)$ on every binder, since every body ends in the family
(#src("whitepaper/Fragment/Decl.lean", 214, 221)[the two generators]).
The recursor eliminates into $Sort ell$, where the _elimination
level_ $ell$ is either a fresh level parameter — _large elimination_
— or $0$ — _small elimination_; the elimination rule below says
which. Every body of its type ends in the motive's value, a member
of $Sort ell$, so its binders carry
#src("whitepaper/Fragment/Decl.lean", 149, 153)[$ann(q) = zn(ell)$],
"a proposition exactly when $ell$ is zero".

#real(label: "In the real checker")[
  The input is a stream of raw declarations: the former, the
  constructors and the recursor as the exporting toolchain stated
  them. The checker recovers the specification from the former's and
  the constructors' types, and checks and stores those two as the
  stream declares them
  (#src("ConLeche/Kernel/Inductives/SumInstall.lean", 102, 103)[a constructor]).
  The recursor it _generates_, as the official kernel does; from the
  stream's recursor record it takes only the name, the level
  parameters and the type, which must be definitionally equal to the
  generated one, and the record's two layout counts, which must equal
  the generated ones
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 394, 407)[the comparison]).
  Which type the recursor eliminates, and how its motive and minor
  premises are laid out — the arguments named on $Nat$ in @ex:nat —
  an unverified pre-pass reads off that type; a wrong reading can
  only make the comparison fail
  (#src("ConLeche/Kernel/Inductives/ClassRead.lean", 24, 32)[the pre-pass]).
  The record's rules are never read; the generated recursor and its
  rules are what is stored
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 560, 563)[the recursor stage]).
]

The recursor is best shown on an example.

#example(name: [$Nat$])[
  The block $Nat$ has no parameters, no indices, sort $Sort 1$, and
  two constructors: $zero$ with no field and $succ$ with one recursive
  field — reflexive with the empty telescope. So $ann(PW) = zn(1) = ann(never)$, and the generated
  constructor types are $zero : Nat$ and
  $succ : forall (n : Nat) thin ann(never). thin Nat$. The recursor
  eliminates into $Sort ell$ for a fresh level parameter $ell$ —
  large elimination, see below — so
  $ann(q) = zn(ell) = ann(whenZero \{ell\})$, and its generated type is

  $
    NatRec.\{ell\} : & forall (C : forall (t : Nat) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (z : C thick zero) thin ann(q). \
    & forall (s : forall (n : Nat) thin ann(q). thin forall (h : C thick n) thin ann(q). thin C thick (succ thick n)) thin ann(q). \
    & forall (t : Nat) thin ann(q). thin C thick t
  $

  — each body ends in $C thick dots$, a member of $Sort ell$, a
  proposition exactly when $ell$ is instantiated to zero.
  $C$ is the _motive_; $z$ and $s$ are the _minor premises_,
  one per constructor, each taking the constructor's fields and, for
  every recursive field, an _inductive hypothesis_ $h$ — the motive at
  that field; $t$ is the _major premise_. The recursor has two rules,
  one per constructor: the major premise built by the constructor
  reduces to the minor premise applied to the fields and to the
  recursor's own value at each recursive field,

  $
    NatRec.\{ell\} thick C thick z thick s thick zero & red z \
    NatRec.\{ell\} thick C thick z thick s thick (succ thick n) & red s thick n thick (NatRec.\{ell\} thick C thick z thick s thick n).
  $

  What the checker stores as the second rule's right-hand side is
  the closed term (the binders' domains omitted)
  $ lambda C thin ann(q). thin lambda z thin ann(q). thin lambda s thin ann(q). thin lambda n thin ann(q). thin s thick n thick (NatRec.\{ell\} thick C thick z thick s thick n); $
  the $iota$ rule applies it to the recursor's arguments and the
  constructor's fields, and $beta$ does the rest.
] <ex:nat>

The general shape is the same with parameters, indices and
telescopes added. The motive takes the indices and a member of the
family:
$ C : forall arrow(y) : arrow(J) thin ann(never). thin forall (t : I thick arrow(x) thick arrow(y)) thin ann(never). thin Sort ell. $
A minor premise for $c_j$ takes the fields, then one inductive
hypothesis per reflexive field — at a field
$ f : forall arrow(z) : arrow(A) thin ann(PW). thin I thick arrow(x) thick arrow(e) $
the hypothesis is
$ forall arrow(z) : arrow(A) thin ann(q). thin C thick arrow(e) thick (f thick arrow(z)), $
which at the empty telescope is the $C thick n$ of @ex:nat — and
ends in
$ C thick arrow(e)_j thick (c_j thick arrow(x) thick arrow(f)). $
The recursor takes the parameters, the motive, the minors, the
indices and the major, and ends in $C thick arrow(y) thick t$.
(Generated:
#src("whitepaper/Fragment/Decl.lean", 223, 225)[the motive],
#src("whitepaper/Fragment/Decl.lean", 236, 247)[an inductive hypothesis],
#src("whitepaper/Fragment/Decl.lean", 261, 270)[a minor premise],
#src("whitepaper/Fragment/Decl.lean", 277, 282)[the recursor's type]
and #src("whitepaper/Fragment/Decl.lean", 319, 326)[a rule's right-hand side];
real checker: #src("ConLeche/Kernel/Inductives/GenRec.lean", 181, 188)[the type],
#src("ConLeche/Kernel/Inductives/GenRec.lean", 193, 212)[a rule].)

*The elimination rule.* Into which sorts may the motive land? For a
type-valued family — $Sort u$ with $u$ never zero — the recursor
eliminates into any $Sort ell$, $ell$ a fresh level parameter: large
elimination. For a proposition-valued family the rule is stricter.
In the model every proof is the point, so a recursor applied to a
proof cannot see which constructor built it or with which fields; a
recursor with a type-valued motive would have to return one value
for all of them. The official kernel allows
large elimination out of a proposition only under the _subsingleton
criterion_: the block has at most one constructor, and every field
of that constructor is either itself a proposition or occurs among
the constructor's result indices — so that a proof of $I thick arrow(x) thick arrow(e)$
determines every field: the propositional ones are all the same
proof, and the others can be read off the indices. Otherwise the
motive lands in $Prop$, $ell = 0$: _small elimination_. In the
fragment the criterion is
#src("whitepaper/Fragment/Decl.lean", 704, 711)[a condition per field]
plus #src("whitepaper/Fragment/Decl.lean", 757)[the constructor count], required of a large
eliminator on a family whose sort _may_ be zero
(#src("whitepaper/Fragment/Decl.lean", 700, 702)[never zero: $1 <= u$ at every valuation]).

#real(label: "In the real checker")[
  The criterion is split in two the same way, but the per-field half
  is asked less often: a count guard — a large eliminator is allowed
  when the sort is never zero, and otherwise only on a block with one
  type former, not nested, with at most one constructor
  (#src("ConLeche/Kernel/Inductives/BlockRec.lean", 82, 84)[the guard],
  #src("ConLeche/Kernel/Inductives/GenRec.lean", 571, 573)[applied]) —
  and the condition per field
  (#src("ConLeche/Kernel/Inductives/SumInstall.lean", 85, 99)[per field]),
  asked only of a family whose sort is _provably_ zero. So a family
  in $Sort u$ with one constructor may eliminate into any sort
  whatever its fields are, where the official kernel insists that
  each field be provably a proposition or an index: a deliberate
  superset, sound because the universe bound (the third check below)
  makes every field a proposition at any valuation that sends $u$ to
  zero.
]

Three of the checks listed below ask whether a sort is $Prop$, and
the checker answers each with the level oracle:

- a field's sort $v$ is a proposition: $v eq.dot 0$ (the
  subsingleton criterion);
- the result sort $u$ is never a proposition: $1 <= u$ (large
  elimination);
- a field's sort does not exceed the result sort — the _universe
  bound_: $v <= u$, unless $u eq.dot 0$, in which case
  #src("whitepaper/Fragment/Decl.lean", 693, 698)[there is no bound]
  (Lean's impredicativity of $Prop$).

In §2 the same question was answered for each binder by its
annotation; here it is asked of the oracle, because the result sort
is in hand. The two meet in the generated declarations: the
constructor types carry $ann(PW) = zn(u)$ at the binders whose body
is the family, the recursor's carry $ann(q) = zn(ell)$, so the model
of @sec:ind-model must handle the recursor at every regime these data
allow.

#example(name: [an indexed proposition with large elimination])[
  Let
  $ P : forall (n : Nat) thin ann(never). thin Prop $
  have one constructor
  $ mk : forall (n : Nat) thin ann(whenZero \{\}). thin P thick n $
  — a proposition-valued family, indexed by a number, with one ordinary
  field $n$ that is not a proposition but occurs in the result's
  index. The subsingleton criterion holds, so the recursor may
  eliminate into $Sort ell$:

  $
    PRec.\{ell\} : & forall (C : forall (n : Nat) thin ann(never). thin forall (t : P thick n) thin ann(never). thin Sort ell) thin ann(q). \
    & forall (h : forall (n : Nat) thin ann(q). thin C thick n thick (mk thick n)) thin ann(q). \
    & forall (n : Nat) thin ann(q). thin forall (t : P thick n) thin ann(q). thin C thick n thick t
  $

  with one rule,
  $ PRec.\{ell\} thick C thick h thick n thick (mk thick n') red h thick n'. $
  Note the two occurrences of the index: $n$ is the recursor's index
  argument, $n'$ the constructor's field. @sec:ind-model returns to
  this example.
] <ex:P>

*The checks.* A block is accepted when
(#src("whitepaper/Fragment/Decl.lean", 713, 758)[fragment],
#src("ConLeche/Kernel/Inductives/BlockTail.lean", 143, 148)[real checker]):
its names are distinct and fresh; the specification is in scope
(positivity included); the generated former's type has a type in the
current environment; each generated constructor's type has a type in
the environment holding the former, and every field's domain has a
sort $v$ that respects the universe bound and, where a large
eliminator asks it, the subsingleton criterion (the binders of a
reflexive field's own telescope respect the universe bound too); the constructor count respects
the elimination rule; and, in the environment holding the former and
the constructors, the generated recursor's type has a type, and so
has #src("whitepaper/Fragment/Decl.lean", 312, 317)[each rule's type] — the recursor's binder prefix
with the constructor's fields in place of the indices and the major.
Each "has a type" is an inference $tack T => S$ of §2, in the empty
context ($S$ is a sort for a generated type, but nothing checks that:
the model needs only the inference) — so the generated types are
checked like a definition's, and the $forall$ rule of @sec:rules
checks each generated annotation against the sort it computes for
the body.

#real(label: "In the real checker")[
  The same steps run in this order, and each generated rule is
  type-checked in the environment holding the rule-less recursor
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 427, 448)[a generated rule]).
]

*What is stored* is the former, the constructors
and the recursor, with its rules
(#src("whitepaper/Fragment/Decl.lean", 525, 566)[fragment]) — the
three kinds of constant that @sec:defs left to this section. An
_inductive type former_ carries its parameter and index counts and
its constructors' names; a _constructor_ its parameter and field
counts; a _recursor_ the sizes of its argument groups — parameters,
motive, minors, indices, then the major (@ex:nat shows them on
$Nat$) — and its reduction rules, one per constructor, each a closed
right-hand side over the recursor's level parameters
(#src("whitepaper/Fragment/Env.lean", 30, 53)[fragment],
#src("ConLeche/Kernel/Env.lean", 241, 254)[real checker]). The
rules' right-hand sides are generated and stored, not inferred: they
mention the recursor itself, and the official kernel infers no rule either.
That the rules are _sound_ is the model's business. It is the
contract's #src("whitepaper/Fragment/EnvModel.lean", 211, 218)[third law], which @def:model of @sec:defs now gains:
every rule of every stored recursor satisfies its $iota$ law
(@def:iota-law below). The next subsection proves it.

== Inductive types: the model <sec:ind-model>

The model of a block has three parts: the sets the family's fibres
denote, the sets the constructors denote, and the set the recursor
denotes. Each is stated against a small extension of §2's axioms.

*The axioms, extended.* Beyond the laws of @sec:lib the inductive
section uses
#src("whitepaper/Fragment/IndLib.lean", 136, 161)[four small laws]:
_separation stays in the universe_ — a separated part of a member of
a positive universe is a member of it; _transitivity_ of the positive
universes — a member of
a member is a member; _tuples_ $tuple(x_1, dots, x_k)$, injective and
universe-closed; and _tags_ $tag(j, x)$, a set with a number
attached, injective, universe-closed and never the point — and one
law about size, _inductive closure_, stated below where it is
needed. Notably absent is any law about least fixed points.

*Least fixed points cost nothing.* The family of a block is the least
fixed point of an operator: "a member is a constructor applied to
fields that are members". In the fragment this is not a set
construction at all. The operator acts on _predicates_, and the least
fixed point of a monotone operator $Phi$ on predicates is
#src("whitepaper/Fragment/IndLib.lean", 231, 234)[a definition]:
$lfp(Phi)(a)$ holds when every predicate closed under $Phi$ holds at
$a$. That it is closed, that it is a fixed point and that it
supports induction are #src("whitepaper/Fragment/IndLib.lean", 240, 259)[ten lines of proof] — the
definition quantifies over all predicates, which the ambient logic's
impredicative $Prop$ permits. Separation then turns a fibre of the
predicate into a set. One thing this does _not_ give for free: the
fibre must be a _member_ of $cal(U)_(phi(u))$, since the former's
type ends in $Sort u$, and a separated part of $cal(U)_(phi(u))$
itself is a member of the next universe, not of this one. To land in
$cal(U)_(phi(u))$ the fibre has to be separated from some member of
$cal(U)_(phi(u))$ that already contains every tagged tuple a
constructor can build — for reflexive fields as for the others. That
bounding set is the one thing the argument genuinely needs from set
theory, and the fragment states it as one law, #src("whitepaper/Fragment/IndLib.lean", 162, 171)[_inductive closure_]:
for any list of #src("whitepaper/Fragment/IndLib.lean", 98, 116)[constructor telescopes] there is a family of members of
the universe closed under every #src("whitepaper/Fragment/IndLib.lean", 122, 130)[_bounded instance_] of every
constructor — fields whose every domain is a member of the universe.
The family the block defines is #src("whitepaper/Fragment/IndSem.lean", 427, 435)[separated from that member], so
#src("whitepaper/Fragment/IndSem.lean", 564, 566)[its fibres are members], and
#src("whitepaper/Fragment/IndSem.lean", 901, 904)[every constructor value lands in it] because the checker's universe
bound on the fields makes every instance it admits a bounded one.

#real[
  That law is proved from the Grothendieck universes. The least
  fixed point is built inside the set theory —
  #src("ConLeche/SetTheory/Derive/LfpTuple.lean", 67, 75)[the intersection of the closed families, separated from a chosen one] —
  so a family in the universe that is closed under the operator must
  exist first. It comes from _accessibility_: an operator is
  accessible when each element it produces depends on only a bounded
  set of elements of its input, for one bound fixed in the universe.
  Such an operator has a closed family in the universe
  (#src("ConLeche/SetModel/Access.lean", 239, 243)[the theorem]): not
  by iterating it $omega$ times, which reflexive fields defeat, but
  along well-founded trees of arbitrary branching, the union over all
  trees kept small by coding a tree as its set of paths through the
  bound. The positivity check's run shows the block's operator
  accessible, for recursive and reflexive fields alike
  (#src("ConLeche/Model/Inductives/BlockAccRunCont.lean", 315, 320)[from the run]),
  and that is
  #src("ConLeche/Model/Inductives/BlockDatum.lean", 925, 935)[the closed family the block's fixed point is separated from].
  Everything else about the least fixed point — the fixed-point
  equation, induction, and the fact that the recursor's graph is a
  least fixed point too — is available for free one level up, as in
  the fragment.
]

*The family and the constructors.* Fix a block as in
@sec:ind-checks, a valuation $phi$, and values $arrow(X)$ for the
parameters. The operator $Phi$ acts on predicates over pairs (index
values $arrow(Y)$, a set $x$): $Phi(Z)(arrow(Y), x)$ holds when for
some constructor $c_j$ and some field values $arrow(F)$ that fit
$c_j$'s field telescope at $arrow(X)$ — read with $I$ standing for
the family that $Z$ describes — $x = tag(j, tuple(arrow(F)))$ and
$arrow(Y)$ are the values of $c_j$'s index expressions at $arrow(F)$.
"Fit" is the semantic reading of a telescope: each value is a member
of the domain it meets, the later domains read under the earlier
values
(#src("whitepaper/Fragment/EnvModel.lean", 60, 67)[fragment]). A
reflexive field's domain is a function space into fibres of $Z$ —
at the empty telescope, a fibre of $Z$ itself — and the function
space is monotone in its fibres
(#src("whitepaper/Fragment/IndLib.lean", 204, 221)[fragment]), so
$Phi$ is monotone and has a least fixed point
(#src("whitepaper/Fragment/IndSem.lean", 353, 356)[the operator],
#src("whitepaper/Fragment/IndSem.lean", 474, 475)[its least fixed point]). Then, in the regime
where $ann(PW)$ does not hold at $phi$ — the family is type-valued —

$
  lden I rden dot.op arrow(X) dot.op arrow(Y) = { x in W(arrow(Y)) mid(|) lfp(Phi)(arrow(Y), x) },
$

with $W$ the bounding family of the closure law, and the constructor
$c_j$ denotes the function that takes the
parameters and the fields and returns $tag(j, tuple(arrow(F)))$. In
the regime where $ann(PW)$ holds — the family is proposition-valued
— the fibre is the truth value $tv(exists x. thin lfp(Phi)(arrow(Y), x))$,
"some constructor reaches these indices", and every constructor
denotes the point.
(Fragment: #src("whitepaper/Fragment/IndSem.lean", 84, 88)[the fibre in each regime],
#src("whitepaper/Fragment/IndSem.lean", 480, 482)[a constructor's value],
#src("whitepaper/Fragment/IndSem.lean", 1352, 1356)[the former's set],
#src("whitepaper/Fragment/IndSem.lean", 1362, 1367)[a constructor's set].)

#real[
  The operator is the same one, read off the stored constructor
  types with the positivity check's variable — a _hole_ — standing
  for the family
  (#src("ConLeche/Model/Annot/LfpHoleOp.lean", 121, 123)[the hole operator]),
  monotone by the positivity check's run
  (#src("ConLeche/Model/Inductives/BlockPosRunCont.lean", 40, 44)[from the run]).
  What the model records of an installed block, and all its recursor
  model later reads, is one clause: the operator is monotone and has
  a closed family
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 261, 265)[the operator]),
  its fibres are the tagged tuples of fitting fields
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 266, 271)[the fibres]),
  and the former at parameters and indices denotes the least fixed
  point's fibre there
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 279, 284)[the former]).
  Its constructors are
  #src("ConLeche/SetModel/TaggedSum.lean", 65)[tagged pairs] of
  #src("ConLeche/SetModel/TupleTower.lean", 87)[nested pairs], the
  two regimes in
  #src("ConLeche/SetModel/TaggedSum.lean", 61, 62)[one carrier].
]

This is where the two regimes of §2 are decided for a whole family
at once, by the one datum $ann(PW)$ stored on the constructors'
binders. A member of a fibre in the first regime is a tagged tuple
and carries its constructor and its fields; a member in the second is
the point and carries nothing. The difference will matter in a moment.

*The recursor.* Fix values $C$ for the motive and $arrow(S)$ for the
minor premises. The recursor's value on a member of the family is
determined by the rules: on $tag(j, tuple(arrow(F)))$ it must be
$S_j$ applied to $arrow(F)$ and to the inductive hypotheses — at
each reflexive field $f$ the function sending $arrow(z)$ to the
recursor's own value at $f dot.op arrow(z)$, which at the empty
telescope is just the recursor's value at $f$. That this equation
has exactly one solution is
the _recursion theorem_, and in the fragment it is proved by the
same device as the family: the recursor's _graph_ — the relation
"the value at $(arrow(Y), x)$ is $v$" — is
#src("whitepaper/Fragment/IndSem.lean", 1006, 1007)[the least fixed point] of
the operator that reads the equation as a step; it is
#src("whitepaper/Fragment/IndSem.lean", 1047, 1050)[single-valued] by
induction over the graph, using that tags and tuples are injective,
and #src("whitepaper/Fragment/IndSem.lean", 1132, 1136)[total] by induction over the
family. When the family is proposition-valued and the motive is
not, the major is the point and carries no fields; the recursor's
value at $(arrow(Y), pt)$ is the value the equation assigns at a chosen
#src("whitepaper/Fragment/IndSem.lean", 928, 940)[_witness_] of the fibre — any $x$ with
$lfp(Phi)(arrow(Y), x)$ — and the subsingleton criterion is what makes
the choice irrelevant: #src("whitepaper/Fragment/Uniq.lean", 60, 65)[any two witnesses are the same tagged tuple], as
@thm:iota's proof shows. The recursor
denotes #src("whitepaper/Fragment/IndSem.lean", 1383, 1387)[the graph of the resulting function], curried over the
parameters, the motive, the minors, the indices and the major — a
#src("whitepaper/Fragment/InstallInd.lean", 753, 754)[member of its generated type], which is law 1 for the recursor.
When the elimination level $ell$ is zero the recursor's type is a
proposition, the recursor and every minor premise denote the point,
and there is nothing to construct.

#real[
  The recursor is built the same way — the proof calls this the
  _graph route_ — and one construction serves every sort. Over the
  set of majors, the graph is
  #src("ConLeche/SetModel/GraphRec.lean", 101, 103)[the least relation]
  closed under the rules, each read over the ways a major _decodes_ —
  is the value of a constructor applied to some fields; a decoding is
  that constructor and those fields; it has
  #src("ConLeche/SetModel/GraphRec.lean", 227, 229)[exactly one value at every major]
  by the family's own induction, and the equation at any decoding is
  #src("ConLeche/SetModel/GraphRec.lean", 266, 270)[the $iota$ law].
  The one fact about sorts it asks is a premise: at every major,
  #src("ConLeche/SetModel/GraphRec.lean", 186, 188)[two decodings are equal, or the motive's value there has at most one member]
  — the elimination rule of @sec:ind-checks, read three ways
  (#src("ConLeche/Model/Inductives/ClassGenUniq.lean", 13, 19)[the three cases],
  #src("ConLeche/Model/Inductives/ClassGenUniq.lean", 57)[the theorem]):
  at $ell = 0$ the motive's values are truth values; at a type-valued
  family, tags and tuples are injective; at a proposition-valued
  family with a large eliminator, the subsingleton criterion makes
  the decoding a function of the index — the fragment's witness
  argument, as one premise.
]

*What the $iota$ rule knows.* Before the $iota$ law, look at what the
rule's premises say and what the model has to supply. The rule fires
on $r.\{arrow(ell)\} thick arrow(a) thick t$ where $r$ is a stored
recursor, $arrow(a)$ are its parameters, motive, minors and indices,
and the major $t$ reduces to a constructor application
$c_j.\{arrow(ell)'\} thick arrow(a)' thick arrow(f)$ for which $r$ has
a rule with right-hand side $R_j$; the reduct is
$R_j[arrow(p) := arrow(ell)]$ applied to the parameters, motive and
minors from $arrow(a)$ and to the fields $arrow(f)$
(#src("whitepaper/Fragment/Rules.lean", 84, 159)[fragment],
#src("ConLeche/Rules/Rel.lean", 178, 217)[real checker]). Its
premises, besides the lookups, are two _telescope certificates_ and
three _comparisons_:

- the recursor's spine, with the reduced major in the major's place,
  is checked against the recursor's stored type: each argument's type
  is inferred and compared with the domain it meets, the domains
  instantiated along the spine; the constructor's spine is checked
  against the constructor's stored type the same way;
- the constructor's levels $arrow(ell)'$ are oracle-equal to the last
  levels of $arrow(ell)$ (a large eliminator carries one extra level
  in front); the constructor's parameters $arrow(a)'$ are definitionally
  equal to the recursor's; and the index expressions of the
  constructor's result type at $arrow(a)' thick arrow(f)$ — the
  _residual_ of its telescope — are definitionally equal to the
  recursor's index arguments.

#real(label: "In the real checker")[
  The rule carries the parameter comparison only for rules whose law
  reads it; a block's rules are installed
  #src("ConLeche/Kernel/Env.lean", 265, 273)[without it], because
  their law holds at any pair of fitting parameter spines (the
  fragment keeps the comparison and uses it). The two certificates
  are walks of their own, relations over lists (@sec:left-out); the
  fragment folds them into the rule.
]

By @thm:sound each
certificate becomes a _fit_ of values to the stored telescope
(#src("whitepaper/Fragment/Sound.lean", 77, 84)[fragment]), and each
comparison an equality of sets
(#src("whitepaper/Fragment/Sound.lean", 201, 206)[the $iota$ case]).
So the $iota$ law is stated on values, with the fits and the
equalities as premises
(#src("whitepaper/Fragment/EnvModel.lean", 102, 161)[fragment],
#src("ConLeche/Model/Annot/Laws.lean", 366, 369)[real proof]):

#definition(name: [the $iota$ law of a rule])[
  Let $r$ be a stored recursor and $R_j$ the right-hand side of its
  rule for the constructor $c_j$. For every valuation, all levels
  $arrow(ell)$, $arrow(ell)'$ of the right lengths, all values
  $arrow(A)$ for the arguments before the major and $arrow(F)'$ for
  the constructor's parameters and fields: if $arrow(A)$ followed by
  $lden c_j.\{arrow(ell)'\} rden dot.op arrow(F)'$ fit the recursor's
  type at $arrow(ell)$, $arrow(F)'$ fit the constructor's type at
  $arrow(ell)'$, the levels $arrow(ell)'$ evaluate as the last of
  $arrow(ell)$, the parameters among $arrow(F)'$ _are_ those among
  $arrow(A)$, and the constructor's index expressions read under
  $arrow(F)'$ _are_ the index values among $arrow(A)$ — then
  $ lden r.\{arrow(ell)\} rden dot.op arrow(A) dot.op (lden c_j.\{arrow(ell)'\} rden dot.op arrow(F)') = lden R_j [arrow(p) := arrow(ell)] rden dot.op (arrow(A) "before the indices") dot.op (arrow(F)' "after the parameters"), $
  and the right-hand side $R_j$ is well-denoted with a well-formed
  application chain along those values.
] <def:iota-law>

The second conjunct is what makes the reduct well-denoted, as the
first claim of @thm:sound demands; the first is the equation. The
$iota$ case of @thm:sound is then a translation: certificates to
fits, comparisons to equalities, the reduced major's value for the
argument's, and the law
(#src("whitepaper/Fragment/Sound.lean", 207, 245)[fragment],
#src("ConLeche/Model/Rules/IotaSound.lean", 69)[real proof]).

#theorem(name: [the $iota$ law holds])[
  Every rule of the recursor of an accepted block satisfies its
  $iota$ law in the model of @sec:ind-model.
  (#src("whitepaper/Fragment/InstallIota.lean", 691, 697)[fragment], with
  #src("whitepaper/Fragment/IndSem.lean", 1201, 1206)[the equation on the semantic recursor]\; real proof:
  #src("ConLeche/Model/Inductives/BlockRecLaw.lean", 448, 456)[the graph's equation, lifted to the law of @def:iota-law].)
] <thm:iota>

#proof[
  _The type-valued family_ ($ann(PW)$ does not hold). The recursor's fit
  puts the major's value $lden c_j rden dot.op arrow(F)'$ in the family
  at the _recursor's_ parameters and indices, the values among
  $arrow(A)$. By the constructor's fit that value computes to
  $tag(j, tuple(arrow(F)))$, $arrow(F)$ the fields among $arrow(F)'$;
  and here is the point of
  the least fixed point: a member of the fibre is a step from
  members (#src("whitepaper/Fragment/IndLib.lean", 248, 251)[the fixed-point equation, read backwards]), so it is
  $tag(j', tuple(arrow(F)''))$ for some constructor $j'$ and fields
  $arrow(F)''$ fitting $c_(j')$'s field telescope _at the recursor's
  parameters_, with the recursor's indices as the values of
  $c_(j')$'s index expressions at $arrow(F)''$. Tags and tuples are
  injective, so $j' = j$ and $arrow(F)'' = arrow(F)$. This
  _inversion_ is everything the right-hand side needs: it puts each
  field in its domain at the recursor's own parameters, which is
  what the $beta$ steps inside $R_j$ require (@lem:beta-cert, with
  the membership supplied), and the recursion theorem's equation at
  $tag(j, tuple(arrow(F)))$ is the rule's equation. None of the three
  comparisons is needed: the fields, their parameters and their
  indices are all read off the tuple.

  _The proposition-valued family_ ($ann(PW)$ holds). Now the major's
  value is the point, and the recursor's fit says only that the fibre
  at the recursor's indices is inhabited: the point carries no
  constructor, no fields, no parameters and no indices. Inversion
  still applies — some constructor reaches those indices with some
  fields $arrow(F)''$ — but nothing connects $arrow(F)''$ to the
  fields $arrow(F)'$ the right-hand side is applied to. This is
  where the comparisons come in. When the elimination level is zero
  both sides of the equation are the point and there is nothing to
  prove. When it is not, the block passed the subsingleton
  criterion: one constructor, so $j' = j$; and each field is a
  proposition or occurs among the constructor's result indices. A
  propositional field is the point on both sides — provided both
  sides read its domain in the same regime, which is what the level
  comparison secures: the constructor's levels evaluate as the
  recursor's, so the block's level parameters have one valuation on
  both sides. An index field's value the index comparison identifies
  with the recursor's index argument, on both sides. So
  $arrow(F)'' = arrow(F)$ after all, and the recursion theorem's
  equation is again the rule's. The parameter comparison played no
  part: the reduct takes its parameters from the recursor's side and
  only its fields from the major, and both kinds of field were fixed
  without it. The fragment's law assumes it all the same, and its
  proof uses it to move the constructor's fit to the recursor's
  parameters.
]

*Why the index comparison is load-bearing.* Return to @ex:P and take
the spine $C, h, 7, mk thick 5$. Every $P thick n$ is inhabited, by
$mk thick n$, so $lden P thick 7 rden = {pt}$, and the recursor's fit
asks only that $lden mk thick 5 rden = pt$ lie in it — which it
does. The fit holds equally for $mk thick 7$. Without the index
comparison the $iota$ law would therefore have to give both
$ lden PRec rden dot.op C dot.op h dot.op 7 dot.op pt = h dot.op 5 quad "and" quad lden PRec rden dot.op C dot.op h dot.op 7 dot.op pt = h dot.op 7, $
so $h dot.op 5 = h dot.op 7$ for every $h$: false. The recursor's set is a
function of its arguments and has one value at index $7$. The
checker's certificate did compare the inferred type $P thick 5$ with
the domain $P thick 7$ and would have refused; but on values that
comparison is ${pt} = {pt}$ and says nothing about $5$ and $7$. The
index comparison, $5 equiv 7$, is what the model can use. In the
type-valued regime the comparison is redundant — the tagged tuple
carries its indices — and the official kernel never makes it: at an
$iota$ step it compares nothing and relies on the term being
well-typed, which its typing judgement guarantees. This proof has no
typing judgement, and on values a definitional equality between two
propositions is an equality of truth values; so the comparison has
to be a premise of the rule.

== Consistency <sec:consistency>

An environment is #src("whitepaper/Fragment/Consistency.lean", 36, 47)[_accepted_] when it is built from the empty
environment by the two steps of §3 and §4: a definition that
passes its checks, or an inductive block that passes its checks and
is installed.
An accepted environment is closed — #src("whitepaper/Fragment/Consistency.lean", 50, 55)[every stored term mentions only stored constants] — which is what
@thm:install-def, the construction of @sec:ind-model and
@thm:install-nest assumed of the environment they extend.

#theorem(name: "Every accepted environment has a model")[
  For every model of the extended theory, every accepted environment
  has a model in it
  (#src("whitepaper/Fragment/Consistency.lean", 57, 69)[fragment]\; real proof:
  #src("ConLeche/MainTheorem.lean", 96, 99)[the main theorem]).
] <thm:accepted-model>

#proof[
  By induction on the acceptance. The empty environment has a model;
  a definition step is @thm:install-def; a block step is the
  construction of @sec:ind-model, #src("whitepaper/Fragment/Install.lean", 124, 129)[assembled]: law 1 is its
  membership claims, law 2 has no new instance, and law 3 is
  @thm:iota — for a nested block, @thm:install-nest.
]

#real[
  The block step is one theorem,
  #src("ConLeche/Model/Inductives/DeclBlockStep.lean", 72, 77)[the install of a block],
  read off the checker's run stage by stage.
]

#corollary(name: "No proof of an empty proposition")[
  Let $I$ be an inductive type with no constructors, no parameters,
  no indices and no level parameters, installed in an accepted
  environment. Then no closed term $e$ has $tack e => I$; in
  particular no stored constant has type $I$
  (#src("whitepaper/Fragment/Consistency.lean", 88, 97)[fragment], and
  #src("whitepaper/Fragment/Consistency.lean", 136, 140)[at the block `inductive False : Prop`]\;
  #src("ConLeche/Model/Fold.lean", 276, 283)[real proof]).
] <cor:consistency>

#proof[
  Take a model of the environment, by @thm:accepted-model, and read
  law 1 for the block's recursor at the valuation that sends every
  level to $0$. Its type is then
  $ forall (C : forall (t : I) thin ann(never). thin Prop) thin ann(q). thin forall (t : I) thin ann(q). thin C thick t $
  with $ann(q)$ holding — the elimination principle of an empty type,
  read as a proposition — and law 1 says that the recursor's set is a
  member of what it denotes: a truth value, which is therefore
  inhabited, so for every motive $C$ and every $t in lden I rden$ the
  fibre $C dot.op t$ is ${pt}$, in particular inhabited. Take $C$ constantly the empty truth
  value. If $e$ had $tack e => I$, @cor:closed would put $lden e rden$
  into $lden I rden$, and the empty truth value would be inhabited.
  Nothing about how the model was built is used — only that one
  exists; the construction of @sec:ind-model does also make
  $lden I rden$ empty outright, as the least fixed point of an
  operator with no step, but the corollary does not need to know.
]

#real[
  The real theorem differs in two ways. Its checker does not read
  `False` from the stream but installs it from a built-in copy and
  rejects a stream that declares it differently — likewise `Eq`,
  `Nat` and a few others (@sec:left-out) — so the main theorem can
  name `False` and say that it denotes the empty set and `Eq` set
  equality, with no hypothesis about the stream (#overview(1)); and
  its acceptance is the run of a program,
  #src("ConLeche/Model/Fold.lean", 198, 200)[the declaration fold],
  rather than a relation, so a bridge theorem turns each accepting
  run into the derivations §3 and §4 consume (@sec:left-out). The
  argument in between is the one above.
]
