#import "../lib.typ": *

// Notation local to this file, matching §2 and §3.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let always = $sans("always")$
#let whenZero = $sans("zero")$
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
corollary.

== Inductive types: what is checked <sec:ind-checks>

An inductive block declares an _indexed family_ by its constructors:
one type, or one proposition, per choice of indices — _type-valued_
or _proposition-valued_, the two regimes of §2 for a whole family at
once. The fragment takes a block with one type former, neither mutual
nor nested; nesting is added in @sec:nested. The block is given by a
#src("whitepaper/Fragment/Spec.lean", 80, 103)[_specification_]
(#src("ConLeche/Kernel/Inductives/BlockParts.lean", 104, 122)[as in con-leche]):

- a name $I$ and level parameters $arrow(p)$;
- a _parameter_ telescope $(x_1 : P_1) dots (x_k : P_k)$ and, under
  it, an _index_ telescope $(y_1 : J_1) dots (y_m : J_m)$; the
  parameters are the same for every constructor and every field, the
  indices vary;
- a result sort $Sort u$: the family has type
  $ forall arrow(x) : arrow(P) thin ann(never). thin forall arrow(y) : arrow(J) thin ann(never). thin Sort u; $
- constructors $c_1, dots, c_n$, each with a list of _fields_ and,
  under the parameters and the fields, the index expressions
  $arrow(e)_j$ of its result $I thick arrow(x) thick arrow(e)_j$.

A field is one of #src("whitepaper/Fragment/Spec.lean", 28, 42)[two kinds]
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 598, 608)[as in con-leche]):

- _ordinary_: its domain does not mention $I$;
- _reflexive_: its domain is
  $ forall arrow(z) : arrow(A) thin ann(PW). thin I thick arrow(x) thick arrow(e), $
  a function, under a telescope of binders $arrow(z)$ whose domains
  do not mention $I$, into the family being defined at the block's own
  parameters and some index expressions. The telescope may be empty;
  then the domain is $I thick arrow(x) thick arrow(e)$, a member of
  the family itself, and the field is simply _recursive_.

Two conditions of shape come with the kinds. No field's domain
mentions $I$ anywhere else — this is
#src("whitepaper/Fragment/Decl.lean", 622, 636)[strict positivity].
And nothing after a reflexive field
#src("whitepaper/Fragment/Decl.lean", 639, 644)[may depend on its value]
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 1246, 1249)[as in con-leche] and the
official kernel): the model will read a constructor's domains without
knowing the values of its reflexive fields.

Two remarks on notation. "Recursive" is the common case, and the name
this document uses for it; one kind covers both, since the generated
terms and the model treat them alike. And here, as in every generated
type below, a binder whose body is the family — a member of $Sort u$
— carries the datum
#src("whitepaper/Fragment/Decl.lean", 145, 148)[$ann(PW) = zn(u)$],
"a proposition exactly when $u$ is zero".

#real[
  Simple, mutual and nested blocks are checked uniformly
  (#overview(5)); this section describes that check on a block of
  the fragment's shape. Its positivity check classifies each field's
  domain after weak head normal form, with $I$ at the block's
  parameters replaced by a variable standing for the family being
  defined; @sec:nested uses the same check
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1453, 1454)[positivity]).
]

Genuinely reflexive fields — a non-empty telescope — matter to the model. A tree type with a constructor
$sans("node") : (Nat -> sans("Tree")) -> sans("Tree")$ has nodes with
countably many children, so a node may have children of every finite
depth and the set of all trees is not the union of the "trees of
depth $k$": it is not reached by iterating the constructors $omega$
times, as $Nat$'s is, and a model must obtain the least fixed point
some other way (@sec:ind-model).

*The generated declarations.* From the specification the checker
generates the types of the type former, the constructors and the
recursor, and the recursor's rules. The type former's type is the one
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

#real[
  The input is a stream of raw declarations: the type former, the
  constructors and the recursor as the exporting toolchain stated
  them. The checker recovers the specification from the type former's and
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

#real[
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

#example(name: [an indexed proposition with large elimination])[
  Let
  $ P : forall (n : Nat) thin ann(never). thin Prop $
  have one constructor
  $ mk : forall (n : Nat) thin ann(always). thin P thick n $
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

*The checks.* A block #src("whitepaper/Fragment/Decl.lean", 713, 758)[is accepted] when
(#src("ConLeche/Kernel/Inductives/BlockTail.lean", 143, 148)[as in con-leche]):

- its names are distinct and fresh;
- the specification is in scope, positivity included;
- the generated type former's type has a type in the current environment;
- each generated constructor's type has a type in the environment
  holding the type former, and every field's domain has a sort $v$ that
  respects the universe bound and, where a large eliminator asks it,
  the subsingleton criterion (the binders of a reflexive field's own
  telescope respect the universe bound too);
- the constructor count respects the elimination rule;
- in the environment holding the type former and the constructors, the
  generated recursor's type has a type, and so has
  #src("whitepaper/Fragment/Decl.lean", 312, 317)[each rule's type] — the
  recursor's binder prefix with the constructor's fields in place of
  the indices and the major.

Each "has a type" is an inference $tack T => S$ of §2, in the empty
context ($S$ is a sort for a generated type, but nothing checks that:
the model needs only the inference) — so the generated types are
checked like a definition's, and the $forall$ rule of @sec:rules
checks each generated annotation against the sort it computes for
the body.

#real[
  The same steps run in this order, and each generated rule is
  type-checked in the environment holding the rule-less recursor
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 427, 448)[a generated rule]).
]

*What is stored.* The block #src("whitepaper/Fragment/Decl.lean", 525, 566)[adds three kinds of constant] to the
environment, the ones @sec:defs left to this section
(#src("whitepaper/Fragment/Env.lean", 56, 72)[the kinds],
#src("ConLeche/Kernel/Env.lean", 241, 254)[as in con-leche]). Written
with the notation of @sec:defs, a stored declaration is one of

- $(c.\{arrow(p)\} : T := v)$ — a definition (@sec:defs);
- $(I.\{arrow(p)\} : T)^sans("type") [k, m; c_1, dots, c_n]$ — a type
  former: $k$ parameters, $m$ indices, constructors $c_1, dots, c_n$;
- $(c_j.\{arrow(p)\} : T)^sans("ctor") [I; k, f]$ — a constructor of
  $I$: $k$ parameters, $f$ fields;
- $(r.\{arrow(ell)\} : T)^sans("rec") [k, 1, n, m; R_1, dots, R_n]$ — a
  recursor: $k$ parameters, one motive, $n$ minors, $m$ indices, the
  major; rules $R_1, dots, R_n$.

The counts are the sizes of the argument groups (@ex:nat shows them
on $Nat$). A rule $R_j$ is a closed right-hand side over the
recursor's level parameters, one per constructor; the rules are
generated and stored, not inferred: they mention the recursor itself,
and the official kernel infers no rule either.

== Inductive types: the model <sec:ind-model>

The model of a block has three parts: the set the type former
denotes at each choice of indices, the sets the constructors denote,
and the set the recursor denotes. With the recursor, the contract of @sec:defs gains its
#src("whitepaper/Fragment/EnvModel.lean", 211, 218)[third law]:
every rule of every stored recursor satisfies its $iota$ law
(@def:iota-law), which this subsection proves. All of it is stated
against an extension of §2's axioms.

*The axioms, extended.* Beyond the laws of @sec:lib this section
assumes that the positive universes $cal(U)_n$, $n >= 1$,
are #src("whitepaper/Fragment/Univ.lean", 43, 88)[_Grothendieck universes_], and
that there are #src("whitepaper/Fragment/IndLib.lean", 46, 63)[tagged tuples]:

+ #src("whitepaper/Fragment/Univ.lean", 49, 64)[_Pairing, union, power set, replacement_],
  on all sets: for sets $a, b, x, A$ and a function $F$ (of the
  meta-theory) from sets to sets, the sets ${a, b}$, $union.big x$, $cal(P)(x)$ and $F[A]$ with
  $ z in {a, b} & <==> z = a or z = b,
    & quad z in union.big x & <==> z in y "for some" y in x, \
    z in cal(P)(x) & <==> z subset.eq x,
    & quad z in F[A] & <==> z = F(w) "for some" w in A. $
+ #src("whitepaper/Fragment/Univ.lean", 65, 72)[_The numerals and $omega$_]:
  a set $sans("num")(k)$ for every natural number $k$, distinct for
  distinct numbers, and the set $omega$ of all numerals.
+ #src("whitepaper/Fragment/Univ.lean", 73, 88)[_Grothendieck universes_]:
  for $n >= 1$, $cal(U)_n$ is transitive — if $A in cal(U)_n$ and
  $x in A$ then $x in cal(U)_n$ — closed under the four operations,
  $ {a, b}, thick union.big x, thick cal(P)(x) & in cal(U)_n quad & "for" a, b, x in cal(U)_n, \
    F[A] & in cal(U)_n quad & "for" A in cal(U)_n "with" F(a) in cal(U)_n "for every" a in A, $
  and contains $omega$.
+ #src("whitepaper/Fragment/IndLib.lean", 49, 63)[_Tagged tuples_]
  $tag(j, x_1, dots, x_k)$, a list of sets with a number $j$
  attached: injective — equal tagged tuples have equal numbers and
  equal components — in $cal(U)_n$ when every component is, and never
  $pt$.

Nothing else is assumed: no law about least fixed points, and none
about the size of an inductive family — both are theorems below.
What the construction uses of the universes follows at once: a
subset of a member is a member (it is in the power set, and the
universe is transitive), so
#src("whitepaper/Fragment/Univ.lean", 127, 130)[a separation from a member is a member]\;
#src("whitepaper/Fragment/Univ.lean", 182, 199)[the union $union.big_(a in A) F(a)$ of a family indexed by a member]
is a member, by replacement then union; and so is
#src("whitepaper/Fragment/Univ.lean", 217, 236)[the countable union $union.big_k F(k)$],
the union over $omega$ —
#src("whitepaper/Fragment/Univ.lean", 29, 35)[the one use of $omega$, and a genuine one]:
the hereditarily finite sets satisfy every other law in this list.

#real[
  The set theory is one class: ZF without infinity, plus a chain of
  universes each of which is a Grothendieck universe stated as the
  matrix of Tarski's Axiom A with transitivity
  (#src("ConLeche/SetTheory/Core.lean", 89, 93)[the universe property],
  #src("ConLeche/SetTheory/Core.lean", 95, 100)[the class]). The
  closure laws of the list, and infinity, are derived from it; the
  fragment takes the derived laws as its interface, as it does for
  the rest of §2's laws.
]

*The operator.* Fix a block as in @sec:ind-checks, a valuation
$phi$, and values $arrow(X)$ for the parameters. A _family_ is a
function $W$ from index values $arrow(Y)$ to sets, its _fibres_. The
block's operator $Phi$ sends a family to a family: its fibre at
$arrow(Y)$ is the set of _constructor values_ whose fields fit a
constructor relative to $W$ and whose index expressions read as
$arrow(Y)$,
$ Phi(W)(arrow(Y)) = { tag(j, arrow(F)) mid(|) arrow(F) "fit the fields of" c_j "relative to" W, "and" arrow(Y) = arrow(e)_j (arrow(F)) }, $
where $arrow(e)_j$ are the index expressions of $c_j$'s result
$I thick arrow(x) thick arrow(e)_j$ (@sec:ind-checks), and
$arrow(e)_j (arrow(F))$ their denotations with the parameters at
$arrow(X)$ and the fields at $arrow(F)$. Values $arrow(F)$ _fit_ a constructor's fields relative to $W$ when
each is a member of its field's set at the earlier values: the set of
an ordinary field is its domain's denotation, read without $W$; the
set of a reflexive field
$f : forall arrow(z) : arrow(A). thin I thick arrow(x) thick arrow(e)$
is the product over its telescope into fibres of $W$, at the field's
own index expressions $arrow(e)$,
$ Pi(arrow(z) in arrow(A), thick W(arrow(e)(arrow(z)))), $
the fibre $W(arrow(e))$ itself when the telescope is empty
(#src("whitepaper/Fragment/IndSem.lean", 274, 294)[a field's set],
#src("whitepaper/Fragment/IndSem.lean", 306, 311)[a fitting list]).
The fibre is a set, built by replacement, union and separation from
the fields' sets
(#src("whitepaper/Fragment/IndSem.lean", 484, 533)[the construction],
#src("whitepaper/Fragment/IndSem.lean", 544, 548)[its members are as displayed]).
When the family is proposition-valued ($ann(PW)$ holds at $phi$) a
constructor value #src("whitepaper/Fragment/IndCommon.lean", 225, 227)[is the point] instead of the tagged tuple,
so every fibre of $Phi(W)$ is a subset of ${pt}$: the truth value
"some constructor reaches these indices".

_Monotone by positivity._ If $W subset.eq W'$ fibrewise then
$Phi(W) subset.eq Phi(W')$ fibrewise, field kind by field kind: an
ordinary field's set does not read the family, and a reflexive
field's set is a product into fibres of the family, which
#src("whitepaper/Fragment/IndLib.lean", 81, 86)[grows with them]
by §2's laws; so a list fitting at $W$ fits at $W'$
(#src("whitepaper/Fragment/IndSem.lean", 596, 609)[a field's set grows],
#src("whitepaper/Fragment/IndSem.lean", 622, 628)[the operator is monotone]).
One restriction: monotonicity holds for families whose fibres are
members of $cal(U)_(phi(u))$, the universe the family lives in. It
matters only for a proposition-valued block. There a reflexive
field's set is a propositional product, $Pi_0$, the truth value of
"every fibre equals ${pt}$" (@sec:interp); a fibre that grew from
${pt}$ to a larger set would make it false. In $cal(U)_0$ every
fibre is a subset of ${pt}$, so a fibre that is ${pt}$ stays ${pt}$.

_Accessible by positivity._ @thm:closed-of-acc below, which supplies
the closed family the least fixed point needs, asks for more than
monotonicity. An _occurrence_ in a family $W$ is a pair
$(arrow(Y), v)$ of index values and a member $v in W(arrow(Y))$ of the
fibre there; write $(arrow(Y), v) in W$. Call $Phi$ #src("whitepaper/Fragment/Access.lean", 68, 78)[_accessible with
the bound_ $A$], a set, when every element $x$ of a fibre of $Phi(W)$
has a _support_: a subset $B subset.eq A$ together with a map $g$ that
names, for each $a in B$, an occurrence $g(a)$ in $W$ — such that $x$
is produced from every family in the universe that contains those
occurrences:
$ forall W in cal(U)_n, arrow(Y), x in Phi(W)(arrow(Y)). thick exists B subset.eq A, g. thick & (forall a in B. thin g(a) in W) \
  & and forall W' in cal(U)_n. thin (forall a in B. thin g(a) in W') => x in Phi(W')(arrow(Y)) $
($W in cal(U)_n$: every fibre of $W$ is a member of $cal(U)_n$).
Whether an element is produced depends on at most $A$-many elements
of the input and on nothing else, for the one set $A$. An accessible
operator #src("whitepaper/Fragment/Access.lean", 80, 85)[is monotone], since the support in $W$ is in the larger $W'$.

The block's operator is accessible. Take as an example a tree type
with a constructor $sans("node") : (Nat -> T) -> T$ and an element
$x = tag(j, f)$ of $Phi(W)$: the field $f$ is a function from the
naturals into a fibre of $W$. Three things have to be shown.

+ _The support._ The value $x$ depends on $W$ only through the
  children $f dot.op 0, f dot.op 1, dots$, so #src("whitepaper/Fragment/IndSem.lean", 1050, 1075)[its support is those
  children]: one occurrence for each argument $z$ of the field,
  $(arrow(e)(z), f dot.op z)$, where $arrow(e)(z)$ are the field's
  index expressions. In general a reflexive field with telescope
  $arrow(z)$ contributes one occurrence per $arrow(z)$ fitting the
  telescope (a recursive field, with the empty telescope, exactly
  one), and an ordinary field contributes nothing; each occurrence is
  named by the field's position and the tuple $arrow(z)$.
+ _A family holding the support produces $x$._ If every child lies
  in the matching fibre of $W'$, then $f$, a function whose
  applications all lie in fibres of $W'$,
  #src("whitepaper/Fragment/IndSem.lean", 1130, 1143)[is a member of the product]
  into those fibres (by η), and ordinary fields do not mention the
  family; so $x in Phi(W')$.
+ _One bound for every family._ The names of the occurrences — field
  position and argument tuple — must come from one set $A$, the same
  whatever $W$ is. For $sans("node")$ that is the naturals. In
  general $A$ collects, per constructor and reflexive field, the
  #src("whitepaper/Fragment/IndSem.lean", 973, 995)[tuples fitting the field's telescope]. A
  telescope may mention earlier fields, but by the second shape
  condition of @sec:ind-checks never a reflexive field's value, so the
  telescopes do not depend on $W$; the bound reads them at the
  _one-fibre family_, every fibre ${pt}$
  (#src("whitepaper/Fragment/IndSem.lean", 845, 855)[the replacement],
  #src("whitepaper/Fragment/IndSem.lean", 959, 964)[the telescope reads alike]).

Hence #src("whitepaper/Fragment/IndSem.lean", 1193, 1200)[the operator is accessible with this bound].

In the type-valued regime, that the bound is a member of
$cal(U)_(phi(u))$, and that $Phi$ maps families in $cal(U)_(phi(u))$
to families in $cal(U)_(phi(u))$, follows from the semantic form of
the checker's universe bound, the
#src("whitepaper/Fragment/IndSem.lean", 632, 653)[_universe bound on the fields_]:
along any instance of any family
in the universe, every ordinary domain and every entry of a reflexive
field's telescope is a member of $cal(U)_(phi(u))$
(#src("whitepaper/Fragment/IndSem.lean", 997, 1001)[the bound is a member],
#src("whitepaper/Fragment/IndSem.lean", 788, 795)[the operator maps the universe to itself]).
It comes from the checker's field-sort check, $v <= u$, read in a
model in which the type former denotes an arbitrary family of the
universe: the type former's type
$ forall arrow(x) : arrow(P). thin forall arrow(y) : arrow(J). thin Sort u $
is inhabited by the graph of any such family, so the environment
holding the type former has
#src("whitepaper/Fragment/InstallInd.lean", 270, 273)[a model for each one],
and @thm:sound read there puts every field's domain in
$cal(U)_(phi(v))$, a member of $cal(U)_(phi(u))$ by cumulativity
(#src("whitepaper/Fragment/InstallInd.lean", 431, 440)[the universe bound, at every family]).

#real[
  The operator is read off the stored constructor types with the
  positivity check's variable — a _hole_ — standing for the family
  (#src("ConLeche/Model/Annot/LfpHoleOp.lean", 121, 123)[the hole operator]),
  and monotonicity and accessibility are read off the positivity
  check's run, case by case: a reading that mentions no hole is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 70, 72)[constant]
  (the ordinary field); a product over a hole-free domain is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 139, 141)[positive when its body is]
  and #src("ConLeche/Semantics/Inductives/HoleAcc.lean", 235, 241)[accessible with its body's bound glued over the domain]
  (the reflexive field); a hole applied to hole-free arguments is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 159, 162)[positive]
  and #src("ConLeche/Semantics/Inductives/HoleAcc.lean", 299, 302)[accessible with the bound ${pt}$]
  (the recursive field). Assembled along the fields, that is
  #src("ConLeche/Model/Inductives/BlockPosRunCont.lean", 40, 44)[the operator's monotonicity]
  and #src("ConLeche/Model/Inductives/BlockAccRunCont.lean", 315, 320)[its accessibility with a bound in the universe]
  (#src("ConLeche/SetModel/Access.lean", 54, 61)[the notion above]).
  The fragment's simplification is to take the field kinds from the
  specification instead of the run; what is proved, and from what, is
  the same. The universe bound on the fields the real proof records
  from a check made for the proof alone, the constructor type-checked
  with the holes in context
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 322, 328)[the recorded bound]);
  the fragment reads it off the constructor's ordinary typing.
]

*The closed family and the least fixed point.* A family $L$ is
#src("whitepaper/Fragment/LfpSet.lean", 64, 67)[_closed_ under $Phi$], in $cal(U)_n$, when every fibre of $L$ is a
member of $cal(U)_n$ and $Phi(L) subset.eq L$ fibrewise.

#theorem(name: "A closed family from accessibility")[
  Let $n >= 1$. An operator $Phi$ on families that maps families in
  $cal(U)_n$ to families in $cal(U)_n$ and is accessible with a bound
  $A in cal(U)_n$ #src("whitepaper/Fragment/Access.lean", 292, 303)[has a closed family] in $cal(U)_n$
  (#src("ConLeche/SetModel/Access.lean", 239, 243)[as in con-leche]).
] <thm:closed-of-acc>

#proof[
  Iterate $Phi$ along #src("whitepaper/Fragment/Access.lean", 163, 198)[well-founded trees] branching over all sets — a
  leaf, or a node with a subtree for every set: the _stage_ at a leaf
  is the empty family, the stage at a node is $Phi$ of the union over
  $a in A$ of its subtrees' stages, and the closed family is the
  union of the stages over all trees.
  It is #src("whitepaper/Fragment/Access.lean", 304, 320)[closed by accessibility]: an element $Phi$ produces from it has
  a support of at most $A$-many occurrences, each in some stage, and
  the node whose subtree at $a$ is a tree of the occurrence $g(a)$'s
  stage produces the element at its own stage.
  It is in the universe because every stage is — $Phi$ preserves the
  universe, which is closed under $A$-indexed unions — and because the union over all
  trees is a union over a _set_: a stage depends on its tree only
  through the tree's _code_, its set of finite paths over $A$, and
  the codes are members of the power set of all finite paths over
  $A$, itself a countable union of members of the universe
  (#src("whitepaper/Fragment/Access.lean", 183, 188)[the code],
  #src("whitepaper/Fragment/Access.lean", 221, 223)[the stage depends on the code only],
  #src("whitepaper/Fragment/Access.lean", 284, 290)[the limit is in the universe]).
  No monotonicity, no ordinals, no cardinals.
]

With a closed family $L_0$ in hand, the least fixed point is a set
construction, inside the set theory: fibrewise
#src("whitepaper/Fragment/LfpSet.lean", 82, 89)[the intersection of the closed families],
separated from $L_0$,
$ lfp(Phi)(arrow(Y)) = { x in L_0 (arrow(Y)) mid(|) x in L(arrow(Y)) "for every closed family" L }. $
Its fibres #src("whitepaper/Fragment/LfpSet.lean", 111, 113)[are members of $cal(U)_n$], as separations from members; it
lies #src("whitepaper/Fragment/LfpSet.lean", 106, 108)[below every closed family]\;
and when $Phi$ is monotone and maps $cal(U)_n$ to itself it is
#src("whitepaper/Fragment/LfpSet.lean", 137, 141)[a fixed point],
$Phi(lfp(Phi)) = lfp(Phi)$, and supports
#src("whitepaper/Fragment/LfpSet.lean", 154, 160)[induction]: a
property that holds of every element $Phi$ produces from the family's
separation by it holds on the whole family — the separation is a
closed family, so the least one lies below it. At a proposition no
bound is needed: every fibre of a family in $cal(U)_0$ is a subset of
${pt}$, so #src("whitepaper/Fragment/LfpSet.lean", 170, 174)[the constant family ${pt}$ is closed] under any operator
into $cal(U)_0$.

*The family and the constructors.* The block's operator has a
closed family in $cal(U)_(phi(u))$ — from @thm:closed-of-acc in the
type-valued regime, the constant family ${pt}$ in the
proposition-valued one
(#src("whitepaper/Fragment/IndSem.lean", 1296, 1301)[the closed family])
— and the family of the block is its least fixed point:
$ lden I rden dot.op arrow(X) dot.op arrow(Y) = lfp(Phi)(arrow(Y)) $
(#src("whitepaper/Fragment/IndSem.lean", 1311, 1314)[the family],
#src("whitepaper/Fragment/IndSem.lean", 1431, 1433)[the type former's set],
its graph over the parameters and indices). Its fibres
#src("whitepaper/Fragment/IndSem.lean", 1316, 1320)[are members] of $cal(U)_(phi(u))$,
which is #src("whitepaper/Fragment/InstallInd.lean", 160, 164)[law 1 for the type former].
The #src("whitepaper/Fragment/IndSem.lean", 1324, 1329)[fixed-point equation],
read in both directions, is what the rest of this section lives on:
a member of the fibre at $arrow(Y)$
#src("whitepaper/Fragment/IndSem.lean", 1331, 1338)[is a constructor value] whose
fields fit the family and whose index expressions read as $arrow(Y)$,
and conversely.
The converse is law 1 for the constructors: $c_j$ denotes the
function that takes the parameters and the fields and returns
$tag(j, arrow(F))$
(#src("whitepaper/Fragment/IndSem.lean", 1446, 1451)[a constructor's set]),
a value #src("whitepaper/Fragment/IndSem.lean", 1340, 1348)[in the fibre] at its index expressions
whenever its fields fit
(#src("whitepaper/Fragment/InstallInd.lean", 656, 660)[the law]).
The forward direction is the _inversion_ the $iota$ law needs, and
the least fixed point's induction principle is
#src("whitepaper/Fragment/IndSem.lean", 1350, 1359)[induction over the family],
on which the recursor is built. In the proposition-valued regime
every constructor value is the point, so the fibre
#src("whitepaper/Fragment/IndSem.lean", 1392, 1396)[is the truth value]
"some constructor reaches these indices" and
every constructor denotes the point; where the recursor needs it —
under a large eliminator — the subsingleton criterion makes the
_decodings_ of the point, the constructors with fitting fields that
reach these indices, all the same tagged tuple
(#src("whitepaper/Fragment/Uniq.lean", 40, 50)[the criterion, semantically],
#src("whitepaper/Fragment/Uniq.lean", 60, 64)[uniqueness],
#src("whitepaper/Fragment/InstallInd.lean", 610, 615)[from the checker's criterion]).

#real[
  The least fixed point is
  #src("ConLeche/SetTheory/Derive/LfpTuple.lean", 67, 75)[the same construction]
  over a tuple of families, one per type former of the block, each a
  graph over an index set. What the model records of an installed
  block is one clause: the operator is monotone, maps the universe to
  itself and has a closed family
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 261, 265)[the operator]\;
  #src("ConLeche/Model/Inductives/BlockDatum.lean", 925, 935)[the constant family at a proposition, and from accessibility in the type-valued regime]),
  its fibres are the tagged tuples of fitting fields
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 266, 271)[the fibres]),
  and the type former denotes
  #src("ConLeche/Model/Annot/BlockLfp.lean", 173, 175)[the least fixed point]
  (#src("ConLeche/Model/Annot/BlockLfp.lean", 359, 362)[the fixed-point equation]).
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
determined by the rules: on $tag(j, arrow(F))$ it must be
$S_j$ applied to $arrow(F)$ and to the inductive hypotheses — at
each reflexive field $f$ the function sending $arrow(z)$ to the
recursor's own value at $f dot.op arrow(z)$, which at the empty
telescope is just the recursor's value at $f$. That this equation
has exactly one solution is
the _recursion theorem_, and in the fragment it is proved by the
same device as the family: the recursor's _graph_ — the relation
"the value at $(arrow(Y), x)$ is $v$" — is
#src("whitepaper/Fragment/IndRec.lean", 91, 94)[the least fixed point] of
#src("whitepaper/Fragment/IndRec.lean", 75, 83)[the operator that reads the equation as a step],
a least fixed point on predicates this time, which the ambient
logic's impredicative $Prop$
#src("whitepaper/Fragment/IndLib.lean", 115, 118)[provides outright]; it is
#src("whitepaper/Fragment/IndRec.lean", 157, 162)[single-valued] by
induction over the graph, using that tagged tuples are injective,
and #src("whitepaper/Fragment/IndRec.lean", 215, 224)[total] by induction over the
family. When the family is proposition-valued and the motive is
not, the major is the point and carries no fields: the equation has
one instance per decoding of the point — per constructor and
fitting fields that reach the indices $arrow(Y)$ — and the graph is
single-valued only because
#src("whitepaper/Fragment/IndRec.lean", 133, 143)[any two decodings agree],
which is what the subsingleton criterion was for, as @thm:iota's
proof shows. The recursor denotes
#src("whitepaper/Fragment/IndRec.lean", 396, 408)[the graph of the resulting function]
(#src("whitepaper/Fragment/IndRec.lean", 183, 188)[its value]), curried over the
parameters, the motive, the minors, the indices and the major — a
#src("whitepaper/Fragment/InstallInd.lean", 875, 878)[member of its generated type], which is law 1 for the recursor
(#src("whitepaper/Fragment/IndRec.lean", 318, 326)[the recursor's typing],
by induction over the family from the minors').
When the elimination level $ell$ is zero the recursor's type is a
proposition, the recursor and every minor premise denote the point,
and there is nothing to construct.

#real[
  The recursor is built the same way, except that its graph, too, is
  a least fixed point inside the set theory — the proof calls this
  the _graph route_ — and one construction serves every sort. Over
  the set of majors, the graph is
  #src("ConLeche/SetModel/GraphRec.lean", 101, 103)[the least relation]
  closed under the rules, each read over the ways a major _decodes_ —
  is the value of a constructor applied to some fields; a decoding is
  that constructor and those fields; it has
  #src("ConLeche/SetModel/GraphRec.lean", 228, 230)[exactly one value at every major]
  by the family's own induction, and the equation at any decoding is
  #src("ConLeche/SetModel/GraphRec.lean", 266, 270)[the $iota$ law].
  The one fact about sorts it asks is a premise: at every major,
  #src("ConLeche/SetModel/GraphRec.lean", 186, 188)[two decodings are equal, or the motive's value there has at most one member]
  — the elimination rule of @sec:ind-checks, read three ways
  (#src("ConLeche/Model/Inductives/ClassGenUniq.lean", 13, 19)[the three cases],
  #src("ConLeche/Model/Inductives/ClassGenUniq.lean", 57)[the theorem]):
  at $ell = 0$ the motive's values are truth values; at a type-valued
  family, tagged tuples are injective; at a proposition-valued
  family with a large eliminator, the subsingleton criterion makes
  the decoding a function of the index — the fragment's uniqueness
  of decodings, as one premise.
]

*What the $iota$ rule knows.* Before the $iota$ law, look at what the
rule's premises say and what the model has to supply. The
#src("whitepaper/Fragment/Rules.lean", 84, 159)[rule fires] on $r.\{arrow(ell)\} thick arrow(a) thick t$ where $r$ is a stored
recursor, $arrow(a)$ are its parameters, motive, minors and indices,
and the major $t$ reduces to a constructor application
$c_j.\{arrow(ell)'\} thick arrow(a)' thick arrow(f)$ for which $r$ has
a rule with right-hand side $R_j$; the reduct is
$R_j[arrow(p) := arrow(ell)]$ applied to the parameters, motive and
minors from $arrow(a)$ and to the fields $arrow(f)$
(#src("ConLeche/Rules/Rel.lean", 178, 217)[as in con-leche]). Its
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

#real[
  The rule carries the parameter comparison only for rules whose law
  reads it; a block's rules are installed
  #src("ConLeche/Kernel/Env.lean", 265, 273)[without it], because
  their law holds at any pair of fitting parameter spines (the
  fragment keeps the comparison and uses it). The two certificates
  are walks of their own, relations over lists (@sec:left-out); the
  fragment folds them into the rule.
]

By @thm:sound each
certificate becomes a #src("whitepaper/Fragment/Sound.lean", 77, 84)[_fit_ of values] to the stored telescope, and each
comparison an equality of sets
(#src("whitepaper/Fragment/Sound.lean", 201, 206)[the $iota$ case]).
So the #src("whitepaper/Fragment/EnvModel.lean", 102, 161)[$iota$ law] is stated on values, with
#src("ConLeche/Model/Annot/Laws.lean", 366, 369)[the fits and the equalities] as premises:

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
$iota$ case of @thm:sound is then
#src("whitepaper/Fragment/Sound.lean", 207, 245)[a translation]: certificates to
fits, comparisons to equalities, the reduced major's value for the
argument's, and #src("ConLeche/Model/Rules/IotaSound.lean", 69)[the law].

#theorem(name: [the $iota$ law holds])[
  Every rule of the recursor of an accepted block
  #src("whitepaper/Fragment/InstallIota.lean", 687, 693)[satisfies its $iota$ law] in the model of @sec:ind-model.
  (Via #src("whitepaper/Fragment/IndRec.lean", 282, 292)[the equation on the semantic recursor]\; in con-leche,
  #src("ConLeche/Model/Inductives/BlockRecLaw.lean", 448, 456)[the graph's equation], lifted to the law of @def:iota-law.)
] <thm:iota>

#proof[
  _The type-valued family_ ($ann(PW)$ does not hold). The recursor's fit
  puts the major's value $lden c_j rden dot.op arrow(F)'$ in the family
  at the _recursor's_ parameters and indices, the values among
  $arrow(A)$. By the constructor's fit that value computes to
  $tag(j, arrow(F))$, $arrow(F)$ the fields among $arrow(F)'$;
  and here is the point of
  the least fixed point: a member of the fibre is a constructor value
  of fitting fields (#src("whitepaper/Fragment/IndSem.lean", 1331, 1338)[the fixed-point equation, read forwards]), so it is
  $tag(j', arrow(F)'')$ for some constructor $j'$ and fields
  $arrow(F)''$ fitting $c_(j')$'s field telescope _at the recursor's
  parameters_, with the recursor's indices as the values of
  $c_(j')$'s index expressions at $arrow(F)''$. Tags and tuples are
  injective, so $j' = j$ and $arrow(F)'' = arrow(F)$. This
  _inversion_ is everything the right-hand side needs: it puts each
  field in its domain at the recursor's own parameters, which is
  what the $beta$ steps inside $R_j$ require (@lem:beta-cert, with
  the membership supplied), and the recursion theorem's equation at
  $tag(j, arrow(F))$ is the rule's equation. None of the three
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
  $arrow(F)'' = arrow(F)$ after all — the two decodings of the point
  agree — and the recursion theorem's
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
  #src("whitepaper/Fragment/Consistency.lean", 57, 70)[has a model in it]
  (#src("ConLeche/MainTheorem.lean", 96, 99)[con-leche's main theorem]).
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
  environment. Then #src("whitepaper/Fragment/Consistency.lean", 89, 98)[no closed term $e$ has] $tack e => I$; in
  particular no stored constant has type $I$
  (#src("whitepaper/Fragment/Consistency.lean", 137, 141)[at the block `inductive False : Prop`]\;
  #src("ConLeche/Model/Fold.lean", 276, 283)[as in con-leche]).
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
