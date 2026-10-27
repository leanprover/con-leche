#import "../lib.typ": *

// Notation local to this file, matching §2 and §3.
#let Sort = $sans("Sort")$
#let Prop = $sans("Prop")$
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
#let TyU = $cal(T)$
#let adm = $op("adm")$
#let PiV = $Pi^sans("v")$

= Adding inductive types <sec:ind>

The second kind of declaration is an inductive block: a type former
with its constructors and its recursor. It is checked and installed by
the same shape of argument as a definition (@sec:env), and its
reduction rule $iota$ reads the environment as $delta$ does. Two
pieces of work are new. The constructed sets (the family, the
constructors, the recursor) must be members of their generated types,
which is law 1. And the $iota$ law must be stated and proved: it is a
third law of the contract of @sec:env, and three more laws let most
$iota$ steps go without checking the constructor application. This
section says what the checker checks for a block and what it stores,
how the model grows by a least fixed point so that the laws keep
holding, when $iota$ needs a certificate, and then the consistency
corollary.

== What is checked <sec:ind-checks>

An inductive block declares an _indexed family_ by its constructors:
one type, or one proposition, per choice of indices. At a valuation
the family is _type-valued_ or _proposition-valued_, as its result
sort evaluates to a positive number or to $0$. These are the two
interpretations of a binder from §2, decided for a whole family at
once. The fragment takes a block with one type former, neither mutual
nor nested; nested blocks are the subject of @sec:nested. The block is given by a
#src("whitepaper/Fragment/Spec.lean", 80, 103)[_specification_]
(#src("ConLeche/Kernel/Inductives/BlockParts.lean", 104, 122)[as in con-leche]):

- a name $I$ and level parameters $arrow(p)$;
- a _parameter_ telescope $(x_1 : P_1) dots (x_k : P_k)$ and, under
  it, an _index_ telescope $(y_1 : J_1) dots (y_m : J_m)$; the
  parameters are the same for every constructor and every field, the
  indices vary;
- a result sort $Sort u$: the family has type
  $ forall arrow(x) : arrow(P). thin forall arrow(y) : arrow(J). thin Sort u; $
- constructors $c_1, dots, c_n$, each with a list of _fields_ and,
  under the parameters and the fields, the index expressions
  $arrow(e)_j$ of its result $I thick arrow(x) thick arrow(e)_j$.

A field is one of #src("whitepaper/Fragment/Spec.lean", 28, 42)[two kinds]
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 598, 608)[as in con-leche]):

- _ordinary_: its domain does not mention $I$;
- _reflexive_: its domain is
  $ forall arrow(z) : arrow(A). thin I thick arrow(x) thick arrow(e), $
  a function, under a telescope of binders $arrow(z)$ whose domains
  do not mention $I$, into the family being defined at the block's own
  parameters and some index expressions. The telescope may be empty;
  then the domain is $I thick arrow(x) thick arrow(e)$, a member of
  the family itself, and the field is simply _recursive_.

Two conditions of shape come with the kinds. No field's domain
mentions $I$ anywhere else; this is
#src("whitepaper/Fragment/Decl.lean", 641, 655)[strict positivity].
And nothing after a reflexive field
#src("whitepaper/Fragment/Decl.lean", 658, 663)[may depend on its value]
(#src("ConLeche/Kernel/Inductives/Positivity.lean", 1246, 1249)[as in con-leche] and the
official kernel), so that the model can read a constructor's domains
without knowing the values of its reflexive fields.

#real[
  Simple, mutual and nested blocks are checked uniformly
  (#overview(5)); this section describes that check on a block of
  the fragment's shape. Its positivity check classifies each field's
  domain after weak head normal form, with $I$ at the block's
  parameters replaced by a variable standing for the family being
  defined; @sec:nested uses the same check
  (#src("ConLeche/Kernel/Inductives/Positivity.lean", 1453, 1454)[positivity]).
]

Reflexive fields with a non-empty telescope matter to the model. A
tree type with a constructor
$sans("node") : (Nat -> sans("Tree")) -> sans("Tree")$ has nodes with
countably many children, so a node may have children of every finite
depth, and the set of all trees is larger than the union of the sets
of trees of depth $k$. Iterating the constructors $omega$ times, which
reaches every member of $Nat$, does not reach every tree, and a model
must obtain the least fixed point some other way (@sec:ind-model).

=== The generated declarations

From the specification the checker
generates the types of the type former, the constructors and the
recursor, and the recursor's rules. The type former's type is the one
displayed above; a constructor's type is
$ forall arrow(x) : arrow(P). thin forall arrow(f) : arrow(F). thin I thick arrow(x) thick arrow(e)_j $
(#src("whitepaper/Fragment/Decl.lean", 210, 217)[the two generators]).
The recursor eliminates into $Sort ell$, where the _elimination
level_ $ell$ is either a fresh level parameter (_large elimination_)
or $0$ (_small elimination_); the elimination rule below says which.

#real[
  The input is a stream of raw declarations: the type former, the
  constructors and the recursor as the exporting toolchain stated
  them. The checker recovers the specification from the type former's and
  the constructors' types, and checks and stores those two as the
  stream declares them
  (#src("ConLeche/Kernel/Inductives/SumInstall.lean", 102, 103)[a constructor]).
  The recursor it _generates_, as the official kernel does. From the
  stream's recursor record it takes only the name, the level
  parameters and the type, which must be definitionally equal to the
  generated one, and the record's two layout counts, which must equal
  the generated ones
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 385, 399)[the comparison]).
  An unverified pre-pass reads off that type which type the recursor
  eliminates and how its motive and minor premises are laid out (the
  arguments named on $Nat$ in @ex:nat); a wrong reading can only make
  the comparison fail
  (#src("ConLeche/Kernel/Inductives/ClassRead.lean", 24, 32)[the pre-pass]).
  The record's rules are never read; the generated recursor and its
  rules are what is stored
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 537, 540)[the recursor stage]).
]

Here is the recursor of the natural numbers.

#example(name: [$Nat$])[
  The block $Nat$ has no parameters, no indices, sort $Sort 1$, and
  two constructors: $zero$ with no field and $succ$ with one recursive
  field (reflexive with the empty telescope). The generated
  constructor types are $zero : Nat$ and
  $succ : forall (n : Nat). thin Nat$. The recursor
  eliminates into $Sort ell$ for a fresh level parameter $ell$
  (large elimination, see below), and its generated type is

  $
    NatRec.\{ell\} : & forall (C : forall (t : Nat). thin Sort ell). \
    & forall (z : C thick zero). \
    & forall (s : forall (n : Nat). thin forall (h : C thick n). thin C thick (succ thick n)). \
    & forall (t : Nat). thin C thick t
  $

  $C$ is the _motive_; $z$ and $s$ are the _minor premises_,
  one per constructor, each taking the constructor's fields and, for
  every recursive field, an _inductive hypothesis_ $h$, the motive at
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
  $ lambda C. thin lambda z. thin lambda s. thin lambda n. thin s thick n thick (NatRec.\{ell\} thick C thick z thick s thick n); $
  the $iota$ rule applies it to the recursor's arguments and the
  constructor's fields, and $beta$ does the rest.
] <ex:nat>

The general shape is the same with parameters, indices and
telescopes added. The motive takes the indices and a member of the
family:
$ C : forall arrow(y) : arrow(J). thin forall (t : I thick arrow(x) thick arrow(y)). thin Sort ell. $
A minor premise for $c_j$ takes the fields, then one inductive
hypothesis per reflexive field. At a field
$ f : forall arrow(z) : arrow(A). thin I thick arrow(x) thick arrow(e) $
the hypothesis is
$ forall arrow(z) : arrow(A). thin C thick arrow(e) thick (f thick arrow(z)), $
which at the empty telescope is the $C thick n$ of @ex:nat. The minor
premise ends in
$ C thick arrow(e)_j thick (c_j thick arrow(x) thick arrow(f)). $
The recursor takes the parameters, the motive, the minors, the
indices and the major, and ends in $C thick arrow(y) thick t$.
(Generated:
#src("whitepaper/Fragment/Decl.lean", 219, 221)[the motive],
#src("whitepaper/Fragment/Decl.lean", 232, 244)[an inductive hypothesis],
#src("whitepaper/Fragment/Decl.lean", 257, 266)[a minor premise],
#src("whitepaper/Fragment/Decl.lean", 273, 278)[the recursor's type]
and #src("whitepaper/Fragment/Decl.lean", 315, 322)[a rule's right-hand side]\;
in con-leche: #src("ConLeche/Kernel/Inductives/GenRec.lean", 175, 182)[the type],
#src("ConLeche/Kernel/Inductives/GenRec.lean", 188, 207)[a rule].)

=== The elimination rule

For a type-valued family, in $Sort u$ with $u$ never zero, the
recursor eliminates into any $Sort ell$, $ell$ a fresh level
parameter: large elimination. For a proposition-valued family the
rule is stricter. In the model every proof is the point, so a
recursor applied to a proof cannot see which constructor built it or
with which fields, and a recursor with a type-valued motive would
have to return one value for all of them. The official kernel allows
large elimination out of a proposition only under the _subsingleton
criterion_: the block has at most one constructor, and every field
of that constructor is either itself a proposition or occurs among
the constructor's result indices. Then a proof of
$I thick arrow(x) thick arrow(e)$ determines every field: the
propositional ones are all the same proof, and the others can be read
off the indices. Otherwise the motive lands in $Prop$, $ell = 0$
(_small elimination_). In the fragment the criterion is
#src("whitepaper/Fragment/Decl.lean", 723, 730)[a condition per field]
plus #src("whitepaper/Fragment/Decl.lean", 776)[the constructor count], required of a large
eliminator on a family whose sort _may_ be zero
(#src("whitepaper/Fragment/Decl.lean", 719, 721)[never zero: $1 <= u$ at every valuation]).

#real[
  The checker asks the constructor count of every family whose sort
  may be zero (#src("ConLeche/Kernel/Inductives/BlockRec.lean", 82, 84)[the guard],
  #src("ConLeche/Kernel/Inductives/GenRec.lean", 548, 550)[applied])
  but the #src("ConLeche/Kernel/Inductives/SumInstall.lean", 85, 99)[per-field condition]
  only of a family whose sort is provably zero, which is sound because
  the universe bound (the third check below) makes every field a
  proposition at any valuation that sends the result sort to zero.
]

Three of the checks listed below ask whether a sort is $Prop$, and
the checker answers each with the level oracle:

- a field's sort $v$ is a proposition: $v eq.dot 0$ (the
  subsingleton criterion);
- the result sort $u$ is never a proposition: $1 <= u$ (large
  elimination);
- a field's sort does not exceed the result sort (the _universe
  bound_): $v <= u$, unless $u eq.dot 0$, in which case
  #src("whitepaper/Fragment/Decl.lean", 712, 717)[there is no bound]
  (Lean's impredicativity of $Prop$).

#example(name: [an indexed proposition with large elimination])[
  Let
  $ P : forall (n : Nat). thin Prop $
  have one constructor
  $ mk : forall (n : Nat). thin P thick n. $
  It is a proposition-valued family, indexed by a number, with one
  ordinary field $n$ that is not a proposition and occurs in the
  result's index. The subsingleton criterion holds, so the recursor
  may eliminate into $Sort ell$:

  $
    PRec.\{ell\} : & forall (C : forall (n : Nat). thin forall (t : P thick n). thin Sort ell). \
    & forall (h : forall (n : Nat). thin C thick n thick (mk thick n)). \
    & forall (n : Nat). thin forall (t : P thick n). thin C thick n thick t
  $

  with one rule,
  $ PRec.\{ell\} thick C thick h thick n thick (mk thick n') red h thick n'. $
  The index occurs twice: $n$ is the recursor's index argument, $n'$
  the constructor's field. @sec:iota uses this example.
] <ex:P>

=== When a block is accepted

A block #src("whitepaper/Fragment/Decl.lean", 732, 777)[is accepted] when
(#src("ConLeche/Kernel/Inductives/BlockTail.lean", 141, 146)[as in con-leche]):

- its names are distinct and fresh;
- the specification is in scope, positivity included;
- the generated type former's type has a type in the current environment;
- each generated constructor's type has a sort in the environment
  holding the type former, and every field's domain has a sort $v$ that
  respects the universe bound and, where a large eliminator asks it,
  the subsingleton criterion (the binders of a reflexive field's own
  telescope respect the universe bound too);
- the constructor count respects the elimination rule;
- in the environment holding the type former and the constructors, the
  generated recursor's type has a type, and so has
  #src("whitepaper/Fragment/Decl.lean", 308, 313)[each rule's type],
  the recursor's binder prefix with the constructor's fields in place
  of the indices and the major.

Each "has a type" is an inference $tack T => S$ of §2, in the empty
context, and each "has a sort" one whose result $S$ reduces to a
sort. So the generated types are checked like a definition's. The model needs
only the inferences: the third claim of @thm:sound makes every
generated type a well-denoted type.

#real[
  The same steps run in this order, and each generated rule is
  type-checked in the environment holding the rule-less recursor
  (#src("ConLeche/Kernel/Inductives/GenRec.lean", 412, 433)[a generated rule]).
]

=== What is stored

The block #src("whitepaper/Fragment/Decl.lean", 532, 573)[adds three kinds of constant] to the
environment, the ones @sec:env left to this section
(#src("whitepaper/Fragment/Env.lean", 66, 82)[the kinds],
#src("ConLeche/Kernel/Env.lean", 165, 182)[as in con-leche]). Written
with the notation of @sec:env, a stored declaration is one of

- $(c.\{arrow(p)\} : T := v)$, a definition (@sec:env);
- $(I.\{arrow(p)\} : T)^sans("type") [k, m; c_1, dots, c_n]$, a type
  former: $k$ parameters, $m$ indices, constructors $c_1, dots, c_n$;
- $(c_j.\{arrow(p)\} : T)^sans("ctor") [I; k, f]$, a constructor of
  $I$: $k$ parameters, $f$ fields;
- $(r.\{arrow(ell)\} : T)^sans("rec") [k, 1, n, m; R_1, dots, R_n]$, a
  recursor: $k$ parameters, one motive, $n$ minors, $m$ indices, the
  major; rules $R_1, dots, R_n$, each
  #src("whitepaper/Fragment/Env.lean", 56, 63)[flagged _K_] when the
  block is K-like (@sec:iota-cases).

The counts are the sizes of the argument groups (@ex:nat shows them
on $Nat$). A rule $R_j$ is a closed right-hand side over the
recursor's level parameters, one per constructor. The rules are
generated and stored without an inferred type: they mention the
recursor itself, and the official kernel infers no rule either.

== The model <sec:ind-model>

The model of a block has three parts: the set the type former
denotes at each choice of indices, the sets the constructors denote,
and the set the recursor denotes. With the recursor, the contract of @sec:env gains its
#src("whitepaper/Fragment/EnvModel.lean", 318, 325)[third law]:
every rule of every stored recursor satisfies its $iota$ law
(@def:iota-law), which this subsection proves. @sec:iota-cases adds
three more laws, facts about the model that let most $iota$ steps go
without a certificate. All of it is stated against an extension of
§2's axioms.

=== The axioms, extended

Beyond the laws of @sec:lib this section
assumes that the positive universes $cal(U)_n$, $n >= 1$,
are #src("whitepaper/Fragment/Univ.lean", 43, 88)[_Grothendieck universes_], and
that there are #src("whitepaper/Fragment/IndLib.lean", 47, 64)[tagged tuples]:

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
  for $n >= 1$, $cal(U)_n$ is transitive (if $A in cal(U)_n$ and
  $x in A$ then $x in cal(U)_n$), closed under the four operations,
  $ {a, b}, thick union.big x, thick cal(P)(x) & in cal(U)_n quad & "for" a, b, x in cal(U)_n, \
    F[A] & in cal(U)_n quad & "for" A in cal(U)_n "with" F(a) in cal(U)_n "for every" a in A, $
  and contains $omega$.
+ #src("whitepaper/Fragment/IndLib.lean", 50, 64)[_Tagged tuples_]
  $tag(j, x_1, dots, x_k)$, a list of sets with a number $j$
  attached: injective (equal tagged tuples have equal numbers and
  equal components), in $cal(U)_n$ when every component is, never
  $pt$, and #src("whitepaper/Fragment/IndLib.lean", 65, 68)[never a member of $pt$], so that a set
  of tagged tuples is strict.

Nothing else is assumed. There is no law about least fixed points
and none about the size of an inductive family; both are theorems
below. What the construction uses of the universes follows at once. A
#src("whitepaper/Fragment/Univ.lean", 115, 120)[subset of a member is a member] (it is in the power set, and the
universe is transitive), so a separation from a member is a member;
#src("whitepaper/Fragment/Univ.lean", 177, 194)[the union $union.big_(a in A) F(a)$ of a family indexed by a member]
is a member, by replacement then union; and so is
#src("whitepaper/Fragment/Univ.lean", 212, 231)[the countable union $union.big_k F(k)$],
the union over $omega$. This is
#src("whitepaper/Fragment/Univ.lean", 29, 35)[the one use of $omega$], and it is needed:
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

=== The operator

Fix a block as in @sec:ind-checks, a valuation
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
is the function space, read as in §2, over its telescope into fibres of $W$
at the field's own index expressions $arrow(e)$,
$ PiV(arrow(z) in arrow(A), thick adm(W(arrow(e)(arrow(z))))), $
and the fibre $W(arrow(e))$ itself when the telescope is empty
(#src("whitepaper/Fragment/IndSem.lean", 282, 303)[a field's set],
#src("whitepaper/Fragment/IndSem.lean", 315, 320)[a fitting list]).
Here #src("whitepaper/Fragment/IndCommon.lean", 188, 195)[$adm(X)$], the _admissible part_ of $X$, is $X$
itself when the family is proposition-valued; when it is type-valued,
it is the members of $X$ that neither are the point nor contain it.
On the family the construction ends with, $adm$ changes nothing,
since there a type-valued fibre is a set of tagged tuples. It is
needed for the arbitrary families the operator is also applied to. A
fibre ${pt}$ would make the field's function space a truth value, and
then the field's set would not grow with the family
(#src("whitepaper/Fragment/IndCommon.lean", 278, 286)[the function space's body]).
The fibre is a set, built by replacement, union and separation from
the fields' sets
(#src("whitepaper/Fragment/IndSem.lean", 501, 550)[the construction],
#src("whitepaper/Fragment/IndSem.lean", 561, 565)[its members are as displayed]).
When the family is proposition-valued ($u$ evaluates to $0$ at $phi$) a
constructor value #src("whitepaper/Fragment/IndCommon.lean", 336, 338)[is the point] instead of the tagged tuple,
so every fibre of $Phi(W)$ is a subset of ${pt}$: the truth value
"some constructor reaches these indices".

=== Accessibility

@thm:closed-of-acc below, which supplies
the closed family the least fixed point needs, asks for
_accessibility_. An _occurrence_ in a family $W$ is a pair
$(arrow(Y), v)$ of index values and a member $v in W(arrow(Y))$ of the
fibre there; write $(arrow(Y), v) in W$. Call $Phi$ #src("whitepaper/Fragment/Access.lean", 68, 78)[_accessible with
the bound_ $A$], a set, when every element $x$ of a fibre of $Phi(W)$
has a _support_: a subset $B subset.eq A$ together with a map $g$ that
names, for each $a in B$, an occurrence $g(a)$ in $W$, such that $x$
is produced from every family in the universe that contains those
occurrences:
$ forall W in cal(U)_n, arrow(Y), x in Phi(W)(arrow(Y)). thick exists B subset.eq A, g. thick & (forall a in B. thin g(a) in W) \
  & and forall W' in cal(U)_n. thin (forall a in B. thin g(a) in W') => x in Phi(W')(arrow(Y)) $
($W in cal(U)_n$: every fibre of $W$ is a member of $cal(U)_n$).
Whether an element is produced depends on at most $A$-many elements
of the input and on nothing else, for the one set $A$. The
fixed-point equation below also needs a monotone operator;
accessibility implies it, on families in the universe:
#src("whitepaper/Fragment/Access.lean", 80, 85)[the support in $W$ lies in any larger $W'$].

The block's operator is accessible. Take as an example the tree type
with a constructor $sans("node") : (Nat -> sans("Tree")) -> sans("Tree")$ and an element
$x = tag(j, f)$ of $Phi(W)$: the field $f$ is a function from the
naturals into a fibre of $W$. Three things have to be shown.

+ _The support._ The value $x$ depends on $W$ only through the
  children $f dot.op 0, f dot.op 1, dots$, so #src("whitepaper/Fragment/IndSem.lean", 1158, 1183)[its support is those
  children]: one occurrence for each argument $z$ of the field,
  $(arrow(e)(z), f dot.op z)$, where $arrow(e)(z)$ are the field's
  index expressions. In general a reflexive field with telescope
  $arrow(z)$ contributes one occurrence per $arrow(z)$ fitting the
  telescope (a recursive field, with the empty telescope, exactly
  one), and an ordinary field contributes nothing. Each occurrence is
  named by the field's position and the tuple $arrow(z)$.
+ _A family holding the support produces $x$._ If every child lies
  in the matching fibre of $W'$, then $f$, a function whose
  applications all lie in fibres of $W'$,
  #src("whitepaper/Fragment/IndSem.lean", 1237, 1250)[is a member of the function space]
  into those fibres (by η), and ordinary fields do not mention the
  family; so $x in Phi(W')$.
+ _One bound for every family._ The names of the occurrences (field
  position and argument tuple) must come from one set $A$, the same
  whatever $W$ is. For $sans("node")$ that is the naturals. In
  general $A$ collects, per constructor and reflexive field, the
  #src("whitepaper/Fragment/IndSem.lean", 1080, 1097)[tuples fitting the field's telescope]. A
  telescope may mention earlier fields, but by the second shape
  condition of @sec:ind-checks never a reflexive field's value, so the
  telescopes do not depend on $W$; the bound reads them at the
  _one-fibre family_, every fibre the same
  #src("whitepaper/Fragment/IndSem.lean", 819, 822)[one-element type]: ${pt}$ when the family is
  proposition-valued, the singleton of a tagged tuple when it is
  type-valued
  (#src("whitepaper/Fragment/IndSem.lean", 885, 896)[the replacement],
  #src("whitepaper/Fragment/IndSem.lean", 1007, 1012)[the telescope reads alike]).

Hence #src("whitepaper/Fragment/IndSem.lean", 1304, 1311)[the operator is accessible with this bound],
and so #src("whitepaper/Fragment/IndSem.lean", 1418, 1423)[monotone].

For a type-valued family, that the bound is a member of
$cal(U)_(phi(u))$, and that $Phi$ maps families in $cal(U)_(phi(u))$
to families in $cal(U)_(phi(u))$, follows from the semantic form of
the checker's universe bound, the
#src("whitepaper/Fragment/IndSem.lean", 601, 622)[_universe bound on the fields_]:
along any instance of any family
in the universe, every ordinary domain and every entry of a reflexive
field's telescope is a member of $cal(U)_(phi(u))$
(#src("whitepaper/Fragment/IndSem.lean", 1105, 1109)[the bound is a member],
#src("whitepaper/Fragment/IndSem.lean", 768, 775)[the operator maps the universe to itself]).
It comes from the checker's field-sort check, $v <= u$, read in a
model in which the type former denotes the one-fibre family: the type
former's type
$ forall arrow(x) : arrow(P). thin forall arrow(y) : arrow(J). thin Sort u $
is inhabited by the graph of any admissible family of types of the
universe, so the environment holding the type former has
#src("whitepaper/Fragment/InstallInd.lean", 243, 247)[a model for each one],
and @thm:sound read in the one for the one-fibre family puts every
field's domain in $TyU_(phi(v))$, and so, since $v <= u$ and the
universes are cumulative, in $cal(U)_(phi(u))$. No field reads an
earlier reflexive field's value, so the domains met along an instance
of any family are those met along an instance of the one-fibre family
(#src("whitepaper/Fragment/InstallInd.lean", 429, 439)[the universe bound, at every family]).

For a proposition-valued family none of this is needed. Every
constructor value is the point, so every fibre of $Phi(W)$ is a
subset of ${pt}$, and
#src("whitepaper/Fragment/LfpSet.lean", 170, 174)[the constant family ${pt}$ is closed]
under $Phi$ and lies in $cal(U)_0$. This closed family needs no bound
in the universe and no universe bound on the fields. Accessibility,
which holds in both cases, is used here only for monotonicity.

#real[
  The operator is read off the stored constructor types with the
  positivity check's variable (a _hole_) standing for the family
  (#src("ConLeche/Model/Env/LfpHoleOp.lean", 104, 106)[the hole operator]),
  and monotonicity and accessibility are read off the positivity
  check's run, case by case. A reading that mentions no hole is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 71, 73)[constant]
  (the ordinary field); a function space over a hole-free domain,
  its fibres types, is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 130, 139)[positive when its body is]
  and #src("ConLeche/Semantics/Inductives/HoleAcc.lean", 233, 243)[accessible with its body's bound glued over the domain]
  (the reflexive field); a hole applied to hole-free arguments is
  #src("ConLeche/Semantics/Inductives/HoleMono.lean", 158, 162)[positive]
  and #src("ConLeche/Semantics/Inductives/HoleAcc.lean", 321, 324)[accessible with the bound ${pt}$]
  (the recursive field). Assembled along the fields, that is
  #src("ConLeche/Model/Inductives/BlockAccRunCont.lean", 310, 315)[the fit's accessibility, for both kinds of family, with a bound in the universe for a type-valued one]
  (#src("ConLeche/SetModel/Access.lean", 56, 63)[the notion above]), and
  #src("ConLeche/Model/Env/BlockLfp.lean", 511, 515)[the operator's monotonicity] follows from it, as in the fragment.
  The fragment's simplification is to take the field kinds from the
  specification instead of the run. The universe bound on the fields the real proof records
  from a check made for the proof alone, the constructor type-checked
  with the holes in context
  (#src("ConLeche/Model/Env/BlockLfp.lean", 450, 456)[the recorded bound]);
  the fragment reads it off the constructor's ordinary typing.
]

=== The least fixed point <sec:ind-lfp>

A family $L$ is
#src("whitepaper/Fragment/LfpSet.lean", 64, 67)[_closed_ under $Phi$], in $cal(U)_n$, when every fibre of $L$ is a
member of $cal(U)_n$ and $Phi(L) subset.eq L$ fibrewise.

#theorem(name: "A closed family from accessibility")[
  Let $n >= 1$. An operator $Phi$ on families that maps families in
  $cal(U)_n$ to families in $cal(U)_n$ and is accessible with a bound
  $A in cal(U)_n$ #src("whitepaper/Fragment/Access.lean", 292, 303)[has a closed family] in $cal(U)_n$
  (#src("ConLeche/SetModel/Access.lean", 240, 244)[as in con-leche]).
] <thm:closed-of-acc>

#proof[
  Iterate $Phi$ along #src("whitepaper/Fragment/Access.lean", 163, 198)[well-founded trees] branching over all sets (a
  tree is a leaf, or a node with a subtree for every set). The
  _stage_ at a leaf is the empty family, the stage at a node is $Phi$ of the union over
  $a in A$ of its subtrees' stages, and the closed family is the
  union of the stages over all trees.
  It is #src("whitepaper/Fragment/Access.lean", 304, 320)[closed by accessibility]: an element $Phi$ produces from it has
  a support of at most $A$-many occurrences, each in some stage, and
  the node whose subtree at $a$ is a tree of the occurrence $g(a)$'s
  stage produces the element at its own stage.
  It is in the universe because every stage is ($Phi$ preserves the
  universe, which is closed under $A$-indexed unions), and because the union over all
  trees is a union over a _set_. A stage depends on its tree only
  through the tree's _code_, its set of finite paths over $A$, and
  the codes are members of the power set of all finite paths over
  $A$, itself a countable union of members of the universe
  (#src("whitepaper/Fragment/Access.lean", 183, 188)[the code],
  #src("whitepaper/Fragment/Access.lean", 221, 223)[the stage depends on the code only],
  #src("whitepaper/Fragment/Access.lean", 284, 290)[the limit is in the universe]).
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
separation by it holds on the whole family, because the separation is
a closed family and the least one lies below it.

=== The family and the constructors

The block's operator has a closed family in $cal(U)_(phi(u))$: for a
type-valued family by @thm:closed-of-acc, for a proposition-valued
one the constant family ${pt}$
(#src("whitepaper/Fragment/IndSem.lean", 1443, 1449)[the closed family]).
The family of the block is its least fixed point,
$ lden I rden dot.op arrow(X) dot.op arrow(Y) = lfp(Phi)(arrow(Y)) $
(#src("whitepaper/Fragment/IndSem.lean", 1458, 1461)[the family],
#src("whitepaper/Fragment/IndSem.lean", 1641, 1643)[the type former's set],
its graph over the parameters and indices). Its fibres
#src("whitepaper/Fragment/IndSem.lean", 1561, 1565)[are types] of $TyU_(phi(u))$ (above),
which is #src("whitepaper/Fragment/InstallInd.lean", 555, 562)[law 1 for the type former].
A type-valued fibre is a set of tagged tuples, hence strict, and a
proposition-valued fibre is a truth value, so either way the fibre is
#src("whitepaper/Fragment/IndSem.lean", 1561, 1564)[a type of the result sort].
A member of a type-valued fibre is a tagged tuple and carries its
constructor and its fields; a member of a proposition-valued fibre is
the point and carries nothing.

The rest of this section rests on
the #src("whitepaper/Fragment/IndSem.lean", 1471, 1477)[fixed-point equation],
read in both directions. A member of the fibre at $arrow(Y)$
#src("whitepaper/Fragment/IndSem.lean", 1478, 1486)[is a constructor value] whose
fields fit the family and whose index expressions read as $arrow(Y)$,
and conversely.
The converse is law 1 for the constructors: $c_j$ denotes the
function that takes the parameters and the fields and returns
$tag(j, arrow(F))$
(#src("whitepaper/Fragment/IndSem.lean", 1656, 1661)[a constructor's set]),
a value #src("whitepaper/Fragment/IndSem.lean", 1487, 1496)[in the fibre] at its index expressions
whenever its fields fit
(#src("whitepaper/Fragment/InstallInd.lean", 779, 785)[the law]).
The forward direction is the _inversion_ the $iota$ law needs. The
least fixed point's induction principle is
#src("whitepaper/Fragment/IndSem.lean", 1497, 1507)[induction over the family],
on which the recursor is built. For a proposition-valued family
every constructor value is the point, so the fibre
#src("whitepaper/Fragment/IndSem.lean", 1539, 1543)[is the truth value]
of "some constructor reaches these indices", and
every constructor denotes the point.

#real[
  The least fixed point is
  #src("ConLeche/SetTheory/Derive/LfpTuple.lean", 78, 87)[the same construction]
  over a tuple of families, one per type former of the block, each a
  graph over an index set. What the model records of an installed
  block is one clause: the operator maps the universe to itself and
  its fit is accessible, for both kinds of family
  (#src("ConLeche/Model/Env/BlockLfp.lean", 388, 395)[the operator]).
  So it has a closed family
  (#src("ConLeche/SetModel/Access.lean", 298, 303)[the constant family at a proposition, and from accessibility for a type-valued family])
  and is
  #src("ConLeche/Model/Env/BlockLfp.lean", 511, 515)[monotone]\;
  its fibres are the tagged tuples of fitting fields
  (#src("ConLeche/Model/Env/BlockLfp.lean", 396, 401)[the fibres]),
  and the type former denotes
  #src("ConLeche/Model/Env/BlockLfp.lean", 181, 183)[the least fixed point]
  (#src("ConLeche/Model/Env/BlockLfp.lean", 517, 520)[the fixed-point equation]).
  Its constructors are
  #src("ConLeche/SetModel/TaggedSum.lean", 65)[tagged pairs] of
  #src("ConLeche/SetModel/TupleTower.lean", 93)[nested pairs], the
  two kinds of family in
  #src("ConLeche/SetModel/TaggedSum.lean", 61, 62)[one carrier].
]

=== The recursor

Fix values $C$ for the motive and $arrow(S)$ for the
minor premises. The recursor's value on a member of the family is
determined by the rules. On $tag(j, arrow(F))$ it must be
$S_j$ applied to $arrow(F)$ and to the inductive hypotheses; at
each reflexive field $f$ the hypothesis is the function sending
$arrow(z)$ to the recursor's own value at $f dot.op arrow(z)$, and at
the empty telescope it is just the recursor's value at $f$. That this
equation has exactly one solution is the _recursion theorem_. In the
fragment it is proved by the same device as the family. The
recursor's _graph_, the relation "the value at $(arrow(Y), x)$ is
$v$", is
#src("whitepaper/Fragment/IndRec.lean", 89, 92)[the least fixed point] of
#src("whitepaper/Fragment/IndRec.lean", 73, 81)[the operator that reads the equation as a step],
a least fixed point on predicates this time, which the ambient
logic's impredicative $Prop$
#src("whitepaper/Fragment/IndLib.lean", 101, 104)[provides outright]. It is
#src("whitepaper/Fragment/IndRec.lean", 155, 159)[single-valued] by
induction over the graph, using that tagged tuples are injective,
and #src("whitepaper/Fragment/IndRec.lean", 213, 219)[total] by induction over the
family.

When the family is proposition-valued and the motive is not, the
major is the point and carries no fields. A major _decodes_ as a
constructor $c_j$ with fields $arrow(F)$ when it is the value of $c_j$
applied to fields $arrow(F)$ that fit $c_j$ and whose index
expressions read as the indices $arrow(Y)$; the pair is a
_decoding_ of the major. The point may have several decodings, and
the equation has one instance per decoding. The graph is
single-valued only because
#src("whitepaper/Fragment/IndRec.lean", 131, 141)[any two decodings agree]:
under a large eliminator the subsingleton criterion
#src("whitepaper/Fragment/InstallInd.lean", 733, 738)[as the checker states it]
#src("whitepaper/Fragment/Uniq.lean", 40, 50)[reads semantically] as
#src("whitepaper/Fragment/Uniq.lean", 60, 64)[uniqueness of decodings],
as @thm:iota's proof shows.

The recursor denotes
#src("whitepaper/Fragment/IndRec.lean", 394, 408)[the graph of the resulting function]
(#src("whitepaper/Fragment/IndRec.lean", 181, 185)[its value]), curried over the
parameters, the motive, the minors, the indices and the major. It is a
#src("whitepaper/Fragment/InstallInd.lean", 1054, 1057)[member of its generated type], which is law 1 for the recursor
(#src("whitepaper/Fragment/IndRec.lean", 316, 325)[the recursor's typing],
by induction over the family from the minors').
When the elimination level $ell$ is zero at the valuation, the
motive's values are truth values and the recursor's value is the point
at every argument. Then so is the recursor's set, since an abstraction
is read by its values, and there is nothing to construct.

#real[
  The recursor is built the same way, except that its graph is also a
  least fixed point inside the set theory (the proof calls this the
  _graph route_), and one construction serves every sort. Over the set
  of majors, the graph is
  #src("ConLeche/SetModel/GraphRec.lean", 100, 104)[the least relation]
  closed under the rules, each read over the decodings of a major.
  The graph has
  #src("ConLeche/SetModel/GraphRec.lean", 232, 234)[exactly one value at every major]
  by the family's own induction, and the equation at any decoding is
  #src("ConLeche/SetModel/GraphRec.lean", 270, 274)[the $iota$ law].
  The one fact about sorts it asks is a premise: at every major,
  #src("ConLeche/SetModel/GraphRec.lean", 190, 192)[two decodings are equal, or the motive's value there has at most one member].
  This is the elimination rule of @sec:ind-checks, read three ways
  (#src("ConLeche/Model/Inductives/ClassGenUniq.lean", 13, 19)[the three cases],
  #src("ConLeche/Model/Inductives/ClassGenUniq.lean", 57)[the theorem]).
  At $ell = 0$ the motive's values are truth values; at a type-valued
  family, tagged tuples are injective; at a proposition-valued family
  with a large eliminator, the subsingleton criterion makes the
  decoding a function of the index, which is the fragment's uniqueness
  of decodings as one premise.
]

=== The $iota$ rule <sec:iota>

The
#src("whitepaper/Fragment/Rules.lean", 95, 174)[rule fires] on $r.\{arrow(ell)\} thick arrow(a) thick t$ where $r$ is a stored
recursor, $arrow(a)$ are its parameters, motive, minors and indices,
and the major $t$ reduces to a constructor application
$c_j.\{arrow(ell)'\} thick arrow(a)' thick arrow(f)$ for which $r$ has
a rule with right-hand side $R_j$. The reduct is
$R_j[arrow(p) := arrow(ell)]$ applied to the parameters, motive and
minors from $arrow(a)$ and to the fields $arrow(f)$
(#src("ConLeche/Rules/Rel.lean", 186, 243)[as in con-leche]). Besides
finding $r$, $c_j$ and the rule in the environment, the fragment's
rule has three _comparisons_ as premises:

- the constructor's levels $arrow(ell)'$ are oracle-equal to the last
  levels of $arrow(ell)$ (a large eliminator carries one extra level
  in front);
- the constructor's parameters $arrow(a)'$ are definitionally
  equal to the recursor's;
- the index expressions of the constructor's result type at
  $arrow(a)' thick arrow(f)$ are definitionally equal to the
  recursor's index arguments.

In one case it also has a _certificate_ on the constructor application
(@sec:iota-cases). The official kernel makes none of these checks. The
fragment's rules make the comparisons in every case except K, and its
proof of the $iota$ law uses them. The checker makes them only in the
certified case of @sec:iota-cases, together with the certificate;
there they belong to the certification tax (@sec:tax).

Nothing checks the recursor's own arguments against its type, and
nothing needs to. The reduction claim is asked only of a redex that
is not the point, and such a redex
#src("whitepaper/Fragment/Sound.lean", 821, 835)[fits the recursor's telescope] as it stands.
Call the arguments of an application its _spine_. Each prefix of the
redex's spine is not the point either ($pt dot.op a = pt$), hence a
graph. The condition the semantic invariant's application rule puts on
the next argument names a function space holding that graph, the
prefix's membership in its own type names another, and by domain
uniqueness the two have one domain, which holds the argument.

#real[
  In the checker's rule every premise on the constructor application
  is conditional on the certified case. A K rule, and a family that is
  never a proposition, fire comparing nothing, as in the official
  kernel. The law there is proved without the comparisons: when the
  redex is not the point, the major is a tagged tuple, which ties the
  constructor application to the recursor's levels and parameters
  (#src("ConLeche/Model/Env/Laws.lean", 521, 555)[what the law
  provides instead]).
]

By @thm:sound each comparison becomes an equality of sets wherever
neither side is the point. So the
#src("whitepaper/Fragment/EnvModel.lean", 119, 186)[$iota$ law] is stated on values, with the fits
and these conditional equalities as premises:

#definition(name: [the $iota$ law of a rule])[
  Let $r$ be a stored recursor and $R_j$ the right-hand side of its
  rule for the constructor $c_j$. Take a valuation, levels
  $arrow(ell)$ and $arrow(ell)'$ of the right lengths, values for
  the recursor's arguments before the major (parameters $arrow(X)$,
  motive $C$, minors $arrow(M)$, indices $arrow(Y)$), and values for
  the constructor's arguments (parameters $arrow(X)'$ and fields
  $arrow(F)$). Suppose
  - $arrow(X), C, arrow(M), arrow(Y)$ followed by
    $lden c_j.\{arrow(ell)'\} rden dot.op arrow(X)' dot.op arrow(F)$
    fit the recursor's type at $arrow(ell)$, and
    $arrow(X)', arrow(F)$ fit the constructor's type at $arrow(ell)'$;
  - $arrow(ell)'$ evaluates as the last levels of $arrow(ell)$;
  - $X'_i = X_i$ at every position where neither is the point;
  - the constructor's index expressions read at its arguments equal
    $arrow(Y)$ at every position where neither side is the point; and
  - the recursor applied to all these values is not the point.
  Then
  $ lden r.\{arrow(ell)\} rden dot.op arrow(X) dot.op C dot.op arrow(M) dot.op arrow(Y) dot.op (lden c_j.\{arrow(ell)'\} rden dot.op arrow(X)' dot.op arrow(F))
    = lden R_j [arrow(p) := arrow(ell)] rden dot.op arrow(X) dot.op C dot.op arrow(M) dot.op arrow(F), $
  and the right-hand side $R_j$ is well-denoted with a well-formed
  application chain along those values.
] <def:iota-law>

The second conjunct makes the reduct well-denoted, as the first claim
of @thm:sound demands; the first is the equation. The $iota$ case of
@thm:sound is then
#src("whitepaper/Fragment/Sound.lean", 1057, 1067)[a translation]. The comparisons become
conditional equalities; the redex's own fit is as above; the
constructor's fit comes from its certificate or from the arguments of
@sec:iota-cases; the reduced major's value replaces the argument's;
and #src("ConLeche/Model/Rules/IotaSound.lean", 88)[the law] gives the rest.

#theorem(name: [the $iota$ law holds])[
  Every rule of the recursor of an accepted block
  #src("whitepaper/Fragment/InstallIota.lean", 822, 828)[satisfies its $iota$ law] in the model of @sec:ind-model.
  (Via #src("whitepaper/Fragment/IndRec.lean", 280, 290)[the equation on the semantic recursor]\; in con-leche,
  #src("ConLeche/Model/Inductives/BlockRecLaw.lean", 874, 880)[the graph's equation], lifted to the law of @def:iota-law.)
] <thm:iota>

#proof[
  First the conditional comparisons become equalities. The recursor's
  and the constructor's telescopes are generated from one parameter
  context and one index context, and both spines fit them. Under equal
  earlier values, two values compared at one position lie in one type,
  whose members are all the point or none, so where the comparison
  says nothing they are both the point
  (#src("whitepaper/Fragment/Ctx.lean", 161, 167)[a conditional comparison of fitting values is an equality]).
  So $arrow(X)' = arrow(X)$, and the constructor's index values are
  $arrow(Y)$.

  _The type-valued family._ The recursor's fit puts the major's value
  $lden c_j rden dot.op arrow(X) dot.op arrow(F)$ in the family at the
  recursor's parameters $arrow(X)$ and indices $arrow(Y)$, and by the
  constructor's fit that value computes to $tag(j, arrow(F))$. A member
  of the fibre is a constructor value of fitting fields
  (#src("whitepaper/Fragment/IndSem.lean", 1478, 1486)[the fixed-point equation, read forwards]),
  and tagged tuples are injective, so the fields fit $c_j$'s field
  telescope at the recursor's parameters, which is what the $beta$
  steps inside $R_j$ require. The recursion theorem's equation at
  $tag(j, arrow(F))$ is the rule's equation.

  _The proposition-valued family._ Here the major's value is the
  point, and the recursor's fit says only that the fibre at the
  recursor's indices is inhabited. The point carries no constructor,
  no fields, no parameters and no indices. When the elimination level
  is zero the recursor's application is the point, and the law asks
  nothing. Otherwise the block passed the subsingleton criterion. It
  has one constructor, so every decoding of the point is by $c_j$, and
  each field is a proposition or occurs among the constructor's result
  indices. A propositional field is the point in both decodings,
  provided both read its domain at one valuation of the block's level
  parameters; the level comparison secures that. The index equality
  identifies an index field's value with the recursor's index
  argument. So the two decodings of the point agree, and the recursion
  theorem's equation is again the rule's.
]

*Why the index comparison is needed.* Take the recursor of @ex:P on
the spine $C, h, 7, mk thick 5$. Every $P thick n$ is inhabited, by
$mk thick n$, so $lden P thick 7 rden = {pt}$, and the recursor's fit
asks only that $lden mk thick 5 rden = pt$ lie in it, which it does.
The fit holds equally for $mk thick 7$. Without the index comparison
the $iota$ law would therefore have to give both
$ lden PRec rden dot.op C dot.op h dot.op 7 dot.op pt = h dot.op 5 quad "and" quad lden PRec rden dot.op C dot.op h dot.op 7 dot.op pt = h dot.op 7, $
so $h dot.op 5 = h dot.op 7$ for every $h$, which is false. The
recursor's set is a function of its arguments and has one value at
index $7$. On values the types $P thick 5$ and $P thick 7$ are both
${pt}$, so no comparison of types could tell them apart; the index
comparison, $5 equiv 7$, is what the model can use. For a type-valued
family the comparison is redundant, because the tagged tuple carries
its indices. The official kernel never makes it: at an $iota$ step it
compares nothing and relies on the term being well-typed, which its
typing judgement guarantees. Our proof has no typing judgement, so
where the major may be the point the comparison has to be a premise
of the rule.

=== When $iota$ needs a certificate <sec:iota-cases>

The official kernel checks nothing at an $iota$ step: the term is
well-typed, so the constructor application it reduces to and that
application's fields are well-typed too. The semantic proof needs the
reduct to be well-denoted and the constructor's arguments to fit its
type wherever the redex is not the point. What supplies that depends
on the major's family at the instance. The model has three more laws
for it, each proved when the block is installed.

*A family that is never a proposition.* If the family's sort is
at least $1$ at every valuation (one oracle test on the levels at
the use), then
#src("whitepaper/Fragment/Rules.lean", 394, 445)[the step needs no certificate]. The model's
#src("whitepaper/Fragment/EnvModel.lean", 278, 296)[_fibre law_] says that a stored family's
fibres are truth values where its stored sort evaluates to zero and
strict sets where it does not; the installation
#src("whitepaper/Fragment/InstallInd.lean", 150, 163)[proves it] from the construction of
@sec:ind-model. The redex is not the point, so the major lies in its
domain, a strict fibre. So the major is not the point, its own
reduction claim applies, and the constructor application it reduces
to is not the point and lies in the same fibre. Hence it fits the
constructor's telescope by the argument of @sec:iota
(#src("whitepaper/Fragment/Sound.lean", 1309, 1323)[the case's proof]). This covers every
redex on `Nat`, `List`, `Bool` and the like.

*A family that may be a proposition.* This is the certified case.
#src("whitepaper/Fragment/Rules.lean", 292, 347)[The rule] makes the
three comparisons of @sec:iota and checks the constructor application:
#tax[the constructor's levels, parameters and index expressions are
compared with the recursor's, and every parameter and field of the
constructor application is inferred by full inference and compared
with the constructor's domain]. At a valuation where the family is a
proposition the constructor's value is the point
(#src("whitepaper/Fragment/Sound.lean", 1003, 1012)[a constructor of a family in `Prop`]),
and an application whose head is the point constrains none of its
arguments. So a field can lie outside its domain in a well-denoted
major. The reduct applies the minor premise to that field, and is
then not well-denoted although the redex is
(#src("whitepaper/Fragment/EtaIota.lean", 681, 692)[a witness], in which the
minor is a graph over ${pt}$ and the field is not the point). This is
the second kind of check of the certification tax (@sec:tax). Other checkers
skip it for the reason they skip the first: in a well-typed major the
fields are well-typed. The major premise itself needs no check. By the
model's
#src("whitepaper/Fragment/EnvModel.lean", 250, 276)[_major-premise law_], wherever the recursor's
domain holds the point as the major, the redex or the constructor is
the point (#src("whitepaper/Fragment/InstallIota.lean", 1046, 1056)[its proof]: a fibre holding the point is a
truth value, so the family is a proposition there). In that case the
reduced constructor application is the point, as the major is.

*K.* A block whose sort is `Prop`, with one constructor, which has no
fields (`Eq`, `HEq`, `True`), is _K-like_, and its rule is flagged.
#src("whitepaper/Fragment/Rules.lean", 493, 527)[Its step] fires on any major whose type
is right, with no constructor in sight. The reduct is the rule's
right-hand side at the recursor's parameters, motive and minors
alone. There is no certificate and no comparison, and the major is
not reduced. What remains is Lean's type check: the major's inferred
type reduces to the family at some arguments, and the constructor
fabricated at their parameters has a type definitionally equal to it.
That check decides whether the step is taken; no claim consumes it.
The model's #src("whitepaper/Fragment/EnvModel.lean", 188, 214)[_K law_] says that at _any_
values fitting the recursor's whole telescope, the major's included,
an application that is not the point equals the right-hand side at
the values before the indices. The installation
#src("whitepaper/Fragment/InstallIota.lean", 981, 1002)[proves it] by inversion of the least fixed
point. The major's value lies in the fibre at the recursor's
parameters and indices, a member of a fibre is a constructor value
reaching those indices, and with one constructor and no fields that
value and those indices are determined. The proof uses neither the
family's sort nor the elimination level, so the law holds for every
one-constructor block without fields; the `Prop` condition is Lean's.

For a structure, @sec:ext-eta shows a further way to fire $iota$
without a certificate, through the projections of the major.

#real[
  The checker decides the case with one level test per redex: whether
  the constructor's family is
  #src("ConLeche/Kernel/CoreDefs.lean", 85, 93)[never a proposition]
  at the levels the rule compares with, read off the sort recorded for
  the family when it was installed. A K rule and a family that is never
  a proposition fire with no check; every
  #src("ConLeche/Kernel/CoreDefs.lean", 102, 104)[other rule] is the
  certified case, as in the fragment.
]

== Consistency <sec:consistency>

An environment is #src("whitepaper/Fragment/Consistency.lean", 36, 50)[_accepted_] when it is built from the empty
environment by the two steps of §3 and §4: a definition that
passes its checks, or an inductive block that passes its checks and
is installed. (A third step, a theorem stored as its statement, joins
in @sec:modular.)
An accepted environment is closed: #src("whitepaper/Fragment/Consistency.lean", 54, 59)[every stored term mentions only stored constants]. This is what
@thm:install-def and the construction of @sec:ind-model
assumed of the environment they extend.

#theorem(name: "Every accepted environment has a model")[
  For every model of the extended theory, every accepted environment
  #src("whitepaper/Fragment/Consistency.lean", 62, 79)[has a model in it]
  (#src("ConLeche/MainTheorem.lean", 99, 102)[con-leche's main theorem]).
] <thm:accepted-model>

#proof[
  By induction on the acceptance. The empty environment has a model;
  a definition step is @thm:install-def; a block step is the
  construction of @sec:ind-model, #src("whitepaper/Fragment/Install.lean", 176, 181)[assembled]: law 1 is its
  membership claims, law 2 has no new instance, and law 3 is
  @thm:iota.
]

#real[
  The block step is one theorem,
  #src("ConLeche/Model/Inductives/DeclBlockStep.lean", 70, 75)[the install of a block],
  read off the checker's run stage by stage.
]

#corollary(name: "No proof of an empty proposition")[
  Let $I$ be an inductive type with no constructors, no parameters,
  no indices and no level parameters, installed in an accepted
  environment. Then #src("whitepaper/Fragment/Consistency.lean", 139, 149)[no closed term $e$ has] $tack e => I$; in
  particular no stored constant has type $I$
  (#src("whitepaper/Fragment/Consistency.lean", 155, 159)[at the block `inductive False : Prop`]\;
  #src("ConLeche/Model/Fold.lean", 308, 315)[as in con-leche]).
] <cor:consistency>

#proof[
  Take a model of the environment, by @thm:accepted-model, and read
  law 1 for the block's recursor at the valuation that sends every
  level to $0$. Its type is then
  $ forall (C : forall (t : I). thin Prop). thin forall (t : I). thin C thick t, $
  the elimination principle of an empty type, read as a
  proposition, and law 1 puts the recursor's set in what it denotes.
  If $e$ had $tack e => I$, @cor:closed would put $lden e rden$ into
  $lden I rden$. Take for $C$ the abstraction over $lden I rden$ that
  is constantly the empty truth value: it lies in the motive's domain,
  so the recursor applied to $C$ and $lden e rden$ lies in $C dot.op
  lden e rden$, the empty truth value: a member of the empty set.
  The proof uses only that a model exists, not how it was built. (The
  construction of @sec:ind-model also makes $lden I rden$ empty
  outright, as the least fixed point of an operator with no step.)
]

#real[
  The real theorem differs in two ways. Its checker does not read
  `False` from the stream but installs it from a built-in copy and
  rejects a stream that declares it differently (likewise `Eq`,
  `Nat` and a few others, @sec:left-out), so the main theorem can
  name `False` and say that it denotes the empty set and `Eq` set
  equality, with no hypothesis about the stream (#overview(1)); and
  its acceptance is the run of a program,
  #src("ConLeche/Model/Fold.lean", 238, 240)[the declaration fold],
  rather than a relation, so a bridge theorem turns each accepting
  run into the derivations §3 and §4 consume (@sec:left-out). The
  argument in between is the one above.
]
