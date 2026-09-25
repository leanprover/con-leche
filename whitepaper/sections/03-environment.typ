#import "../lib.typ": *

// Notation local to this file, matching §2.
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

= Adding an environment <sec:env>

§2 fixed an environment and assumed a model of it: an assignment $M$
of a set to every constant at every list of levels, and three laws
about the stored constants. This section is about where that model
comes from. The environment grows one declaration at a time — a
definition, or an inductive block with its constructors and recursor
— and each step is checked by the relations of §2. We say what the
checker checks at each step, what the checker stores, and how the
model grows with the environment so that the three laws keep holding;
the consistency corollary at the end is then two lines. The two
reduction rules that §2 deferred because they read the environment,
$delta$ and $iota$, are stated here.

== Definitions <sec:defs>

*The environment* is a list of the constants accepted so far, most
recent first
(#src("whitepaper/Fragment/Env.lean", 88, 104)[fragment],
#src("ConLeche/Kernel/Env.lean", 677)[real checker]). A stored
constant has its level parameters $arrow(p)$, its type — a closed
term over $arrow(p)$ — and its _kind_
(#src("whitepaper/Fragment/Env.lean", 45, 79)[fragment],
#src("ConLeche/Kernel/Env.lean", 461, 475)[real checker]): a
_definition_ carries a value; an _inductive type former_ carries its
parameter and index counts and the names of its constructors; a
_constructor_ names its type and carries its parameter and field
counts; a _recursor_ carries the shape of its telescope — how many
parameters, motives, minor premises and indices precede the major
premise — and its reduction rules, one per constructor, each a closed
right-hand side over the recursor's level parameters
(#src("whitepaper/Fragment/Env.lean", 30, 43)[fragment],
#src("ConLeche/Kernel/Env.lean", 249, 262)[real checker]). A name is
stored at most once. The fragment has no axioms, no theorems as
distinct from definitions, and no quotients (§5).

*The $delta$ rule.* A definition unfolds to its value at the levels
it is used at
(#src("whitepaper/Fragment/Rules.lean", 77, 83)[fragment],
#src("ConLeche/Rules/Rel.lean", 129, 133)[real checker]). With the
head rule of @sec:rules, an applied definition unfolds at its head.

#rules(
  rule(name: "δ",
    $c "stored as a definition with parameters" arrow(p) "and value" v$,
    $|arrow(ell)| = |arrow(p)|$,
    $Gamma tack c.\{arrow(ell)\} red v[arrow(p) := arrow(ell)]$),
)

*What a definition must satisfy.* Before the checker stores a
definition $c$ with parameters $arrow(p)$, type $T$ and value $v$, it
checks four things
(#src("whitepaper/Fragment/Decl.lean", 395, 405)[fragment],
#src("ConLeche/Kernel/Checker.lean", 36, 52)[real checker]): the
name is fresh; the type has a sort, $tack T => S red Sort u$; the
value's inferred type is definitionally equal to the declared type,
$tack v => T' $ and $tack T' equiv T$; and both terms are _in scope_
— closed, mentioning only stored constants, using only the level
parameters $arrow(p)$
(#src("whitepaper/Fragment/Decl.lean", 383, 387)[fragment]). All
in the empty context: stored terms are closed. The scope check is
what lets the model read a stored term without looking at anything
that is added later: the interpretation of a term depends only on
the constants it mentions, the variables below its depth and the
level parameters it uses
(#src("whitepaper/Fragment/Hygiene.lean", 364, 366)[constants],
#src("whitepaper/Fragment/Hygiene.lean", 308, 310)[variables],
#src("whitepaper/Fragment/Hygiene.lean", 420, 422)[parameters]).

*The contract between §2 and §3.* Here, once more and in full, is
what §2 assumed of the environment: #src("whitepaper/Fragment/EnvModel.lean", 163, 189)[a _model_]
is an assignment $M(c, arrow(n))$ of a set to every constant $c$ and
every list of natural numbers $arrow(n)$ — the values of its level
parameters — such that

+ #src("whitepaper/Fragment/EnvModel.lean", 167, 174)[every stored constant is a member of its type]: for every
  stored $c$ with parameters $arrow(p)$ and type $T$, at every list
  of levels $arrow(ell)$ of the right length and every valuation
  $phi$, the instantiated type $T[arrow(p) := arrow(ell)]$ is
  well-denoted and $M(c, phi(arrow(ell))) in lden T[arrow(p) := arrow(ell)] rden$;
+ #src("whitepaper/Fragment/EnvModel.lean", 175, 181)[a definition's value denotes the constant]: for a stored
  definition $c$ with value $v$, the instantiated value is
  well-denoted and $lden v[arrow(p) := arrow(ell)] rden = M(c, phi(arrow(ell)))$;
+ #src("whitepaper/Fragment/EnvModel.lean", 182, 189)[every recursor rule satisfies its $iota$ law], a statement
  about sets that @sec:ind-model spells out.

The real proof's carrier has the same three laws among others
(#src("ConLeche/Model/Annot/EnvModelM.lean", 71, 100)[the invariant],
#src("ConLeche/Model/Annot/Laws.lean", 436, 439)[the $iota$ law]).
The laws mention the model only at the _stored_ terms — the types,
the values, the rules' right-hand sides — and quantify over sets
where a use site would have terms. That is deliberate: when a fresh
constant is added, no stored term mentions it, so every old law is
read off the extended assignment exactly as off the old one, and
nothing has to be re-proved. The empty environment has a model
trivially: any assignment, and three laws with nothing to say
(#src("whitepaper/Fragment/EnvModel.lean", 191, 196)[fragment]).

#theorem(name: "Installing a definition")[
  If the environment has a model and the definition $c$ passes the
  checks above, then the environment extended with $c$ has a model.
  // TODO-LINK: Install.lean once it lands
  (Fragment: `Install.lean`; #src("ConLeche/Model/Install.lean", 446, 448)[real proof].)
] <thm:install-def>

#proof[
  Let $M$ be the model. Define $M'$ as $M$ on every old constant and,
  at $c$ and a list $arrow(n)$, as the set $lden v rden$ read at the
  valuation that sends $arrow(p)$ to $arrow(n)$ — $v$ is closed and
  uses no other parameter, so no $rho$ and no other part of $phi$
  enters. The old laws hold for $M'$ because no stored term mentions
  $c$. For the new constant, @cor:closed and the second claim of
  @thm:sound do the work: from $tack v => T'$ the value and $T'$ are
  well-denoted and $lden v rden in lden T' rden$; from $tack T => S$
  the type is well-denoted; so the second claim applies to
  $tack T' equiv T$ and gives $lden v rden in lden T rden$. This holds
  at every valuation, and instantiating the level parameters is the
  same as changing the valuation (@sec:interp), so it holds at every
  $arrow(ell)$: that is law 1, and law 2 is the definition of $M'$
  at $c$. Law 3 has no new instance.
]

The proof is two lines because everything difficult was done in §2:
the checks a definition passes are exactly the premises of the
corollary, and the corollary's conclusion is exactly law 1. The same
shape recurs for inductive blocks — the checker infers the generated
types like any other terms, and @thm:sound turns each inference into
a membership — with one genuinely new piece of work, the $iota$ law.

== Inductive types: what is checked <sec:ind-checks>

An inductive block declares a family of types by its constructors.
The fragment takes single, non-mutual, non-nested blocks — the
real checker's "fixpoint route"
(#overview(5)) — with parameters, indices, and constructors whose
fields may be recursive or reflexive. The block is given by a
_specification_
(#src("whitepaper/Fragment/Decl.lean", 166, 189)[fragment],
#src("ConLeche/Kernel/Inductives/NativeParts.lean", 179, 192)[real checker]):

- a name $I$ and level parameters $arrow(p)$;
- a _parameter_ telescope $(x_1 : P_1) dots (x_k : P_k)$ and, under
  it, an _index_ telescope $(y_1 : J_1) dots (y_m : J_m)$; the
  parameters are the same for every constructor and every field, the
  indices vary;
- a result sort $Sort u$: the family has type
  $forall arrow(x) : arrow(P) thin ann(never). thin forall arrow(y) : arrow(J) thin ann(never). thin Sort u$;
- constructors $c_1, dots, c_n$, each with a list of _fields_ and,
  under the parameters and the fields, the index expressions
  $arrow(e)_j$ of its result $I thick arrow(x) thick arrow(e)_j$.

A field is one of three kinds
(#src("whitepaper/Fragment/Decl.lean", 129, 142)[fragment],
#src("ConLeche/Kernel/Inductives/NativeParts.lean", 62, 70)[real checker]):
_ordinary_, with a domain that does not mention $I$; _recursive_, with
domain $I thick arrow(x) thick arrow(e)$ — a member of the family
being defined, at the block's own parameters and some index
expressions; or _reflexive_, with domain
$forall arrow(z) : arrow(A). thin I thick arrow(x) thick arrow(e)$ — a
function into the family. This is the strictly positive shape, and
the only one the fragment admits: no field's domain mentions $I$
anywhere else (in the fragment, the specification's pieces are
scope-checked in the environment _before_ $I$ is added, so they
cannot mention it at all — #src("whitepaper/Fragment/Decl.lean", 411, 424)[the scope of a field];
the real checker classifies the normalised domains,
#src("ConLeche/Kernel/Inductives/NativeParts.lean", 97, 113)[positivity]).

Reflexive fields matter to the model. A tree type with a constructor
$sans("node") : (Nat -> sans("Tree")) -> sans("Tree")$ has nodes with
countably many children, so its values are not built up in finitely
many stages from the constructors: the set of all trees is not the
union of "trees of depth $k$" over $k in NN$, because a node may have
children of every depth. Such a type is _large_ — it lives in a
universe strictly above $Nat$ — and its model cannot be an ordinary
inductive construction inside $cal(U)_1$. @sec:ind-model says how the
fragment avoids the issue and how the real proof settles it.

*The generated declarations.* From the specification the checker
generates the types of the former, the constructors and the
recursor, and the recursor's rules; nothing about them is read from
the input (the real checker reads the stream's records, recognises the
block's shape, generates the same declarations, and rejects a record
that is not the generated one — #overview(5)). The former's type is
the one displayed above; a constructor's type is
$forall arrow(x) : arrow(P) thin ann(PW). thin forall arrow(f) : arrow(F) thin ann(PW). thin I thick arrow(x) thick arrow(e)_j$
with the annotation
#src("whitepaper/Fragment/Decl.lean", 205, 208)[$ann(PW) = zn(u)$]
on every binder: every body ends in the family, which is a
proposition exactly when $u$ is zero
(#src("whitepaper/Fragment/Decl.lean", 256, 263)[the two generators]).
The recursor is best shown on an example.

#example(name: [$Nat$])[
  The block $Nat$ has no parameters, no indices, sort $Sort 1$, and
  two constructors: $zero$ with no field and $succ$ with one recursive
  field. So $ann(PW) = zn(1) = ann(never)$, and the generated
  constructor types are $zero : Nat$ and
  $succ : forall (n : Nat) thin ann(never). thin Nat$. The recursor
  eliminates into $Sort u$ for a fresh level parameter $u$ — _large
  elimination_, see below — and its generated type is

  $
    NatRec.\{u\} : & forall (M : forall (t : Nat) thin ann(never). thin Sort u) thin ann(q). \
    & forall (z : M thick zero) thin ann(q). \
    & forall (s : forall (n : Nat) thin ann(q). thin forall (h : M thick n) thin ann(q). thin M thick (succ thick n)) thin ann(q). \
    & forall (t : Nat) thin ann(q). thin M thick t
  $

  with #src("whitepaper/Fragment/Decl.lean", 209, 213)[$ann(q) = zn(u) = ann(whenZero \{u\})$] on
  every binder: each body ends in $M thick dots$, a member of
  $Sort u$, so it is a proposition exactly when $u$ is instantiated
  to zero. $M$ is the _motive_; $z$ and $s$ are the _minor premises_,
  one per constructor, each taking the constructor's fields and, for
  every recursive field, an _inductive hypothesis_ $h$ — the motive at
  that field; $t$ is the _major premise_. The recursor has two rules,
  one per constructor: the major premise built by the constructor
  reduces to the minor premise applied to the fields and to the
  recursor's own value at each recursive field,

  $
    NatRec.\{u\} thick M thick z thick s thick zero & red z \
    NatRec.\{u\} thick M thick z thick s thick (succ thick n) & red s thick n thick (NatRec.\{u\} thick M thick z thick s thick n).
  $

  What the checker stores as the second rule's right-hand side is
  the closed term
  $ lambda M thick z thick s thick n. thin s thick n thick (NatRec.\{u\} thick M thick z thick s thick n); $
  the $iota$ rule applies it to the recursor's arguments and the
  constructor's fields, and $beta$ does the rest.
] <ex:nat>

The general shape is the same with parameters, indices and
reflexive fields added: the motive takes the indices and a member of
the family, $forall arrow(y) : arrow(J) thin ann(never). thin forall (t : I thick arrow(x) thick arrow(y)) thin ann(never). thin Sort ell$;
a minor premise for $c_j$ takes the fields, then one inductive
hypothesis per recursive or reflexive field — at a reflexive field
$f : forall arrow(z) : arrow(A). thin I thick arrow(x) thick arrow(e)$
the hypothesis is $forall arrow(z) : arrow(A) thin ann(q). thin M thick arrow(e) thick (f thick arrow(z))$
— and ends in $M thick arrow(e)_j thick (c_j thick arrow(x) thick arrow(f))$;
the recursor takes the parameters, the motive, the minors, the indices
and the major, and ends in $M thick arrow(y) thick t$. The fragment's
generators are
#src("whitepaper/Fragment/Decl.lean", 265, 267)[the motive],
#src("whitepaper/Fragment/Decl.lean", 277, 290)[an inductive hypothesis],
#src("whitepaper/Fragment/Decl.lean", 297, 306)[a minor premise],
#src("whitepaper/Fragment/Decl.lean", 313, 318)[the recursor's type]
and #src("whitepaper/Fragment/Decl.lean", 338, 345)[a rule's right-hand side]
(real checker: #src("ConLeche/Kernel/Inductives/NativeParts.lean", 349, 361)[the type],
#src("ConLeche/Kernel/Inductives/NativeParts.lean", 368, 386)[a rule]); the
only real complication in them is de Bruijn bookkeeping, which the
named form hides. The annotation on the recursor's binders is
$ann(q) = zn(ell)$ where $ell$ is the _elimination level_: $u$ for a
large eliminator, $0$ for a small one.

*The elimination rule.* Into which sorts may the motive land? For a
family in $Sort u$ with $u$ never zero — a family of _types_ — the
recursor eliminates into any $Sort ell$, $ell$ a fresh level
parameter: _large elimination_. For a family of _propositions_ the
rule is stricter. In the model every proof is the point, so a
recursor applied to a proof cannot see which constructor built it
or with which fields; a recursor into types would have to return one
value for all of them. Lean allows
large elimination out of a proposition only under the _subsingleton
criterion_: the block has at most one constructor, and every field
of that constructor is either itself a proposition or occurs among
the constructor's result indices — so that a proof of $I thick arrow(x) thick arrow(e)$
determines every field: the propositional ones are all the same
proof, and the others can be read off the indices. Otherwise the
motive lands in $Prop$, $ell = 0$: _small elimination_. In the
fragment the criterion is
#src("whitepaper/Fragment/Decl.lean", 450, 457)[a condition per field]
plus #src("whitepaper/Fragment/Decl.lean", 491)[the constructor count], required of a large
eliminator on a family whose sort _may_ be zero
(#src("whitepaper/Fragment/Decl.lean", 446, 448)[never zero: $1 <= u$ at every valuation]);
the real checker runs the same two checks
(#src("ConLeche/Kernel/Inductives/SumInstall.lean", 124, 138)[per field],
#src("ConLeche/Kernel/Inductives/NativeInstall.lean", 584, 588)[the count]).

Here the annotation datum reappears. "This field is a proposition"
is a question about the field's sort $v$, and the checker answers it
with the level oracle: #ann[$v eq.dot 0$]. The same oracle decides
the universe bound on the fields of a family of types — every
field's sort is at most $u$, #src("whitepaper/Fragment/Decl.lean", 439, 444)[or the family is a proposition and there is no bound], which is
Lean's impredicativity of $Prop$ — and whether the family's sort is
never zero. In §2 the coloured datum decided how to interpret each
binder; here the same kind of zero-ness question decides what the
recursor may do. The two are linked: the recursor's binders are
annotated $ann(q) = zn(ell)$, and the model of @sec:ind-model has to
account for the recursor in every regime the annotation can put it
in.

#example(name: [an indexed proposition with large elimination])[
  Let $P : forall (n : Nat) thin ann(never). thin Prop$ have one
  constructor $mk : forall (n : Nat) thin ann(whenZero \{\}). thin P thick n$
  — a family of propositions, indexed by a number, with one ordinary
  field $n$ that is not a proposition but occurs in the result's
  index. The subsingleton criterion holds, so the recursor may
  eliminate into $Sort u$:

  $
    PRec.\{u\} : & forall (M : forall (n : Nat) thin ann(never). thin forall (t : P thick n) thin ann(never). thin Sort u) thin ann(q). \
    & forall (h : forall (n : Nat) thin ann(q). thin M thick n thick (mk thick n)) thin ann(q). \
    & forall (n : Nat) thin ann(q). thin forall (t : P thick n) thin ann(q). thin M thick n thick t
  $

  with one rule, $PRec.\{u\} thick M thick h thick n thick (mk thick n') red h thick n'$.
  Note the two occurrences of the index: $n$ is the recursor's index
  argument, $n'$ the constructor's field. @sec:ind-model returns to
  this example.
] <ex:P>

*The checks.* A block is accepted when
(#src("whitepaper/Fragment/Decl.lean", 459, 492)[fragment],
#src("ConLeche/Kernel/Inductives/NativeInstall.lean", 617)[real checker]):
its names are distinct and fresh; the specification is in scope
(positivity included); the generated former's type has a sort in the
current environment; each generated constructor's type has a sort in
the environment holding the former, and every field's domain has a
sort $v$ that respects the universe bound and, where a large
eliminator asks it, the subsingleton criterion; the constructor count
respects the elimination rule; and the generated recursor's type has
a sort in the environment holding the former and the constructors.
Each "has a sort" is an inference $tack T => S$ (with $S$ reducing to
a sort) of §2, in the empty context — so the generated types are
checked exactly like a definition's, and the $forall$ rule of
@sec:rules checks each generated annotation against the sort it
computes for the body. What is stored is the former, the constructors
and the recursor, with its rules
(#src("whitepaper/Fragment/Decl.lean", 353, 375)[fragment]). The
rules are generated and stored, not checked: they mention the
recursor itself, and Lean's kernel infers no rule either. That the
rules are _sound_ is the model's business — it is law 3 of the
contract, and the next subsection proves it.

== Inductive types: the model <sec:ind-model>

The model of a block has three parts: the sets the family's fibres
denote, the sets the constructors denote, and the set the recursor
denotes. Each is stated against a small extension of §2's library.

*The library, extended.* Beyond the laws of @sec:lib the inductive
section uses
#src("whitepaper/Fragment/IndLib.lean", 50, 78)[four more]:
_separation_ — the members of a set that satisfy a property form a
set, and a separated part of a member of a positive universe is a
member of it; _transitivity_ of the positive universes — a member of
a member is a member; _tuples_ $tuple(x_1, dots, x_k)$, injective and
universe-closed; and _tags_ $tag(j, x)$, a set with a number
attached, injective, universe-closed and never the point. That is the
whole extension. Notably absent is any law about least fixed points.

*Least fixed points cost nothing.* The family of a block is the least
fixed point of an operator: "a member is a constructor applied to
fields that are members". In the fragment this is not a set
construction at all. The operator acts on _predicates_, and the least
fixed point of a monotone operator $Phi$ on predicates is
#src("whitepaper/Fragment/IndLib.lean", 138, 141)[a definition]:
$lfp(Phi)(a)$ holds when every predicate closed under $Phi$ holds at
$a$. That it is closed, that it is a fixed point and that it
supports induction are #src("whitepaper/Fragment/IndLib.lean", 147, 165)[ten lines of proof] — the
definition quantifies over all predicates, which the ambient logic's
impredicative $Prop$ permits. Separation then turns a fibre of the
predicate into a set: the family at given parameters and indices is
the set of members of the universe $cal(U)_(phi(u))$ that satisfy the
predicate, and it lies in the next universe because a separated part
of a member does. Nothing more is needed, for reflexive fields as
for the others: the universe bound on the fields is what puts every
tagged tuple in $cal(U)_(phi(u))$. The real proof works inside the
set theory instead and pays for it: its least fixed point is
#src("ConLeche/SetTheory/Derive/LfpFam.lean", 64, 71)[an intersection of closed families], which needs a closed
family in the universe to exist — for finitary blocks
#src("ConLeche/SetModel/Iter.lean", 8, 24)[the $omega$-iterate], and
for blocks with reflexive fields, where no countable iteration
reaches a fixed point, #src("ConLeche/SetModel/Container.lean", 598, 600)[a theorem about containers] that builds
the closed family from tree codes. This is the largest single piece of
the real model, and the fragment shows it is not intrinsic to the
argument: what the argument needs of a least fixed point is its
fixed-point equation and its induction principle, and those are
available for free one level up.

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
recursive field's domain is a fibre of $Z$; a reflexive field's is a
function space into fibres of $Z$, and the function space is
monotone in its fibres
(#src("whitepaper/Fragment/IndLib.lean", 114, 128)[fragment]), so
$Phi$ is monotone and has a least fixed point. Then, in the regime
where $ann(PW)$ does not hold at $phi$ — the family is a family of
types —

$
  lden I rden dot arrow(X) dot arrow(Y) = { x in cal(U)_(phi(u)) mid(|) lfp(Phi)(arrow(Y), x) },
$

and the constructor $c_j$ denotes the function that takes the
parameters and the fields and returns $tag(j, tuple(arrow(F)))$. In
the regime where $ann(PW)$ holds — a family of propositions — the
fibre is the truth value $tv(exists x. thin lfp(Phi)(arrow(Y), x))$,
"some constructor reaches these indices", and every constructor
denotes the point.
// TODO-LINK: IndSem.lean once it lands
(Fragment: `IndSem.lean`. In the real proof
the constructors are #src("ConLeche/SetModel/TaggedSum.lean", 72, 76)[tagged pairs] of
#src("ConLeche/SetModel/TupleTower.lean", 87)[nested pairs], the same two regimes
#src("ConLeche/SetModel/TaggedSum.lean", 109, 121)[in one definition].)

This is where the two regimes of §2 are decided for a whole family
at once, by the one datum $ann(PW)$ stored on the constructors'
binders. A member of a fibre in the first regime is a tagged tuple
and carries its constructor and its fields; a member in the second is
the point and carries nothing. The difference will matter in a moment.

*The recursor.* Fix values $M$ for the motive and $arrow(S)$ for the
minor premises. The recursor's value on a member of the family is
determined by the rules: on $tag(j, tuple(arrow(F)))$ it must be
$S_j$ applied to $arrow(F)$ and to the inductive hypotheses — the
recursor's own value at each recursive field, and at a reflexive
field the function sending $arrow(z)$ to the recursor's value at
$f dot arrow(z)$. That this equation has exactly one solution is
the _recursion theorem_, and in the fragment it is proved by the
same device as the family: the recursor's _graph_ — the relation
"the value at $(arrow(Y), x)$ is $v$" — is the least fixed point of
the operator that reads the equation as a step; it is total by
induction over the family, and single-valued by induction over the
graph, using that tags and tuples are injective. The recursor
denotes the graph of the resulting function, curried over the
parameters, the motive, the minors, the indices and the major — a
member of its generated type, which is law 1 for the recursor.
// TODO-LINK: IndSem.lean once it lands
(Fragment: `IndSem.lean`;
#src("ConLeche/SetModel/RecGraph.lean", 232, 235)[the real proof's recursion theorem].)
When the elimination level $ell$ is zero the recursor's type is a
proposition, the recursor and every minor premise denote the point,
and there is nothing to construct.

*Inversion is what $iota$ needs.* Before the $iota$ law, look at what
the $iota$ rule knows and what the model has to supply. The rule fires
on $r.\{arrow(u)\} thick arrow(a) thick t$ where $arrow(a)$ are the
recursor's parameters, motive, minors and indices, and the major $t$
reduces to a constructor application $c_j.\{arrow(u)'\} thick arrow(a)' thick arrow(f)$;
the reduct is the rule's right-hand side at $arrow(u)$, applied to
the parameters, motive and minors from $arrow(a)$ and to the fields
$arrow(f)$
(#src("whitepaper/Fragment/Rules.lean", 84, 156)[fragment],
#src("ConLeche/Rules/Rel.lean", 179, 224)[real checker]). Its
premises, besides the lookups, are two _telescope certificates_ and
three _comparisons_:

- the recursor's spine, with the reduced major in the major's place,
  is checked against the recursor's stored type: each argument's type
  is inferred and compared with the domain it meets, the domains
  instantiated along the spine; the constructor's spine is checked
  against the constructor's stored type the same way;
- the constructor's levels $arrow(u)'$ are oracle-equal to the last
  levels of $arrow(u)$ (a large eliminator carries one extra level in
  front); the constructor's parameters $arrow(a)'$ are definitionally
  equal to the recursor's; and the index expressions of the
  constructor's result type at $arrow(a)' thick arrow(f)$ — the
  _residual_ of its telescope — are definitionally equal to the
  recursor's index arguments.

The certificates are, in the real checker, walks of their own
(§5); the fragment folds them into the rule. By @thm:sound each
certificate becomes a _fit_ of values to the stored telescope
(#src("whitepaper/Fragment/Sound.lean", 77, 84)[fragment]), and each
comparison an equality of sets
(#src("whitepaper/Fragment/Sound.lean", 201, 206)[the $iota$ case]).
So the $iota$ law is stated on values, with the fits and the
equalities as premises
(#src("whitepaper/Fragment/EnvModel.lean", 102, 161)[fragment],
#src("ConLeche/Model/Annot/Laws.lean", 436, 439)[real proof]):

#definition(name: [the $iota$ law of a rule])[
  For every valuation, all levels $arrow(u)$, $arrow(u)'$ of the
  right lengths, all values $arrow(A)$ for the arguments before the
  major and $arrow(F)'$ for the constructor's parameters and fields:
  if $arrow(A)$ followed by $lden c_j rden dot arrow(F)'$ fit the
  recursor's type at $arrow(u)$, $arrow(F)'$ fit the constructor's
  type at $arrow(u)'$, the levels $arrow(u)'$ evaluate as the last of
  $arrow(u)$, the parameters among $arrow(F)'$ _are_ those among
  $arrow(A)$, and the constructor's index expressions read under
  $arrow(F)'$ _are_ the index values among $arrow(A)$ — then
  $ lden r rden dot arrow(A) dot (lden c_j rden dot arrow(F)') = lden R_j rden dot (arrow(A) "before the indices") dot (arrow(F)' "after the parameters"), $
  and the right-hand side $R_j$ is well-denoted with a well-formed
  application chain along those values.
] <def:iota-law>

The second conjunct is what makes the reduct well-denoted, as the
first claim of @thm:sound demands; the first is the equation. The
$iota$ case of @thm:sound is then a translation: certificates to
fits, comparisons to equalities, the reduced major's value for the
argument's, and the law
(#src("whitepaper/Fragment/Sound.lean", 207, 245)[fragment],
#src("ConLeche/Model/Rules/IotaSound.lean", 87)[real proof]).

#theorem(name: [the $iota$ law holds])[
  Every rule of the recursor of an accepted block satisfies its
  $iota$ law in the model of @sec:ind-model.
  // TODO-LINK: Install.lean once it lands
  (Fragment: `Install.lean`; real proof:
  #src("ConLeche/Model/Inductives/DeclNative.lean", 62, 66)[the whole install].)
] <thm:iota>

#proof[
  _The family of types_ ($ann(PW)$ does not hold). The recursor's fit
  puts the major's value $lden c_j rden dot arrow(F)'$ in the family
  at the _recursor's_ parameters and indices, the values among
  $arrow(A)$. That value is $tag(j, tuple(arrow(F)))$ with
  $arrow(F)$ the fields among $arrow(F)'$; and here is the point of
  the least fixed point: a member of the fibre is a step from
  members (#src("whitepaper/Fragment/IndLib.lean", 155, 158)[the fixed-point equation, read backwards]), so it is
  $tag(j', tuple(arrow(F)''))$ for some constructor $j'$ and fields
  $arrow(F)''$ fitting $c_(j')$'s field telescope _at the recursor's
  parameters_, with the recursor's indices as the values of
  $c_(j')$'s index expressions at $arrow(F)''$. Tags and tuples are
  injective, so $j' = j$ and $arrow(F)'' = arrow(F)$. This
  _inversion_ is everything the right-hand side needs: it puts each
  field in its domain at the recursor's own parameters, which is
  what the $beta$ steps inside $R_j$ require (@lem:beta-cert, with
  the membership supplied), and the recursion theorem's equation at
  $tag(j, tuple(arrow(F)))$ is the rule's equation. The three
  comparisons are not used.

  _The family of propositions_ ($ann(PW)$ holds). Now the major's
  value is the point, and the recursor's fit says only that the fibre
  at the recursor's indices is inhabited: the point carries no
  constructor, no fields, no parameters and no indices. Inversion
  still applies — some constructor reaches those indices with some
  fields $arrow(F)''$ — but nothing connects $arrow(F)''$ to the
  fields $arrow(F)'$ the right-hand side is applied to. This is
  what the three comparisons are for. When the elimination level is
  zero both sides of the equation are the point and there is nothing
  to prove. When it is not, the block passed the subsingleton
  criterion: one constructor, so $j' = j$; and each field is a
  proposition, whose value is the point on both sides, or occurs
  among the constructor's result indices, whose values the index
  comparison identifies with the recursor's index arguments on both
  sides — the parameter comparison and the level comparison do the
  same for the parameters and levels the fields' domains are read
  at. So $arrow(F)'' = arrow(F)$ after all, and the recursion
  theorem's equation is again the rule's.
]

*Why the comparisons are load-bearing.* Return to @ex:P. Its
recursor's fit for the spine $M, h, 7, t$ says that $lden t rden$
is a member of $lden P thick 7 rden$; when $P thick 7$ is true that
fibre is ${pt}$, and $lden mk thick 5 rden = pt$ is a member of it.
So without the index comparison the $iota$ law — a statement about
values, which cannot see that the checker would have compared
$P thick 5$ with $P thick 7$ and refused — would have to equate
$lden PRec rden dot M dot h dot 7 dot pt$ with $h dot 5$, and, by the
same token with $mk thick 7$, with $h dot 7$; and $h dot 5 = h dot 7$
does not hold for every $h$. The recursor's set is a function of its
arguments and has one value at index $7$; the rule may fire only
where the constructor's index expressions agree with the recursor's
indices, which is exactly what the comparison certifies. In the
regime of types the comparison is redundant — the tagged tuple
carries its indices — and Lean's kernel, which type-checks the
major's type against the recursor's, never needs it as a separate
step; a semantic proof does, because a definitional equality between
two propositions, $P thick 5 equiv P thick 7$, is an equality of
truth values and says nothing about $5$ and $7$. The fragment's
first draft of the $iota$ rule carried the certificates alone, and
this example is what put the comparisons back.

== Consistency <sec:consistency>

An environment is _accepted_ when it is built from the empty
environment by the two steps of this section: a definition that
passes its checks, or an inductive block that passes its checks and
is installed.
// TODO-LINK: Consistency.lean once it lands
(Fragment: `Consistency.lean`; the real checker's declaration fold is
#src("ConLeche/Model/Fold.lean", 225, 227)[folded over the same way].)

#theorem(name: "Every accepted environment has a model")[
  For every model of the extended library, every accepted environment
  has a model in it.
  // TODO-LINK: Consistency.lean once it lands
  (Fragment: `Consistency.lean`; real proof:
  #src("ConLeche/MainTheorem.lean", 96, 99)[the main theorem].)
] <thm:accepted-model>

#proof[
  By induction on the acceptance. The empty environment has a model;
  a definition step is @thm:install-def; a block step is the
  construction of @sec:ind-model, whose laws 1 and 2 come from the
  checks in the same way as for a definition, and whose law 3 is
  @thm:iota.
]

#corollary(name: "No proof of an empty proposition")[
  No accepted environment stores a constant whose type is an
  inductive proposition with no constructors — a constant $c$ of type
  $I$, where $I$ is stored as a type former of sort $Prop$ with no
  parameters, no indices and no constructors.
  // TODO-LINK: Consistency.lean once it lands
  (Fragment: `Consistency.lean`;
  #src("ConLeche/Model/Fold.lean", 308, 315)[real proof].)
] <cor:consistency>

#proof[
  Take the model of @thm:accepted-model. By law 1, $M(c)$ is a member
  of $lden I rden$. The operator of a block with no constructors has
  no step, so the empty predicate is closed under it and the least
  fixed point is empty; the fibre is the truth value of a false
  proposition, the empty set. Nothing is a member of it.
]

The real theorem differs in two ways. Its checker does not read
`False` from the stream but installs it from a built-in copy and
rejects a stream that declares it differently — likewise `Eq`, `Nat`
and a few others (§5) — so the main theorem can name `False` and say
that it denotes the empty set and `Eq` set equality, with no
hypothesis about the stream (#overview(1)); and its acceptance is
the run of a program, the declaration fold, rather than a relation,
so a bridge theorem turns each accepting run into the derivations
this section consumes (§5). The argument in between is the one
above.
