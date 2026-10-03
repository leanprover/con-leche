#import "../lib.typ": *

// Notation local to this file, matching §2–§4.
#let PW = $italic("pw")$
#let never = $sans("never")$
#let always = $sans("always")$
#let Sort = $sans("Sort")$
#let zn = $sans("zeroness")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
#let tag = $op("tag")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

= What extensionality gives for free <sec:ext>

The official kernel has a few rules of definitional equality that the
fragment does not have: reduction of a recursor on a proof that is
not a constructor application (K-like reduction), η for structures,
and unit-likeness. @sec:left-out lists them among the omissions; this section
says what adding them would cost. The answer is one case of the
master induction each, and no new idea. In the model, each rule is a
consequence of what the values _are_: a proof is the point, a
function is the graph of its applications, a constructor value is a
tagged tuple of its fields, and a member of an inductive family is a
value one constructor step produces. Every one of these is a
statement of the form "a set is determined by its parts", and each is
either an extensionality law of the assumed set theory or follows
directly from one. (η for functions, which the fragment already has, is the
same law at graphs: a member of a function space is
#src("whitepaper/Fragment/Lib.lean", 92)[the graph of its
applications], and §2 proved its case.) Below, each rule is stated in
words, then the argument against the assumed laws, then, set off,
the real proof's case.

Recall what @sec:ind sets up. A constructor application $c thick arrow(p)
thick arrow(f)$ of a block whose family is type-valued denotes
a #src("whitepaper/Fragment/IndLib.lean", 49, 63)[tagged tuple]
$tag(i, chevron.l lden f_1 rden, ..., lden f_n rden chevron.r)$ — the
#src("whitepaper/Fragment/IndCommon.lean", 212, 214)[constructor's number $i$], then its fields — and
the family at parameters and indices denotes
#src("whitepaper/Fragment/IndSem.lean", 1309, 1312)[the least set closed
under the constructor steps], so that
#src("whitepaper/Fragment/IndSem.lean", 1329, 1336)[a member of the
family is a tagged tuple that one constructor step produces] from
members of the field domains (this is the fixed-point equation of §4,
#src("whitepaper/Fragment/LfpSet.lean", 137, 141)[read from left to
right]). When the family is proposition-valued — the binders of the
constructors' types, whose bodies are the family, are annotated
$ann(zn(u))$ for the result sort $Sort u$, and that datum holds at
$phi$ — the family denotes
#src("whitepaper/Fragment/IndSem.lean", 585, 588)[a truth value]
instead: the constructor step's tuple is not stored, only whether some
such tuple exists, and #src("whitepaper/Fragment/IndSem.lean", 1390, 1394)[a
member of the family, like a constructor application, is the point].
Tuples and tags are injective
(#src("whitepaper/Fragment/IndLib.lean", 52)[tuples],
#src("whitepaper/Fragment/IndLib.lean", 59)[tags]) and a tagged
value is #src("whitepaper/Fragment/IndLib.lean", 63)[$!= pt$].

== Proof irrelevance and propositional extensionality <sec:ext-irrel>

These two are not rules that need adding; they are built into the
model, and §2 used the first already. A proposition denotes a
#src("whitepaper/Fragment/Lib.lean", 115, 121)[truth value], a subset of
${pt}$, so any two proofs of any two propositions denote the same
set — the proof-irrel case of @thm:sound, which
#src("ConLeche/Model/Rules/DefEqSound.lean", 309, 316)[never compared the two propositions]. And two
propositions that imply each other have
#src("whitepaper/Fragment/Lib.lean", 146, 147)[the same truth value], by extensionality of sets: that is Lean's
axiom `propext`, which therefore
#src("ConLeche/Model/AxiomMem.lean", 414, 422)[holds in the model].

== K-like reduction <sec:ext-k>

*The rule.* Take an inductive proposition with one constructor whose
only arguments are the block's parameters — `Eq` is the example that
matters: `Eq.refl a : Eq a a` has no field of its own. Its recursor
normally fires only when the major premise reduces to a constructor
application. Under Lean's K-like rule it fires on _any_ major $h$ of
the right type: the checker reads $h$'s type, reduces it to the family
at some parameters $arrow(p)$ and indices, fabricates the constructor
application $c thick arrow(p)$, checks that this application's type is
definitionally equal to $h$'s type — for `Eq` this is the comparison
of the two endpoints, $a equiv b$ — and then reduces as if $h$ were
$c thick arrow(p)$. For `Eq.rec` this is what makes a cast along a
proof of $a = a$ compute even when the proof is a variable.

*In the model.* The family is a proposition, so its fibre at
$arrow(p)$ and any indices is a truth value, and the rule is best
read as a reduction step $h red c thick arrow(p)$ on the major, after
which the ordinary $iota$ rule fires on a constructor application.

#lemma(name: "K")[
  Let $h$ and $c thick arrow(p)$ be well-denoted, each denoting a
  member of a truth value. Then
  $lden h rden = lden c thick arrow(p) rden$, so the step
  $h red c thick arrow(p)$ preserves the denotation and the semantic
  invariant.
] <lem:k>

#proof[
  A member of a truth value is
  #src("whitepaper/Fragment/Lib.lean", 129, 130)[the point]; both
  sides are one. The reduct's semantic invariant is the hypothesis.
]

The checker's type comparison is not idle. It puts the fabrication
into the recursor's _own_ fibre — for `Eq`, it is the comparison
$a equiv b$ — which is what the $iota$ rule's spine check on
the reduct needs; and the inference of the fabrication's type is what
makes it well-denoted. Both are premises of @lem:k, not steps of its
proof.

#real[
  The rule is stated exactly so, as a reduction of the stuck major
  to the fabrication
  (#src("ConLeche/Rules/Rel.lean", 225, 244)[the rescue]), and
  #src("ConLeche/Model/Rules/IotaSound.lean", 505, 506)[its case]
  identifies the two values by proof irrelevance; no theorem about
  the block is consulted.
]

== η for structures <sec:ext-eta>

*The rule.* A _structure_ is a block with one constructor `mk`, no
indices, no recursive field, and a type-valued family.
The official kernel equates any $s$ of the structure type with the
constructor applied to $s$'s projections: $s equiv$ `mk` $arrow(p)
thick s.1 dots s.n$. The check is that $s$'s type reduces to the
structure at the parameters $arrow(p)$, and compares each field of
the constructor application with the corresponding projection of
$s$. The fragment has no projection terms (@sec:left-out); read $s.i$ below as
the projection defined through the recursor, `S.rec` $(lambda
arrow(f). thin f_i) thick s$, whose value is the $i$-th component of
the tuple by the ι law — or as a primitive projection, whose
interpretation reads the component directly. The argument is the
same either way.

#lemma(name: "structure η")[
  Let $s$ denote a member of the structure's family at $arrow(p)$,
  and let $f_i$ denote the $i$-th component of that member's tuple
  for each $i$. Then $lden$ `mk` $arrow(p) thick f_1 dots f_n rden =
  lden s rden$.
] <lem:eta-struct>

#proof[
  By the fixed-point equation, the member $lden s rden$ is a value one
  constructor step produces: $lden s rden = tag(0, chevron.l x_1, ...,
  x_n chevron.r)$ for some $x_1, ..., x_n$ in the field domains. There
  is only one constructor, so the tag is $0$. Tuples and tags are
  injective, so "the $i$-th component of $lden s rden$" is a function
  of $lden s rden$, and it is $x_i$; that is what $f_i$ denotes. The
  constructor application denotes $tag(0, chevron.l lden f_1 rden, ...,
  lden f_n rden chevron.r) = tag(0, chevron.l x_1, ..., x_n chevron.r)$, the
  same set.
]

Nothing was proved about the structure: the equation is what "member
of the family" means, read from left to right, plus the fact that a
tuple determines its components. In the soundness case the checker's
field comparisons deliver $lden a_i rden = lden s.i rden$ for the
fields $a_i$ the constructor was actually applied to, and the lemma
does the rest. A block declared in `Prop` is never granted the rule;
where an instance of a `Sort u` structure happens to be a
proposition, both sides are the point, and the law's proposition case
covers it.

#real[
  The checker has the rule as
  #src("ConLeche/Rules/Rel.lean", 431, 434)[a certificate on the fields],
  with
  #src("ConLeche/Model/Rules/DefEqSound.lean", 321, 323)[its soundness case],
  and uses the same certificate to rescue a recursor stuck on a
  non-constructor $s$
  (#src("ConLeche/Model/Rules/IotaSound.lean", 584, 585)[the η rescue]).
  Whether a type has the rule at all is decided once, at its install,
  from its shape — one constructor, no index, not a proposition, in a
  block where no constructor is recursive — and
  #src("ConLeche/Kernel/Inductives/BlockInstall.lean", 67, 80)[recorded with the type]\;
  and the law itself is established there too, not at the use. It is
  the η law of the structure's _projection table_ — the record of
  its fields' types that the checker stores for every
  one-constructor, index-free type (@sec:left-out, "Projections")
  (#src("ConLeche/Model/Inductives/FixKit.lean", 804, 805)[a member is the constructor at the parameters and its own projections]),
  proved when
  #src("ConLeche/Model/Inductives/BlockStageTables.lean", 10, 12)[the checker stores the table],
  by the argument above on the tagged tuple.
]

== Unit-likeness <sec:ext-unit>

*The rule.* A block with one constructor, no indices and no fields —
`PUnit`, or at `Prop` the proposition `True` — has, up to
definitional equality, one element: the checker equates any two terms
whose types reduce to it.

#lemma(name: "unit-likeness")[
  If $s$ and $t$ denote members of the family of such a block, at the
  same parameters, then $lden s rden = lden t rden$.
] <lem:unit>

#proof[
  When the family is type-valued, @lem:eta-struct with $n = 0$:
  each member is $tag(0, chevron.l chevron.r)$, the one tagged empty
  tuple. When it is proposition-valued, the family is a truth value
  and both members are the point.
]

The two regimes are the two shapes a "set with at most one member"
takes in the model, and the lemma is the same sentence in each.

#real[
  The checker has the rule for
  #src("ConLeche/Rules/Rel.lean", 463, 468)[any stored unit-like family],
  with
  #src("ConLeche/Model/Rules/DefEqSound.lean", 698, 699)[its soundness case].
  Unit-likeness is recorded at the install like η (one constructor,
  no index, no field, in a block where no constructor is recursive),
  and the law is established there from the fixed point
  (#src("ConLeche/Model/Inductives/FixKit.lean", 1754, 1755)[the fibre is the one tagged empty tuple]).
  Neither `PUnit` nor `True` is special to the checker: both are
  installed like any other block.
]
