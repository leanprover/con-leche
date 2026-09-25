#import "../lib.typ": *

// Notation local to this file, matching §2 and §3.
#let PW = $italic("pw")$
#let never = $sans("never")$
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

Lean's kernel has a few rules of definitional equality that the
fragment does not have: reduction of a recursor on a proof that is
not a constructor application (K-like reduction), η for structures,
and unit-likeness. §5 lists them among the omissions; this section
says what adding them would cost. The answer is one case of the
master induction each, and no new idea. In the model, each rule is a
consequence of what the values _are_: a proof is the point, a
function is the graph of its applications, a constructor value is a
tagged tuple of its fields, and a member of an inductive family is a
value one constructor step produces. Every one of these is a
statement of the form "a set is determined by its parts", and each is
either an extensionality law of the library or follows from one in a
line or two. Below, each rule is stated in words, then the argument
against the laws of the library, then the link to the real proof's
case.

Recall what §3 sets up. A constructor application $c thick arrow(p)
thick arrow(f)$ of a block whose family is not a proposition denotes
a #src("whitepaper/Fragment/IndLib.lean", 65, 78)[tagged tuple]
$tag(i, chevron.l lden f_1 rden, ..., lden f_n rden chevron.r)$ — the
constructor's number $i$, then its fields — and the family at
parameters and indices denotes the least set closed under the
constructor steps, so that #src("whitepaper/Fragment/IndLib.lean", 155, 158)[a member of the family is a tagged tuple that
one constructor step produces] from members of the field domains
(this is the fixed-point equation of §3, read from left to right).
When the family _is_ a proposition — the block's binders are
annotated $ann(zn(u))$ for the result sort $Sort u$, and that datum
holds at $phi$ — the family denotes a truth value instead: the
constructor step's tuple is not stored, only whether some such tuple
exists, and a constructor application denotes the point. Tuples and
tags are injective (#src("whitepaper/Fragment/IndLib.lean", 67)[tuples],
#src("whitepaper/Fragment/IndLib.lean", 74)[tags]) and a tagged
value is #src("whitepaper/Fragment/IndLib.lean", 78)[never the point].

== Proof irrelevance and propositional extensionality

These two are not rules that need adding; they are built into the
model, and §2 used the first already. A proposition denotes a
#src("whitepaper/Fragment/Lib.lean", 47)[truth value], a subset of
${pt}$, so any two proofs of any two propositions denote the same
set — the proof-irrel case of @thm:sound, which never compared the
two propositions (#src("ConLeche/Model/Rules/DefEqSound.lean", 313, 320)[real proof]). And two
propositions that imply each other have
#src("whitepaper/Fragment/Lib.lean", 112, 113)[the same truth value], by extensionality of sets: that is Lean's
axiom `propext`, which the real checker accepts and
#src("ConLeche/Model/AxiomMem.lean", 879, 883)[the real model verifies] the same way.

== η for functions

The fragment has this rule, and §2 proved its case: a member of a
function space is #src("whitepaper/Fragment/Lib.lean", 80)[the graph
of its applications], and where the annotation says "proposition"
both sides are the point
(#src("ConLeche/Model/Rules/DefEqSound.lean", 197, 204)[real proof]).
It is listed here because the three rules below are the same law at
the other kinds of value.

== K-like reduction

_The rule._ Take an inductive proposition with one constructor whose
only arguments are the block's parameters — `Eq` is the example that
matters: `Eq.refl a : Eq a a` has no field of its own. Its recursor
normally fires only when the major premise reduces to a constructor
application. Under Lean's K-like rule it fires on _any_ major $h$ of
the right type: the kernel reads $h$'s type, reduces it to the family
at some parameters $arrow(p)$ and indices, fabricates the constructor
application $c thick arrow(p)$, checks that this application's type is
definitionally equal to $h$'s type — for `Eq` this is the comparison
of the two endpoints, $a equiv b$ — and then reduces as if $h$ were
$c thick arrow(p)$. For `Eq.rec` this is what makes a cast along a
proof of $a = a$ compute even when the proof is a variable.

_In the model._ The family is a proposition, so its fibre at
$arrow(p)$ and any indices is a truth value.

#lemma(name: "K")[
  Let $h$ and $c thick arrow(p)$ be well-denoted, both denoting
  members of fibres of a propositional family. Then
  $lden h rden = lden c thick arrow(p) rden$, and the recursor's ι
  law gives the same value on either major.
] <lem:k>

#proof[
  The major $h$ denotes a member of a truth value, hence
  #src("whitepaper/Fragment/Lib.lean", 103, 104)[the point]; so
  does the fabricated $c thick arrow(p)$, being a constructor
  application of a proposition (a proof-λ applied to arguments, and
  #src("whitepaper/Fragment/Lib.lean", 65)[the point applied to
  anything is the point]). The ι law of §3 is an equation between
  sets, stated for the recursor applied to any major that denotes a
  member of the fibre; it does not know which term supplied the
  member. So the rule's right-hand side denotes the same set whether
  the recursor is applied to $h$ or to $c thick arrow(p)$.
]

The kernel's type comparison is not idle. It is the certificate that
puts the fabricated application in the _same_ fibre as $h$ — for
`Eq`, that $a$ and $b$ denote the same set, so that the fibre
$tv(lden a rden = lden b rden)$ is inhabited and the recursor's
minor premise, which was checked at $a = a$, applies. In the
soundness case it is what makes the fabrication well-denoted with
the major's type, and after that the case is @lem:k. The real
checker reduces the stuck major to the fabrication
(#src("ConLeche/Rules/Rel.lean", 225, 244)[the rescue]) and the case
(#src("ConLeche/Model/Rules/IotaSound.lean", 524, 525)[real proof])
identifies the two values by proof irrelevance; no theorem about the
block is consulted.

== η for structures

_The rule._ A _structure_ is a block with one constructor `mk`, no
indices, and a family that is not a proposition. Lean's kernel
equates any $s$ of the structure type with the constructor applied
to $s$'s projections: $s equiv$ `mk` $arrow(p) thick s.1 dots s.n$.
The kernel checks that $s$'s type reduces to the structure at the
parameters $arrow(p)$, and compares each field of the constructor
application with the corresponding projection of $s$. The fragment
has no projection terms (§5); read $s.i$ below as the projection
defined through the recursor, `S.rec` $(lambda arrow(f). thin f_i)
thick s$, whose value is the $i$-th component of the tuple by the ι
law — or as a primitive projection, whose interpretation reads the
component directly, as the real proof's does. The argument is the
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
tuple determines its components. In the soundness case the kernel's
field comparisons deliver $lden a_i rden = lden s.i rden$ for the
fields $a_i$ the constructor was actually applied to, and the lemma
does the rest. Where the structure's instance is a proposition both
sides are the point, and the kernel does not try the rule there.
The real checker has the rule as
#src("ConLeche/Rules/Rel.lean", 438, 441)[a certificate on the
fields], with its case at
#src("ConLeche/Model/Rules/DefEqSound.lean", 339, 341)[the real proof],
and uses the same certificate to rescue a recursor stuck on a
non-constructor $s$
(#src("ConLeche/Model/Rules/IotaSound.lean", 603, 604)[the η rescue]).
The law itself it establishes once per block, at the block's
install: on the native route by the argument above, on the tagged
tower that models the block —
#src("ConLeche/Model/Inductives/FixEntryLaw.lean", 27, 28)[a member is
the constructor at the parameters and its own projections] — and on
the route for mutual and nested blocks by firing, in the model, a
theorem `T._model.eta` that the frontend generates and the checker
has verified
(#src("ConLeche/Kernel/Inductives/Modeled.lean", 587, 596)[the
theorem's pinned shape],
#src("ConLeche/Model/IndEtaLaw.lean", 111)[its firing]).

== Unit-likeness

_The rule._ A structure whose one constructor has no fields at all
— `PUnit`, or at `Prop` the proposition `True` — has, up to
definitional equality, one element: the kernel equates any two terms
whose types reduce to it.

#lemma(name: "unit-likeness")[
  If $s$ and $t$ denote members of the family of such a block, at the
  same parameters, then $lden s rden = lden t rden$.
] <lem:unit>

#proof[
  When the family is not a proposition, @lem:eta-struct with $n = 0$:
  each member is $tag(0, chevron.l chevron.r)$, the one tagged empty
  tuple. When it is, the family is a truth value and both members are
  the point.
]

The two regimes are the two shapes a "set with at most one member"
takes in the model, and the lemma is the same sentence in each. The
real checker has two rules: one for
#src("ConLeche/Rules/Rel.lean", 425, 428)[the pinned `PUnit`], whose
case is that #src("ConLeche/Model/Rules/DefEqSound.lean", 325, 327)[both
sides denote the point] (`PUnit` is modelled as ${pt}$ outright), and one
for #src("ConLeche/Rules/Rel.lean", 470, 475)[any stored unit-like
family], with its case at
#src("ConLeche/Model/Rules/DefEqSound.lean", 716, 717)[the real proof]
and the law established at the install, from the fixed point on the
native route (#src("ConLeche/Model/Inductives/FixZeroField.lean", 112, 113)[the
fibre is the one tagged empty tuple]) and from a verified
`T._model.unitlike` on the other
(#src("ConLeche/Model/IndUnitLaw.lean", 234)[its firing]).

== What is not free

The rules above are sound because of what the values are, and the
checker's certificates enter only to put the terms into the sets the
lemmas speak about. Two features of §2 are of a different kind: there
the certificate is not a convenience but the whole of the argument.
A β-step at a binder that may be a proposition needs the argument to
lie in the λ's domain, and the model cannot recover that domain —
the λ denotes the point, and the point remembers nothing
(@lem:beta-cert); the checker's inference and comparison of the
argument's type is the only source of the fact. And no rule can chain
two equalities through a middle term, because nothing supplies that
term's semantic invariant (@sec:claims). Extensionality says what a
set is once its parts are known; it does not say where the parts come
from. That is what the certificates, and the shape of the rules, are
for.
