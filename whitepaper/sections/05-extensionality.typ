#import "../lib.typ": *

// Notation local to this file, matching §2–§4.
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
and unit-likeness. §6 lists them among the omissions; this section
says what adding them would cost. The answer is one case of the
master induction each, and no new idea. In the model, each rule is a
consequence of what the values _are_: a proof is the point, a
function is the graph of its applications, a constructor value is a
tagged tuple of its fields, and a member of an inductive family is a
value one constructor step produces. Every one of these is a
statement of the form "a set is determined by its parts", and each is
either an extensionality law of the assumed set theory or follows from one in a
line or two. (η for functions, which the fragment already has, is the
same law at graphs: a member of a function space is
#src("whitepaper/Fragment/Lib.lean", 92)[the graph of its
applications], and §2 proved its case.) Below, each rule is stated in
words, then the argument against the assumed laws, then the
link to the real proof's case.

Recall what §4 sets up. A constructor application $c thick arrow(p)
thick arrow(f)$ of a block whose family is not a proposition denotes
a #src("whitepaper/Fragment/IndLib.lean", 65, 78)[tagged tuple]
$tag(i, chevron.l lden f_1 rden, ..., lden f_n rden chevron.r)$ — the
constructor's number $i$, then its fields
(#src("whitepaper/Fragment/IndSem.lean", 329, 331)[fragment]) — and
the family at parameters and indices denotes
#src("whitepaper/Fragment/IndSem.lean", 323, 326)[the least set closed
under the constructor steps], so that
#src("whitepaper/Fragment/IndSem.lean", 365, 367)[a member of the
family is a tagged tuple that one constructor step produces] from
members of the field domains (this is the fixed-point equation of §4,
#src("whitepaper/Fragment/IndLib.lean", 152, 155)[read from left to
right]). When the family _is_ a proposition — the binders of the
constructors' types, whose bodies are the family, are annotated
$ann(zn(u))$ for the result sort $Sort u$, and that datum holds at
$phi$ — the family denotes
#src("whitepaper/Fragment/IndSem.lean", 84, 87)[a truth value]
instead: the constructor step's tuple is not stored, only whether some
such tuple exists, and #src("whitepaper/Fragment/IndSem.lean", 378, 381)[a
member of the family, like a constructor application, is the point].
Tuples and tags are injective
(#src("whitepaper/Fragment/IndLib.lean", 67)[tuples],
#src("whitepaper/Fragment/IndLib.lean", 74)[tags]) and a tagged
value is #src("whitepaper/Fragment/IndLib.lean", 78)[never the point].

== Proof irrelevance and propositional extensionality

These two are not rules that need adding; they are built into the
model, and §2 used the first already. A proposition denotes a
#src("whitepaper/Fragment/Lib.lean", 115, 121)[truth value], a subset of
${pt}$, so any two proofs of any two propositions denote the same
set — the proof-irrel case of @thm:sound, which never compared the
two propositions (#src("ConLeche/Model/Rules/DefEqSound.lean", 313, 320)[real proof]). And two
propositions that imply each other have
#src("whitepaper/Fragment/Lib.lean", 146, 147)[the same truth value], by extensionality of sets: that is Lean's
axiom `propext`, which the real checker accepts and
#src("ConLeche/Model/AxiomMem.lean", 484, 492)[the real model verifies] the same way.

== K-like reduction

_The rule._ Take an inductive proposition with one constructor whose
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

_In the model._ The family is a proposition, so its fibre at
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

The kernel's type comparison is not idle. It puts the fabrication
into the recursor's _own_ fibre — for `Eq`, it is the comparison
$a equiv b$ — which is what the $iota$ rule's telescope certificate on
the reduct needs; and the inference of the fabrication's type is what
makes it well-denoted. Both are premises of @lem:k, not steps of its
proof. The real checker states the rule exactly so, as a reduction of
the stuck major to the fabrication
(#src("ConLeche/Rules/Rel.lean", 225, 244)[the rescue]), and its case
(#src("ConLeche/Model/Rules/IotaSound.lean", 524, 525)[real proof])
identifies the two values by proof irrelevance; no theorem about the
block is consulted.

== η for structures

_The rule._ A _structure_ is a block with one constructor `mk`, no
indices, no recursive field, and a family that is not a proposition.
Lean's kernel equates any $s$ of the structure type with the
constructor applied to $s$'s projections: $s equiv$ `mk` $arrow(p)
thick s.1 dots s.n$. The kernel checks that $s$'s type reduces to the
structure at the parameters $arrow(p)$, and compares each field of
the constructor application with the corresponding projection of
$s$. The fragment has no projection terms (§6); read $s.i$ below as
the projection defined through the recursor, `S.rec` $(lambda
arrow(f). thin f_i) thick s$, whose value is the $i$-th component of
the tuple by the ι law — or as a primitive projection, whose
interpretation reads the component directly, as the real proof's
does. The argument is the same either way.

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
does the rest. Where the structure's instance is a proposition both
sides are the point, and the checker does not try the rule there.
The real checker has the rule as
#src("ConLeche/Rules/Rel.lean", 438, 441)[a certificate on the
fields], with its case at
#src("ConLeche/Model/Rules/DefEqSound.lean", 339, 341)[the real proof],
and uses the same certificate to rescue a recursor stuck on a
non-constructor $s$
(#src("ConLeche/Model/Rules/IotaSound.lean", 603, 604)[the η rescue]).
The law itself it establishes once per block, at the block's
install. On the native route this is the argument above, on the
tagged tower that models the block
(#src("ConLeche/Model/Inductives/FixEntryLaw.lean", 27, 28)[a member is
the constructor at the parameters and its own projections]); on the
route for mutual and nested blocks it is the firing, in the model, of
a theorem `T._model.eta` that the stream supplies and the checker has
verified
(#src("ConLeche/Kernel/Inductives/Modeled.lean", 587, 596)[the
statement shape the checker requires],
#src("ConLeche/Model/IndEtaLaw.lean", 111)[its firing]).

== Unit-likeness

_The rule._ A block with one constructor, no indices and no fields —
`PUnit`, or at `Prop` the proposition `True` — has, up to
definitional equality, one element: the checker equates any two terms
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
real checker has two rules. One is for
#src("ConLeche/Rules/Rel.lean", 425, 428)[the pinned `PUnit`], which
#src("ConLeche/Model/Rules/DefEqSoundKit.lean", 678, 680)[the real model
interprets as ${pt}$ outright], so that
#src("ConLeche/Model/Rules/DefEqSound.lean", 325, 327)[both sides denote
the point]. The other is for
#src("ConLeche/Rules/Rel.lean", 470, 475)[any stored unit-like family],
with its case at
#src("ConLeche/Model/Rules/DefEqSound.lean", 716, 717)[the real proof];
the law is established at the install, from the fixed point on the
native route (#src("ConLeche/Model/Inductives/FixZeroField.lean", 109, 112)[the
fibre is the one tagged empty tuple]) and from a verified
`T._model.unitlike` on the other
(#src("ConLeche/Model/IndUnitLaw.lean", 234)[its firing]).

== What is not free

The rules above are sound because of what the values are; the
checker's certificates enter only to put the terms into the sets the
lemmas speak about. Two things in §2 are of a different kind: the
β-step at a binder that may be a proposition, where the point
remembers no domain and the certificate is the only source of the
membership (@lem:beta-cert); and the chaining of two equalities
through a middle term, whose semantic invariant nothing supplies
(@sec:claims). Extensionality says what a set is once its parts are
known; it does not say where the parts come from.
