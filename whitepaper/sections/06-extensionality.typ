#import "../lib.typ": *

// Notation local to this file, matching §2–§4.
#let Sort = $sans("Sort")$
#let red = sym.arrow.r.squiggly
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
#let tag = $op("tag")$
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

= Consequences of extensionality <sec:ext>

The official kernel has two rules of definitional equality that the
fragment does not have: η for structures, and unit-likeness.
@sec:left-out lists them among the omissions. This section shows that
adding either would cost one case of the induction of @sec:claims and
no new idea. In the model, each rule follows from what the values
are. A proof is the point, a function is the graph of its
applications, a constructor value is a tagged tuple of its fields, and
a member of an inductive family is a value that one constructor step
produces. Each of these says that a set is determined by its parts,
and each is an extensionality law of the assumed set theory or follows
directly from one. η for functions, which the fragment has, is the
same law at graphs: a member of a function space is
#src("whitepaper/Fragment/Lib.lean", 110)[the graph of its
applications], and §2 proved its case. The K rule of
@sec:iota-cases, which the fragment also has, rests on a law of the
same kind, inversion of the least fixed point.

Recall what @sec:ind sets up. A constructor application $c thick arrow(p)
thick arrow(f)$ of a block whose family is type-valued denotes
a #src("whitepaper/Fragment/IndLib.lean", 50, 64)[tagged tuple]
$tag(i, lden f_1 rden, ..., lden f_n rden)$, the
#src("whitepaper/Fragment/IndCommon.lean", 336, 338)[constructor's number $i$] followed by its fields.
The family at parameters and indices denotes
#src("whitepaper/Fragment/IndSem.lean", 1458, 1461)[the least set closed
under the constructor steps], so that
#src("whitepaper/Fragment/IndSem.lean", 1478, 1486)[a member of the
family is a tagged tuple that one constructor step produces] from
members of the field domains. This is the fixed-point equation of §4,
#src("whitepaper/Fragment/LfpSet.lean", 137, 141)[read from left to
right]. When the family is proposition-valued (its result sort
$Sort u$ has $u$ evaluating to $0$ at $phi$), the family denotes
#src("whitepaper/Fragment/IndSem.lean", 592, 595)[a truth value]
instead. The constructor step's tuple is not stored, only whether some
such tuple exists, and #src("whitepaper/Fragment/IndSem.lean", 1539, 1543)[a
member of the family, like a constructor application, is the point].
Tagged tuples are injective
(#src("whitepaper/Fragment/IndLib.lean", 53)[tuples],
#src("whitepaper/Fragment/IndLib.lean", 60)[tags]) and a tagged
tuple is #src("whitepaper/Fragment/IndLib.lean", 64)[$!= pt$].

== Proof irrelevance and propositional extensionality <sec:ext-irrel>

These two need no rule; they are built into the model, and §2 used
the first already. A proposition denotes a
#src("whitepaper/Fragment/Lib.lean", 142, 148)[truth value], a subset of
${pt}$, so any two proofs of any two propositions denote the same
set. That is the proof-irrel case of @thm:sound, which
#src("ConLeche/Model/Rules/DefEqSound.lean", 281, 283)[never compared the two propositions]. And two
propositions that imply each other have
#src("whitepaper/Fragment/Lib.lean", 173, 174)[the same truth value], by extensionality of sets. This is Lean's
axiom `propext`, which therefore
#src("ConLeche/Model/AxiomMem.lean", 297, 304)[holds in the model].

== η for structures <sec:ext-eta>

*The rule.* A _structure_ is a block with one constructor `mk`, no
indices, no recursive field, and a type-valued family.
The official kernel equates any $s$ of the structure type with the
constructor applied to $s$'s projections: $s equiv$ `mk` $arrow(p)
thick s.1 dots s.n$. The check is that $s$'s type reduces to the
structure at the parameters $arrow(p)$, and compares each field of
the constructor application with the corresponding projection of
$s$. The fragment has no projection terms (@sec:left-out). Read $s.i$
below as the projection defined through the recursor,
`S.rec` $(lambda arrow(f). thin f_i) thick s$, whose value is the
$i$-th component of the tuple by the ι law, or as a primitive
projection, whose interpretation reads the component directly. The
argument is the same either way.

#lemma(name: "structure η")[
  Let $s$ denote a member of the structure's family at $arrow(p)$,
  and let $f_i$ denote the $i$-th component of that member's tuple
  for each $i$. Then $lden$ `mk` $arrow(p) thick f_1 dots f_n rden =
  lden s rden$.
] <lem:eta-struct>

#proof[
  By the fixed-point equation, the member $lden s rden$ is a value one
  constructor step produces: $lden s rden = tag(0, x_1, ...,
  x_n)$ for some $x_1, ..., x_n$ in the field domains. There
  is only one constructor, so the tag is $0$. Tagged tuples are
  injective, so the $i$-th component of $lden s rden$ is a function
  of $lden s rden$, and it is $x_i$; that is what $f_i$ denotes. The
  constructor application denotes $tag(0, lden f_1 rden, ...,
  lden f_n rden) = tag(0, x_1, ..., x_n)$, the
  same set.
]

The lemma proves nothing specific to the structure. The equation is
what membership in the family means, read from left to right, plus
the fact that a tuple determines its components. In the soundness
case the checker's field comparisons deliver
$lden a_i rden = lden s.i rden$ for the fields $a_i$ the constructor
was actually applied to, and the lemma does the rest. A block declared
in `Prop` is never granted the rule. Where an instance of a `Sort u`
structure happens to be a proposition, both sides are the point, and
the law's proposition case covers it.

*ι through the projections.* The same law on values, that a member is
the constructor at its projections, gives a second way to fire $iota$
on a block of a structure's shape (one constructor, no indices, no
recursive field). For such a block whose instances may be
propositions, $iota$ can go through the projections of the major instead of a
constructor application:
$ S.sans("rec") thick arrow(p) thick C thick m thick x red m thick (S.p_1 thick arrow(p) thick x) dots (S.p_k thick arrow(p) thick x). $
#src("whitepaper/Fragment/EtaIota.lean", 242, 260)[This step is sound] with no certificate,
no comparison and no reduction of the major, given the plain $iota$
law and the structure-η law on values. The redex is not the point, so
the whole spine, the major included, fits the recursor's telescope
(@sec:iota). Where the structure is a proposition the major is the
point, and
#src("whitepaper/Fragment/EtaIota.lean", 402, 410)[so are its projections]
when every field's sort is `Prop` wherever the structure's is; the
reduct is then the minor at the point, which is the recursor's value
there. The step must expand the major as found, before any reduction
of it, and also when it already is a constructor application. A major
that denotes the point may reduce to a term that is not well-denoted,
and the projections of that reduct break the reduction claim
(#src("whitepaper/Fragment/EtaIota.lean", 707, 724)[the witness]).
For a structure without fields the step is K's step
(#src("whitepaper/Fragment/EtaIota.lean", 349, 356)[the reducts coincide]). The fragment
has no projections, so this step is a theorem about the claims, and
not a rule of its relations.

#real[
  The checker has the rule as Lean has it,
  #src("ConLeche/Rules/Rel.lean", 479, 490)[the constructor's fields compared with the projections of the other side],
  with
  #src("ConLeche/Model/Rules/DefEqSound.lean", 655, 657)[its soundness case].
  It uses the same law when it prepares the major premise of a
  recursor on a structure that is never a proposition at the instance.
  The major is taken as found, before any head normalisation, and the
  constructor is applied to its projections, with no further check
  (#src("ConLeche/Rules/Rel.lean", 275, 285)[the rule],
  #src("ConLeche/Model/Rules/IotaSound.lean", 721, 722)[its soundness case]).
  Only if that does not give a constructor application is the major
  head-normalised, and the same expansion is tried once more on the
  result. Whether a type has the rule at all is decided once, when it
  is installed, from its shape (one constructor, no index, not a
  proposition, in a block where no constructor is recursive), and
  #src("ConLeche/Kernel/Inductives/BlockInstall.lean", 67, 80)[recorded with the type]\;
  the law itself is established there too, not at the use. It is the
  η law of the structure's _projection table_, the record of its
  fields' types that the checker stores for every one-constructor,
  index-free type (@sec:left-out, "Projections")
  (#src("ConLeche/Model/Inductives/FixKit.lean", 720, 721)[a member is the constructor at the parameters and its own projections]).
  It is proved when
  #src("ConLeche/Model/Inductives/BlockStageTables.lean", 10, 12)[the checker stores the table],
  by the argument above on the tagged tuple.
]

== Unit-likeness <sec:ext-unit>

*The rule.* A block with one constructor, no indices and no fields,
such as `PUnit` or, at `Prop`, the proposition `True`, has one element
up to definitional equality: the checker equates any two terms whose
types reduce to it.

#lemma(name: "unit-likeness")[
  If $s$ and $t$ denote members of the family of such a block, at the
  same parameters, then $lden s rden = lden t rden$.
] <lem:unit>

#proof[
  When the family is type-valued, @lem:eta-struct with $n = 0$:
  each member is $tag(0)$, the one tagged empty
  tuple. When it is proposition-valued, the family is a truth value
  and both members are the point.
]

A set with at most one member takes one of two shapes in the model:
the singleton of the empty tagged tuple for a type-valued family, and
a truth value for a proposition-valued one. The lemma holds for both
by the same argument.

#real[
  The checker has the rule for
  #src("ConLeche/Rules/Rel.lean", 515, 520)[any stored unit-like family],
  with
  #src("ConLeche/Model/Rules/DefEqSound.lean", 293, 294)[its soundness case].
  Unit-likeness is recorded at installation, like η (one constructor,
  no index, no field, in a block where no constructor is recursive),
  and the law is established there from the fixed point
  (#src("ConLeche/Model/Inductives/FixKit.lean", 1730, 1731)[the fibre is the one tagged empty tuple]).
  Neither `PUnit` nor `True` is special to the checker: both are
  installed like any other block.
]
