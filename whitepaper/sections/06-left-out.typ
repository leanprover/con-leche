#import "../lib.typ": *

= What we left out

The fragment of §2–§5 is the real checker with everything removed that
does not change the shape of the argument. This section lists what was
removed, with one sentence on what the real proof does about it and a
link to where it lives; then it describes where the real proof's
architecture differs from the fragment's even on the features they
share.

== Dropped features

#left-out[Projections][Lean's primitive projection `e.i`, the `i`-th
field of a structure value. The real checker #src("ConLeche/Rules/Rel.lean", 166, 175)[reduces a projection of a
constructor application to that field] and #src("ConLeche/Rules/Rel.lean", 560, 570)[infers its type from
the structure's stored projection table]\; in the model a structure
value is a nested pair and a projection reads a component, which #src("ConLeche/Model/ProjInstall.lean", 411, 415)[the
install of a structure's projection functions] establishes.]

#left-out[Mutual and nested inductive types][The real checker installs
natively only what the fragment does: a single, non-mutual, non-nested
block. For a mutual or nested block the frontend generates, in-process,
#src("ConLeche/Frontend/InModel.lean", 41)[an explicit model of the block] — a tag type and one auxiliary indexed
family — together with theorems proving the recursor's reduction rules. The generated declarations
are checked by the declaration fold — `checkDecls`, the loop that
installs and checks the declarations one after another — like any
other, and the block is then #src("ConLeche/Kernel/Inductives/Modeled.lean", 794)[installed against them].]

#left-out[Nat and String literals, and the fast Nat path][Numerals and
strings are terms of their own; the checker expands a literal to its
constructor form when reduction needs it
(#src("ConLeche/Rules/Rel.lean", 136, 138)[natLit],
#src("ConLeche/Rules/Rel.lean", 143, 145)[strLit]) and folds #src("ConLeche/Rules/Rel.lean", 148, 151)[`Nat.succ`] and #src("ConLeche/Rules/Rel.lean", 155, 160)[the
binary `Nat` operations] on literals with machine arithmetic. The folding is sound only for
the operations as the toolchain defines them, so the checker compares
each stream's definition against #src("ConLeche/Kernel/NatOpPins.lean", 8, 21)[a pinned copy] and the model
#src("ConLeche/Model/NatEqs.lean", 1099, 1103)[establishes the operations' recurrences] from that comparison.]

#left-out[Quotients][`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and the
axiom `Quot.sound` are installed from #src("ConLeche/Kernel/Basis/Quot.lean", 8, 14)[a built-in pin] and modelled by #src("ConLeche/SetTheory/Derive/Quot.lean", 69, 71)[the
set-theoretic quotient of a set by a relation], for which the pinned
constants are #src("ConLeche/Model/BasisQuot.lean", 2224, 2228)[shown to be members of their types].]

#left-out[Pinned blocks][In the fragment `False` is whatever empty
proposition the stream declares. The real checker does not read
`False`, `Eq`, `Nat`, `PUnit`, `Empty` or `Quot` from the stream: it
installs each from a hand-written copy of the toolchain's declaration
(#src("ConLeche/Kernel/Basis/False.lean", 38, 40)[`False`, for instance],
#src("ConLeche/Kernel/Basis/Builder.lean", 8, 15)[the builder]) and rejects a
stream that declares them differently, which is how the main theorem
can name `False` and `Eq` and say what they denote.]

#left-out[Axioms][The fragment has none. The real checker accepts
exactly Lean's three standard axioms: `propext` and `Classical.choice`,
each #src("ConLeche/Kernel/StdAxioms.lean", 10, 17)[pinned to the toolchain's statement] and each #src("ConLeche/Model/AxiomMem.lean", 879, 883)[true in the
model] — `propext` by the extensionality of truth values, `choice` by
choice in the meta-logic — and `Quot.sound` as
part of the pinned `Quot` block above. Any other axiom record declines
the stream, with two tolerated exceptions: a declared but unused
`sorryAx` installs nothing, and Lean's compiler-trust axioms are
accepted as pinned definitions of their own types.]

#left-out[Theorems and opaques][The fragment has definitions only. The
real checker never unfolds a theorem or an opaque — #src("ConLeche/Rules/Rel.lean", 130, 133)[only a definition
unfolds] — which is what
makes the `And` rescue below necessary.]

#left-out[K-like reduction][A recursor of a proposition with one
field-less constructor, such as `Eq.rec`, fires on a proof that is not
a constructor application: the checker #src("ConLeche/Rules/Rel.lean", 225, 244)[fabricates the constructor
application] from the proof's type and equates the two by proof
irrelevance. §5 shows this
follows from the extensionality of the model.]

#left-out[Structure η and unit-likeness][#src("ConLeche/Rules/Rel.lean", 438, 441)[A constructor applied to the
projections of `b` is definitionally equal to `b`], and #src("ConLeche/Rules/Rel.lean", 470, 475)[any two terms of a
structure type with one field-less constructor are equal]
(#src("ConLeche/Rules/Rel.lean", 425, 428)[unitLike])\; the real proof takes the
two laws from theorems about the installed type
(#src("ConLeche/Model/IndEtaLaw.lean", 111)[η],
#src("ConLeche/Model/IndUnitLaw.lean", 234)[unit-likeness]), and §5 derives both from
extensionality.]

#left-out[The `And` rescue][A concession to the fact that this checker
never unfolds a theorem, unlike Lean's kernel, which still does: at a
stuck proof `h` of `A ∧ B` — which older elaborators emit for a case
split on a conjunction — the recursor #src("ConLeche/Rules/Rel.lean", 287, 307)[fires on `And.intro h.1 h.2`],
fabricated and certified the way the K rescue is.]

#left-out[`let`][The fragment has no `let`. The real checker's
#src("ConLeche/Kernel/Core.lean", 1852, 1881)[annotation pass], which runs once when a declaration enters, replaces
every `let x := v; b` by `b[x := v]`, so no later stage ever sees one.]

#left-out[The infer-only grade][The real checker infers types at #src("ConLeche/Rules/Rel.lean", 77, 82)[two
grades]: the full grade of the
fragment, and an "infer-only" grade used inside reduction and the
equality test on terms that were checked once already, which #src("ConLeche/Rules/Rel.lean", 551, 554)[skips the
argument check] at an application whose binder is annotated #ann[never] and the domain check at a
`λ`. Beside it sits #src("ConLeche/Rules/Rel.lean", 410, 412)[a fast path for proof irrelevance] that reads the
annotations at the two terms' heads instead of inferring their types. Both are licensed by the
semantic invariant of §2: at a #ann[never] binder the domain can be read off the
function's set, and two terms whose head annotations say #ann[always a
proposition] both denote the one proof point.]

#left-out[Fuel, memo tables, the executable checker and its bridge
theorem][In the fragment the relations are the checker. The real
checker is a program with fuel, and a theorem of its own — #src("ConLeche/Verify/Rules/Bridge.lean", 25, 28)[the
_bridge_] — says that every accepting run of it, at any fuel, yields a
derivation in the relations\; the checker the
binary runs is a further clone with memo tables, proved to #src("ConLeche/Verify/Cached/SimC.lean", 10, 15)[simulate the
fuelled one]. The
subsection below says how these fit together.]

#left-out[The two-phase parallel fold][#src("ConLeche/Cached/Installed.lean", 450, 455)[The fold] installs every
declaration first and then checks the recorded declarations one by one,
each against the prefix of the environment it was installed at\; the binary runs the
second phase on #src("ConLeche/Cached/Installed.lean", 350, 361)[a pool of workers] whose results are reassembled in
record order, so its verdict is the fold's. #src("ConLeche/Verify/Cached/MainC.lean", 50, 53)[The proof reads an
accept of the fold] as an environment in which every declaration was
checked where it was installed, which is what the one-declaration-at-a-time
argument of §3 and §4 needs.]

#left-out[The erased intermediate layer][The paper interprets annotated
terms directly. The real proof reads a checker term into a second,
erased term language first and interprets that; the subsection below
describes it.]

== How the real proof differs from the fragment

*Free variables carry their types.* The paper uses named variables and a
context; the fragment's Lean uses de Bruijn indices and a context. The
real checker keeps no context at all. When it opens a binder it
substitutes a free variable that carries its own type,
#src("ConLeche/Kernel/Expr.lean", 344, 346)[`fvar idx type`], identified by the depth at which it was opened\; so a variable is never
looked up, the relations are indexed by the opening depth in place of a
context, and two free variables are #src("ConLeche/Rules/Rel.lean", 356, 357)[compared by depth alone]. Stored types are closed
terms, and the statement's relation reads them with de Bruijn indices
under binders, with no opening at all.

*An erased intermediate layer.* The real proof does not interpret the
checker's terms directly. It first reads a term into an erased language,
#src("ConLeche/Semantics/Syntax.lean", 66, 90)[`AnnotTerm`]: de Bruijn
indices, sorts at concrete numbers (the level valuation already
applied), built-in constants at concrete levels, and at every binder
the sort of the body as a number — the annotation and the level
valuation combined into one numeral. That reading, #src("ConLeche/Model/Annot/Bit.lean", 153, 156)[`denoteMeta`], is partial only for
syntactic reasons — a `let`, an unknown constant, a wrong number of
levels, a projection with no table — and it reads the annotation without
checking it: the check is the semantic invariant, which the theorem below
demands of the reading. The interpretation
#src("ConLeche/Semantics/Interp.lean", 150, 160)[`interp`] then maps
the erased term to a set, dispatching on the numeral at each binder.
The paper folds the two steps into one denotation that reads the
coloured datum at the level valuation directly.

*Six relations, not three, and a second grade.* Beside reduction,
definitional equality and inference the real description has three
list-walking relations: #src("ConLeche/Rules/Rel.lean", 576, 587)[the certification of an argument spine against
a binder telescope],
#src("ConLeche/Rules/Rel.lean", 590, 594)[pairwise definitional equality], and #src("ConLeche/Rules/Rel.lean", 599, 601)[the per-field
certificates of structure η] at a family of projection functions. A rule with a premise
about a list needs a relation of its own in a mutual block; the paper
inlines them into the rules that use them. Inference also carries a
grade index, the infer-only grade above.

*The bridge and the recomposition.* Because the real checker is a
program, its proof has three parts where the paper has one. #src("ConLeche/Verify/Rules/Bridge.lean", 25, 28)[The bridge] turns an accepting
run at any fuel into a derivation — one induction on fuel, each checker
site landing on one rule. #src("ConLeche/Model/Rules/Sound.lean", 43, 44)[The soundness] is the paper's
induction: one structural induction over the six relations, each case a
lemma about one rule, never mentioning the implementation. #src("ConLeche/Model/Rules/Recompose.lean", 49, 54)[The
recomposition] is
a few lines per claim: bridge the run, apply the soundness, and hand
the result to the declaration fold.

*The statement over `Denotes`.* The main theorem is not stated over the
erased layer and `interp` but over #src("ConLeche/Denotes.lean", 132, 135)[`Denotes`], a relation on the checker's
own terms with no intermediate language, one rule per syntax form,
written to be read in one sitting; and over the structure #src("ConLeche/Denotes.lean", 270, 290)[`Model`] built on it. #src("ConLeche/Model/Denotes.lean", 222, 228)[A theorem]
connects the two: wherever the erased reading exists and satisfies the
semantic invariant, its interpretation is a `Denotes`-denotation of the term. The paper's theorem is
the model side directly.

*The cached checker and its simulation.* The core the binary runs is #src("ConLeche/Cached/CoreC.lean", 8, 11)[a
clone of the pure one] over a term representation that carries a
precomputed hash in every node, with memo tables for reduction,
equality and inference. #src("ConLeche/Verify/Cached/SimC.lean", 10, 15)[A simulation proof] shows
that every successful run of the cached core is a successful run of the
pure fuelled core at some fuel, with the memo tables' invariant
preserved\; the main
theorem #src("ConLeche/Verify/Cached/MainC.lean", 50, 53)[composes it with the fold's soundness].

*The frontend.* Between the export file and the declaration fold sit a
parser and a few transformations of the parsed list: the pinned
declarations are moved to the front; the projection functions of
structures the native install does not serve are #src("ConLeche/Frontend/ProjRec.lean", 283, 284)[rewritten to recursor
form]\; and the models
of mutual and nested blocks are #src("ConLeche/Frontend/InModel.lean", 41)[generated]. Everything generated is
checked, so a wrong generation cannot be accepted; but the theorem is
about the list the fold receives, and that the list means the same as
the export is a review claim about small, inspectable rewrites, not a
theorem. The fragment has no frontend: its stream is its environment.
