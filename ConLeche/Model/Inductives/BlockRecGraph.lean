module

public import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecIdxConv

public section

/-!
# The recursor model at the run: ONE graph producer

The endpoint's regime premise
(`BlockRecPre` at every level assignment and base frame) is produced
here by ONE theorem, `graphRecPre_core`, from the graph kit
(`GraphRecKit`, `SetModel/GraphRec.lean`; its family candidate
`famCandG_hCand`, `Semantics/Tower/BlockRecTower.lean`).  No level or
sort split reaches the candidate: the only sort-dependent fact is the
kit's `huniq` (§4), and it is the kernel's elimination guard read
three ways.

* **Majors** (§1): the classes' tagged elements at a prefix spine —
  `blockRecIs`/`blockRecCr`.
* **Decodings** (§1, `blockGraphDec`): the class, the constructor and
  the fields, which fit the constructor at the CARRIER and inject to
  the major.  A rule's own spine is one, at ANY
  sort — so the ι law never chooses a decoding.
* **Predecessors** (§1, `graphPredG`): the majors among the targets
  of the rule's guarded calls (`blockGraphCallAt`) — by DEFINITION, so no
  depth, no subterm relation, no regularity.
* **Bound and step**: the conclusion at the major (`blockRecMot`) and
  the residue at the decoding's fields and the graph's `ih` values
  (`blockGraphStep`).
* **Induction** (§5): the block's recorded LFP CLAUSE
  (`LfpClause.ind`), the property carried to every class of a member.
* **`huniq`** (§4): `ℓ = 0` — the bound is a truth value; `w ≠ 0` —
  `mkInj`; `w = 0, ℓ ≠ 0` — the counting guard leaves one constructor
  of one member and the subsingleton criterion makes its fields a
  function of the index (`blockStoredFit_srcVals_zero`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The kit's data at a block -/

section Data

/-- **The fit of a decoding, as a parameter**: the kit is
stated over a relation `fit xs c i j fs` — "the fields `fs` fit class
`c`'s constructor `j` at the index tuple `i`, at the prefix spine
`xs`, at the CARRIER".  The block's own instance is the STORED fit
(`blockStoredFitRel`) — at the carrier the hole fit is the stored fit
(`BlockModelAt.carrier`); the target check's is the lfp clause's HOLE
fit (`Target*`). -/
@[expose] def blockStoredFitRel (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (mem : Nat → Nat) (xs : List V) (c : Nat) (i : V) (j : Nat) (fs : List V) : Prop :=
  d.StoredFit ψ (consList (xs.take d.nP) ρ) i (mem c) j fs

/-- **A decoding at the prefix spine `xs`, over ANY classes**: class
`c`'s index sets `Is xs c` and injections `injX c`
are parameters, so a class may be a member of the block or a
container's instantiation (an outside major).  `u` is class `e.1`'s
tagged element built by constructor `e.2.1` from the fields `e.2.2`,
which `fit` that constructor. -/
@[expose] def graphDecG (Is : List V → Nat → V) (injX : Nat → Nat → List V → V)
    (nCt : Nat → Nat) (K : Nat) (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V)
    (u : V) (e : Nat × Nat × List V) : Prop :=
  e.1 < K ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ Is xs e.1 ∧
    fit xs e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (injX e.1 e.2.1 e.2.2)

/-- **A decoding's predecessors, over ANY classes**: the majors among
the targets the rule's guarded calls name at its fields. -/
@[expose] noncomputable def graphPredG (Is Cr : List V → Nat → V) (K : Nat)
    (call : List V → Nat → Nat → List V → V → Prop) (xs : List V) (e : Nat × Nat × List V) :
    V :=
  sep (unionSet K (Is xs) (Cr xs)) (call xs e.1 e.2.1 e.2.2)

theorem mem_graphPredG {Is Cr : List V → Nat → V} {K : Nat}
    {call : List V → Nat → Nat → List V → V → Prop} {xs : List V} {e : Nat × Nat × List V}
    {v : V} :
    v ∈ˢ graphPredG Is Cr K call xs e ↔
      v ∈ˢ unionSet K (Is xs) (Cr xs) ∧ call xs e.1 e.2.1 e.2.2 v :=
  mem_sep

/-- **The step**: the rule's residue at the decoding's fields and the
`ih` values the graph `g` supplies. -/
@[expose] noncomputable def blockGraphStep (ρ : Nat → V) (Rb0 : Nat → Nat → AnnotTerm)
    (ihv : List V → Nat → Nat → List V → V → List V) (xs : List V) (e : Nat × Nat × List V)
    (g : V) : V :=
  interp V (consList (ihv xs e.1 e.2.1 e.2.2 g) (consList (xs ++ e.2.2) ρ)) (Rb0 e.1 e.2.1)


end Data

end ConLeche.Model
