module

public import ConLeche.Model.Inductives.MutualShadow
public import ConLeche.Model.Inductives.FixRealChains
public import ConLeche.Model.Inductives.FixAssemblyKit
public import ConLeche.Semantics.Tower.MutualLeafFacts
public section

/-!
# The auxiliary family's chains (task #278, M2.4)

The mutual block's members are fibres of ONE fixpoint-route family at
the tag — the tagged union of the members' index towers
(`Semantics/Tower/MutualLeafI.lean`).  This module spells that
family's chain data off the constructors' readings
(`MutualData.lean`) and proves what the fixpoint route's premise
theorem (`fixPre_of`) asks of it:

* the chain data: the REAL chains `mutFss` (constructor `J`'s field
  entries as read at the members' leaves), the X-source chains
  `mutFss0` — the real ones with `Sort 0` at the recursive slots,
  which is all the X-chain ever reads there (`xEntry` replaces a
  recursive slot by `slotXI`), so the X-chains mention no member —
  the recursive positions `mutRss`, the reflexive telescopes
  `mutTlss`, and the TAGGED index expressions `mutEss'`/`mutEiss'`
  (`mutualEss`/`mutualEiss`: a member occurrence `T_{m'} p⃗ e⃗` is the
  auxiliary family at `⟨inj m' ⟨e⃗⟩⟩`);
* the walk's inputs at every constructor (`ChainFacts` at the
  auxiliary family, `mutualChainFacts_at`) and, from them,
  `XChainsOk`, `FixChainsOkI` and `ChainsRealI` for the whole block
  (`mutualChainFacts_of`).

The one new step over the fixpoint route is the TAG: a slot's index
fit is `SpineFit ρp [tagTyAV] [inj m' ⟨e⃗⟩]`, which is the member's
own fit through `tagTuple_mem`, and a tagged tuple's grading is
`tagTupleAV_facts` at the frame the slot is read in.  That the tagged
tuples mention no recursive slot is `NoBVar_liftN`: their head is the
member's tupler lifted past every field read so far.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chain data -/

variable (nP n : Nat)

/-- Constructor `J`'s REAL field chain: its field entries as read at
the members' leaves. -/
@[expose] def mutFss (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J => ((dsF J ψ).drop nP).map (·.2.2)

/-- Constructor `J`'s X-SOURCE chain: the real one with `Sort 0` at
the recursive slots — the X-chain reads a recursive slot as the
family's (`xEntry`), so this chain mentions no member. -/
@[expose] def mutFss0 (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J =>
    shadowFs nP (kindsOf (ksF J)) (nFs J) (((dsF J ψ).drop nP).map (·.2.2))

/-- The recursive positions, per constructor. -/
@[expose] def mutRss (ksF : Nat → List (RecFieldKind × Nat)) : List (List Bool) :=
  (List.range n).map fun J => rsOf (kindsOf (ksF J))

/-- The reflexive telescopes, per constructor. -/
@[expose] def mutTlss (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (ψ : Name → Nat) : List (List (List (Nat × Nat × AnnotTerm))) :=
  (List.range n).map fun J => tssF J ψ

/-- The constructors' OWN index readings, per constructor. -/
@[expose] def mutEss0 (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  (List.range n).map fun J => esF J ψ

/-- The recursive slots' OWN index readings, per constructor. -/
@[expose] def mutEiss0 (eissF : Nat → (Name → Nat) → List (List AnnotTerm)) (ψ : Name → Nat) :
    List (List (List AnnotTerm)) :=
  (List.range n).map fun J => eissF J ψ

/-- Each constructor's own member. -/
@[expose] def mutMems (memF : Nat → Nat) : List Nat := (List.range n).map memF

/-- Each constructor's field count. -/
@[expose] def mutNFs (nFs : Nat → Nat) : List Nat := (List.range n).map nFs

/-- Each constructor's recursive slots' target members. -/
@[expose] def mutTgts (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat) :
    List (List Nat) :=
  (List.range n).map fun J => (List.range (nFs J)).map (tgtAt (ksF J))

variable {nP n}

omit [SetTheory V] in
theorem mutFss_length {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat} :
    (mutFss nP n dsF ψ).length = n := by simp [mutFss]

omit [SetTheory V] in
theorem mutFss_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {ψ : Name → Nat}
    {J : Nat} (hJ : J < n) :
    (mutFss nP n dsF ψ).getD J [] = ((dsF J ψ).drop nP).map (·.2.2) := by
  simp [mutFss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutFss0_length {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {ψ : Name → Nat} :
    (mutFss0 nP n dsF ksF nFs ψ).length = n := by simp [mutFss0]

omit [SetTheory V] in
theorem mutFss0_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) :
    (mutFss0 nP n dsF ksF nFs ψ).getD J []
      = shadowFs nP (kindsOf (ksF J)) (nFs J) (((dsF J ψ).drop nP).map (·.2.2)) := by
  simp [mutFss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutRss_getD {ksF : Nat → List (RecFieldKind × Nat)} {J : Nat} (hJ : J < n) :
    (mutRss n ksF).getD J [] = rsOf (kindsOf (ksF J)) := by
  simp [mutRss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutTlss_getD {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {ψ : Name → Nat} {J : Nat} (hJ : J < n) :
    (mutTlss n tssF ψ).getD J [] = tssF J ψ := by
  simp [mutTlss, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutEss0_length {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} :
    (mutEss0 n esF ψ).length = n := by simp [mutEss0]

omit [SetTheory V] in
theorem mutEss0_getD {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) : (mutEss0 n esF ψ).getD J [] = esF J ψ := by
  simp [mutEss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutEiss0_length {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} :
    (mutEiss0 n eissF ψ).length = n := by simp [mutEiss0]

omit [SetTheory V] in
theorem mutEiss0_getD {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat}
    {J : Nat} (hJ : J < n) : (mutEiss0 n eissF ψ).getD J [] = eissF J ψ := by
  simp [mutEiss0, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutMems_getD {memF : Nat → Nat} {J : Nat} (hJ : J < n) :
    (mutMems n memF).getD J 0 = memF J := by
  simp [mutMems, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutNFs_getD {nFs : Nat → Nat} {J : Nat} (hJ : J < n) :
    (mutNFs n nFs).getD J 0 = nFs J := by
  simp [mutNFs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]

omit [SetTheory V] in
theorem mutTgts_getD {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat} {J i : Nat}
    (hJ : J < n) (hi : i < nFs J) :
    ((mutTgts n ksF nFs).getD J []).getD i 0 = tgtAt (ksF J) i := by
  simp [mutTgts, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ,
    List.getElem?_range hi]

/-! ## The tagged index expressions -/

/-- The constructors' TAGGED index expressions. -/
@[expose] def mutEss' (W : Nat) (Idss : List (List AnnotTerm)) (memF nFs : Nat → Nat)
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) : List (List AnnotTerm) :=
  mutualEss W Idss (mutMems n memF) (mutNFs n nFs) (mutEss0 n esF ψ)

/-- The recursive slots' TAGGED index expressions. -/
@[expose] def mutEiss' (W : Nat) (Idss : List (List AnnotTerm))
    (ksF : Nat → List (RecFieldKind × Nat)) (nFs : Nat → Nat)
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm)) (ψ : Name → Nat) :
    List (List (List AnnotTerm)) :=
  mutualEiss W Idss (mutTgts n ksF nFs) (mutTlss n tssF ψ)
    (mutEiss0 n eissF ψ)

omit [SetTheory V] in
theorem mutEss'_getD {W : Nat} {Idss : List (List AnnotTerm)} {memF nFs : Nat → Nat}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} {J : Nat} (hJ : J < n) :
    (mutEss' (n := n) W Idss memF nFs esF ψ).getD J []
      = [tagTupleAV W (memF J) (nFs J) Idss (esF J ψ)] := by
  unfold mutEss' mutualEss
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [mutEss0_length]; exact hJ)]
  simp only [Option.map_some, Option.getD_some]
  rw [mutMems_getD hJ, mutNFs_getD hJ, mutEss0_getD hJ]

omit [SetTheory V] in
theorem mutEss'_length {W : Nat} {Idss : List (List AnnotTerm)} {memF nFs : Nat → Nat}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ : Name → Nat} :
    (mutEss' (n := n) W Idss memF nFs esF ψ).length = n := by
  unfold mutEss' mutualEss
  rw [List.length_map, List.length_range, mutEss0_length]

omit [SetTheory V] in
theorem mutEiss'_getDJ {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) (hlen : (eissF J ψ).length = nFs J) :
    (mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []
      = (List.range (nFs J)).map fun i =>
          [tagTupleAV W (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length) Idss
            ((eissF J ψ).getD i [])] := by
  unfold mutEiss' mutualEiss
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by rw [mutEiss0_length]; exact hJ)]
  simp only [Option.map_some, Option.getD_some]
  rw [mutEiss0_getD hJ, hlen]
  apply List.map_congr_left
  intro i hi
  rw [mutTgts_getD hJ (List.mem_range.mp hi), mutTlss_getD hJ]

omit [SetTheory V] in
theorem mutEiss'_getD {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J i : Nat}
    (hJ : J < n) (hi : i < nFs J) (hlen : (eissF J ψ).length = nFs J) :
    ((mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []).getD i []
      = [tagTupleAV W (tgtAt (ksF J) i) (i + ((tssF J ψ).getD i []).length) Idss
          ((eissF J ψ).getD i [])] := by
  rw [mutEiss'_getDJ hJ hlen, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

omit [SetTheory V] in
theorem mutEiss'_lengthJ {W : Nat} {Idss : List (List AnnotTerm)}
    {ksF : Nat → List (RecFieldKind × Nat)} {nFs : Nat → Nat}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)} {ψ : Name → Nat} {J : Nat}
    (hJ : J < n) (hlen : (eissF J ψ).length = nFs J) :
    ((mutEiss' (n := n) W Idss ksF nFs tssF eissF ψ).getD J []).length = nFs J := by
  rw [mutEiss'_getDJ hJ hlen, List.length_map, List.length_range]

end ConLeche.Model
