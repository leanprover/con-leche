module

import ConLeche.Semantics.Tower.MutualLeafI
public import ConLeche.SetTheory.Derive.LfpSplit
public import ConLeche.Model.Inductives.MutualStageFormer
import ConLeche.Model.Inductives.BlockRep
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.BlockRepOne
public section

/-!
# `tupleLfpAV` — the `k`-ary least fixed point as a DERIVED term former (task #315, M4)

The uniform block model records a block as the least pre-fixed TUPLE of an
operator on tuples of families (`lfpTuple`).  The term language has
one fixpoint primitive, `lfpFam`, over a single index set; rather than
add a tuple primitive (28 `interp`-unfolding sites, every tier above),
the `k`-ary fixed point is a DERIVED term former with an API — the
`Std.HashMap`/`PropWhen` pattern: the representation is private to
this module, consumers see the former, its semantic operator and
their laws only.

**The API.**  For a block of `k` members with index telescopes `Idss`
(at the parameter frame) and constructors in GLOBAL order — each with
its member `mems`, field count `nFs`, recursive-field targets `tgts`,
recursive flags `rss`, reflexive telescopes `tlss`, recursive fields'
index expressions `Eiss₀`, field domains `Fss₀` and result index
expressions `Ess₀`:

* `tupleLfpAV W w pps nIdx Idss mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ m`
  — member `m`'s leaf: the λ-tower over the parameters and the
  member's own indices returning the `m`-th component of the block's
  least fixed point at the index tuple;
* `tupleLfpΦ W w ρp k Idss mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀` — the
  block's tuple operator at a parameter frame, a meta-level function
  on tuples of families (the block model's `Φ`);
* `TupleLfpOk` — the premise at a parameter frame (the block's chains
  graded);
* the laws: **`tupleLfpAV_fold`** (the interp law: the leaf at fitting
  parameters and indices is `app (lfpTuple w k Is Φ m) ⟨ı⃗⟩`),
  **`tupleLfpΦ_functor`** (`Φ` monotone, space-preserving, with a
  closed tuple), the leaf's closedness and grading (`tupleLfpAV_below`,
  `tupleLfpAV_wellDenotedV`, `tupleLfpAV_mem`) and **the formers' stage
  of the mutual install at the API** (`stageTupleFormers`: the run of
  `mutualFormers` conses the `k` members with their `k`-ary leaves,
  every member stored with its data crossed and its leaf typed — what
  `FormersTyped` and `IsBlockModel.former` read).  The stage's premises are
  two further sealed `Prop`s, `TupleLfpBlockOk` (stability and
  closedness of the block's data) and, per member, `TupleLfpStageOk`
  (the chains graded at the member's parameter frames); their
  introductions from the constructors' readings are the recursor
  stage's (`MutualChains.lean`'s facts), and the intros `of_tagged`
  expose the representation to that stage's ASSEMBLY only.

**The representation** (private): the members' leaves are #278's
`mutualTyAVI` (`Semantics/Tower/MutualLeafI.lean`) — ONE `lfpFam`
over the tagged sum of the members' index tuples, member `m` its
fibre at tag `m` — and the operator is the split of the fixpoint
route's functor at the tagged data through the split/join theorem
(`SetTheory/Derive/LfpSplit.lean`, `lfpTuple_splitFun`) along the
tagged encoding `tagEnc`.  Nothing of the tag leaves this module
(DESIGN §U.7).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal MutualFormerA)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The representation: the tagged data and the tagged encoding -/

/-- The members' index telescopes as a list, in member order (the
representation's `Idss`; the API is stated over the FUNCTION `Ids`). -/
@[expose] def tupleIdss (k : Nat) (Ids : Nat → List AnnotTerm) : List (List AnnotTerm) :=
  (List.range k).map Ids

theorem tupleIdss_length (k : Nat) (Ids : Nat → List AnnotTerm) : (tupleIdss k Ids).length = k := by
  simp [tupleIdss]

theorem tupleIdss_getElem? {k : Nat} {Ids : Nat → List AnnotTerm} {m : Nat} (hm : m < k) :
    (tupleIdss k Ids)[m]? = some (Ids m) := by
  simp [tupleIdss, List.getElem?_map, List.getElem?_range hm]

theorem tupleIdss_getD {k : Nat} {Ids : Nat → List AnnotTerm} {m : Nat} (hm : m < k) :
    (tupleIdss k Ids).getD m [] = Ids m := by
  rw [List.getD_eq_getElem?_getD, tupleIdss_getElem? hm]; rfl

/-- The constructors' tagged index expressions (the representation's). -/
@[expose] def tupleEss (W : Nat) (Idss : List (List AnnotTerm)) (mems nFs : List Nat)
    (Ess₀ : List (List AnnotTerm)) : List (List AnnotTerm) :=
  mutualEss W Idss mems nFs Ess₀

/-- The recursive slots' tagged index expressions (the representation's). -/
@[expose] def tupleEiss (W : Nat) (Idss : List (List AnnotTerm)) (tgts : List (List Nat))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss₀ : List (List (List AnnotTerm))) :
    List (List (List AnnotTerm)) :=
  mutualEiss W Idss tgts tlss Eiss₀

/-- The auxiliary family's index set: the 1-tuples of the tags. -/
@[expose] noncomputable def tupleU (W : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm)) : V :=
  idxSet W ρp (auxIds W Idss)

/-- **The tagged encoding** of member `mm`'s index tuple `i` (a tower
of the member's arity) into the auxiliary family's index set: the
1-tuple of the tag `inj mm ⟨ı⃗, pt⟩`, the components read off `i`. -/
@[expose] noncomputable def tagEnc (W : Nat) (Ids : Nat → List AnnotTerm) (mm : Nat) (i : V) : V :=
  tupW W [inj mm (mkTower (((List.range (Ids mm).length).map fun l => projS l i) ++ [pt]))]

/-- The encoding at a tower of the member's arity decodes it. -/
theorem tagEnc_mkTower (W : Nat) {Ids : Nat → List AnnotTerm} {mm : Nat} {is : List V}
    (hlen : is.length = (Ids mm).length) :
    tagEnc W Ids mm (mkTower is) = tupW W [inj mm (mkTower (is ++ [pt]))] := by
  unfold tagEnc
  have h : ((List.range (Ids mm).length).map fun l => projS l (mkTower is)) = is := by
    rw [← hlen]
    apply List.ext_getElem
    · simp
    · intro l _ h2
      rw [List.getElem_map, List.getElem_range, projS_mkTower l is h2]
  rw [h]

/-- The auxiliary family's index set: the 1-tuples of the tags. -/
theorem mem_tupleU {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (hT : TagOk W ρp Idss)
    {u : V} :
    u ∈ˢ tupleU W ρp Idss ↔ ∃ t, t ∈ˢ tagSet W ρp Idss ∧ u = mkTower [t] := by
  have hv := (tagTyAV_facts hT).1
  constructor
  · intro hu
    obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hT.1 hu
    have hlen := hsp.length_eq
    match hl : projList (auxIds W Idss).length u, hsp, heq with
    | [t], hsp, heq =>
      refine ⟨t, ?_, heq⟩
      have := hsp.1
      rwa [hv] at this
  · rintro ⟨t, ht, rfl⟩
    refine mkTower_mem_teleOfFields hT.1 (Fs := auxIds W Idss) ⟨?_, trivial⟩
    rw [hv]
    exact ht

/-- A tag is a member's tagged index tuple at a fitting spine. -/
theorem tagSet_elim {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (hT : TagOk W ρp Idss)
    {t : V} (ht : t ∈ˢ tagSet W ρp Idss) :
    ∃ m Ids is, Idss[m]? = some Ids ∧ SpineFit ρp Ids is ∧ t = inj m (mkTower (is ++ [pt])) := by
  obtain ⟨m, a, ha, rfl⟩ := sumSet_elim hT.1 ht
  cases hm : Idss[m]? with
  | none =>
    exfalso
    have hu : (uChains Idss)[m]? = none := by rw [uChains_getElem?, hm]; rfl
    unfold sumFibre at ha
    rw [hu] at ha
    exact not_mem_empty _ ha
  | some Ids =>
    have hu : (uChains Idss)[m]? = some (Ids ++ [idxEqAV []]) := by rw [uChains_getElem?, hm]; rfl
    rw [sumFibre_of_getElem? hu] at ha
    obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hT.1 ha
    obtain ⟨is, hl, hsp', -⟩ := spineFit_append_idxEq.mp hsp
    exact ⟨m, Ids, is, hm, hsp', by rw [heq, hl]⟩

/-- **The tagged encoding is an encoding** (`IdxEnc`) of the members'
index-tuple sets into the auxiliary family's: a member's index tuple
is a tower of its arity, its tag lands in the union, every element of
the union is some member's tag, and tags decode uniquely. -/
theorem tagEnc_idxEnc {W : Nat} {ρp : Nat → V} {k : Nat} {Ids : Nat → List AnnotTerm}
    (hT : TagOk W ρp (tupleIdss k Ids)) :
    IdxEnc k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) := by
  have hW := hT.1
  -- a member's index tuple is a tower of a fitting spine
  have helim : ∀ m i, i ∈ˢ idxSet W ρp (Ids m) →
      ∃ is, SpineFit ρp (Ids m) is ∧ is.length = (Ids m).length ∧ i = mkTower is := by
    intro m i hi
    obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hW hi
    exact ⟨_, hsp, hsp.length_eq, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m hm i hi
    obtain ⟨is, hsp, hl, rfl⟩ := helim m i hi
    rw [tagEnc_mkTower W hl, tupW_pos hW]
    exact (mem_tupleU hT).mpr ⟨_, tagTuple_mem hT (tupleIdss_getElem? hm) hsp, rfl⟩
  · intro u hu
    obtain ⟨t, ht, rfl⟩ := (mem_tupleU hT).mp hu
    obtain ⟨m, Ids', is, hm, hsp, rfl⟩ := tagSet_elim hT ht
    have hmk : m < k := by
      have := (List.getElem?_eq_some_iff.mp hm).1
      rw [tupleIdss_length] at this
      exact this
    obtain rfl : Ids m = Ids' := Option.some.inj ((tupleIdss_getElem? hmk).symm.trans hm)
    refine ⟨m, hmk, mkTower is, mkTower_mem_teleOfFields hW hsp, ?_⟩
    rw [tagEnc_mkTower W hsp.length_eq, tupW_pos hW]
  · intro m m' _ _ i i' hi hi' heq
    obtain ⟨is, hsp, hl, rfl⟩ := helim m i hi
    obtain ⟨is', hsp', hl', rfl⟩ := helim m' i' hi'
    rw [tagEnc_mkTower W hl, tagEnc_mkTower W hl', tupW_pos hW, tupW_pos hW] at heq
    have h1 := mkTower_inj (by rfl) heq
    obtain ⟨rfl, h2⟩ := inj_inj (List.singleton_inj.mp h1)
    refine ⟨rfl, ?_⟩
    have h3 := mkTower_inj (by simp [hl, hl']) h2
    rw [List.append_cancel_right h3]

/-! ## The API: the former, the operator, the premise -/

/-- **Member `m`'s leaf** of a block of `k` members with index
telescopes `Ids`: the λ-tower over the parameters (`pps`) and the
member's own `nIdx` indices returning the `m`-th component of the
block's least fixed point at the index tuple (the representation:
`mutualTyAVI` at the tagged data). -/
def tupleLfpAV (W w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (nIdx k : Nat)
    (Ids : Nat → List AnnotTerm) (mems nFs : List Nat) (tgts : List (List Nat))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : List (List (List AnnotTerm))) (Fss₀ Ess₀ : List (List AnnotTerm)) (m : Nat) :
    AnnotTerm :=
  mutualTyAVI W w pps nIdx (tupleIdss k Ids) rss tlss (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀)
    Fss₀ (tupleEss W (tupleIdss k Ids) mems nFs Ess₀) m

/-- **The block's tuple operator** at a parameter frame: a meta-level
function on tuples of families over the members' index-tuple sets
(the representation: the split of the fixpoint route's functor at the
tagged data). -/
noncomputable def tupleLfpΦ (W w : Nat) (ρp : Nat → V) (k : Nat) (Ids : Nat → List AnnotTerm)
    (mems nFs : List Nat) (tgts : List (List Nat)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss₀ : List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : List (List AnnotTerm)) : (Nat → V) → Nat → V :=
  splitFun k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids)
    (fixFunVI W w ρp (auxIds W (tupleIdss k Ids)) (auxIds W (tupleIdss k Ids)).length rss tlss
      (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀) Fss₀ (tupleEss W (tupleIdss k Ids) mems nFs Ess₀))

/-- **The premise at a parameter frame**: the members' index
telescopes graded at a common positive universe `W`, and the block's
chains graded (the representation: `TagOk` and the fixpoint route's
`XChainsOk` at the tagged data).  Established from the constructors'
readings (`TupleLfpOk.of_tagged` now; the untagged introduction is
the recursor stage's). -/
def TupleLfpOk (W w : Nat) (ρp : Nat → V) (k : Nat) (Ids : Nat → List AnnotTerm)
    (mems nFs : List Nat) (tgts : List (List Nat)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss₀ : List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : List (List AnnotTerm)) : Prop :=
  TagOk W ρp (tupleIdss k Ids) ∧
  XChainsOk W w ρp (auxIds W (tupleIdss k Ids)) rss tlss (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀)
    Fss₀ (tupleEss W (tupleIdss k Ids) mems nFs Ess₀)

section Premise

variable {W w : Nat} {ρp : Nat → V} {k : Nat} {Ids : Nat → List AnnotTerm} {mems nFs : List Nat}
  {tgts : List (List Nat)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : List (List (List AnnotTerm))} {Fss₀ Ess₀ : List (List AnnotTerm)}

theorem TupleLfpOk.of_tagged (hT : TagOk W ρp (tupleIdss k Ids))
    (hX : XChainsOk W w ρp (auxIds W (tupleIdss k Ids)) rss tlss
      (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀) Fss₀ (tupleEss W (tupleIdss k Ids) mems nFs Ess₀)) :
    TupleLfpOk W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ :=
  ⟨hT, hX⟩

/-- The index universe is positive. -/
theorem TupleLfpOk.W_pos (h : TupleLfpOk W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) :
    W ≠ 0 :=
  h.1.1

/-- Every member's index telescope is graded at `W`. -/
theorem TupleLfpOk.idxOk (h : TupleLfpOk W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    {m : Nat} (hm : m < k) : IdxOk W ρp (Ids m) := by
  refine h.1.2 _ ?_
  rw [← tupleIdss_getD (Ids := Ids) hm, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [tupleIdss_length]; exact hm)]
  exact List.getElem_mem _

end Premise

/-! ## The laws -/

section Laws

variable {W w : Nat} {k : Nat} {Ids : Nat → List AnnotTerm} {mems nFs : List Nat}
  {tgts : List (List Nat)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : List (List (List AnnotTerm))} {Fss₀ Ess₀ : List (List AnnotTerm)}

/-- **`Φ` is a monotone, space-preserving tuple functor with a closed
tuple** (the block model's `functor` clause), from the premise. -/
theorem tupleLfpΦ_functor {ρp : Nat → V}
    (h : TupleLfpOk W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) :
    MonoTuple w k (fun m => idxSet W ρp (Ids m))
      (tupleLfpΦ W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) ∧
    MapsTuple w k (fun m => idxSet W ρp (Ids m))
      (tupleLfpΦ W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) ∧
    ∃ L, IsClosedTuple w k (fun m => idxSet W ρp (Ids m))
      (tupleLfpΦ W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) L :=
  have henc := tagEnc_idxEnc h.1
  ⟨splitFun_mono henc (fixFunVI_mono h.2), splitFun_maps henc (fixFunVI_maps h.2),
    splitFun_closed_exists henc (fixFunVI_closed_exists h.2)⟩

/-- **The interp law** (the block model's `leaf` clause): member `m`'s leaf
at a spine fitting its parameters and its own indices is the `m`-th
component of the block's least fixed point at the index tuple — the
tower of the index spine. -/
theorem tupleLfpAV_fold {ρ : Nat → V} {as is : List V} {pps : List (Nat × Nat × AnnotTerm)}
    {nP m : Nat} (hm : m < k)
    (h : TupleLfpOk W w (consList as ρ) k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    (hIds : Ids m = (pps.drop nP).map (·.2.2))
    (hsp : SpineFit ρ ((pps.take nP).map (·.2.2)) as)
    (hi : SpineFit (consList as ρ) ((pps.drop nP).map (·.2.2)) is) :
    (as ++ is).foldl SetTheory.app (interp V ρ
        (tupleLfpAV W w pps (pps.drop nP).length k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ m))
      = SetTheory.app (lfpTuple w k (fun m => idxSet W (consList as ρ) (Ids m))
          (tupleLfpΦ W w (consList as ρ) k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀) m)
          (mkTower is) := by
  have hW := h.W_pos
  have hn : is.length = (pps.drop nP).length := by rw [hi.length_eq, List.length_map]
  have hIdsG : (tupleIdss k Ids)[m]? = some ((pps.drop nP).map (·.2.2)) := by
    rw [tupleIdss_getElem? hm, hIds]
  have hspAll : SpineFit ρ (pps.map (·.2.2)) (as ++ is) := by
    have hh := hsp.append hi
    have hpps : pps.map (·.2.2) = (pps.take nP).map (·.2.2) ++ (pps.drop nP).map (·.2.2) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hpps]; exact hh
  have hbase : MutualBaseI W w (consList (as ++ is) ρ) (pps.drop nP).length (tupleIdss k Ids) rss tlss
      (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀) Fss₀ (tupleEss W (tupleIdss k Ids) mems nFs Ess₀)
      m := by
    refine ⟨?_, ?_, _, hIdsG, by rw [List.length_map], ?_⟩
    · rw [consList_append, ← hn, shiftE_consList]; exact h.1
    · rw [consList_append, ← hn, shiftE_consList]; exact h.2.hok
    · rw [consList_append, ← hn, shiftE_consList, ConLeche.Semantics.frameIdx_consList']; exact hi
  unfold tupleLfpAV
  rw [ConLeche.Semantics.mutualTyAVI_fold hspAll hbase]
  have hsh : shiftE (pps.drop nP).length 0 (consList (as ++ is) ρ) = consList as ρ := by
    rw [consList_append, ← hn]; exact shiftE_consList is (consList as ρ)
  have hfr : ConLeche.Semantics.frameIdx (pps.drop nP).length (consList (as ++ is) ρ) = is := by
    rw [consList_append, ← hn]; exact ConLeche.Semantics.frameIdx_consList' is (consList as ρ)
  rw [hsh, hfr]
  have htup : mkTower is ∈ˢ idxSet W (consList as ρ) (Ids m) := by
    rw [hIds]; exact mkTower_mem_teleOfFields hW hi
  unfold tupleLfpΦ
  rw [app_lfpTuple_splitFun (tagEnc_idxEnc h.1) (fixFunVI_mono h.2) (fixFunVI_maps h.2)
    (fixFunVI_closed_exists h.2) hm htup, tagEnc_mkTower W (by rw [hn, hIds, List.length_map])]
  rfl

end Laws

/-! ## The stage premises -/

/-- **The block's data, stable and closed** (sealed): the index
universe, the index telescopes and the constructor data depend on the
block's level parameters only; the index telescopes are closed at the
parameters and the block's chains at the parameters, the family and
the tuple. -/
def TupleLfpBlockOk (nP : Nat) (lps : List Name) (W : (Name → Nat) → Nat) (k : Nat)
    (Ids : (Name → Nat) → Nat → List AnnotTerm) (mems nFs : List Nat) (tgts : List (List Nat))
    (rss : List (List Bool)) (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)) : Prop :=
  (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
    W ψ₁ = W ψ₂ ∧ Ids ψ₁ = Ids ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss₀ ψ₁ = Eiss₀ ψ₂ ∧
      Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess₀ ψ₁ = Ess₀ ψ₂) ∧
  (∀ ψ : Name → Nat, ∀ Ids' ∈ tupleIdss k (Ids ψ), FieldsBelow nP Ids') ∧
  (∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (W ψ) (auxIds (W ψ) (tupleIdss k (Ids ψ))) 1 rss (tlss ψ)
    (tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ)) (Fss₀ ψ)
    (tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ)), FieldsBelow (nP + 2) chain)

/-- **Member `t`'s chain facts at its parameter frames** (sealed): the
representation's `MemberChainsOk` at the tagged data. -/
def TupleLfpStageOk (V : Type w) [SetTheory V] (nP t : Nat) (resSort : Level)
    (W : (Name → Nat) → Nat) (k : Nat) (Ids : (Name → Nat) → Nat → List AnnotTerm)
    (mems nFs : List Nat) (tgts : List (List Nat)) (rss : List (List Bool))
    (tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss₀ : (Name → Nat) → List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm))
    (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop :=
  MemberChainsOk V nP t resSort W (fun ψ => tupleIdss k (Ids ψ)) rss tlss
    (fun ψ => tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ)) Fss₀
    (fun ψ => tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ)) pps

section Premises

variable {nP : Nat} {lps : List Name} {W : (Name → Nat) → Nat} {k : Nat}
  {Ids : (Name → Nat) → Nat → List AnnotTerm} {mems nFs : List Nat} {tgts : List (List Nat)}
  {rss : List (List Bool)} {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

/-- The block premise, from the representation's facts (the recursor
stage's assembly introduces it). -/
theorem TupleLfpBlockOk.of_tagged
    (hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      W ψ₁ = W ψ₂ ∧ Ids ψ₁ = Ids ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss₀ ψ₁ = Eiss₀ ψ₂ ∧
        Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess₀ ψ₁ = Ess₀ ψ₂)
    (hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids' ∈ tupleIdss k (Ids ψ), FieldsBelow nP Ids')
    (hchainBelow : ∀ ψ : Name → Nat,
      ∀ chain ∈ chainsXI (W ψ) (auxIds (W ψ) (tupleIdss k (Ids ψ))) 1 rss (tlss ψ)
        (tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ)) (Fss₀ ψ)
        (tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ)), FieldsBelow (nP + 2) chain) :
    TupleLfpBlockOk nP lps W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ :=
  ⟨hParams, hIdsBelow, hchainBelow⟩

/-- The member premise, from the representation's facts (the recursor
stage's assembly introduces it). -/
theorem TupleLfpStageOk.of_tagged {t : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : MemberChainsOk V nP t resSort W (fun ψ => tupleIdss k (Ids ψ)) rss tlss
      (fun ψ => tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ)) Fss₀
      (fun ψ => tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ)) pps) :
    TupleLfpStageOk V nP t resSort W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ pps :=
  h

/-- The member premise, read back at the representation (the
assembly's seam, `of_tagged`'s inverse). -/
theorem TupleLfpStageOk.tagged {t : Nat} {resSort : Level}
    {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : TupleLfpStageOk V nP t resSort W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ pps) :
    MemberChainsOk V nP t resSort W (fun ψ => tupleIdss k (Ids ψ)) rss tlss
      (fun ψ => tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ)) Fss₀
      (fun ψ => tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ)) pps :=
  h

/-- The block's data are stable under the level parameters. -/
theorem TupleLfpBlockOk.params (hB : TupleLfpBlockOk nP lps W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    {ψ₁ ψ₂ : Name → Nat} (hφ : ∀ q ∈ lps, ψ₁ q = ψ₂ q) :
    W ψ₁ = W ψ₂ ∧ Ids ψ₁ = Ids ψ₂ ∧ tlss ψ₁ = tlss ψ₂ ∧ Eiss₀ ψ₁ = Eiss₀ ψ₂ ∧
      Fss₀ ψ₁ = Fss₀ ψ₂ ∧ Ess₀ ψ₁ = Ess₀ ψ₂ :=
  hB.1 ψ₁ ψ₂ hφ

end Premises

/-! ## The stage laws -/

section StageLaws

variable {nP : Nat} {W : (Name → Nat) → Nat} {k : Nat} {Ids : (Name → Nat) → Nat → List AnnotTerm}
  {mems nFs : List Nat} {tgts : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

/-- **The leaf is closed**, from its binder data and the block
premise. -/
theorem tupleLfpAV_below {lps : List Name}
    (hB : TupleLfpBlockOk nP lps W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    {w nIdx t : Nat} {pps : List (Nat × Nat × AnnotTerm)} (hp : DomsBelow 0 pps)
    (hlen : pps.length = nP + nIdx) (ψ : Name → Nat) :
    Term.bvarsBelow 0
      (tupleLfpAV (W ψ) w pps nIdx k (Ids ψ) mems nFs tgts rss (tlss ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ)
        t).erase :=
  mutualTyAVI_below hp hlen (hB.2.1 ψ) (hB.2.2 ψ)

/-- **The leaf is graded and valid under its tower**, from the
former's data and the member premise. -/
theorem tupleLfpAV_wellDenotedV {m : EnvModel V env} {cvT : ConstantVal} {nIdx t : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps)
    (hC : TupleLfpStageOk V nP t resSort W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ pps)
    (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ
      (tupleLfpAV (W ψ) (resSort.eval ψ) (pps ψ) nIdx k (Ids ψ) mems nFs tgts rss (tlss ψ) (Eiss₀ ψ)
        (Fss₀ ψ) (Ess₀ ψ) t) :=
  mutualTyAVI_wellDenotedV (mutualLeafWalks hFD hC ψ ρ).1 (mutualLeafWalks hFD hC ψ ρ).2

/-- **The leaf inhabits its former's type**, from the former's data and
the member premise. -/
theorem tupleLfpAV_mem {m : EnvModel V env} {cvT : ConstantVal} {nIdx t : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT (nP + nIdx) resSort pps)
    (hC : TupleLfpStageOk V nP t resSort W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ pps)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ
        (tupleLfpAV (W ψ) (resSort.eval ψ) (pps ψ) nIdx k (Ids ψ) mems nFs tgts rss (tlss ψ) (Eiss₀ ψ)
          (Fss₀ ψ) (Ess₀ ψ) t)
      ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ))) :=
  mutualTyAVI_mem (mutualLeafWalks hFD hC ψ ρ).1

end StageLaws

/-! ## The formers' stage at the API -/

/-- **The formers' stage of the mutual install**: the block's `k`
members consed with their `k`-ary leaves (`tupleLfpAV … t`), the
model's leaves off the block the pre-block model's, and every member
stored at the formers' environment with the block's empty capability
record, its data crossed to the formers' model and its leaf typed at
its former's reading (what `FormersTyped` and `IsBlockModel.former` read
at the block model).  Premises: the block premise, and per member its
binder data at the pre-block model and its member premise. -/
theorem stageTupleFormers {F nP : Nat} {resSort : Level} {lps : List Name}
    {W : (Name → Nat) → Nat} {k : Nat} {Ids : (Name → Nat) → Nat → List AnnotTerm}
    {mems nFs : List Nat} {tgts : List (List Nat)} {rss : List (List Bool)}
    {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
    {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}
    {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hB : TupleLfpBlockOk nP lps W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    {formers : List (ConstantVal × Nat)} {env₁ : Env} {fms : List MutualFormerA}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hrun : ConLeche.mutualFormers (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) nP formers env
      = .ok (env₁, fms))
    (hnd : (fms.map (fun f => f.cvTa.name)).Nodup)
    (hmem : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = lps ∧
      FormerData mp.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) ∧
      TupleLfpStageOk V nP t resSort W k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ (ppsF t)) :
    ∃ mp₁ : EnvModelM V μ env₁,
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        mp₁.base2.acval f.cvTa.name
          = fun ψ => tupleLfpAV (W ψ) (resSort.eval ψ) (ppsF t ψ) f.nIdx k (Ids ψ) mems nFs tgts rss
              (tlss ψ) (Eiss₀ ψ) (Fss₀ ψ) (Ess₀ ψ) t) ∧
      (∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name) →
        mp₁.base2.acval n = mp.base2.acval n) ∧
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        env₁.find? f.cvTa.name = some (.indInfo f.cvTa {}) ∧
        FormerData mp₁.base2 f.cvTa (nP + f.nIdx) resSort (ppsF t) ∧
        ∀ (ψ : Name → Nat) (ρ : Nat → V),
          interp V ρ (mp₁.base2.acval f.cvTa.name ψ)
            ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (resSort.eval ψ)))) := by
  have hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      W ψ₁ = W ψ₂ ∧ tupleIdss k (Ids ψ₁) = tupleIdss k (Ids ψ₂) ∧ tlss ψ₁ = tlss ψ₂ ∧
        tupleEiss (W ψ₁) (tupleIdss k (Ids ψ₁)) tgts (tlss ψ₁) (Eiss₀ ψ₁)
          = tupleEiss (W ψ₂) (tupleIdss k (Ids ψ₂)) tgts (tlss ψ₂) (Eiss₀ ψ₂) ∧
        Fss₀ ψ₁ = Fss₀ ψ₂ ∧
        tupleEss (W ψ₁) (tupleIdss k (Ids ψ₁)) mems nFs (Ess₀ ψ₁)
          = tupleEss (W ψ₂) (tupleIdss k (Ids ψ₂)) mems nFs (Ess₀ ψ₂) := by
    intro ψ₁ ψ₂ hφ
    obtain ⟨hW, hI, htl, hEi, hF, hE⟩ := hB.params hφ
    rw [hW, hI, htl, hEi, hF, hE]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨mp₁, hleaf, hoff⟩ := stageMutualFormers (V := V) (μ := μ) (F := F) (nP := nP)
    (resSort := resSort) (lps := lps) (W := W) (Idss := fun ψ => tupleIdss k (Ids ψ)) (rss := rss)
    (tlss := tlss) (Eiss' := fun ψ => tupleEiss (W ψ) (tupleIdss k (Ids ψ)) tgts (tlss ψ) (Eiss₀ ψ))
    (Fss₀ := Fss₀) (Ess' := fun ψ => tupleEss (W ψ) (tupleIdss k (Ids ψ)) mems nFs (Ess₀ ψ))
    (ppsF := ppsF) hParams hB.2.1 hB.2.2 mp hE hrun hnd hmem
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hrun
  -- every member is fresh before the block, and its type resolves there
  have hok : ∀ f ∈ fms, MemberConsOk env f.cvTa := fun f hf =>
    MemberConsOk.ofCheck (ConLeche.mutualFormerChecks_checked hchecks f hf).choose_spec
  have hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none := fun f hf => (hok f hf).fresh
  obtain ⟨hF, hG, hproj⟩ := consMutualFormers_extend (env := env) hfresh hnd
  have hag : ∀ n : Name, (env.find? n).isSome = true → mp.base2.acval n = mp₁.base2.acval n := by
    intro n hn
    refine (hoff n fun t f hf hne => ?_).symm
    rw [hne, hfresh f (List.mem_of_getElem? hf)] at hn
    exact nomatch hn
  refine ⟨mp₁, hleaf, hoff, fun t f hf => ?_⟩
  obtain ⟨-, hFD, hC⟩ := hmem t f hf
  refine ⟨consMutualFormers_find?_self (List.mem_of_getElem? hf) hnd, ?_, ?_⟩
  · exact hFD.crossEnv (constsBound_of_constsResolve _ (hok f (List.mem_of_getElem? hf)).resolve)
      hF hG hproj hag
  · intro ψ ρ
    rw [hleaf t f hf]
    exact tupleLfpAV_mem hFD hC ψ ρ

/-! ## The fibre law (sealed)

The block model's `fibre` clause at the derived former: component `mm`'s
fibre of the operator at `(X, t)` is the set of the tagged towers of
the spines fitting one of member `mm`'s constructors at `(X, t)` — a
recursive field read at the TARGET member's component of `X`, the
constructor's index expressions at the spine the components of `t`.
Stated over the UNTAGGED lists, positionally in the block's global
constructor order (`J`); the representation's tag is translated away
inside (`slotSet_tag_eq`, `fitsFrom_tag_iff`, `tagTerm_iff`). -/

section Fibre

variable {W w : Nat} {ρp : Nat → V} {k : Nat} {Ids : Nat → List AnnotTerm}

/-- A tagged tuple's arguments fit its member's index telescope when
the tuple is graded (the tupler is a λ-tower over that telescope). -/
theorem tagTupleAV_fit_of_wellDenoted {Idss : List (List AnnotTerm)} (hT : TagOk W ρp Idss)
    {m : Nat} {IdsT : List AnnotTerm} (hm : Idss[m]? = some IdsT)
    {d : Nat} {τ : Nat → V} (hfr : shiftE d 0 τ = ρp) {Es : List AnnotTerm}
    (hlen : Es.length = IdsT.length) (hok : WellDenoted V τ (tagTupleAV W m d Idss Es)) :
    SpineFit ρp IdsT (Es.map (interp V τ)) := by
  have hg : Idss.getD m [] = IdsT := by rw [List.getD_eq_getElem?_getD, hm]; rfl
  have hf : interp V τ ((tagTuplerAV W m Idss).liftN d 0)
      = interp V ρp (mkLamsC W (tuplerData W IdsT)
          (sumInjAtAV W (uChains Idss) IdsT.length (numeralAV m)
            (mkTowerGoU W IdsT (idxEqAV [])))) := by
    rw [interp_liftN, hfr]
    unfold tagTuplerAV sumMkAV
    rw [hg]
  have hlenT : Es.length ≤ (tuplerData W IdsT).length := by
    rw [hlen]; simp [tuplerData]
  unfold tagTupleAV at hok
  have := spineFit_of_wellDenoted_lams (u := W) hT.1 hlenT hok hf
  rwa [List.take_of_length_le (by rw [hlen]; simp [tuplerData]), tuplerData_doms] at this

/-- **A tagged recursive slot is the target member's untagged slot**:
at the auxiliary family's join of a tuple `X`, the slot at the one
tagged index expression is the slot at the raw expressions on the
target's component. -/
theorem slotSet_tag_eq (hT : TagOk W ρp (tupleIdss k Ids)) {X : Nat → V}
    {tgt : Nat} (htgt : tgt < k) {i : Nat} {as : List V} (hlen : as.length = i)
    {tl : List (Nat × Nat × AnnotTerm)} {Eis₀ : List AnnotTerm}
    (hlenE : Eis₀.length = (Ids tgt).length)
    (hfit : SlotFit W w ρp (auxIds W (tupleIdss k Ids)) tl
      [tagTupleAV W tgt (i + tl.length) (tupleIdss k Ids) Eis₀] as) :
    slotSet w W (consList as ρp) tl [tagTupleAV W tgt (i + tl.length) (tupleIdss k Ids) Eis₀]
        (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
      = slotSet w W (consList as ρp) tl Eis₀ (X tgt) := by
  have henc := tagEnc_idxEnc hT
  have hW := hT.1
  have hm := tupleIdss_getElem? (Ids := Ids) htgt
  have hbody : ∀ bs : List V, FitsS (teleOfFields (consList as ρp) (tl.map (·.2.2))) bs →
      SetTheory.app
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
          (tupW W ([tagTupleAV W tgt (i + tl.length) (tupleIdss k Ids) Eis₀].map
            (interp V (consList bs (consList as ρp)))))
        = SetTheory.app (X tgt) (tupW W (Eis₀.map (interp V (consList bs (consList as ρp))))) := by
    intro bs hbs
    have hsp : SpineFit (consList as ρp) (tl.map (·.2.2)) bs := fitsS_teleOfFields.mp hbs
    obtain ⟨hokTag, -⟩ := hfit.2.2 bs hsp
    have hokT : WellDenoted V (consList (as ++ bs) ρp)
        (tagTupleAV W tgt (i + tl.length) (tupleIdss k Ids) Eis₀) :=
      hokTag _ (List.mem_singleton.mpr rfl)
    have hfr : shiftE (i + tl.length) 0 (consList (as ++ bs) ρp) = ρp := by
      rw [show i + tl.length = (as ++ bs).length from by
        rw [List.length_append, hlen, hsp.length_eq, List.length_map]]
      exact shiftE_consList _ _
    have hfitU := tagTupleAV_fit_of_wellDenoted hT hm hfr hlenE hokT
    obtain ⟨-, hEok⟩ := WellDenoted.mkAppN_inv hokT
    obtain ⟨hval, -⟩ := tagTupleAV_facts hT hm hfr hEok hfitU
    rw [← consList_append, List.map_singleton, hval]
    have hvals : (Eis₀.map (interp V (consList (as ++ bs) ρp))).length = (Ids tgt).length := by
      rw [List.length_map, hlenE]
    rw [← tagEnc_mkTower W hvals, app_joinE henc htgt (mkTower_mem_teleOfFields hW hfitU),
      tupW_pos hW]
  unfold slotSet
  refine Subset.antisymm (piTele_mono fun bs hbs => ?_) (piTele_mono fun bs hbs => ?_)
  · rw [List.nil_append, hbody bs hbs]; exact Subset.refl _
  · rw [List.nil_append, hbody bs hbs]; exact Subset.refl _

/-- **The tagged fit is the untagged fit**: along a constructor's
domains, a spine fits the tagged slots at the join of `X` iff it fits
the raw slots at the target members' components of `X`
(`spineFit_chainXIGo_iff`'s tag translation). -/
theorem fitsFrom_tag_iff (hT : TagOk W ρp (tupleIdss k Ids)) {X : Nat → V} {t : V}
    {rs : List Bool} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis' Eis₀ : List (List AnnotTerm)} {tgtOf : Nat → Nat} {n : Nat}
    (hE : ∀ i, i < n → rs.getD i false = true →
      Eis'.getD i []
          = [tagTupleAV W (tgtOf i) (i + (tls.getD i []).length) (tupleIdss k Ids) (Eis₀.getD i [])] ∧
        tgtOf i < k ∧ (Eis₀.getD i []).length = (Ids (tgtOf i)).length) :
    ∀ (Fs : List AnnotTerm) (i : Nat) (as fs : List V), as.length = i → i + Fs.length ≤ n →
      SlotsFitX W w ρp (auxIds W (tupleIdss k Ids)) rs tls Eis'
        (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
        t i as Fs →
      (FitsFrom rs (fun i ρ => slotSet w W ρ (tls.getD i []) (Eis'.getD i [])
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X))
          i (consList as ρp) Fs fs ↔
        FitsFrom rs (fun i ρ => slotSet w W ρ (tls.getD i []) (Eis₀.getD i []) (X (tgtOf i)))
          i (consList as ρp) Fs fs)
  | [], _, _, [], _, _, _ => Iff.rfl
  | [], _, _, _ :: _, _, _, _ => Iff.rfl
  | _ :: _, _, _, [], _, _, _ => Iff.rfl
  | F :: Fs, i, as, a :: fs, hi, hn, hfit => by
    subst hi
    have hI : IdxOk W ρp (auxIds W (tupleIdss k Ids)) := auxIds_idxOk hT
    have hlt : as.length < n := by simp at hn; omega
    show a ∈ˢ (if rs.getD as.length false then
          slotSet w W (consList as ρp) (tls.getD as.length []) (Eis'.getD as.length [])
            (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
        else interp V (consList as ρp) F) ∧
        FitsFrom rs _ (as.length + 1) (cons a (consList as ρp)) Fs fs ↔
      a ∈ˢ (if rs.getD as.length false then
          slotSet w W (consList as ρp) (tls.getD as.length []) (Eis₀.getD as.length [])
            (X (tgtOf as.length))
        else interp V (consList as ρp) F) ∧
        FitsFrom rs _ (as.length + 1) (cons a (consList as ρp)) Fs fs
    have hhead : (if rs.getD as.length false then
          slotSet w W (consList as ρp) (tls.getD as.length []) (Eis'.getD as.length [])
            (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
        else interp V (consList as ρp) F)
        = (if rs.getD as.length false then
          slotSet w W (consList as ρp) (tls.getD as.length []) (Eis₀.getD as.length [])
            (X (tgtOf as.length))
        else interp V (consList as ρp) F) := by
      by_cases hri : rs.getD as.length false = true
      · rw [if_pos hri, if_pos hri]
        obtain ⟨hE', htgt, hlenE⟩ := hE _ hlt hri
        rw [hE']
        exact slotSet_tag_eq hT htgt rfl hlenE (by rw [← hE']; exact hfit.1 hri)
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true),
          if_neg (by rw [hri']; exact Bool.false_ne_true)]
    have hx : interp V (consList as (cons t (cons
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
          ρp))) (xEntry W (auxIds W (tupleIdss k Ids)) rs tls Eis' F as.length)
        = (if rs.getD as.length false then
          slotSet w W (consList as ρp) (tls.getD as.length []) (Eis'.getD as.length [])
            (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
        else interp V (consList as ρp) F) := by
      by_cases hri : rs.getD as.length false = true
      · rw [xEntry_rec hI F as t hri (hfit.1 hri), if_pos hri]
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri', if_neg (by rw [hri']; exact Bool.false_ne_true)]
    rw [hhead, consList_snoc']
    refine and_congr_right fun ha => ?_
    have ha' : a ∈ˢ interp V (consList as (cons t (cons
        (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
        ρp))) (xEntry W (auxIds W (tupleIdss k Ids)) rs tls Eis' F as.length) := by
      rw [hx, hhead]; exact ha
    exact fitsFrom_tag_iff hT hE Fs (as.length + 1) (as ++ [a]) fs (length_snoc' a as)
      (by simp at hn ⊢; omega) (hfit.2 a ha')

/-- The tagged slots' expressions, positionally. -/
theorem tupleEiss_getD_getD {Idss : List (List AnnotTerm)} {tgts : List (List Nat)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss₀ : List (List (List AnnotTerm))}
    {J i : Nat} (hJ : J < Eiss₀.length) (hi : i < (Eiss₀.getD J []).length) :
    ((tupleEiss W Idss tgts tlss Eiss₀).getD J []).getD i []
      = [tagTupleAV W ((tgts.getD J []).getD i 0) (i + ((tlss.getD J []).getD i []).length) Idss
          ((Eiss₀.getD J []).getD i [])] := by
  have hi' : i < (Eiss₀[J]?.getD []).length := by rwa [List.getD_eq_getElem?_getD] at hi
  unfold tupleEiss mutualEiss
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ,
    List.getElem?_range hi', Option.map_some, Option.getD_some]

/-- The tagged terminators, positionally. -/
theorem tupleEss_getD {Idss : List (List AnnotTerm)} {mems nFs : List Nat}
    {Ess₀ : List (List AnnotTerm)} {J : Nat} (hJ : J < Ess₀.length) :
    (tupleEss W Idss mems nFs Ess₀).getD J []
      = [tagTupleAV W (mems.getD J 0) (nFs.getD J 0) Idss (Ess₀.getD J [])] := by
  unfold tupleEss mutualEss
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]
  rfl

/-- The first equation's sides are graded when the equation chain is
(the tail sits under the head's equality, whose domain may be empty). -/
theorem wellDenoted_idxEqAV_head {a b : AnnotTerm} {r : List (AnnotTerm × AnnotTerm)} {ρ : Nat → V}
    (hok : WellDenoted V ρ (idxEqAV ((a, b) :: r))) : WellDenoted V ρ a ∧ WellDenoted V ρ b := by
  unfold idxEqAV negAV at hok
  rw [WellDenoted_pi] at hok
  have hc : WellDenoted V ρ (.pi 0 0 (.eqE a b) ((eqChainAV r).liftN 1 0)) := hok.1
  rw [WellDenoted_pi, WellDenoted_eqE] at hc
  exact hc.1

/-- **The block's lists are well-shaped** (the untagged data): the
per-constructor lists have the constructors' length, every
constructor's member and every recursive field's target are members,
and the index expressions have their member's arity. -/
structure TupleLfpShape (k : Nat) (Ids : Nat → List AnnotTerm) (mems nFs : List Nat)
    (tgts : List (List Nat)) (rss : List (List Bool)) (Eiss₀ : List (List (List AnnotTerm)))
    (Fss₀ Ess₀ : List (List AnnotTerm)) : Prop where
  lenE : Ess₀.length = Fss₀.length
  lenEi : Eiss₀.length = Fss₀.length
  nF : ∀ J, J < Fss₀.length → nFs.getD J 0 = (Fss₀.getD J []).length
  eiLen : ∀ J, J < Fss₀.length → (Eiss₀.getD J []).length = (Fss₀.getD J []).length
  memLt : ∀ J, J < Fss₀.length → mems.getD J 0 < k
  esLen : ∀ J, J < Fss₀.length → (Ess₀.getD J []).length = (Ids (mems.getD J 0)).length
  tgtOk : ∀ J, J < Fss₀.length → ∀ i, i < (Fss₀.getD J []).length →
    (rss.getD J []).getD i false = true →
    (tgts.getD J []).getD i 0 < k ∧
      ((Eiss₀.getD J []).getD i []).length = (Ids ((tgts.getD J []).getD i 0)).length

/-- **The tagged terminator at a fitting spine**: its one equation
holds iff the constructor's member is the tuple's and the raw index
expressions' values are the tuple's components. -/
theorem tagTerm_iff (hT : TagOk W ρp (tupleIdss k Ids)) {mem : Nat} (hmem : mem < k)
    {mm : Nat} {t : V} (ht : t ∈ˢ idxSet W ρp (Ids mm)) {Y : V} {fs : List V} {nF : Nat}
    (hlen : fs.length = nF) {Es₀ : List AnnotTerm} (hlenE : Es₀.length = (Ids mem).length)
    (hok : WellDenoted V (consList fs ρp) (tagTupleAV W mem nF (tupleIdss k Ids) Es₀)) :
    EqAll (consList fs (cons (tagEnc W Ids mm t) (cons Y ρp)))
        (eqsXI (auxIds W (tupleIdss k Ids)).length nF
          [tagTupleAV W mem nF (tupleIdss k Ids) Es₀]) ↔
      mem = mm ∧ ∀ l, l < (Ids mm).length →
        interp V (consList fs ρp) (Es₀.getD l default) = projS l t := by
  have hW := hT.1
  have hm := tupleIdss_getElem? (Ids := Ids) hmem
  have hfr : shiftE nF 0 (consList fs ρp) = ρp := by rw [← hlen]; exact shiftE_consList _ _
  have hfitU := tagTupleAV_fit_of_wellDenoted hT hm hfr hlenE hok
  obtain ⟨-, hEok⟩ := WellDenoted.mkAppN_inv hok
  obtain ⟨hval, -⟩ := tagTupleAV_facts hT hm hfr hEok hfitU
  obtain ⟨hsp, heq⟩ := towerSet_elim_teleOfFields hW ht
  generalize hisdef : projList (Ids mm).length t = is at hsp heq
  have hlenIs : is.length = (Ids mm).length := hsp.length_eq
  have hproj : projS 0 (tagEnc W Ids mm t) = inj mm (mkTower (is ++ [pt])) := by
    rw [heq, tagEnc_mkTower W hlenIs, tupW_pos hW]
    exact projS_mkTower 0 [inj mm (mkTower (is ++ [pt]))] (by simp)
  have hlenV : (Es₀.map (interp V (consList fs ρp))).length = (Ids mem).length := by
    rw [List.length_map, hlenE]
  rw [EqAll_eqsXI_gen hlen]
  have h1 : (∀ l, l < (auxIds W (tupleIdss k Ids)).length →
      interp V (consList fs ρp) (([tagTupleAV W mem nF (tupleIdss k Ids) Es₀]).getD l default)
        = projS l (tagEnc W Ids mm t)) ↔
      inj mem (mkTower (Es₀.map (interp V (consList fs ρp)) ++ [pt]))
        = inj mm (mkTower (is ++ [pt])) := by
    constructor
    · intro h
      have := h 0 (by simp [auxIds])
      rwa [List.getD_cons_zero, hval, hproj] at this
    · intro h l hl
      have hl0 : l = 0 := by simp [auxIds] at hl; omega
      subst hl0
      rw [List.getD_cons_zero, hval, hproj]
      exact h
  rw [h1]
  constructor
  · intro h
    obtain ⟨rfl, h2⟩ := inj_inj h
    have h3 := List.append_cancel_right (mkTower_inj (by simp [hlenV, hlenIs]) h2)
    refine ⟨rfl, fun l hl => ?_⟩
    have hlE : l < Es₀.length := by rw [hlenE]; exact hl
    have hlI : l < is.length := by rw [hlenIs]; exact hl
    have := congrArg (fun L => L[l]?) h3
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlE, List.getElem?_eq_getElem hlI,
      Option.map_some, Option.some.injEq] at this
    rw [heq, projS_mkTower l is hlI, ← this, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlE]
    rfl
  · rintro ⟨rfl, h⟩
    have hv : Es₀.map (interp V (consList fs ρp)) = is := by
      apply List.ext_getElem (by rw [hlenV, hlenIs])
      intro l hl₁ hl₂
      have hlE : l < Es₀.length := by rw [List.length_map] at hl₁; exact hl₁
      have hl' : l < (Ids mem).length := by rw [hlenIs] at hl₂; exact hl₂
      have := h l hl'
      rw [heq, projS_mkTower l is hl₂, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlE] at this
      rw [List.getElem_map]
      exact this
    rw [hv]

/-- **The fibre of the operator** (the block model's `fibre` clause):
component `mm`'s fibre at `(X, t)` is the set of the tagged towers
`injW w J ⟨f⃗, pt⟩` of the spines `f⃗` fitting one of member `mm`'s
constructors `J` at `(X, t)` — a recursive field read at the target
member's component of `X`, the constructor's index expressions at the
spine the components of `t`. -/
theorem tupleLfpΦ_fibre {mems nFs : List Nat} {tgts : List (List Nat)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss₀ : List (List (List AnnotTerm))}
    {Fss₀ Ess₀ : List (List AnnotTerm)}
    (h : TupleLfpOk W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀)
    (hS : TupleLfpShape k Ids mems nFs tgts rss Eiss₀ Fss₀ Ess₀)
    {X : Nat → V} (hX : InTupleSpace w k (fun m => idxSet W ρp (Ids m)) X)
    {mm : Nat} (hmm : mm < k) {t : V} (ht : t ∈ˢ idxSet W ρp (Ids mm)) (x : V) :
    x ∈ˢ SetTheory.app (tupleLfpΦ W w ρp k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ X mm) t ↔
      ∃ J fs, J < Fss₀.length ∧ mems.getD J 0 = mm ∧
        FitsFrom (rss.getD J []) (fun i ρ => slotSet w W ρ ((tlss.getD J []).getD i [])
            ((Eiss₀.getD J []).getD i []) (X ((tgts.getD J []).getD i 0))) 0 ρp (Fss₀.getD J []) fs ∧
        (∀ l, l < (Ids mm).length →
          interp V (consList fs ρp) ((Ess₀.getD J []).getD l default) = projS l t) ∧
        x = injW w J (mkTower (fs ++ [pt])) := by
  have hT := h.1
  have hW := hT.1
  have henc := tagEnc_idxEnc hT
  have hY : joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X
      ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W (tupleIdss k Ids))) := by
    rw [lfpFamSpace_eq]; exact joinE_mem henc hX
  have hτ : tagEnc W Ids mm t ∈ˢ idxSet W ρp (auxIds W (tupleIdss k Ids)) := henc.mem mm hmm t ht
  unfold tupleLfpΦ
  rw [app_splitFun ht, fixFunVI_app hY, famFI_app hτ]
  -- the tagged chain fit is the untagged fit
  have hfitJ : ∀ J, J < Fss₀.length → ∀ fs : List V,
      SpineFit (cons (tagEnc W Ids mm t) (cons
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
          ρp))
        (chainXIGo W (auxIds W (tupleIdss k Ids)) (rss.getD J []) (tlss.getD J [])
          ((tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀).getD J []) (Fss₀.getD J []) 0) fs ↔
      FitsFrom (rss.getD J []) (fun i ρ => slotSet w W ρ ((tlss.getD J []).getD i [])
          ((Eiss₀.getD J []).getD i []) (X ((tgts.getD J []).getD i 0))) 0 ρp (Fss₀.getD J []) fs := by
    intro J hJ fs
    have hsx := h.2.hfit _ hY _ hτ J hJ
    exact (spineFit_chainXIGo_iff (w := w) h.2.hI (Fss₀.getD J []) 0 [] fs rfl hsx).trans
      (fitsFrom_tag_iff hT (n := (Fss₀.getD J []).length) (fun i hi hri =>
        ⟨tupleEiss_getD_getD (by rw [hS.lenEi]; exact hJ) (by rw [hS.eiLen J hJ]; exact hi),
          (hS.tgtOk J hJ i hi hri).1, (hS.tgtOk J hJ i hi hri).2⟩)
        (Fss₀.getD J []) 0 [] fs rfl (by simp) hsx)
  -- the tagged terminator at a fitting spine is the untagged equations
  have htermJ : ∀ J, J < Fss₀.length → ∀ fs : List V, fs.length = (Fss₀.getD J []).length →
      SpineFit (cons (tagEnc W Ids mm t) (cons
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
          ρp))
        (chainXIGo W (auxIds W (tupleIdss k Ids)) (rss.getD J []) (tlss.getD J [])
          ((tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀).getD J []) (Fss₀.getD J []) 0) fs →
      (EqAll (consList fs (cons (tagEnc W Ids mm t) (cons
          (joinE k (fun m => idxSet W ρp (Ids m)) (tupleU W ρp (tupleIdss k Ids)) (tagEnc W Ids) X)
          ρp)))
        (eqsXI (auxIds W (tupleIdss k Ids)).length (Fss₀.getD J []).length
          ((tupleEss W (tupleIdss k Ids) mems nFs Ess₀).getD J [])) ↔
        mems.getD J 0 = mm ∧ ∀ l, l < (Ids mm).length →
          interp V (consList fs ρp) ((Ess₀.getD J []).getD l default) = projS l t) := by
    intro J hJ fs hlenfs hsp
    rw [tupleEss_getD (by rw [hS.lenE]; exact hJ), hS.nF J hJ]
    -- the terminator is graded at the fitting prefix
    have hok0 := h.2.hok _ hY _ hτ
    have hchain : chainXI W (auxIds W (tupleIdss k Ids)) (auxIds W (tupleIdss k Ids)).length
        (rss.getD J []) (tlss.getD J []) ((tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀).getD J [])
        (Fss₀.getD J []) ((tupleEss W (tupleIdss k Ids) mems nFs Ess₀).getD J [])
        ∈ chainsXI W (auxIds W (tupleIdss k Ids)) (auxIds W (tupleIdss k Ids)).length rss tlss
          (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀) Fss₀
          (tupleEss W (tupleIdss k Ids) mems nFs Ess₀) :=
      List.mem_of_getElem? (by rw [chainsXI_getElem?, if_pos hJ])
    have hFok := hok0 _ hchain
    unfold chainXI at hFok
    have hlenC := chainXIGo_length (rss.getD J []) (tlss.getD J [])
      ((tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀).getD J []) (u := W)
      (Ids := auxIds W (tupleIdss k Ids)) (Fss₀.getD J []) 0
    have hwd := fieldsOkB_getD hFok (j := (Fss₀.getD J []).length)
      (by rw [List.length_append, hlenC, List.length_singleton]; exact Nat.lt_succ_self _)
      (bs := fs) (by rw [← hlenC, List.take_left]; exact hsp)
    rw [← hlenC, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self] at hwd
    rw [hlenC, tupleEss_getD (by rw [hS.lenE]; exact hJ), hS.nF J hJ] at hwd
    simp only [List.getElem?_cons_zero, Option.getD_some] at hwd
    have heqs : eqsXI (auxIds W (tupleIdss k Ids)).length (Fss₀.getD J []).length
        [tagTupleAV W (mems.getD J 0) (Fss₀.getD J []).length (tupleIdss k Ids) (Ess₀.getD J [])]
        = [((tagTupleAV W (mems.getD J 0) (Fss₀.getD J []).length (tupleIdss k Ids)
            (Ess₀.getD J [])).liftN 2 (Fss₀.getD J []).length,
          projAV 0 (.bvar (Fss₀.getD J []).length))] := by
      simp only [eqsXI, auxIds, List.length_singleton, List.range_succ, List.range_zero,
        List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [heqs] at hwd
    obtain ⟨hokT, -⟩ := wellDenoted_idxEqAV_head hwd
    rw [← hlenfs, WellDenoted_chainXI_ord] at hokT
    rw [hlenfs] at hokT
    exact tagTerm_iff hT (hS.memLt J hJ) ht hlenfs (hS.esLen J hJ) hokT
  by_cases hw : w = 0
  · subst hw
    constructor
    · intro hx
      obtain ⟨rfl, J, fs, hJ, hlen, hsp, hall⟩ := fixStepI_zero_elim hx
      obtain ⟨hmemJ, heqs⟩ := (htermJ J hJ fs hlen hsp).mp hall
      refine ⟨J, fs, hJ, hmemJ, (hfitJ J hJ fs).mp hsp, heqs, ?_⟩
      rw [injW_zero]
    · rintro ⟨J, fs, hJ, hmemJ, hf, hall, rfl⟩
      have hsp := (hfitJ J hJ fs).mpr hf
      have hlen : fs.length = (Fss₀.getD J []).length := hf.length_eq
      rw [injW_zero]
      unfold fixStepI
      refine pt_mem_sumSet_zero (i := J) (a := pt) ?_
      unfold sumFibre
      rw [chainsXI_getElem?, if_pos hJ]
      unfold chainXI
      refine pt_mem_tower_teleOfFields (as := fs ++ [pt]) ?_
      exact spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, (htermJ J hJ fs hlen hsp).mpr ⟨hmemJ, hall⟩⟩
  · constructor
    · intro hx
      obtain ⟨J, fs, rfl, hJ, hlen, hsp, hall⟩ := fixStepI_elim hw hx
      obtain ⟨hmemJ, heqs⟩ := (htermJ J hJ fs hlen hsp).mp hall
      refine ⟨J, fs, hJ, hmemJ, (hfitJ J hJ fs).mp hsp, heqs, ?_⟩
      rw [injW_pos hw]
    · rintro ⟨J, fs, hJ, hmemJ, hf, hall, rfl⟩
      have hsp := (hfitJ J hJ fs).mpr hf
      have hlen : fs.length = (Fss₀.getD J []).length := hf.length_eq
      rw [injW_pos hw]
      unfold fixStepI
      refine inj_mem hw ?_
      unfold sumFibre
      rw [chainsXI_getElem?, if_pos hJ]
      unfold chainXI
      refine mkTower_mem hw (fitsS_teleOfFields.mpr ?_)
      exact spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, (htermJ J hJ fs hlen hsp).mpr ⟨hmemJ, hall⟩⟩

end Fibre

/-! ## The seam for the assembly

The recursor stage's ASSEMBLY (`MutualCore.lean`) reads the
constructors' chains at the auxiliary family and folds the
constructors' residuals to its fibre (#278's `mutualCtorFold`), so it
sees the representation — through these two laws and the `of_tagged`
intros, and nothing else does (DESIGN §U.7 (c)). -/

section Seam

variable {W w : Nat} {k : Nat} {Ids : Nat → List AnnotTerm} {mems nFs : List Nat}
  {tgts : List (List Nat)} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : List (List (List AnnotTerm))} {Fss₀ Ess₀ : List (List AnnotTerm)}

/-- **The representation** (the assembly's seam): member `m`'s leaf
is #278's `mutualTyAVI` at the tagged data. -/
theorem tupleLfpAV_repr (pps : List (Nat × Nat × AnnotTerm)) (nIdx m : Nat) :
    tupleLfpAV W w pps nIdx k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ m
      = mutualTyAVI W w pps nIdx (tupleIdss k Ids) rss tlss
          (tupleEiss W (tupleIdss k Ids) tgts tlss Eiss₀) Fss₀
          (tupleEss W (tupleIdss k Ids) mems nFs Ess₀) m := by
  rfl

/-- The leaf is a λ-tower over its binder data. -/
theorem tupleLfpAV_lams (pps : List (Nat × Nat × AnnotTerm)) (nIdx m : Nat) :
    ∃ B : AnnotTerm,
      tupleLfpAV W w pps nIdx k Ids mems nFs tgts rss tlss Eiss₀ Fss₀ Ess₀ m = mkLamsC (w + 1) pps B := by
  rw [tupleLfpAV_repr]
  exact ⟨_, mutualTyAVI_eq_mkLamsC _ _ _ _ _ _ _ _ _ _ _⟩

end Seam

end ConLeche.Model
