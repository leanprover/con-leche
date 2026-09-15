module

public import ConLeche.Semantics.Tower.MutualLeafI
public import ConLeche.SetTheory.Derive.LfpSplit
public import ConLeche.Model.Inductives.MutualStageFormer
import ConLeche.Model.Inductives.MutualFormersKit
public section

/-!
# `tupleLfpAV` — the `k`-ary least fixed point as a DERIVED term former (task #315, M4)

The uniform datum records a block as the least pre-fixed TUPLE of an
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
  on tuples of families (the datum's `Φ`);
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
  `FormersTyped` and `BlockRep.former` read).  The stage's premises are
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
tuple** (the datum's `functor` clause), from the premise. -/
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

/-- **The interp law** (the datum's `leaf` clause): member `m`'s leaf
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
its former's reading (what `FormersTyped` and `BlockRep.former` read
at the datum).  Premises: the block premise, and per member its
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

end ConLeche.Model
