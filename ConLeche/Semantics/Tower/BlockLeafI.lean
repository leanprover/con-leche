module

public import ConLeche.Semantics.Tower.BlockTuple
public import ConLeche.Semantics.Tower.FixLeafI
import ConLeche.Semantics.Univ
import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# The type-former leaf of a BLOCK of `k` recursive families (task #315)

The `k = 1` route's carrier is the least pre-fixed FAMILY of one
constructor-tower functor (`fixFamI`, `FixLeafI.lean`).  A block of `k`
mutually recursive families is the least pre-fixed TUPLE of ONE functor
on tuples of families (`lfpTuple`,
`ConLeche/SetTheory/Derive/LfpTuple.lean`), member `m`'s component
living over its OWN index-tuple set `I_m` at its own index universe
`u_m` — no member tag enters any index set, and a member whose indices
are all propositions keeps `u_m = 0` and the point tuple:

    T_m := λ p⃗ ı⃗_m. proj_m (lfpTuple.{u⃗, w} ⟨I_0, …, I_{k-1}⟩ F) ⟨ı⃗_m⟩
    F   := λ (Xs : ⟨I_0 → Sort w, …⟩). ⟨λ t. Σ_j tower_{m,j}(Xs, t)⟩_m

A recursive field of constructor `j` of member `m` targeting member `c`
reads `proj_c Xs ⟨e⃗⟩` — the k = 1 slot with ONE projection in front of
the family variable, and the index tuple built by the TARGET's own
tupler (`slotXBI`).  Constructor tags stay MEMBER-LOCAL: member `m`'s
sum runs over member `m`'s own constructors, `sumMkAV w j` with `j` the
member-local position, exactly the k = 1 code per member.

This module: the spelled pieces, their readings and gradings, the
block's semantic operator, and the leaf's three laws
(`blockTyG_mem/_wellDenoted/_fold`) under one hereditary premise
(`ParamsOkXBI`).  The functor's semantic laws (monotonicity, the closed
tuple, the fixed point, the per-member fibre law) are in `BlockFamI.lean`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower
open ConLeche.Term (lv tupleIdxSort tupleFamSort)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The block's level list -/

/-- The block's level instantiation of `lfpTuple k`: one index
universe per member, then the block's own sort. -/
def blockUs (k w : Nat) (uf : Nat → Nat) : List Nat := (List.range k).map uf ++ [w]

theorem blockUs_lt {k w : Nat} {uf : Nat → Nat} {m : Nat} (hm : m < k) :
    lv (blockUs k w uf) m = uf m := by
  unfold blockUs ConLeche.Term.lv
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hm),
    List.getElem?_map, List.getElem?_range hm]
  rfl

theorem blockUs_top (k w : Nat) (uf : Nat → Nat) : lv (blockUs k w uf) k = w := by
  unfold blockUs ConLeche.Term.lv
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The block's family-tuple sort, the numeral every binder of
`lfpTuple k`'s type carries. -/
abbrev blockR (k w : Nat) (uf : Nat → Nat) : Nat := tupleFamSort k (blockUs k w uf)

/-- The block's index-tuple sort. -/
abbrev blockS (k w : Nat) (uf : Nat → Nat) : Nat := tupleIdxSort (blockUs k w uf)

theorem blockR_ne_zero (k w : Nat) (uf : Nat → Nat) : blockR k w uf ≠ 0 :=
  tupleFamSort_ne_zero k _

theorem blockS_ne_zero (k w : Nat) (uf : Nat → Nat) : blockS k w uf ≠ 0 :=
  tupleIdxSort_ne_zero _

/-! ## The target-aware recursive slot and the members' chains -/

/-- **The recursive slot of a block**: the k = 1 slot (`slotXI`,
`FixLeafI.lean`) with the target member's projection in front of the
family variable and the TARGET's index tupler building the tuple —
`Π a⃗ : A⃗, proj_c Xs ⟨e⃗_i(a⃗)⟩`. -/
def slotXBI (uc : Nat) (Idc : List AnnotTerm) (c : Nat)
    (tl : List (Nat × Nat × AnnotTerm)) (Eis : List AnnotTerm) (i : Nat) : AnnotTerm :=
  mkPisAV (liftTele2 i tl)
    (.app (projAV c (.bvar (i + 1 + tl.length)))
      (AnnotTerm.mkAppN ((tuplerAV uc Idc).liftN (i + 2 + tl.length) 0)
        (Eis.map (·.liftN 2 (i + tl.length)))))

/-- The X-chain of one constructor of one member, from position `i` on:
a recursive slot reads the TARGET component of the family tuple, an
ordinary domain is lifted past `Xs` and `t`. -/
def chainXBIGo (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) : List AnnotTerm → Nat → List AnnotTerm
  | [], _ => []
  | F :: Fs, i =>
    (if rs.getD i false then
      slotXBI (uf (tgts.getD i 0)) (Idss (tgts.getD i 0)) (tgts.getD i 0)
        (tls.getD i []) (Eis.getD i []) i
     else F.liftN 2 i) :: chainXBIGo uf Idss rs tgts tls Eis Fs (i + 1)

/-- The X-chain entry at position `i` (the head of `chainXBIGo`
there): a recursive slot at the field's TARGET, or the lifted
domain. -/
def xEntryB (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool) (tgts : List Nat)
    (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm)) (F : AnnotTerm)
    (i : Nat) : AnnotTerm :=
  if rs.getD i false then
    slotXBI (uf (tgts.getD i 0)) (Idss (tgts.getD i 0)) (tgts.getD i 0)
      (tls.getD i []) (Eis.getD i []) i
  else F.liftN 2 i

omit [SetTheory V] in
theorem chainXBIGo_cons (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) (F : AnnotTerm) (Fs : List AnnotTerm) (i : Nat) :
    chainXBIGo uf Idss rs tgts tls Eis (F :: Fs) i
      = xEntryB uf Idss rs tgts tls Eis F i :: chainXBIGo uf Idss rs tgts tls Eis Fs (i + 1) :=
  rfl

omit [SetTheory V] in
theorem chainXBIGo_length (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) :
    ∀ (Fs : List AnnotTerm) (i : Nat), (chainXBIGo uf Idss rs tgts tls Eis Fs i).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, i => by simp [chainXBIGo, chainXBIGo_length uf Idss rs tgts tls Eis Fs (i + 1)]

/-- One constructor's X-chain, equation-terminated at the member's own
index arity. -/
def chainXBI (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (nIdx : Nat) (rs : List Bool)
    (tgts : List Nat) (tls : List (List (Nat × Nat × AnnotTerm)))
    (Eis : List (List AnnotTerm)) (Fs Es : List AnnotTerm) : List AnnotTerm :=
  chainXBIGo uf Idss rs tgts tls Eis Fs 0 ++ [idxEqAV (eqsXI nIdx Fs.length Es)]

/-- Member `m`'s constructors' X-chains. -/
def chainsXBI (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tgtss : List (List Nat))
    (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) :
    List (List AnnotTerm) :=
  (List.range Fss.length).map fun j =>
    chainXBI uf Idss nIdx (rss.getD j []) (tgtss.getD j []) (tlss.getD j [])
      (Eiss.getD j []) (Fss.getD j []) (Ess.getD j [])

theorem chainsXBI_getElem? (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) (nIdx : Nat)
    (rss : List (List Bool)) (tgtss : List (List Nat))
    (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss : List (List (List AnnotTerm))) (Fss Ess : List (List AnnotTerm)) (j : Nat) :
    (chainsXBI uf Idss nIdx rss tgtss tlss Eiss Fss Ess)[j]?
      = if j < Fss.length then
          some (chainXBI uf Idss nIdx (rss.getD j []) (tgtss.getD j []) (tlss.getD j [])
            (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))
        else none := by
  unfold chainsXBI
  rw [List.getElem?_map]
  split
  · next h => rw [List.getElem?_range h]; rfl
  · next h => rw [List.getElem?_eq_none (by simpa using h)]; rfl

/-! ## The operator, the carrier tuple, and the leaf -/

/-- Member `m`'s arm of the block operator, under the family-tuple
binder: `λ (t : I_m). Σ_j tower_{m,j}(Xs, t)`. -/
def blockArmG (w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : AnnotTerm :=
  .lam (w + 1) ((idxTyAV (uf m) (Idss m)).liftN 1 0)
    (sumBodyAV w (Chs m))

/-- The family tuple's type, spelled at the block's own index sets
(`Fams` at the concrete `⟨I_0, …⟩` rather than at a bound tuple). -/
def famsTyBAV (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) : AnnotTerm :=
  ndTowerAV (blockR k w uf) (fun m => famTyAV (uf m) w (Idss m)) 0 0 k

/-- The index-set tuple `⟨I_0, …, I_{k-1}⟩`. -/
def idxTupAV (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm) : AnnotTerm :=
  ndMkTowerAV (blockS k w uf) (fun m => .sort (uf m)) (fun m => idxTyAV (uf m) (Idss m)) 0 k

/-- **The block's operator**: ONE λ over the family tuple, the tuple of
the members' arms. -/
def blockFunG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm)) :
    AnnotTerm :=
  .lam (blockR k w uf) (famsTyBAV k w uf Idss)
    (ndMkTowerAV (blockR k w uf) (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
      (fun m => blockArmG w uf Idss Chs m) 0 k)

/-- The block's carrier tuple: `lfpTuple k` at the index-set tuple and
the operator. -/
def blockBodyG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm)) :
    AnnotTerm :=
  AnnotTerm.mkAppN (.const (.lfpTuple k) (blockUs k w uf))
    [idxTupAV k w uf Idss, blockFunG k w uf Idss Chs]

/-- **Member `m`'s type-former leaf**: the λ-tower over the parameter
and index domains, the carrier tuple's `m`-th component at the tuple of
the index variables. -/
def blockTyG (k w : Nat) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (pps : List (Nat × Nat × AnnotTerm)) (m : Nat) : AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2))
    (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
        (Idss m).length 0))
      (mkTowerGo (uf m) (Idss m)))

/-! ## The block's semantic operator -/

/-- The members' index-tuple sets at a parameter frame. -/
noncomputable def blockIdx (uf : Nat → Nat) (ρp : Nat → V) (Idss : Nat → List AnnotTerm) :
    Nat → V := fun m => idxSet (uf m) ρp (Idss m)

/-- The operator's fibre at `(Y, t)` for member `m`, with `Y` the
family tuple AS A VALUE (the frame's family slot, which the chains read
through `projS`) — `fixStepI`'s twin. -/
noncomputable def blockStepG (w : Nat) (ρp : Nat → V) (Chs : Nat → List (List AnnotTerm))
    (m : Nat) (Y t : V) : V :=
  sumSet w (sumFibre w (cons t (cons Y ρp)) (Chs m))

/-- **The block's tuple operator**: componentwise the member's own
graph over its own index-tuple set, the argument tuple passed to the
chains as the uniform tupler of its components. -/
noncomputable def blockPhiG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    (Nat → V) → Nat → V :=
  fun Xs m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
    (blockStepG w ρp Chs m (ndMkTowerSet Xs 0 k))

/-- **The block's carrier**: the least pre-fixed tuple of its
operator. -/
noncomputable def blockFamG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    Nat → V :=
  lfpTuple w k (blockIdx uf ρp Idss)
    (blockPhiG k w ρp uf Idss Chs)

/-! ## The premises and the level bookkeeping -/

/-- The members' index telescopes are graded, below `k`. -/
def BlockIdxOk (k : Nat) (uf : Nat → Nat) (ρp : Nat → V) (Idss : Nat → List AnnotTerm) : Prop :=
  ∀ m, m < k → IdxOk (uf m) ρp (Idss m)

/-- The family tuple's carrier at the block's own index sets. -/
noncomputable def famsSpaceB (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) : V :=
  ndTowerSet V (blockR k w uf) (fun m => lfpFamSpace V w (idxSet (uf m) ρp (Idss m))) 0 k

/-- **The X-chains are graded** at every family tuple of the tuple
space and every index tuple of the member (`FixChainsOkI` at `k`). -/
def BlockChainsOkG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    Prop :=
  ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ m, m < k → ∀ t, t ∈ˢ idxSet (uf m) ρp (Idss m) →
    SumFieldsOkB w (cons t (cons Y ρp))
      (Chs m)

section Levels

variable {k w : Nat} {uf : Nat → Nat}

theorem uf_le_levMax {m : Nat} (hm : m < k) :
    uf m ≤ ConLeche.Term.levMax (blockUs k w uf) := by
  have h : lv (blockUs k w uf) m = uf m := blockUs_lt hm
  rw [← h]
  exact ConLeche.Term.lv_le_levMax _ m

theorem univ_uf_mem_blockS {m : Nat} (hm : m < k) :
    (univ (uf m) : V) ∈ˢ (univ (blockS k w uf) : V) :=
  univ_mono (Nat.succ_le_succ (uf_le_levMax hm)) _ (univ_mem_univ _)

theorem famSpace_mem_blockR {m : Nat} (hm : m < k) {I : V} (hI : I ∈ˢ (univ (uf m) : V)) :
    lfpFamSpace V w I ∈ˢ (univ (blockR k w uf) : V) := by
  have h := piR_mem_univ (u := uf m) (v := w + 1) hI (fun _ _ => univ_mem_univ w)
  rw [if_neg (Nat.succ_ne_zero _)] at h
  refine univ_mono ?_ _ h
  refine Nat.max_le_of_le_of_le (Nat.le_trans (uf_le_levMax hm) (Nat.le_max_left _ _)) ?_
  have : w + 1 = lv (blockUs k w uf) k + 1 := by rw [blockUs_top]
  rw [this]
  exact Nat.le_max_right _ _

end Levels

/-! ## The two spelled tuples -/

section Facts

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- **The index-set tuple**: its value, its grading. -/
theorem idxTupAV_facts (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    interp V ρp (idxTupAV k w uf Idss) = ndMkTowerSet (blockIdx uf ρp Idss) 0 k ∧
      WellDenoted V ρp (idxTupAV k w uf Idss) :=
  ndMkTowerAV_facts (blockS_ne_zero k w uf) k 0
    (fun _ _ => rfl) (fun _ _ => trivial)
    (fun m hm => univ_uf_mem_blockS (by omega))
    (fun m hm => (idxTyAV_facts (hI m (by omega))).1)
    (fun m hm => (idxTyAV_facts (hI m (by omega))).2.2)
    (fun m hm => (idxTyAV_facts (hI m (by omega))).2.1)

/-- **The family tuple's type**: its value, its grading. -/
theorem famsTyBAV_facts (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    interp V ρp (famsTyBAV k w uf Idss) = famsSpaceB k w ρp uf Idss ∧
      WellDenoted V ρp (famsTyBAV k w uf Idss) :=
  ⟨ndTowerAV_interp V k 0 0 ρp (shiftE_zero_zero ρp)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).1)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1),
   ndTowerAV_wellDenoted V k 0 0 ρp (shiftE_zero_zero ρp)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).1)
      (fun m hm => (famTyAV_facts (w := w) (hI m (by omega))).2.2)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1)⟩

/-- The index-set tuple's components are the members' index sets. -/
theorem projS_idxTup {m : Nat} (hm : m < k) :
    projS m (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) = idxSet (uf m) ρp (Idss m) := by
  rw [projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  rfl

end Facts

/-! ## The operator's reading -/

/-- The block operator's value: one λ over the family tuple, the tuple
of the members' graphs. -/
noncomputable def blockFunVG (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    V :=
  lamR (blockR k w uf) (famsSpaceB k w ρp uf Idss) fun Y =>
    ndMkTowerSet (fun m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
      (blockStepG w ρp Chs m Y)) 0 k

section Operator

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

theorem blockStepG_univ (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m)) :
    blockStepG w ρp Chs m Y t ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB (hok Y hY m hm t ht)

/-- Member `m`'s graph lives in its own family space. -/
theorem blockArmG_mem (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) :
    lamR (w + 1) (idxSet (uf m) ρp (Idss m))
        (blockStepG w ρp Chs m Y)
      ∈ˢ lfpFamSpace V w (idxSet (uf m) ρp (Idss m)) :=
  lamR_mem fun _ ht => blockStepG_univ hok hY hm ht

/-- The frame under the operator's family-tuple binder. -/
theorem idxTyAV_lift1B (h : IdxOk (uf m) ρp (Idss m)) (Y : V) :
    interp V (cons Y ρp) ((idxTyAV (uf m) (Idss m)).liftN 1 0) = idxSet (uf m) ρp (Idss m) ∧
      WellDenoted V (cons Y ρp) ((idxTyAV (uf m) (Idss m)).liftN 1 0) := by
  rw [interp_liftN, WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]
  exact ⟨(idxTyAV_facts h).1, (idxTyAV_facts h).2.2⟩

/-- **A member's arm**: its value and its grading, under the operator's
binder. -/
theorem blockArmG_facts (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs)
    {Y : V} (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {m : Nat} (hm : m < k) :
    interp V (cons Y ρp) (blockArmG w uf Idss Chs m)
        = lamR (w + 1) (idxSet (uf m) ρp (Idss m))
            (blockStepG w ρp Chs m Y) ∧
      WellDenoted V (cons Y ρp) (blockArmG w uf Idss Chs m) := by
  obtain ⟨hiv, hiok⟩ := idxTyAV_lift1B (m := m) (hI m hm) Y
  constructor
  · unfold blockArmG
    rw [interp_lam, hiv]
    refine lamR_congr fun t ht => ?_
    exact sumBodyAV_interp (hok Y hY m hm t ht)
  · unfold blockArmG
    rw [WellDenoted_lam]
    refine ⟨hiok, fun t ht => ?_, fun _ => (univ w : V), fun t ht => ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hiv] at ht
      exact sumBodyAV_wellDenoted (hok Y hY m hm t ht)
    · rw [hiv] at ht
      rw [sumBodyAV_interp (hok Y hY m hm t ht)]
      exact blockStepG_univ hok hY hm ht

/-- **The block's operator**: its value and its grading. -/
theorem blockFunG_facts (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    interp V ρp (blockFunG k w uf Idss Chs)
        = blockFunVG k w ρp uf Idss Chs ∧
      WellDenoted V ρp (blockFunG k w uf Idss Chs) := by
  obtain ⟨hfv, hfok⟩ := famsTyBAV_facts (w := w) hI
  have hbody : ∀ Y : V, Y ∈ˢ famsSpaceB k w ρp uf Idss →
      interp V (cons Y ρp) (ndMkTowerAV (blockR k w uf)
          (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
          (fun m => blockArmG w uf Idss Chs m) 0 k)
        = ndMkTowerSet (fun m => lamR (w + 1) (idxSet (uf m) ρp (Idss m))
            (blockStepG w ρp Chs m Y)) 0 k ∧
      WellDenoted V (cons Y ρp) (ndMkTowerAV (blockR k w uf)
          (fun m => (famTyAV (uf m) w (Idss m)).liftN 1 0)
          (fun m => blockArmG w uf Idss Chs m) 0 k) := by
    intro Y hY
    have hty : ∀ m, m < k →
        interp V (cons Y ρp) ((famTyAV (uf m) w (Idss m)).liftN 1 0)
          = lfpFamSpace V w (idxSet (uf m) ρp (Idss m)) := fun m hm => by
      rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
      exact (famTyAV_facts (hI m hm)).1
    refine ndMkTowerAV_facts (blockR_ne_zero k w uf) k 0
      (fun m hm => hty m (by omega)) (fun m hm => ?_)
      (fun m hm => famSpace_mem_blockR (by omega) (idxTyAV_facts (hI m (by omega))).2.1)
      (fun m hm => (blockArmG_facts hI hok hY (by omega)).1)
      (fun m hm => (blockArmG_facts hI hok hY (by omega)).2)
      (fun m hm => blockArmG_mem hok hY (by omega))
    rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]
    exact (famTyAV_facts (w := w) (hI m (by omega))).2.2
  refine ⟨?_, ?_⟩
  · unfold blockFunG blockFunVG
    rw [interp_lam, hfv]
    exact lamR_congr fun Y hY => (hbody Y hY).1
  · unfold blockFunG
    rw [WellDenoted_lam]
    refine ⟨hfok, fun Y hY => ?_, fun _ => famsSpaceB k w ρp uf Idss, fun Y hY => ?_,
      fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
    · rw [hfv] at hY; exact (hbody Y hY).2
    · rw [hfv] at hY
      rw [(hbody Y hY).1]
      exact ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0
        fun m hm => blockArmG_mem hok hY (by omega)

end Operator

/-! ## The carrier tuple's reading -/

section Body

variable {k w : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

theorem lfpFamSpace_eq' (w : Nat) (I : V) : lfpFamSpace V w I = famSpace w I :=
  piR_pos (Nat.succ_ne_zero w)

/-- The spelled index tuple inhabits the constant's first domain. -/
theorem idxTup_mem (hI : BlockIdxOk (V := V) k uf ρp Idss) :
    ndMkTowerSet (blockIdx uf ρp Idss) 0 k
      ∈ˢ tupleSortsSpace V k (blockUs k w uf) :=
  ndMkTowerSet_mem (blockS_ne_zero k w uf) k 0 fun m hm => by
    have hmk : m < k := by omega
    rw [blockUs_lt (w := w) hmk]
    exact (idxTyAV_facts (hI m hmk)).2.1

/-- At the spelled index tuple the constant's family-tuple space IS the
block's own. -/
theorem tupleFamsSpace_eq (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) :
    tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k)
      = famsSpaceB k w ρp uf Idss := by
  unfold tupleFamsSpace famsSpaceB
  refine ndTowerSet_congr V k 0 fun m hm => ?_
  have hmk : m < k := by omega
  rw [projS_idxTup hmk, blockUs_top]

/-- The block's operator inhabits the constant's second domain. -/
theorem blockFunVG_mem (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (blockR k w uf) (famsSpaceB k w ρp uf Idss)
        fun _ => famsSpaceB k w ρp uf Idss :=
  lamR_mem fun Y hY =>
    ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun m hm => blockArmG_mem hok hY (by omega)

/-- **The induced tuple operator IS the block's**, on the tuple space
and below `k` — the congruence `lfpTuple_congr` consumes. -/
theorem tupleOpV_blockFunVG {Xs : Nat → V} (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) {m : Nat} (hm : m < k) :
    tupleOpV V k (blockFunVG k w ρp uf Idss Chs) Xs m
      = blockPhiG k w ρp uf Idss Chs Xs m := by
  have hmem : ndMkTowerSet Xs 0 k ∈ˢ famsSpaceB k w ρp uf Idss :=
    ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun c hc => by
      rw [lfpFamSpace_eq']
      exact hXs c (by omega)
  show projS m (SetTheory.app _ (mkTower ((List.range k).map Xs))) = _
  rw [← ndMkTowerSet_zero]
  unfold blockFunVG
  rw [app_lamR_pos (blockR_ne_zero k w uf) hmem, projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  rfl

/-- The constant's application at the block's two spelled arguments. -/
theorem blockBodyG_app (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    SetTheory.app (SetTheory.app (lfpTupleV V k (blockUs k w uf))
        (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        (blockFunVG k w ρp uf Idss Chs)
      = ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k := by
  have hIs := idxTup_mem (w := w) hI
  have hF : blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [tupleFamsSpace_eq k w ρp uf Idss]; exact blockFunVG_mem hok
  rw [lfpTupleV_app V hIs hF,
    ndMkTowerSet_zero (blockFamG k w ρp uf Idss Chs) k]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  have hmk : m < k := List.mem_range.mp hm
  rw [blockUs_top]
  refine lfpTuple_congr (fun c hc => projS_idxTup hc) (fun X hX c hc => ?_) hmk
  have hX' : InTupleSpace w k (blockIdx uf ρp Idss) X := fun c hc => by
    have h : X c ∈ˢ famSpace w (projS c (ndMkTowerSet (blockIdx uf ρp Idss) 0 k)) := hX c hc
    rwa [projS_idxTup hc] at h
  exact tupleOpV_blockFunVG hX' hc

/-- **The carrier tuple reads to the tuple of the members' carriers.** -/
theorem blockBodyG_interp (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    interp V ρp (blockBodyG k w uf Idss Chs)
      = ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k := by
  have hiv := (idxTupAV_facts (w := w) hI).1
  have hfv := (blockFunG_facts hI hok).1
  show SetTheory.app (SetTheory.app (interp V ρp (.const (.lfpTuple k) (blockUs k w uf)))
    (interp V ρp (idxTupAV k w uf Idss)))
    (interp V ρp (blockFunG k w uf Idss Chs)) = _
  rw [show interp V ρp (.const (.lfpTuple k) (blockUs k w uf))
      = lfpTupleV V k (blockUs k w uf) from rfl, hiv, hfv]
  exact blockBodyG_app hI hok

/-- **The carrier tuple is in the block's family-tuple space**, with
no premise at all: the least pre-fixed tuple is total. -/
theorem blockFamG_tuple_mem (k w : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (Chs : Nat → List (List AnnotTerm)) :
    ndMkTowerSet (blockFamG k w ρp uf Idss Chs) 0 k
      ∈ˢ famsSpaceB k w ρp uf Idss :=
  ndMkTowerSet_mem (blockR_ne_zero k w uf) k 0 fun m hm => by
    rw [lfpFamSpace_eq']
    exact lfpTuple_mem w k (blockIdx uf ρp Idss) _ m (by omega)

/-- **The carrier tuple is graded.** -/
theorem blockBodyG_wellDenoted (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkG k w ρp uf Idss Chs) :
    WellDenoted V ρp (blockBodyG k w uf Idss Chs) := by
  obtain ⟨hiv, hiok⟩ := idxTupAV_facts (w := w) hI
  obtain ⟨hfv, hfok⟩ := blockFunG_facts hI hok
  have hIs := idxTup_mem (w := w) hI
  have hc : interp V ρp (.const (.lfpTuple k) (blockUs k w uf))
      = lfpTupleV V k (blockUs k w uf) := rfl
  have hF : blockFunVG k w ρp uf Idss Chs
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [tupleFamsSpace_eq k w ρp uf Idss]; exact blockFunVG_mem hok
  have hhead : SetTheory.app (interp V ρp (.const (.lfpTuple k) (blockUs k w uf)))
      (interp V ρp (idxTupAV k w uf Idss))
      ∈ˢ piR (tupleFamSort k (blockUs k w uf))
        (piR (tupleFamSort k (blockUs k w uf))
          (tupleFamsSpace V k (blockUs k w uf) (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
          fun _ => tupleFamsSpace V k (blockUs k w uf)
            (ndMkTowerSet (blockIdx uf ρp Idss) 0 k))
        fun _ => tupleFamsSpace V k (blockUs k w uf)
          (ndMkTowerSet (blockIdx uf ρp Idss) 0 k) := by
    rw [hc, hiv]
    exact app_mem_piR_pos (blockR_ne_zero k w uf) (lfpTupleV_mem V k (blockUs k w uf)) hIs
  show WellDenoted V ρp (.app (.app (.const (.lfpTuple k) (blockUs k w uf)) _) _)
  rw [WellDenoted_app]
  refine ⟨?_, hfok, tupleFamSort k (blockUs k w uf), _, _, hhead, ?_,
    fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, hiok, tupleFamSort k (blockUs k w uf),
      tupleSortsSpace V k (blockUs k w uf), _,
      hc ▸ lfpTupleV_mem V k (blockUs k w uf), hiv ▸ hIs,
      fun h0 => absurd h0 (blockR_ne_zero k w uf)⟩
  · rw [hfv]; exact hF

end Body

/-! ## The leaf's three laws -/

/-- The base of member `m`'s leaf premise, at the frame below the
parameters AND the member's index binders: the block's index
telescopes graded there, its X-chains graded there, and the frame's
index tuple fitting the member's telescope. -/
def BlockBaseG (k w : Nat) (ρ : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : Prop :=
  BlockIdxOk k uf (shiftE (Idss m).length 0 ρ) Idss ∧
  BlockChainsOkG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs ∧
  SpineFit (shiftE (Idss m).length 0 ρ) (Idss m) (frameIdx (Idss m).length ρ)

/-- `ParamsOkG`: member `m`'s leaf's one hereditary premise — the
parameter and index telescope graded, `BlockBaseG` at the base. -/
def ParamsOkG (k w : Nat) (ρ : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (Chs : Nat → List (List AnnotTerm))
    (m : Nat) : List (Nat × Nat × AnnotTerm) → Prop
  | [] => BlockBaseG k w ρ uf Idss Chs m
  | d :: pps => d.2.1 ≠ 0 ∧ WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 →
        ParamsOkG k w (cons a ρ) uf Idss Chs m pps

section Leaf

variable {k w : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- The leaf's body at the base frame: member `m`'s carrier at the
frame's index tuple. -/
theorem blockLeafBodyG_facts {ρ : Nat → V} {m : Nat} (hm : m < k)
    (h : BlockBaseG k w ρ uf Idss Chs m) :
    interp V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m)))
        = SetTheory.app
            (blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m)
            (tupW (uf m) (frameIdx (Idss m).length ρ)) ∧
      interp V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m))) ∈ˢ (univ w : V) ∧
      WellDenoted V ρ (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0)) (mkTowerGo (uf m) (Idss m))) := by
  obtain ⟨hI, hok, hsp⟩ := h
  have hρ : consList (frameIdx (Idss m).length ρ) (shiftE (Idss m).length 0 ρ) = ρ :=
    consList_frameIdx (Idss m).length ρ
  have hbv : interp V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0)
      = ndMkTowerSet (blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs) 0 k := by
    rw [interp_liftN]
    exact blockBodyG_interp hI hok
  have hbok : WellDenoted V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0) := by
    rw [WellDenoted_liftN]
    exact blockBodyG_wellDenoted hI hok
  have hbmem : interp V ρ ((blockBodyG k w uf Idss Chs).liftN
      (Idss m).length 0)
      ∈ˢ famsSpaceB k w (shiftE (Idss m).length 0 ρ) uf Idss := by
    rw [hbv]; exact blockFamG_tuple_mem k w _ uf Idss Chs
  have hpv : interp V ρ (projAV m ((blockBodyG k w uf Idss Chs).liftN (Idss m).length 0))
      = blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m := by
    rw [projAV_interp, hbv, projS_ndMkTowerSet k 0 m hm, Nat.zero_add]
  have hpok : WellDenoted V ρ (projAV m ((blockBodyG k w uf Idss Chs).liftN (Idss m).length 0)) :=
    projAV_wellDenoted_ndTower V (blockR_ne_zero k w uf) m k 0 _ ρ hm
      (fun c hc => famSpace_mem_blockR (by omega)
        (idxTyAV_facts (hI c (by omega))).2.1) hbok hbmem
  have htv : interp V ρ (mkTowerGo (uf m) (Idss m)) = tupW (uf m) (frameIdx (Idss m).length ρ) := by
    have h1 := mkTowerGo_interp (ρp := shiftE (Idss m).length 0 ρ)
      (bs := frameIdx (Idss m).length ρ) (fun _ => (hI m hm).2) hsp
    rw [hρ] at h1
    rw [h1]
    rfl
  have htok : WellDenoted V ρ (mkTowerGo (uf m) (Idss m)) := by
    have h1 := mkTowerGo_wellDenoted (ρp := shiftE (Idss m).length 0 ρ)
      (bs := frameIdx (Idss m).length ρ) (hI m hm).1 hsp
    rwa [hρ] at h1
  have htmem : tupW (uf m) (frameIdx (Idss m).length ρ)
      ∈ˢ idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m) := tupW_mem hsp
  have hfam : blockFamG k w (shiftE (Idss m).length 0 ρ) uf Idss Chs m
      ∈ˢ famSpace w (idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m)) :=
    lfpTuple_mem w k _ _ m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [interp_app, hpv, htv]
  · rw [interp_app, hpv, htv]
    exact famSpace_app hfam htmem
  · rw [WellDenoted_app]
    refine ⟨hpok, htok, w + 1, idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m),
      fun _ => (univ w : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hpv]
      have := hfam
      rwa [← lfpFamSpace_eq' (V := V) w
        (idxSet (uf m) (shiftE (Idss m).length 0 ρ) (Idss m))] at this
    · rw [htv]; exact htmem

/-- **The leaf inhabits its type's reading.** -/
theorem blockTyG_mem {m : Nat} (hm : m < k) :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkG k w ρ uf Idss Chs m pps →
      interp V ρ (blockTyG k w uf Idss Chs pps m)
        ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], _, h => (blockLeafBodyG_facts hm h).2.1
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => blockTyG_mem hm (h.2.2 a ha))

/-- **The leaf is graded.** -/
theorem blockTyG_wellDenoted {m : Nat} (hm : m < k) :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkG k w ρ uf Idss Chs m pps →
      WellDenoted V ρ (blockTyG k w uf Idss Chs pps m)
  | [], _, h => (blockLeafBodyG_facts hm h).2.2
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam (w + 1) d.2.2 (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
    rw [WellDenoted_lam]
    exact ⟨h.2.1, fun a ha => blockTyG_wellDenoted hm (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => blockTyG_mem hm (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter-and-index
spine the leaf computes member `m`'s carrier at the spine's tuple. -/
theorem blockTyG_fold {m : Nat} (hm : m < k)
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hbase : BlockBaseG k w (consList as ρ) uf Idss Chs m) :
    as.foldl SetTheory.app
        (interp V ρ (blockTyG k w uf Idss Chs pps m))
      = SetTheory.app
          (blockFamG k w (shiftE (Idss m).length 0 (consList as ρ)) uf Idss Chs m)
          (tupW (uf m) (frameIdx (Idss m).length (consList as ρ))) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [blockTyG,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp']
  exact (blockLeafBodyG_facts hm hbase).1

end Leaf


/-! ## The slot chains: the fixpoint route's instance

Everything above is generic in the members' constructor chains `Chs`
(per member, one chain per constructor, each ending in its index
equation) — lane HOLE2's hole chains are the other instance.  The
fixpoint route's X-chains (`chainsXBI`, recursive slots at the fields'
targets) are the instance below: each of its operators is the generic
one at `slotChs`, by definition. -/

/-- **The slot chains**: member `m`'s constructors' X-chains. -/
abbrev slotChs (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
    (rsss : Nat → List (List Bool)) (tgtsss : Nat → List (List Nat))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Eisss : Nat → List (List (List AnnotTerm))) (Fsss Esss : Nat → List (List AnnotTerm)) :
    Nat → List (List AnnotTerm) := fun m =>
  chainsXBI uf Idss (Idss m).length (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) (Esss m)

section Slot

variable (k w : Nat) (ρp ρ : Nat → V) (uf : Nat → Nat) (Idss : Nat → List AnnotTerm)
  (rsss : Nat → List (List Bool)) (tgtsss : Nat → List (List Nat))
  (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
  (Eisss : Nat → List (List (List AnnotTerm))) (Fsss Esss : Nat → List (List AnnotTerm))

/-- Member `m`'s arm, at the slot chains. -/
abbrev blockArmAV (m : Nat) : AnnotTerm :=
  blockArmG w uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss) m

/-- The block's operator term, at the slot chains. -/
abbrev blockFunAV : AnnotTerm :=
  blockFunG k w uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- The block's carrier tuple term, at the slot chains. -/
abbrev blockBodyAV : AnnotTerm :=
  blockBodyG k w uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- Member `m`'s type-former leaf, at the slot chains. -/
abbrev blockTyAV (pps : List (Nat × Nat × AnnotTerm)) (m : Nat) : AnnotTerm :=
  blockTyG k w uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss) pps m

/-- Member `m`'s fibre, at the slot chains. -/
noncomputable abbrev blockStepV (m : Nat) (Y t : V) : V :=
  blockStepG w ρp (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss) m Y t

/-- The block's tuple operator, at the slot chains. -/
noncomputable abbrev blockPhi : (Nat → V) → Nat → V :=
  blockPhiG k w ρp uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- The block's carrier, at the slot chains. -/
noncomputable abbrev blockFam : Nat → V :=
  blockFamG k w ρp uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- The operator's value, at the slot chains. -/
noncomputable abbrev blockFunV : V :=
  blockFunVG k w ρp uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- The slot chains are graded. -/
abbrev BlockChainsOkI : Prop :=
  BlockChainsOkG k w ρp uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss)

/-- The leaf's base premise, at the slot chains. -/
abbrev BlockBaseI (m : Nat) : Prop :=
  BlockBaseG k w ρ uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss) m

/-- The leaf's hereditary premise, at the slot chains. -/
abbrev ParamsOkXBI (m : Nat) (pps : List (Nat × Nat × AnnotTerm)) : Prop :=
  ParamsOkG k w ρ uf Idss (slotChs uf Idss rsss tgtsss tlsss Eisss Fsss Esss) m pps

end Slot

end ConLeche.Semantics
