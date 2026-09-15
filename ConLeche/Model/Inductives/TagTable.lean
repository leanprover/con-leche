module

public import ConLeche.Semantics.Tower.MutualLeafI
import ConLeche.Semantics.Tower.FixSquashI
public section

/-!
# The mutual block's tag table (task #279 D-1, DESIGN §M.60 (j))

The fixpoint kit tags a value by its constructor's MEMBER-LOCAL
position through a tag table `tbl : List (List Nat)` (row `m` = the
flat positions of member `m`'s constructors, `ConLeche/Semantics/Tower/
SumCase.lean`).  This module is the mutual reduction's table: rows are
the filters of the flat constructor range by the constructor→member
map, so they are Nodup and disjoint (`TblOk`), a flat constructor is
in its member's row, and its local tag maps back to it
(`mutTagTbl_flatOf_locOf`).  The kit's premise `OffOk` at the auxiliary
family's tag index follows from `TagOk` and the table's validity
(`offOk_of_tagOk`): the tag universe is positive, there is one index,
and every index tuple `⟨inj m ⟨ı⃗⟩⟩` is a tag tuple.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The mutual block's tag table**: row `m` lists the flat positions
`J < n` of member `m`'s constructors (`memF J = m`), in order. -/
@[expose] def mutTagTbl (k : Nat) (memF : Nat → Nat) (n : Nat) : List (List Nat) :=
  (List.range k).map fun m => (List.range n).filter fun J => memF J == m

omit [SetTheory V] in
theorem mutTagTbl_getD {k n : Nat} {memF : Nat → Nat} {m : Nat} (hm : m < k) :
    (mutTagTbl k memF n).getD m [] = (List.range n).filter fun J => memF J == m := by
  unfold mutTagTbl
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

omit [SetTheory V] in
theorem mutTagTbl_getD_ge {k n : Nat} {memF : Nat → Nat} {m : Nat} (hm : k ≤ m) :
    (mutTagTbl k memF n).getD m [] = [] := by
  unfold mutTagTbl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [List.length_map, List.length_range]; exact hm)]
  rfl

omit [SetTheory V] in
/-- Row `m` holds exactly member `m`'s constructors. -/
theorem mem_mutTagTbl_row {k n : Nat} {memF : Nat → Nat} {m J : Nat} (hm : m < k) :
    J ∈ (mutTagTbl k memF n).getD m [] ↔ J < n ∧ memF J = m := by
  rw [mutTagTbl_getD hm, List.mem_filter, List.mem_range]
  simp

omit [SetTheory V] in
/-- **The table is valid**: rows Nodup, distinct rows disjoint. -/
theorem mutTagTbl_tblOk (k : Nat) (memF : Nat → Nat) (n : Nat) : TblOk (mutTagTbl k memF n) := by
  refine ⟨fun row hrow => ?_, fun i j hij J hJi hJj => ?_⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.mp hrow
    exact List.Nodup.sublist List.filter_sublist List.nodup_range
  · by_cases hi : i < k
    · by_cases hj : j < k
      · rw [mem_mutTagTbl_row hi] at hJi
        rw [mem_mutTagTbl_row hj] at hJj
        omega
      · rw [mutTagTbl_getD_ge (by omega)] at hJj
        exact List.not_mem_nil hJj
    · rw [mutTagTbl_getD_ge (by omega)] at hJi
      exact List.not_mem_nil hJi

omit [SetTheory V] in
/-- At a valid table an entry of row `m` at its local tag is itself:
`flatOf tbl n m (locOf tbl J) = J`. -/
theorem flatOf_locOf_of_mem {tbl : List (List Nat)} (h : TblOk tbl) {m J : Nat}
    (hmem : J ∈ tbl.getD m []) (n : Nat) : flatOf tbl n m (locOf tbl J) = J := by
  cases tbl with
  | nil => exact absurd hmem (by simp)
  | cons r rs =>
    have hfind := find?_row_of_mem h hmem
    have hloc : locOf (r :: rs) J = ((r :: rs).getD m []).idxOf J := by
      unfold locOf
      rw [hfind]
    rw [flatOf_cons, hloc, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr hmem), Option.getD_some,
      List.getElem_idxOf]

omit [SetTheory V] in
/-- **A constructor's local tag maps back to it** in the mutual table. -/
theorem mutTagTbl_flatOf_locOf {k n : Nat} {memF : Nat → Nat} {J : Nat} (hJ : J < n) (hm : memF J < k) :
    flatOf (mutTagTbl k memF n) n (memF J) (locOf (mutTagTbl k memF n) J) = J :=
  flatOf_locOf_of_mem (mutTagTbl_tblOk k memF n) ((mem_mutTagTbl_row hm).mpr ⟨hJ, rfl⟩) n

omit [SetTheory V] in
/-- The local tag is a row position: below the member's constructor count. -/
theorem mutTagTbl_locOf_lt {k n : Nat} {memF : Nat → Nat} {J : Nat} (hJ : J < n) (hm : memF J < k) :
    locOf (mutTagTbl k memF n) J < ((mutTagTbl k memF n).getD (memF J) []).length := by
  have hmem : J ∈ (mutTagTbl k memF n).getD (memF J) [] := (mem_mutTagTbl_row hm).mpr ⟨hJ, rfl⟩
  have hne : mutTagTbl k memF n ≠ [] := by
    unfold mutTagTbl
    intro h
    rw [List.map_eq_nil_iff, List.range_eq_nil] at h
    omega
  obtain ⟨r, rs, htbl⟩ : ∃ r rs, mutTagTbl k memF n = r :: rs := by
    cases hh : mutTagTbl k memF n with
    | nil => exact absurd hh hne
    | cons r rs => exact ⟨r, rs, rfl⟩
  rw [htbl] at hmem ⊢
  have hloc : locOf (r :: rs) J = ((r :: rs).getD (memF J) []).idxOf J := by
    unfold locOf
    rw [find?_row_of_mem (htbl ▸ mutTagTbl_tblOk k memF n) hmem]
  rw [hloc]
  exact List.idxOf_lt_length_iff.mpr hmem

/-! ## The kit's premise at the tag index -/

/-- The sum's fibres at a tag element lie in the tag universe. -/
theorem tagFibre_univ {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (hT : TagOk W ρp Idss)
    (k : V) : natFibre (sumFibre W ρp (uChains Idss)) k ∈ˢ (univ W : V) := by
  unfold natFibre
  split
  · rename_i h
    unfold sumFibre
    cases hi : (uChains Idss)[Classical.choose h]? with
    | none => exact empty_mem_univ W
    | some Fs =>
      exact towerSet_univ_teleOfFields ((hT.sumOk Fs (List.mem_of_getElem? hi)).toBound hT.1)
  · exact empty_mem_univ W

/-- **Every index tuple of the auxiliary family is a tag tuple**:
`⟨inj m ⟨ı⃗⟩⟩ = spair (inj m …) pt`, a graded pair over the tag set,
whose first component is a graded pair over `ω`. -/
theorem tagTuple_of_mem {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (hT : TagOk W ρp Idss)
    {t : V} (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) : TagTuple t := by
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim ht
  obtain ⟨hv, hu, -⟩ := tagTyAV_facts hT
  -- the spine is one tag element
  rcases is with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact hsp.elim
  · obtain ⟨ha, -⟩ := hsp
    rw [hv] at ha
    rw [tupW_pos hT.1]
    show TagTuple (spair a pt)
    have haS : a ∈ˢ sigmaSet W omega (natFibre (sumFibre W ρp (uChains Idss))) := ha
    obtain ⟨kk, p, hk, -, -, hpos⟩ := mem_sigma_elim haS
    refine ⟨⟨W, W, tagSet W ρp Idss, fun _ => unitSet, ?_, hu, fun _ _ => unitSet_mem_univ W⟩,
      ⟨W, W, omega, natFibre (sumFibre W ρp (uChains Idss)), ?_, omega_mem_univ_pos hT.1,
        fun k _ => tagFibre_univ hT k⟩, ?_⟩
    · rw [show Nat.max W W = W from Nat.max_self W]
      exact spair_mem hT.1 ha pt_mem_unitSet
    · rw [sfst_spair, show Nat.max W W = W from Nat.max_self W]
      exact haS
    · rw [sfst_spair, hpos hT.1, sfst_spair]
      exact hk
  · exact hsp.2.elim

/-- **The kit's tag-table premise at the auxiliary family's index**,
from the tag's grading and the table's validity. -/
theorem offOk_of_tagOk {tbl : List (List Nat)} {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (hT : TagOk W ρp Idss) (htbl : TblOk tbl) : OffOk tbl W ρp (auxIds W Idss) :=
  fun _ => ⟨hT.1, by simp [auxIds], htbl, fun t ht => tagTuple_of_mem hT ht⟩

end ConLeche.Model
