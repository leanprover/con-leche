module

public import ConLeche.Model.Inductives.BlockRecTyped
public section

/-!
# The recursors' stage: the readings at the datum (task #315 U-8, M4 s4a)

The block's recursor types are read (`mutualRecDataAV`, `MutualRecRead.lean`)
off lists in BLOCK ORDER — the members' leaves, index counts and index
data, the constructors' data — and off two position tables, a minor's
member (`mots`) and its fields' targets (`tgts`).  `BlockReadings`
(`BlockRecTyped.lean`) says those readings are the datum's.  Here the
lists and tables are BUILT from the datum: member `t`'s entries are its
readers, the constructor list is the members' `cds` flattened in block
order, the position tables are the same flattening of the members'
indices and target readers — so that `BlockReadings` holds at them by
position (`blockReadings_of`), the one non-positional clause (`below`,
the readings' closedness) taken from the stored recursor type's own
(`MutualRecData.below`).

The flattening is `List.flatMap` over `List.range d.k`; the datum's
`minorIdx c j` is exactly the flat position of member `c`'s
constructor `j` (`getElem?_flatMap_range`), and every flat position
decomposes that way (`flatMap_range_index`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen
  BinderMeta MutualFormerA)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The members stored at the datum's readings -/

/-- **A member is stored at the datum's readings** — the recursor
stage's one run fact beyond the datum (M4 s4a): its checked constant is
what the store finds under its name, at the block's level parameters,
its telescope ends in its OWN sort (equivalent to the block's), and
its parameter data are the datum's.  Supplied by `blockReps_of`. -/
structure MemberStored (m : EnvModel V env) (lps : List Name) (nP : Nat) (f : MutualFormerA)
    (resSort : Level) (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  find : env.find? f.cvTa.name = some (.indInfo f.cvTa {})
  lps : f.cvTa.levelParams = lps
  strip : ∃ bs : List (Expr × BinderMeta),
    f.cvTa.type.stripPis (nP + f.nIdx) = some (bs, Expr.sort f.s)
  sEq : ∀ ψ : Name → Nat, f.s.eval ψ = resSort.eval ψ
  data : FormerData m f.cvTa (nP + f.nIdx) resSort pps

/-! ## Positions in a block-ordered flat list -/

omit [SetTheory V] in
theorem flatMap_range_succ {α : Type} (L : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap L = (List.range k).flatMap L ++ L k := by
  rw [List.range_succ, List.flatMap_append]
  simp

omit [SetTheory V] in
theorem length_flatMap_range {α : Type} (L : Nat → List α) (k : Nat) :
    ((List.range k).flatMap L).length = ((List.range k).map fun t => (L t).length).sum := by
  rw [List.length_flatMap]

omit [SetTheory V] in
/-- Member `c`'s entry `j` sits at the flat position `offset c + j`. -/
theorem getElem?_flatMap_range {α : Type} (L : Nat → List α) :
    ∀ (k c j : Nat), c < k → j < (L c).length →
      ((List.range k).flatMap L)[((List.range c).map fun t => (L t).length).sum + j]? = (L c)[j]?
  | 0, _, _, hc, _ => absurd hc (Nat.not_lt_zero _)
  | k + 1, c, j, hc, hj => by
    rw [flatMap_range_succ]
    rcases Nat.lt_or_ge c k with hck | hck
    · rw [List.getElem?_append_left]
      · exact getElem?_flatMap_range L k c j hck hj
      · rw [length_flatMap_range]
        have := sum_range_lt (fun t => (L t).length) k c hck
        omega
    · obtain rfl : c = k := by omega
      rw [List.getElem?_append_right (by rw [length_flatMap_range]; omega), length_flatMap_range,
        Nat.add_sub_cancel_left]

omit [SetTheory V] in
/-- Every flat position is some member's entry. -/
theorem flatMap_range_index {α : Type} (L : Nat → List α) :
    ∀ (k J : Nat), J < ((List.range k).map fun t => (L t).length).sum →
      ∃ c j, c < k ∧ j < (L c).length ∧ J = ((List.range c).map fun t => (L t).length).sum + j
  | 0, _, hJ => by simp at hJ
  | k + 1, J, hJ => by
    rw [List.range_succ, List.map_append, List.sum_append] at hJ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hJ
    rcases Nat.lt_or_ge J (((List.range k).map fun t => (L t).length).sum) with hlt | hge
    · obtain ⟨c, j, hc, hj, rfl⟩ := flatMap_range_index L k J hlt
      exact ⟨c, j, Nat.lt_succ_of_lt hc, hj, rfl⟩
    · exact ⟨k, J - ((List.range k).map fun t => (L t).length).sum, Nat.lt_succ_self k, by omega,
        by omega⟩

/-! ## The readings, built from the datum -/

namespace BlockRepData

variable (d : BlockRepData V)

/-- The members' leaves, in block order. -/
@[expose] def recLs (m : EnvModel V env) (ψ : Name → Nat) : List AnnotTerm :=
  (List.range d.k).map fun t => m.acval (d.memberName t) ψ

/-- The members' index counts, in block order. -/
@[expose] def recNIdxs : List Nat := (List.range d.k).map d.nIdxAt

/-- The block's parameter data (member `0`'s). -/
@[expose] def recPps (ψ : Name → Nat) : List (Nat × Nat × AnnotTerm) := (d.ppsM 0 ψ).take d.nP

/-- The members' index data, in block order. -/
@[expose] def recIpss (ψ : Name → Nat) : List (List (Nat × Nat × AnnotTerm)) :=
  (List.range d.k).map fun t => (d.ppsM t ψ).drop d.nP

/-- The constructors' data, member by member. -/
@[expose] def recCds (ψ : Name → Nat) : List CtorDatumR :=
  (List.range d.k).flatMap fun c => d.cds c ψ

/-- The minors' members, as a list. -/
@[expose] def recMotsL : List Nat :=
  (List.range d.k).flatMap fun c => List.replicate (d.ctorsM c).length c

/-- A minor's member. -/
@[expose] def recMots (J : Nat) : Nat := d.recMotsL.getD J 0

/-- The minors' target readers, as a list. -/
@[expose] def recTgtsL : List (Nat → Nat) :=
  (List.range d.k).flatMap fun c => (List.range (d.ctorsM c).length).map fun j => d.tgts c j

/-- A minor's fields' targets. -/
@[expose] def recTgts (J : Nat) : Nat → Nat := d.recTgtsL.getD J (fun _ => 0)

/-- The member table (member `0` off the block). -/
@[expose] def recTname (q : Nat) : Name := d.memberName (if q < d.k then q else 0)

theorem recLs_length (m : EnvModel V env) (ψ : Name → Nat) : (d.recLs m ψ).length = d.k := by
  simp [recLs]

theorem recLs_getD (m : EnvModel V env) (ψ : Name → Nat) {t : Nat} (ht : t < d.k) :
    (d.recLs m ψ).getD t default = m.acval (d.memberName t) ψ :=
  getD_range_map _ _ _ ht _

omit [SetTheory V] in
theorem recNIdxs_getD {t : Nat} (ht : t < d.k) : d.recNIdxs.getD t 0 = d.nIdxAt t :=
  getD_range_map _ _ _ ht _

omit [SetTheory V] in
theorem recIpss_getD (ψ : Name → Nat) {t : Nat} (ht : t < d.k) :
    (d.recIpss ψ).getD t [] = (d.ppsM t ψ).drop d.nP :=
  getD_range_map _ _ _ ht _

omit [SetTheory V] in
theorem cds_length (c : Nat) (ψ : Name → Nat) : (d.cds c ψ).length = (d.ctorsM c).length :=
  fixCtorDataList_length _ _ _ _ _ _ _ _

omit [SetTheory V] in
theorem recCds_length (ψ : Name → Nat) : (d.recCds ψ).length = d.nCtors := by
  unfold recCds nCtors
  rw [length_flatMap_range]
  congr 1
  exact List.map_congr_left fun c _ => d.cds_length c ψ

omit [SetTheory V] in
theorem minorIdx_eq_offset (c j : Nat) (ψ : Name → Nat) :
    d.minorIdx c j = ((List.range c).map fun t => (d.cds t ψ).length).sum + j := by
  unfold minorIdx
  congr 2
  exact List.map_congr_left fun t _ => (d.cds_length t ψ).symm

omit [SetTheory V] in
theorem recCds_getElem? (ψ : Name → Nat) {c j : Nat} (hc : c < d.k) (hj : j < (d.ctorsM c).length) :
    (d.recCds ψ)[d.minorIdx c j]? = (d.cds c ψ)[j]? := by
  rw [d.minorIdx_eq_offset c j ψ]
  exact getElem?_flatMap_range _ d.k c j hc (by rw [d.cds_length]; exact hj)

omit [SetTheory V] in
theorem cds_getElem? (ψ : Name → Nat) {c j : Nat} {cA : ConstantVal × Nat}
    (hj : (d.ctorsM c)[j]? = some cA) :
    (d.cds c ψ)[j]? = some (cA.1.name, cA.2, d.dsF c j ψ, d.esF c j ψ,
      ConLeche.recIdxOf (d.ksF c j), d.eissF c j ψ, d.tssF c j ψ) := by
  unfold cds
  rw [fixCtorDataList_getElem?, hj, Nat.zero_add]
  rfl

omit [SetTheory V] in
theorem recMots_at {c j : Nat} (hc : c < d.k) (hj : j < (d.ctorsM c).length) :
    d.recMots (d.minorIdx c j) = c := by
  unfold recMots recMotsL
  have := getElem?_flatMap_range (fun c => List.replicate (d.ctorsM c).length c) d.k c j hc
    (by rw [List.length_replicate]; exact hj)
  simp only [List.length_replicate] at this
  have hm : d.minorIdx c j = ((List.range c).map fun t => (d.ctorsM t).length).sum + j := rfl
  rw [List.getD_eq_getElem?_getD, hm, this, List.getElem?_replicate_of_lt hj]
  rfl

omit [SetTheory V] in
theorem recTgts_at {c j : Nat} (hc : c < d.k) (hj : j < (d.ctorsM c).length) :
    d.recTgts (d.minorIdx c j) = d.tgts c j := by
  unfold recTgts recTgtsL
  have := getElem?_flatMap_range (fun c => (List.range (d.ctorsM c).length).map fun j => d.tgts c j)
    d.k c j hc (by rw [List.length_map, List.length_range]; exact hj)
  simp only [List.length_map, List.length_range] at this
  have hm : d.minorIdx c j = ((List.range c).map fun t => (d.ctorsM t).length).sum + j := rfl
  rw [List.getD_eq_getElem?_getD, hm, this, List.getElem?_map, List.getElem?_range hj]
  rfl

omit [SetTheory V] in
/-- Every minor is some member's constructor. -/
theorem minor_index {J : Nat} (hJ : J < d.nCtors) :
    ∃ c j cA, c < d.k ∧ (d.ctorsM c)[j]? = some cA ∧ J = d.minorIdx c j := by
  obtain ⟨c, j, hc, hj, rfl⟩ := flatMap_range_index (fun c => d.ctorsM c) d.k J hJ
  exact ⟨c, j, _, hc, List.getElem?_eq_getElem hj, rfl⟩

omit [SetTheory V] in
theorem recTname_lt {q : Nat} (hq : q < d.k) : d.recTname q = d.memberName q := by
  unfold recTname
  rw [if_pos hq]

/-- **Member `t`'s recursor type's binder data** at the datum's lists. -/
@[expose] def blockRds (m : EnvModel V env) (elimL : Level) (t : Nat) (ψ : Name → Nat) :
    List (Nat × Nat × AnnotTerm) :=
  mutualRecDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
    d.recMots d.recTgts t

/-- **Member `t`'s recursor type's conclusion**. -/
@[expose] def blockConc (t : Nat) : AnnotTerm := mutualConcAV d.k d.nCtors (d.nIdxAt t) t

end BlockRepData

/-! ## `BlockReadings` at them -/

/-- **The readings built from the datum are the datum's**: every clause
by position, the closedness the stored recursor types' own. -/
theorem BlockRepData.blockReadings_of (d : BlockRepData V) (m : EnvModel V env) (ψ : Name → Nat)
    (elimL : Level)
    (hbelow : ∀ mm, mm < d.k →
      DomsBelow 0 (mutualRecDataAV m ψ (d.recLs m ψ) d.nP d.recNIdxs elimL (d.recPps ψ)
        (d.recIpss ψ) (d.recCds ψ) d.recMots d.recTgts mm)) :
    BlockReadings m d ψ elimL (d.recLs m ψ) d.recNIdxs (d.recPps ψ) (d.recIpss ψ) (d.recCds ψ)
      d.recMots d.recTgts where
  lsLen := d.recLs_length m ψ
  leafAt := fun t ht => d.recLs_getD m ψ ht
  nIdxAt := fun t ht => d.recNIdxs_getD ht
  ppsDom := rfl
  ipsAt := fun t ht => d.recIpss_getD ψ ht
  cdsLen := d.recCds_length ψ
  cdsAt := fun c j cA hc hj => by
    rw [d.recCds_getElem? ψ hc (List.getElem?_eq_some_iff.mp hj).1, d.cds_getElem? ψ hj]
  motsAt := fun c j hc hj => d.recMots_at hc hj
  tgtsAt := fun c j hc hj => d.recTgts_at hc hj
  below := hbelow

end ConLeche.Model
