module

public import ConLeche.Semantics.Tower.FixFamI

@[expose] public section

/-!
# The mutual block's tag family and tag tuplers (task #278)

The tag family of a mutual block — the tagged union of the members'
index towers (`tagTyAV`, `tagSet`), member `m`'s tag tupler
(`tagTuplerAV`) and the tagged tuple at index expressions
(`tagTupleAV`), the auxiliary family's one-domain index telescope
(`auxIds`), their premise (`TagOk`) and laws — together with the
block's tagged data spellings (`mutualEss`, `mutualEiss`).

Split out of `MutualLeafI.lean` so that the cased family functor
(`CaseFamI.lean`), which the member leaf is based on, can sit between
them: the leaf imports the cased functor, and the cased functor
imports this module.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The tag family and the tag tuplers -/

/-- The tag type at the parameter frame: the tagged union of the
members' index towers. -/
def tagTyAV (W : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm := sumBodyAV W (uChains Idss)

/-- The tag set at the parameter frame. -/
noncomputable def tagSet (W : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm)) : V :=
  sumSet W (sumFibre W ρp (uChains Idss))

/-- Member `m`'s tag tupler: `λ ı⃗_m, inj m ⟨ı⃗_m⟩` (the sum route's
constructor leaf at the tag family, over member `m`'s index telescope
alone). -/
def tagTuplerAV (W m : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  sumMkAV W m (tuplerData W (Idss.getD m [])) (Idss.getD m []) (uChains Idss)

/-- The tag tupler's type: `Π ı⃗_m, tag`. -/
def tagTuplerTyAV (W m : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  mkPisAV (tuplerData W (Idss.getD m [])) ((tagTyAV W Idss).liftN (Idss.getD m []).length 0)

/-- A tagged tuple at index expressions scoped `d` binders below the
parameter frame: member `m`'s tupler, lifted, applied to them. -/
def tagTupleAV (W m d : Nat) (Idss : List (List AnnotTerm)) (Es : List AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN ((tagTuplerAV W m Idss).liftN d 0) Es

/-- The auxiliary family's index telescope: the tag, and nothing else. -/
def auxIds (W : Nat) (Idss : List (List AnnotTerm)) : List AnnotTerm := [tagTyAV W Idss]

/-- The members' index telescopes graded at the parameter frame, with
their bound (`IdxOk` at every member). -/
def TagOk (W : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm)) : Prop :=
  W ≠ 0 ∧ ∀ Ids ∈ Idss, IdxOk W ρp Ids

theorem TagOk.sumOk {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) : SumFieldsOkB W ρp (uChains Idss) :=
  SumFieldsOkB_uChains fun Ids hIds => (h.2 Ids hIds).1

/-- **The tag type**: its value, its membership, its grading. -/
theorem tagTyAV_facts {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) :
    interp V ρp (tagTyAV W Idss) = tagSet W ρp Idss ∧
      tagSet W ρp Idss ∈ˢ (univ W : V) ∧ WellDenoted V ρp (tagTyAV W Idss) :=
  ⟨sumBodyAV_interp h.sumOk, sumSet_univ_of_okB h.sumOk, sumBodyAV_wellDenoted h.sumOk⟩

/-- The auxiliary family's index telescope is graded. -/
theorem auxIds_idxOk {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) : IdxOk W ρp (auxIds W Idss) := by
  obtain ⟨hv, hm, hok⟩ := tagTyAV_facts h
  refine ⟨⟨hok, fun _ => hv ▸ hm, fun _ _ => trivial⟩, ⟨hv ▸ hm, fun _ _ => trivial⟩⟩

/-- Member `m`'s tagged tuple at a fitting index spine is in the tag set. -/
theorem tagTuple_mem {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (h : TagOk W ρp Idss)
    {m : Nat} {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids) {is : List V}
    (hsp : SpineFit ρp Ids is) :
    inj m (mkTower (is ++ [pt])) ∈ˢ tagSet W ρp Idss := by
  have hj : (uChains Idss)[m]? = some (Ids ++ [idxEqAV []]) := by
    rw [uChains_getElem?, hm]; rfl
  have hmem : mkTower (is ++ [pt]) ∈ˢ sumFibre W ρp (uChains Idss) m := by
    rw [sumFibre_of_getElem? hj]
    exact mkTower_mem_teleOfFields h.1 (hsp.append ⟨pt_mem_idxEqAV_nil _, trivial⟩)
  have := injW_mem (w := W) hmem
  rwa [injW_pos h.1] at this

/-- The tag tupler's premise at member `m` (`MkPreS` at no parameter
binders, the body the tag type lifted under the index binders). -/
theorem tagTupler_pre {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} (h : TagOk W ρp Idss)
    {m : Nat} {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids) :
    MkPreS W m ρp Ids (uChains Idss) ((tagTyAV W Idss).liftN Ids.length 0) [] := by
  refine ⟨h.sumOk, by rw [uChains_getElem?, hm]; rfl, fun bs hsp => ?_⟩
  refine ⟨sumFibre W ρp (uChains Idss), ?_, ?_⟩
  · rw [interp_liftN, ← hsp.length_eq, shiftE_consList]
    exact (tagTyAV_facts h).1
  · rw [if_neg h.1, sumFibre_of_getElem? (by rw [uChains_getElem?, hm]; rfl)]
    exact mkTower_mem_teleOfFields h.1 (hsp.append ⟨pt_mem_idxEqAV_nil _, trivial⟩)

theorem tagTuplerData_zero (W : Nat) (Ids : List AnnotTerm) :
    ∀ d ∈ ([] : List (Nat × Nat × AnnotTerm)) ++ tuplerData W Ids, (W = 0 ↔ d.2.1 = 0) := by
  intro d hd
  simp only [List.nil_append] at hd
  obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
  exact Iff.rfl

/-- **The tag tupler**: it inhabits `Π ı⃗_m, tag` and is graded. -/
theorem tagTuplerAV_facts {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) {m : Nat} {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids) :
    interp V ρp (tagTuplerAV W m Idss) ∈ˢ interp V ρp (tagTuplerTyAV W m Idss) ∧
      WellDenoted V ρp (tagTuplerAV W m Idss) := by
  have hg : Idss.getD m [] = Ids := by
    rw [List.getD_eq_getElem?_getD, hm]; rfl
  unfold tagTuplerAV tagTuplerTyAV
  rw [hg]
  have hpre := tagTupler_pre h hm
  have hIds : Ids = (tuplerData W Ids).map (·.2.2) := (tuplerData_doms W Ids).symm
  constructor
  · have := sumMkAV_mem (pds := []) (fds := tuplerData W Ids) (ρ := ρp)
      (bodyC := (tagTyAV W Idss).liftN Ids.length 0) (Fss := uChains Idss) (j := m)
      (tagTuplerData_zero W Ids) (by rw [← hIds]; exact hpre)
    simpa [← hIds] using this
  · have := sumMkAV_wellDenoted (pds := []) (fds := tuplerData W Ids) (ρ := ρp)
      (bodyC := (tagTyAV W Idss).liftN Ids.length 0) (Fss := uChains Idss) (j := m)
      (tagTuplerData_zero W Ids) (by rw [← hIds]; exact hpre)
    simpa [← hIds] using this

/-- **The tag tupler's fold**: along a fitting index spine it computes
the tagged tuple. -/
theorem tagTuplerAV_fold {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) {m : Nat} {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids)
    {is : List V} (hsp : SpineFit ρp Ids is) :
    is.foldl SetTheory.app (interp V ρp (tagTuplerAV W m Idss)) = inj m (mkTower (is ++ [pt])) := by
  have hg : Idss.getD m [] = Ids := by
    rw [List.getD_eq_getElem?_getD, hm]; rfl
  unfold tagTuplerAV
  rw [hg]
  have hIds : Ids = (tuplerData W Ids).map (·.2.2) := (tuplerData_doms W Ids).symm
  have := sumMkAV_fold (w := W) h.1 (pds := []) (fds := tuplerData W Ids) (Fss := uChains Idss)
    (ρ := ρp) (as := []) (bs := is) (j := m) trivial (by rw [← hIds]; exact hsp)
    (by simpa [consList] using h.sumOk) (by rw [← hIds, uChains_getElem?, hm]; rfl)
  simpa [← hIds] using this

/-- **A tagged tuple at index expressions**, `d` binders below the
parameter frame: its value is the tagged tuple of the expressions'
values, and it is graded, when the values fit member `m`'s index
telescope. -/
theorem tagTupleAV_facts {W : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (h : TagOk W ρp Idss) {m : Nat} {Ids : List AnnotTerm} (hm : Idss[m]? = some Ids)
    {d : Nat} {τ : Nat → V} (hfr : shiftE d 0 τ = ρp) {Es : List AnnotTerm}
    (hEok : ∀ E ∈ Es, WellDenoted V τ E)
    (hsp : SpineFit ρp Ids (Es.map (interp V τ))) :
    interp V τ (tagTupleAV W m d Idss Es)
        = inj m (mkTower (Es.map (interp V τ) ++ [pt])) ∧
      WellDenoted V τ (tagTupleAV W m d Idss Es) := by
  have hg : Idss.getD m [] = Ids := by
    rw [List.getD_eq_getElem?_getD, hm]; rfl
  have hfv : interp V τ ((tagTuplerAV W m Idss).liftN d 0)
      = interp V ρp (tagTuplerAV W m Idss) := by
    rw [interp_liftN, hfr]
  have hfok : WellDenoted V τ ((tagTuplerAV W m Idss).liftN d 0) := by
    rw [WellDenoted_liftN, hfr]; exact (tagTuplerAV_facts h hm).2
  have hIds : Ids = (tuplerData W Ids).map (·.2.2) := (tuplerData_doms W Ids).symm
  have hchain : AppChainOk (interp V τ ((tagTuplerAV W m Idss).liftN d 0))
      (Es.map (interp V τ)) := by
    rw [hfv]
    have hmem := (tagTuplerAV_facts h hm).1
    unfold tagTuplerAV at hmem ⊢
    unfold tagTuplerTyAV at hmem
    rw [hg] at hmem ⊢
    refine appChainOk_of_mkPisAV (m := W) (ds := tuplerData W Ids)
      (b := sumInjAtAV W (uChains Idss) Ids.length (numeralAV m) (mkTowerGoU W Ids (idxEqAV [])))
      (C := (tagTyAV W Idss).liftN Ids.length 0) (tagTuplerData_zero W Ids) ?_ hmem
      (by rw [tuplerData_doms]; exact hsp)
    have := underTowerOk_of_mkPreS (pds := []) (fds := tuplerData W Ids) (tagTupler_pre h hm) hIds
    simpa using this
  have hf := mkAppN_wellDenoted_of_chain hfok hEok hchain
  refine ⟨?_, hf.1⟩
  unfold tagTupleAV
  rw [hf.2, hfv]
  exact tagTuplerAV_fold h hm hsp

/-! ## The block's tagged data spellings -/

/-- The constructors' tagged index expressions: constructor `J` of
member `mems J`, with `nFs J` fields, gets the one expression
`⟨inj (mems J) ⟨e⃗_J⟩⟩` (its own expressions scoped at the constructor
frame, `nFs J` binders below the parameters). -/
def mutualEss (W : Nat) (Idss : List (List AnnotTerm)) (mems : List Nat) (nFs : List Nat)
    (Ess : List (List AnnotTerm)) : List (List AnnotTerm) :=
  (List.range Ess.length).map fun J =>
    [tagTupleAV W (mems.getD J 0) (nFs.getD J 0) Idss (Ess.getD J [])]

/-- The recursive slots' tagged index expressions: slot `i` of
constructor `J`, targeting member `tgts J i` under a telescope of
length `(tlss J i).length`, gets the one expression
`⟨inj (tgts J i) ⟨e⃗_i⟩⟩` (its own expressions scoped `i + tele` binders
below the parameters). -/
def mutualEiss (W : Nat) (Idss : List (List AnnotTerm)) (tgts : List (List Nat))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss : List (List (List AnnotTerm))) :
    List (List (List AnnotTerm)) :=
  (List.range Eiss.length).map fun J =>
    (List.range (Eiss.getD J []).length).map fun i =>
      [tagTupleAV W ((tgts.getD J []).getD i 0) (i + ((tlss.getD J []).getD i []).length) Idss
        ((Eiss.getD J []).getD i [])]

end ConLeche.Semantics
