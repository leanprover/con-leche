module

public import ConLeche.Semantics.Tower.FixFamI

@[expose] public section

/-!
# The mutual block's members as fibres of one fixed point (task #278)

A mutual block `T_1 … T_k` over one parameter telescope, member `m`
with index telescope `ı⃗_m : Ids_m`, is modelled by ONE least fixed
point over the **tagged sum of the members' index tuples**:

* the **tag family** at the parameter frame is the sum leaf's tagged
  union of the members' index towers, `tagTyAV := sumBodyAV W (uChains
  Idss)`, whose elements are `inj m (mkTower (ı⃗ ++ [pt]))` — member
  `m`'s index tuple behind its tag (`W`, the tag's sort, is positive);
* member `m`'s **tag tupler** `tagTuplerAV W m Idss` is the sum route's
  constructor leaf `sumMkAV` at the tag: `λ ı⃗_m, inj m ⟨ı⃗_m⟩` — a
  tagged tuple at index EXPRESSIONS is the tupler applied to them
  (`tagTupleAV`), never a substitution;
* the **auxiliary family** is the fixpoint route's family
  (`fixBodyAVI`, `FixLeafI.lean`) at the ONE index telescope
  `[tagTyAV]`, with every constructor's index expressions and every
  recursive slot's replaced by their tagged tuple (`mutualEss`,
  `mutualEiss`): a member occurrence `T_{m'} p⃗ e⃗` becomes the family at
  `⟨inj m' ⟨e⃗⟩⟩`.  Everything the fixpoint route proves of its family —
  monotonicity, the closed member, the fixed point, the fibre as the
  restricted tagged union, the recursor's fixed point — is
  INSTANTIATED here, never restated;
* member `m`'s **leaf** `mutualTyAVI` is the λ-tower over its own
  parameter and index binders returning the auxiliary family at
  `⟨inj m ⟨ı⃗_m⟩⟩` — a fibre of the one fixed point (task #279's
  R1, the form (M0)).

This module: the spelled pieces, their readings and gradings, and the
member leaf's laws (`mutualTyAVI_mem`, `_wellDenoted`, `_fold`) under
one hereditary premise (`ParamsOkMI`).
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

/-! ## The auxiliary family and the member leaf -/

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

/-- The auxiliary family at the parameter frame: the fixpoint route's
family at the tag index and the tagged expressions. -/
def auxBodyAV (W w : Nat) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  fixBodyAVI W w (auxIds W Idss) 1 rss tlss Eiss' Fss Ess'

/-- The auxiliary family's semantic value at the parameter frame. -/
noncomputable def auxFamI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : V :=
  fixFamI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess'

/-- The 1-tuple around a tagged tuple, as the auxiliary family's index
tuple. -/
noncomputable def auxTup (W : Nat) (t : V) : V := tupW W [t]

/-- **Member `m`'s leaf**: the λ-tower over the parameter binders and
member `m`'s index binders (`pps` — the parameters, then `Ids_m`,
`nIdx` of them), returning the auxiliary family at the 1-tuple of the
tagged tuple of the index variables. -/
def mutualTyAVI (W w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (nIdx : Nat)
    (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) (m : Nat) : AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2))
    (.app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
      (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
        [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)]))

/-- The base of the member leaf's premise, at a frame whose last `nIdx`
binders are member `m`'s index variables: the tag and the chains
graded at the parameter frame `shiftE nIdx 0 ρ`, and the index
variables a fitting spine of member `m`'s telescope. -/
def MutualBaseI (W w : Nat) (ρ : Nat → V) (nIdx : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m : Nat) : Prop :=
  TagOk W (shiftE nIdx 0 ρ) Idss ∧
  FixChainsOkI W w (shiftE nIdx 0 ρ) (auxIds W Idss) 1 rss tlss Eiss' Fss Ess' ∧
  ∃ Ids, Idss[m]? = some Ids ∧ Ids.length = nIdx ∧
    SpineFit (shiftE nIdx 0 ρ) Ids (frameIdx nIdx ρ)

/-- The member leaf's hereditary premise: the parameter and index
binders graded, `MutualBaseI` at the base. -/
def ParamsOkMI (W w : Nat) (ρ : Nat → V) (nIdx : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m : Nat) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => MutualBaseI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m
  | d :: pps => d.2.1 ≠ 0 ∧ WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → ParamsOkMI W w (cons a ρ) nIdx Idss rss tlss Eiss' Fss Ess' m pps

/-- The index variables of the last `nIdx` binders read to the frame's
index tuple (`map_idxVarsAV_interp`'s shape at the leaf's frame). -/
theorem teleVarsAV_interp (nIdx : Nat) (ρ : Nat → V) :
    (teleVarsAV nIdx).map (interp V ρ) = frameIdx nIdx ρ := by
  unfold teleVarsAV frameIdx
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  simp

/-- **The member leaf's body** at its frame: its value — the auxiliary
family at the 1-tuple of the member's tagged tuple of the frame's index
variables — its membership in the block's universe, and its grading. -/
theorem mutualLeafBody_facts {W w : Nat} {ρ : Nat → V} {nIdx : Nat} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)} {m : Nat}
    (h : MutualBaseI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m) :
    interp V ρ (.app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)]))
      = SetTheory.app (auxFamI W w (shiftE nIdx 0 ρ) Idss rss tlss Eiss' Fss Ess')
          (auxTup W (inj m (mkTower (frameIdx nIdx ρ ++ [pt])))) ∧
    interp V ρ (.app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)])) ∈ˢ (univ w : V) ∧
    WellDenoted V ρ (.app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)])) := by
  obtain ⟨hT, hok, Ids, hm, hlen, hsp⟩ := h
  have hI : IdxOk W (shiftE nIdx 0 ρ) (auxIds W Idss) := auxIds_idxOk hT
  -- the frame is `consList (frameIdx nIdx ρ) (shiftE nIdx 0 ρ)`
  have hρ : ρ = consList (frameIdx nIdx ρ) (shiftE nIdx 0 ρ) := (consList_frameIdx nIdx ρ).symm
  have hlenF : (frameIdx nIdx ρ).length = nIdx := frameIdx_length nIdx ρ
  -- the tagged tuple of the index variables
  have hvars : (teleVarsAV nIdx).map (interp V ρ) = frameIdx nIdx ρ := teleVarsAV_interp nIdx ρ
  have hvok : ∀ E ∈ teleVarsAV nIdx, WellDenoted V ρ E := by
    intro E hE
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hE
    trivial
  have htag := tagTupleAV_facts hT hm (d := nIdx) (τ := ρ) rfl (Es := teleVarsAV nIdx)
    hvok (by rw [hvars]; exact hsp)
  rw [hvars] at htag
  -- the 1-tuple: the auxiliary tupler applied to the tagged tuple
  have hbody := fixBodyAVI_facts hI hok
  have hfv : interp V ρ ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
      = interp V (shiftE nIdx 0 ρ) (auxBodyAV W w Idss rss tlss Eiss' Fss Ess') := by
    rw [interp_liftN]
  have hfok : WellDenoted V ρ ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0) := by
    rw [WellDenoted_liftN]; exact hbody.2.2
  have htv : interp V ρ ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
      = interp V (shiftE nIdx 0 ρ) (tuplerAV W (auxIds W Idss)) := by rw [interp_liftN]
  have htok : WellDenoted V ρ ((tuplerAV W (auxIds W Idss)).liftN nIdx 0) := by
    rw [WellDenoted_liftN]; exact tuplerAV_wellDenoted hI
  have hsp1 : SpineFit (shiftE nIdx 0 ρ) (auxIds W Idss) [inj m (mkTower (frameIdx nIdx ρ ++ [pt]))] := by
    refine ⟨?_, trivial⟩
    rw [(tagTyAV_facts hT).1]
    exact tagTuple_mem hT hm hsp
  have hchain : AppChainOk (interp V ρ ((tuplerAV W (auxIds W Idss)).liftN nIdx 0))
      ([tagTupleAV W m nIdx Idss (teleVarsAV nIdx)].map (interp V ρ)) := by
    rw [htv, List.map_singleton, htag.1]
    exact appChainOk_of_mkPisAV (ds := tuplerData W (auxIds W Idss)) (b := mkTowerGo W (auxIds W Idss))
      (C := (idxTyAV W (auxIds W Idss)).liftN (auxIds W Idss).length 0)
      (fun _ hd => by obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd; exact Iff.rfl)
      (tuplerAV_under hI) (tuplerAV_mem hI) (by rw [tuplerData_doms]; exact hsp1)
  have htup := mkAppN_wellDenoted_of_chain htok (fun a ha => by
      rw [List.mem_singleton] at ha; subst ha; exact htag.2) hchain
  have htupv : interp V ρ (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
      [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)])
      = auxTup W (inj m (mkTower (frameIdx nIdx ρ ++ [pt]))) := by
    rw [htup.2, List.map_singleton, htag.1, htv]
    exact tuplerAV_fold hI hsp1
  have hmemT : auxTup W (inj m (mkTower (frameIdx nIdx ρ ++ [pt])))
      ∈ˢ idxSet W (shiftE nIdx 0 ρ) (auxIds W Idss) := tupW_mem hsp1
  have hfam : auxFamI W w (shiftE nIdx 0 ρ) Idss rss tlss Eiss' Fss Ess'
      ∈ˢ lfpFamSpace V w (idxSet W (shiftE nIdx 0 ρ) (auxIds W Idss)) := hbody.2.1
  have hval : interp V ρ (.app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)]))
      = SetTheory.app (auxFamI W w (shiftE nIdx 0 ρ) Idss rss tlss Eiss' Fss Ess')
          (auxTup W (inj m (mkTower (frameIdx nIdx ρ ++ [pt])))) := by
    rw [interp_app, htupv, hfv]
    unfold auxBodyAV auxFamI
    rw [hbody.1]
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]
    exact famSpace_app (by rw [← lfpFamSpace_eq]; exact hfam) hmemT
  · rw [WellDenoted_app]
    refine ⟨hfok, htup.1, w + 1, idxSet W (shiftE nIdx 0 ρ) (auxIds W Idss),
      fun _ => (univ w : V), ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hfv]
      unfold auxBodyAV
      rw [hbody.1]
      exact hfam
    · rw [htupv]; exact hmemT

/-- **The member leaf inhabits its type's reading.** -/
theorem mutualTyAVI_mem {W w nIdx : Nat} {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss Ess' : List (List AnnotTerm)} {m : Nat} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkMI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m pps →
      interp V ρ (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss Ess' m)
        ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], ρ, h => (mutualLeafBody_facts h).2.1
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => mutualTyAVI_mem (h.2.2 a ha))

/-- **The member leaf is graded.** -/
theorem mutualTyAVI_wellDenoted {W w nIdx : Nat} {Idss : List (List AnnotTerm)}
    {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)} {m : Nat} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkMI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m pps →
      WellDenoted V ρ (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss Ess' m)
  | [], _, h => (mutualLeafBody_facts h).2.2
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam (w + 1) d.2.2 (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) _))
    rw [WellDenoted_lam]
    exact ⟨h.2.1, fun a ha => mutualTyAVI_wellDenoted (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => mutualTyAVI_mem (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The member leaf's application fold**: along a fitting parameter-
and-index spine it computes the auxiliary family at the 1-tuple of the
member's tagged index tuple. -/
theorem mutualTyAVI_fold {W w nIdx : Nat} {Idss : List (List AnnotTerm)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss Ess' : List (List AnnotTerm)} {m : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hbase : MutualBaseI W w (consList as ρ) nIdx Idss rss tlss Eiss' Fss Ess' m) :
    as.foldl SetTheory.app (interp V ρ (mutualTyAVI W w pps nIdx Idss rss tlss Eiss' Fss Ess' m))
      = SetTheory.app (auxFamI W w (shiftE nIdx 0 (consList as ρ)) Idss rss tlss Eiss' Fss Ess')
          (auxTup W (inj m (mkTower (frameIdx nIdx (consList as ρ) ++ [pt])))) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [mutualTyAVI,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp']
  exact (mutualLeafBody_facts hbase).1

end ConLeche.Semantics
