module

public import ConLeche.Semantics.Tower.CaseFamI

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
  (both of those, with their laws, are `MutualTagI.lean`);
* the **auxiliary family** is the CASED family functor (`caseBodyAVI`,
  `caseFamI`, `CaseFamI.lean`) at the ONE index telescope `[tagTyAV]`,
  with every constructor's index expressions and every recursive slot's
  replaced by their tagged tuple (`mutualEss`, `mutualEiss`): a member
  occurrence `T_{m'} p⃗ e⃗` becomes the family at `⟨inj m' ⟨e⃗⟩⟩`.  At a
  tuple of member `m` the sum ranges over member `m`'s suffix of the
  global chain list from `offs m` on, so an element's tag is
  member-local (DESIGN §U.15 (c), task #315 M6 s4).  Everything the
  cased functor proves of its family — monotonicity, the closed member,
  the fixed point, the fibre as the restricted tagged union, the
  recursor's fixed point — is INSTANTIATED here, never restated;
* member `m`'s **leaf** `mutualTyAVI` is the λ-tower over its own
  parameter and index binders returning the auxiliary family at
  `⟨inj m ⟨ı⃗_m⟩⟩` — a fibre of the one fixed point (task #279's
  R1, the form (M0)).

This module: the auxiliary family, the member leaf, their readings and
gradings, and the leaf's laws (`mutualTyAVI_mem`, `_wellDenoted`,
`_fold`) under one hereditary premise (`ParamsOkMI`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The auxiliary family and the member leaf -/

/-- The auxiliary family at the parameter frame: the cased family
functor at the tag index and the tagged expressions, with the block's
per-member chain offsets `offs`. -/
def auxBodyAV (W w : Nat) (Idss : List (List AnnotTerm)) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  caseBodyAVI W w Idss Idss.length offs rss tlss Eiss' Fss Ess'

/-- The auxiliary family's semantic value at the parameter frame. -/
noncomputable def auxFamI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : V :=
  caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess'

/-- The 1-tuple around a tagged tuple, as the auxiliary family's index
tuple. -/
noncomputable def auxTup (W : Nat) (t : V) : V := tupW W [t]

/-- **Member `m`'s leaf**: the λ-tower over the parameter binders and
member `m`'s index binders (`pps` — the parameters, then `Ids_m`,
`nIdx` of them), returning the auxiliary family at the 1-tuple of the
tagged tuple of the index variables. -/
def mutualTyAVI (W w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (nIdx : Nat)
    (Idss : List (List AnnotTerm)) (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) (m : Nat) : AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2))
    (.app ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
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
    {offs : Nat → Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)} {m : Nat}
    (h : MutualBaseI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m) :
    interp V ρ (.app ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)]))
      = SetTheory.app (auxFamI W w (shiftE nIdx 0 ρ) Idss offs rss tlss Eiss' Fss Ess')
          (auxTup W (inj m (mkTower (frameIdx nIdx ρ ++ [pt])))) ∧
    interp V ρ (.app ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)])) ∈ˢ (univ w : V) ∧
    WellDenoted V ρ (.app ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
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
  have hbody := caseBodyAVI_facts (offs := offs) hT rfl hok
  have hfv : interp V ρ ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
      = interp V (shiftE nIdx 0 ρ) (auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess') := by
    rw [interp_liftN]
  have hfok : WellDenoted V ρ ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0) := by
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
  have hfam : auxFamI W w (shiftE nIdx 0 ρ) Idss offs rss tlss Eiss' Fss Ess'
      ∈ˢ lfpFamSpace V w (idxSet W (shiftE nIdx 0 ρ) (auxIds W Idss)) := hbody.2.1
  have hval : interp V ρ (.app ((auxBodyAV W w Idss offs rss tlss Eiss' Fss Ess').liftN nIdx 0)
        (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN nIdx 0)
          [tagTupleAV W m nIdx Idss (teleVarsAV nIdx)]))
      = SetTheory.app (auxFamI W w (shiftE nIdx 0 ρ) Idss offs rss tlss Eiss' Fss Ess')
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
theorem mutualTyAVI_mem {W w nIdx : Nat} {Idss : List (List AnnotTerm)} {offs : Nat → Nat}
    {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss Ess' : List (List AnnotTerm)} {m : Nat} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkMI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m pps →
      interp V ρ (mutualTyAVI W w pps nIdx Idss offs rss tlss Eiss' Fss Ess' m)
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
    {offs : Nat → Nat} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
    {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)} {m : Nat} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkMI W w ρ nIdx Idss rss tlss Eiss' Fss Ess' m pps →
      WellDenoted V ρ (mutualTyAVI W w pps nIdx Idss offs rss tlss Eiss' Fss Ess' m)
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
theorem mutualTyAVI_fold {W w nIdx : Nat} {Idss : List (List AnnotTerm)} {offs : Nat → Nat}
    {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss' : List (List (List AnnotTerm))}
    {Fss Ess' : List (List AnnotTerm)} {m : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hbase : MutualBaseI W w (consList as ρ) nIdx Idss rss tlss Eiss' Fss Ess' m) :
    as.foldl SetTheory.app
        (interp V ρ (mutualTyAVI W w pps nIdx Idss offs rss tlss Eiss' Fss Ess' m))
      = SetTheory.app
          (auxFamI W w (shiftE nIdx 0 (consList as ρ)) Idss offs rss tlss Eiss' Fss Ess')
          (auxTup W (inj m (mkTower (frameIdx nIdx (consList as ρ) ++ [pt])))) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [mutualTyAVI,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp']
  exact (mutualLeafBody_facts hbase).1

end ConLeche.Semantics
