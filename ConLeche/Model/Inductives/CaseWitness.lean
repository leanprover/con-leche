module

public import ConLeche.Model.Inductives.FixWitness
public import ConLeche.Semantics.Tower.CaseFamI
public section

/-!
# The closure witness of the CASED family functor (task #315, M6 s4)

`FixWitness.lean` exhibits the fixpoint route's family functor
`fixFunVI` as a container (shapes the shadow tuples, positions the
recursive fields' spines, targets the calls' tuples, the builder the
curried slots) and reads the closed member family off
`container_closed_exists`.  The CASED functor `caseFunVI`
(`Semantics/Tower/CaseFamI.lean`) sums, at a tuple of member `m`, over
member `m`'s SUFFIX of the same chain list, so its elements are the
fixpoint functor's elements RE-TAGGED by `J ↦ J - offs m`.  It is
therefore the same container with the tuple's member recorded in the
shape (`caseShape`: the member's numeral paired with the shadow
tuple) and the builder re-tagging the fixpoint builder's value
(`retag`) — a wrapper over `FixWitness`'s exported per-shape lemmas,
not a re-proof (DESIGN §U.15 (c)).

`caseClosed_of` is the positive-sort witness; `caseClosed_all` adds
the `Prop`-valued case (`caseFunVI_closed_zero`).  Consumer: the
assembly's `mutualCaseClosed_of` (`MutualChains.lean`), which feeds the
sealed premise `TupleLfpOk` (`TupleLfp.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The numeral singleton and the re-tagging -/

/-- The singleton of a numeral, as a subset of `ω`. -/
noncomputable def natSingle (m : Nat) : V := sep omega fun k => k = vnat m

theorem mem_natSingle {m : Nat} {k : V} : k ∈ˢ natSingle m ↔ k = vnat m := by
  unfold natSingle
  rw [mem_sep]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact vnat_mem_omega m, h⟩⟩

theorem natSingle_mem {w : Nat} (hw : w ≠ 0) (m : Nat) : (natSingle m : V) ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact univ_sep_mem (omega_mem_univ_succ w')

/-- Re-tagging a tagged value by an offset: `inj J y ↦ inj (J - o) y`. -/
noncomputable def retag (o : Nat) (x : V) : V := inj (natIdx (sfst x) - o) (ssnd x)

theorem retag_inj (o J : Nat) (y : V) : retag o (inj J y) = inj (J - o) y := by
  unfold retag inj
  rw [sfst_spair, ssnd_spair, natIdx_vnat]

/-! ## The witness -/

section Block

variable {W w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {Idss : List (List AnnotTerm)}
  (hI : IdxOk W ρp (auxIds W Idss))
  {ksF : Nat → List RecFieldKind} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
  {Fss Ess : List (List AnnotTerm)}
  (hrss : ∀ j, j < Fss.length → rss.getD j [] = rsOf (ksF j))
  (hC : ∀ j, j < Fss.length → ChainFacts W w nP (Fss.getD j []).length ρp (auxIds W Idss) (ksF j)
    (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
include hw hI hrss hC

/-- **A closed member family exists for the cased functor** (positive
sort): the fixpoint functor's container with the tuple's member paired
into the shape and the builder's value re-tagged by the member's
offset. -/
theorem caseClosed_of (offs : Nat → Nat) :
    ∃ L, IsClosedFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss Fss Ess) L := by
  have hfitX : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) →
      ∀ t, t ∈ˢ idxSet W ρp (auxIds W Idss) → ∀ j, j < Fss.length →
        SlotsFitX W w ρp (auxIds W Idss) (rss.getD j []) (tlss.getD j []) (Eiss.getD j []) X t 0 []
          (Fss.getD j []) := by
    intro X hX t ht j hj
    rw [hrss j hj]
    exact (fixChain_of hI hX ht (hC j hj)).2
  obtain ⟨L, hL, hclosed⟩ := container_closed_exists hw (I := idxSet W ρp (auxIds W Idss))
    (caseFamFI W w ρp Idss offs rss tlss Eiss Fss Ess)
    (fun t => sigmaPairs (natSingle (caseTag t)) fun _ =>
      shapeSet W w nP ρp (auxIds W Idss) ksF Fss Ess t)
    (fun a' => posSet w ρp rss tlss Fss (ssnd a'))
    (fun a' p => posTgt W ρp tlss Eiss Fss (ssnd a') p)
    (fun a' g => retag (offs (natIdx (sfst a'))) (mkShape w ρp rss tlss Fss (ssnd a') g))
    (fun t _ => (univ_isTGUniverse hw).sigmaPairs_mem (natSingle_mem hw _)
      fun _ _ => shapeSet_mem hw hC t)
    (fun _ a' _ ha' => by
      obtain ⟨k, -, a, ha, rfl⟩ := mem_sigmaPairs.mp ha'
      rw [ssnd_kpair]
      exact posSet_mem hw hrss hC ha)
    (fun _ a' p _ ha' hp => by
      obtain ⟨k, -, a, ha, rfl⟩ := mem_sigmaPairs.mp ha'
      rw [ssnd_kpair] at hp ⊢
      exact posTgt_mem hw hrss hC ha hp)
    (fun _ a' g _ ha' hg => by
      obtain ⟨k, -, a, ha, rfl⟩ := mem_sigmaPairs.mp ha'
      rw [ssnd_kpair]
      have hm := mkShape_mem hw hrss hC ha hg
      obtain ⟨y, hy⟩ := mkShape_tag w ρp rss tlss Fss a g
      rw [hy] at hm ⊢
      rw [retag_inj]
      exact inj_mem_univ hw (inj_comp_mem hw hm))
    (fun X hX t ht x hx => by
      rw [← lfpFamSpace_eq] at hX
      rw [caseFamFI_app ht] at hx
      obtain ⟨j, fs, rfl, hJ, -, hsp, hall⟩ := caseStepI_elim hw hx
      -- the element at the GLOBAL tag is in the fixpoint functor's fibre
      have hmem : inj (offs (caseTag t) + j) (mkTower (fs ++ [pt]))
          ∈ˢ fixStepI W w ρp (auxIds W Idss) (auxIds W Idss).length rss tlss Eiss Fss Ess X t := by
        unfold fixStepI
        refine inj_mem hw ?_
        rw [sumFibre_of_getElem? (by rw [chainsXI_getElem?, if_pos hJ])]
        refine mkTower_mem_teleOfFields hw ?_
        unfold chainXI
        exact spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, hall⟩
      obtain ⟨a, ha, g, hg, heq⟩ :=
        fixStep_elim_container hw hI hrss hC hX ht (hfitX X hX t ht) hmem
      refine ⟨kpair (vnat (caseTag t)) a,
        mem_sigmaPairs.mpr ⟨vnat (caseTag t), mem_natSingle.mpr rfl, a, ha, rfl⟩, g, ?_, ?_⟩
      · show g ∈ˢ piSet (posSet w ρp rss tlss Fss (ssnd (kpair (vnat (caseTag t)) a)))
          fun p => SetTheory.app X (posTgt W ρp tlss Eiss Fss (ssnd (kpair (vnat (caseTag t)) a)) p)
        rw [ssnd_kpair]
        exact hg
      · show inj j (mkTower (fs ++ [pt]))
          = retag (offs (natIdx (sfst (kpair (vnat (caseTag t)) a))))
              (mkShape w ρp rss tlss Fss (ssnd (kpair (vnat (caseTag t)) a)) g)
        rw [sfst_kpair, ssnd_kpair, natIdx_vnat]
        obtain ⟨y, hy⟩ := mkShape_tag w ρp rss tlss Fss a g
        rw [hy] at heq ⊢
        rw [retag_inj]
        obtain ⟨hJ', hy'⟩ := inj_inj heq
        rw [← hy', ← hJ', Nat.add_sub_cancel_left])
  refine ⟨L, hL, ?_⟩
  rw [caseFunVI_app (by rw [lfpFamSpace_eq]; exact hL)]
  exact hclosed

end Block

/-- **The closed family at every sort**: the container witness above
at a positive sort, the top family at a `Prop`-valued block. -/
theorem caseClosed_all {W w nP : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)}
    (hI : IdxOk W ρp (auxIds W Idss))
    {ksF : Nat → List RecFieldKind} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AnnotTerm)))} {Eiss : List (List (List AnnotTerm))}
    {Fss Ess : List (List AnnotTerm)}
    (hrss : ∀ j, j < Fss.length → rss.getD j [] = rsOf (ksF j))
    (hC : ∀ j, j < Fss.length → ChainFacts W w nP (Fss.getD j []).length ρp (auxIds W Idss) (ksF j)
      (tlss.getD j []) (Fss.getD j []) (Eiss.getD j []) (Ess.getD j []))
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss Fss Ess) (offs : Nat → Nat) :
    ∃ L, IsClosedFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss Fss Ess) L := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact caseFunVI_closed_zero hok
  · exact caseClosed_of (Nat.pos_iff_ne_zero.mp hw) hI hrss hC offs

end ConLeche.Model
