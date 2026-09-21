module

public import ConLeche.Model.Inductives.BlockChains
public import ConLeche.Model.Inductives.FixWitness
public section

/-!
# The closure witness of the block functor at `k` members (task #315 M3)

`FixWitness.lean` at `k`: the block's tuple operator `blockPhi` is a
CONTAINER in the sense of `ConLeche/SetModel/TupleContainer.lean`, so
`blockPhi_closed_container` (lane S, `Semantics/Tower/BlockFamI.lean`)
yields the closed tuple `BlockChainsOk.hclosed` asks for, for every
block — finitary or not, any sort.

The presentation is the one-member one with ONE change, which is
falsifier F1's finding: **the shapes are tagged by (component,
constructor) GLOBALLY**.  The kit (`tupleContainer_closed_exists`) tags
its shapes by component internally and then STRIPS that tag before
reading a shape's positions and targets, so a shape that is only a
constructor's shadow tuple does not determine them — the same
constructor shape can occur at two components with different targets.
A shape here is therefore `inj m a`, with `m` the component and `a`
member `m`'s own shadow tuple (the k = 1 shape); `shapeComp` and
`shapeBody` read the two halves back, and the positions, the targets
and the builder are the one-member data at the component the shape
carries.

Everything else is the one-member witness's: the shadow machinery is
target-blind (`shadowOf`, `shadowFs`, `ShadowRel`, `agreeOff_shadow`),
the shapes are the same shadow tuples, the positions the same tagged
telescope spines and the builder the same curried λ-tower.  The target
appears in exactly three places: a recursive position's slot fits its
TARGET member's index telescope (`blockSlotFit_shadow`), a position's
target is an index tuple OF THAT MEMBER (`blockPosTgt_mem`), and the
spine folds land in the target's component of the tuple
(`blockStepV_elim_container`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The global tag -/

/-- The COMPONENT a block shape is tagged with. -/
noncomputable def shapeComp (a : V) : Nat := natIdx (sfst a)

/-- The shape under its component tag: the component's own shadow
tuple, which is the one-member shape. -/
noncomputable def shapeBody (a : V) : V := ssnd a

theorem shapeComp_inj (m : Nat) (a : V) : shapeComp (inj m a) = m := by
  unfold shapeComp
  rw [sfst_inj, natIdx_vnat]

theorem shapeBody_inj (m : Nat) (a : V) : shapeBody (inj m a) = a := by
  unfold shapeBody
  rw [ssnd_inj]

/-! ## The container data -/

/-- **The block's shapes at component `m`**: member `m`'s shadow
tuples, tagged with `m`. -/
noncomputable def blockShapeSet (w nP : Nat) (ρp : Nat → V) (uf : Nat → Nat)
    (Idss : Nat → List AnnotTerm) (ksF : Nat → Nat → List RecFieldKind)
    (Fsss Esss : Nat → List (List AnnotTerm)) (m : Nat) (t : V) : V :=
  image (inj m) (shapeSet (uf m) w nP ρp (Idss m) (ksF m) (Fsss m) (Esss m) t)

/-- The positions of a block shape: the recursive fields' telescope
spines of the constructor it carries, at the component it carries. -/
noncomputable def blockPosSet (w : Nat) (ρp : Nat → V) (rsss : Nat → List (List Bool))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Fsss : Nat → List (List AnnotTerm)) (a : V) : V :=
  posSet w ρp (rsss (shapeComp a)) (tlsss (shapeComp a)) (Fsss (shapeComp a)) (shapeBody a)

/-- **The target COMPONENT of a position**: the field's target member. -/
noncomputable def blockPosTgtM (tgtsss : Nat → List (List Nat))
    (a p : V) : Nat :=
  ((tgtsss (shapeComp a)).getD (shapeTag (shapeBody a)) []).getD (natIdx (sfst p)) 0

/-- **The target INDEX TUPLE of a position**: the call's index tuple,
at the target member's index-tuple sort. -/
noncomputable def blockPosTgtI (uf : Nat → Nat) (ρp : Nat → V)
    (tgtsss : Nat → List (List Nat))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Eisss : Nat → List (List (List AnnotTerm))) (Fsss : Nat → List (List AnnotTerm))
    (a p : V) : V :=
  posTgt (uf (blockPosTgtM tgtsss a p)) ρp (tlsss (shapeComp a)) (Eisss (shapeComp a))
    (Fsss (shapeComp a)) (shapeBody a) p

/-- The builder: the component's own tagged tuple, the recursive slots
holding the curried function on the positions. -/
noncomputable def blockMkShape (w : Nat) (ρp : Nat → V) (rsss : Nat → List (List Bool))
    (tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm))))
    (Fsss : Nat → List (List AnnotTerm)) (m : Nat) (a g : V) : V :=
  mkShape w ρp (rsss m) (tlsss m) (Fsss m) (shapeBody a) g

theorem mem_blockShapeSet {w nP : Nat} {ρp : Nat → V} {uf : Nat → Nat}
    {Idss : Nat → List AnnotTerm} {ksF : Nat → Nat → List RecFieldKind}
    {Fsss Esss : Nat → List (List AnnotTerm)} {m : Nat} {t a : V} :
    a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t ↔
      ∃ a', a' ∈ˢ shapeSet (uf m) w nP ρp (Idss m) (ksF m) (Fsss m) (Esss m) t ∧
        a = inj m a' := mem_image

/-! ## The block's container facts -/

section Block

variable {k w nP : Nat} (hw : w ≠ 0) {ρp : Nat → V} {uf : Nat → Nat}
  {Idss : Nat → List AnnotTerm} (hI : BlockIdxOk (V := V) k uf ρp Idss)
  {nOf : Nat → Nat} {ksF : Nat → Nat → List RecFieldKind} {rsss : Nat → List (List Bool)}
  {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
  (hlenF : ∀ m, m < k → (Fsss m).length = nOf m)
  (hrss : ∀ m, m < k → ∀ j, j < nOf m → (rsss m).getD j [] = rsOf (ksF m j))
  (hC : ∀ m, m < k → ∀ j, j < nOf m →
    ChainFactsB k w nP ((Fsss m).getD j []).length ρp uf Idss m (ksF m j)
      ((tgtsss m).getD j []) ((tlsss m).getD j []) ((Fsss m).getD j [])
      ((Eisss m).getD j []) ((Esss m).getD j []))
include hw hlenF hrss hC

omit hw hrss in
/-- The shadow chain facts at a member, in the form the one-member
shadow lemmas consume. -/
theorem blockChainFactsS {m : Nat} (hm : m < k) (j : Nat) (hj : j < (Fsss m).length) :
    ChainFactsS w nP ((Fsss m).getD j []).length (Idss m).length ρp (ksF m j)
      ((tlsss m).getD j []) ((Fsss m).getD j []) ((Eisss m).getD j []) ((Esss m).getD j []) :=
  (hC m hm j (by rw [← hlenF m hm]; exact hj)).toS

omit hw in
/-- **The recursive slot at a shadow prefix fits its TARGET member's
index telescope**, and that target is a member of the block. -/
theorem blockSlotFit_shadow {m : Nat} (hm : m < k) {j : Nat} (hj : j < (Fsss m).length)
    {as' : List V}
    (hfit : SpineFit ρp
      (shadowFs nP (ksF m j) ((Fsss m).getD j []).length ((Fsss m).getD j [])) as')
    {i : Nat} (hi : i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length) :
    ((tgtsss m).getD j []).getD i 0 < k ∧
      SlotFit (uf (((tgtsss m).getD j []).getD i 0)) w ρp (Idss (((tgtsss m).getD j []).getD i 0))
        (((tlsss m).getD j []).getD i []) (((Eisss m).getD j []).getD i []) (as'.take i) := by
  have hjn : j < nOf m := by rw [← hlenF m hm]; exact hj
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  rw [hrss m hm j hjn] at hri
  have hr : recAt nP (ksF m j) (nP + i) :=
    (recAt_iff_rsOf (by rw [(hC m hm j hjn).hks]; exact hik)).mpr hri
  have hsp := spineFit_take_prefix hfit (i := i) (by rw [shadowFs_length]; exact Nat.le_of_lt hik)
  exact ((hC m hm j hjn).gr i hik (as'.take i) hsp).2.2 hr

omit hrss in
/-- **The block's shape set at a component is a member.** -/
theorem blockShapeSet_mem {m : Nat} (hm : m < k) (t : V) :
    blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t ∈ˢ (univ w : V) := by
  have hS := shapeSet_mem (u := uf m) (Ids := Idss m) hw (blockChainFactsS hlenF hC hm) t
  exact (univ_isTGUniverse hw).image_mem hS fun a ha =>
    inj_mem_univ hw ((univ_isTGUniverse hw).transitive hS ha)

omit hw hlenF hrss hC in
theorem blockShapeSet_data {m : Nat} {t a : V}
    (ha : a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t) :
    ∃ a', a = inj m a' ∧ shapeComp a = m ∧ shapeBody a = a' ∧
      a' ∈ˢ shapeSet (uf m) w nP ρp (Idss m) (ksF m) (Fsss m) (Esss m) t := by
  obtain ⟨a', ha', rfl⟩ := mem_blockShapeSet.mp ha
  exact ⟨a', rfl, shapeComp_inj m a', shapeBody_inj m a', ha'⟩

/-- **The positions of a block shape are a member.** -/
theorem blockPosSet_mem {m : Nat} (hm : m < k) {t a : V}
    (ha : a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t) :
    blockPosSet w ρp rsss tlsss Fsss a ∈ˢ (univ w : V) := by
  obtain ⟨a', rfl, hcomp, hbody, ha'⟩ := blockShapeSet_data ha
  obtain ⟨j, as', hj, -, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha'
  unfold blockPosSet posSet
  rw [hcomp, hbody, htag, hfields]
  refine (univ_isTGUniverse hw).sigmaPairs_mem (recTags_mem hw _ _) fun q hq => ?_
  obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hq
  rw [natIdx_vnat]
  unfold spineSet
  exact towerSet_univ_of_okB fun _ =>
    FieldsOkB.toBound hw (blockSlotFit_shadow hlenF hrss hC hm hj hfit hi).2.1

/-- **A position's target is a member of the block, and an index tuple
OF THAT MEMBER.** -/
theorem blockPosTgt_mem {m : Nat} (hm : m < k) {t a p : V}
    (ha : a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t)
    (hp : p ∈ˢ blockPosSet w ρp rsss tlsss Fsss a) :
    blockPosTgtM tgtsss a p < k ∧
      blockPosTgtI uf ρp tgtsss tlsss Eisss Fsss a p ∈ˢ
        idxSet (uf (blockPosTgtM tgtsss a p)) ρp (Idss (blockPosTgtM tgtsss a p)) := by
  obtain ⟨a', rfl, hcomp, hbody, ha'⟩ := blockShapeSet_data ha
  obtain ⟨j, as', hj, -, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha'
  unfold blockPosSet posSet at hp
  rw [hcomp, hbody, htag, hfields] at hp
  obtain ⟨q, hq, r, hr, rfl⟩ := mem_sigmaPairs.mp hp
  obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hq
  rw [natIdx_vnat] at hr
  have hslot := blockSlotFit_shadow hlenF hrss hC hm hj hfit hi
  have htgtM : blockPosTgtM tgtsss (inj m a') (kpair (vnat i) r)
      = ((tgtsss m).getD j []).getD i 0 := by
    unfold blockPosTgtM
    rw [hcomp, hbody, htag, sfst_kpair, natIdx_vnat]
  refine ⟨by rw [htgtM]; exact hslot.1, ?_⟩
  unfold blockPosTgtI posTgt
  rw [htgtM, hcomp, hbody, htag, hfields, sfst_kpair, ssnd_kpair, natIdx_vnat]
  unfold spineSet at hr
  have hbs := (towerSet_elim_teleOfFields hw hr).1
  rw [List.length_map] at hbs
  obtain ⟨-, hv⟩ := hslot.2.2.2 _ hbs
  rw [consList_append] at hv
  exact tupW_mem hv

/-- **The builder keeps members.** -/
theorem blockMkShape_mem {m : Nat} (hm : m < k) {t a g : V}
    (ha : a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t) (hg : g ∈ˢ (univ w : V)) :
    blockMkShape w ρp rsss tlsss Fsss m a g ∈ˢ (univ w : V) := by
  obtain ⟨a', rfl, hcomp, hbody, ha'⟩ := blockShapeSet_data ha
  obtain ⟨j, as', hj, rfl, -, hfit, -, htag, hfields⟩ := shapeSet_data hw ha'
  have hamem : inj j (mkTower (as' ++ [pt])) ∈ˢ (univ w : V) :=
    (univ_isTGUniverse hw).transitive
      (shapeSet_mem (u := uf m) (Ids := Idss m) hw (blockChainFactsS hlenF hC hm) t) ha'
  have hcomp' : ∀ x, x ∈ as' → x ∈ˢ (univ w : V) := fun x hx =>
    mkTower_comp_mem hw (inj_comp_mem hw hamem) x (List.mem_append_left _ hx)
  unfold blockMkShape mkShape
  rw [hbody, htag, hfields]
  refine inj_mem_univ hw (mkTower_mem_univ hw fun x hx => ?_)
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hi
    by_cases hri : ((rsss m).getD j []).getD i false = true
    · rw [if_pos hri]
      have hmem : i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length :=
        mem_recIdx.mpr ⟨hi, hri⟩
      refine lamTower_mem_univ hw (blockSlotFit_shadow hlenF hrss hC hm hj hfit hmem).2.1
        fun bs _ => ?_
      exact app_mem_univ hw hg
    · rw [if_neg hri]
      by_cases hil : i < as'.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil, Option.getD_some]
        exact hcomp' _ (List.getElem_mem hil)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        exact (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)
  · rw [List.mem_singleton] at hx
    subst hx
    exact (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)

/-! ## The element decomposition -/

omit hw in
/-- **A spine fitting a member's X-chain has its shadow fitting the
shadow fields**: the ordinary domains do not mention the recursive
slots, and a recursive slot reads `Sort 0` at the shadow value —
whatever member it targets. -/
theorem blockShadowOf_fits {m : Nat} (hm : m < k) {j : Nat} (hj : j < (Fsss m).length)
    {Y t : V} :
    ∀ (Fs' : List AnnotTerm) (i : Nat) (as bs : List V), as.length = i →
      Fs' = ((Fsss m).getD j []).drop i →
      SpineFit (consList as (cons t (cons Y ρp)))
        (chainXBIGo uf Idss ((rsss m).getD j []) ((tgtsss m).getD j []) ((tlsss m).getD j [])
          ((Eisss m).getD j []) Fs' i) bs →
      SpineFit (consList (shadowOf nP (ksF m j) as) ρp)
        ((shadowFs nP (ksF m j) ((Fsss m).getD j []).length ((Fsss m).getD j [])).drop i)
        (shadowOfGo nP (ksF m j) i bs)
  | [], i, as, bs, _, hF, h => by
    cases bs with
    | nil =>
      have hlen : ((Fsss m).getD j []).length ≤ i := by
        have := congrArg List.length hF
        rw [List.length_nil, List.length_drop] at this
        omega
      rw [List.drop_eq_nil_of_le (by rw [shadowFs_length]; exact hlen)]
      trivial
    | cons b bs => exact h.elim
  | F :: Fs', i, as, bs, hi, hF, h => by
    subst hi
    cases bs with
    | nil => exact h.elim
    | cons b bs =>
    rw [chainXBIGo_cons] at h
    obtain ⟨hb, hrest⟩ := h
    have hjn : j < nOf m := by rw [← hlenF m hm]; exact hj
    have hlt : as.length < ((Fsss m).getD j []).length := by
      have := congrArg List.length hF
      rw [List.length_cons, List.length_drop] at this
      omega
    have hdropF := List.drop_eq_getElem_cons hlt
    rw [← hF] at hdropF
    obtain ⟨hFget, hFs'⟩ := List.cons.inj hdropF
    have hFgetD : F = ((Fsss m).getD j []).getD as.length default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact hFget
    have hltS : as.length
        < (shadowFs nP (ksF m j) ((Fsss m).getD j []).length ((Fsss m).getD j [])).length := by
      rw [shadowFs_length]; exact hlt
    rw [List.drop_eq_getElem_cons hltS]
    have hget : (shadowFs nP (ksF m j) ((Fsss m).getD j []).length ((Fsss m).getD j []))[as.length]
        = if recAt nP (ksF m j) (nP + as.length) then AnnotTerm.sort 0
          else ((Fsss m).getD j []).getD as.length default := by
      have := shadowFs_getElem? (nP := nP) (ks := ksF m j) (Fs := (Fsss m).getD j []) hlt
      rw [List.getElem?_eq_getElem hltS] at this
      exact Option.some.inj this
    rw [hget]
    show (if recAt nP (ksF m j) (nP + as.length) then shadowVal else b) ∈ˢ _ ∧ SpineFit _ _ _
    refine ⟨?_, ?_⟩
    · by_cases hr : recAt nP (ksF m j) (nP + as.length)
      · rw [if_pos hr, if_pos hr, interp_sort]
        exact shadowVal_mem
      · rw [if_neg hr, if_neg hr]
        have hri : ((rsss m).getD j []).getD as.length false = false := by
          rw [hrss m hm j hjn]
          exact Bool.eq_false_iff.mpr fun h =>
            hr ((recAt_iff_rsOf (nP := nP) (by rw [(hC m hm j hjn).hks]; exact hlt)).mpr h)
        rw [xEntryB_ord F as t hri] at hb
        have hnb := (hC m hm j hjn).nb as.length hlt
        rw [← hFgetD] at hnb
        rw [← hFgetD,
          ← interp_congr_noBVar F hnb (agreeOff_shadow (shadowRel_shadowOf nP (ksF m j) as) ρp)]
        exact hb
    · have ih := blockShadowOf_fits hm hj (Y := Y) (t := t) Fs' (as.length + 1)
        (as ++ [b]) bs (length_snoc' b as) hFs' (by rw [← consList_snoc']; exact hrest)
      have hsh : shadowOf nP (ksF m j) (as ++ [b])
          = shadowOf nP (ksF m j) as
            ++ [if recAt nP (ksF m j) (nP + as.length) then shadowVal else b] := by
        unfold shadowOf
        rw [shadowOfGo_append, Nat.zero_add]
        rfl
      rw [hsh, ← consList_snoc'] at ih
      exact ih

include hI in
set_option maxHeartbeats 3200000 in
/-- **Every element of the block's fibre is a container element**: its
shadow tuple, TAGGED WITH ITS COMPONENT, is a shape; its recursive
slots' spine folds a function on the positions into the TARGET
components of the tuple; and it is the builder's value at both. -/
theorem blockStepV_elim_container {Xs : Nat → V}
    (hXs : InTupleSpace w k (blockIdx uf ρp Idss) Xs) {m : Nat} (hm : m < k) {t : V}
    (ht : t ∈ˢ idxSet (uf m) ρp (Idss m))
    (hfitX : ∀ j, j < (Fsss m).length →
      SlotsFitXB k w ρp uf Idss ((rsss m).getD j []) ((tgtsss m).getD j []) ((tlsss m).getD j [])
        ((Eisss m).getD j []) (ndMkTowerSet Xs 0 k) t 0 [] ((Fsss m).getD j []))
    {x : V} (hx : x ∈ˢ blockStepV w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss m
      (ndMkTowerSet Xs 0 k) t) :
    ∃ a, a ∈ˢ blockShapeSet w nP ρp uf Idss ksF Fsss Esss m t ∧
      ∃ g, g ∈ˢ piSet (blockPosSet w ρp rsss tlsss Fsss a)
          (fun p => SetTheory.app (Xs (blockPosTgtM tgtsss a p))
            (blockPosTgtI uf ρp tgtsss tlsss Eisss Fsss a p)) ∧
        x = blockMkShape w ρp rsss tlsss Fsss m a g := by
  obtain ⟨is, hsp, rfl⟩ := mem_idxSet_elim ht
  obtain ⟨j, fs, rfl, hj, hlen, hfs, hall⟩ := blockStepV_elim hw hx
  have hjn : j < nOf m := by rw [← hlenF m hm]; exact hj
  have hEs : ((Esss m).getD j []).length = (Idss m).length := (hC m hm j hjn).hEs
  have hfam : ∀ c, c < k → ∀ t', SetTheory.app (Xs c) t' ∈ˢ (univ w : V) := fun c hc t' =>
    famApp_mem_univ (by rw [lfpFamSpace_eq']; exact hXs c hc) t'
  -- the shape: the shadow tuple, tagged with the component
  have hsh : SpineFit ρp
      (shadowFs nP (ksF m j) ((Fsss m).getD j []).length ((Fsss m).getD j []))
      (shadowOf nP (ksF m j) fs) := by
    have := blockShadowOf_fits hlenF hrss hC hm hj (Y := ndMkTowerSet Xs 0 k)
      (t := tupW (uf m) is) ((Fsss m).getD j []) 0 [] fs rfl List.drop_zero.symm hfs
    rw [List.drop_zero] at this
    exact this
  have hidx : idxValsAt ρp ((Esss m).getD j []) (shadowOf nP (ksF m j) fs)
      = isOfW (uf m) (Idss m).length (tupW (uf m) is) := by
    rw [isOfW_tupW (hI m hm) hsp, idxValsAt_shadowS (hC m hm j hjn).toS hlen]
    rw [← hlen] at hall
    exact idxValsAt_of_eqsXI (hI m hm) hsp hEs hall
  obtain ⟨a', ha'def⟩ : ∃ a' : V, a' = inj j (mkTower (shadowOf nP (ksF m j) fs ++ [pt])) :=
    ⟨_, rfl⟩
  have ha' : a' ∈ˢ shapeSet (uf m) w nP ρp (Idss m) (ksF m) (Fsss m) (Esss m)
      (tupW (uf m) is) := by
    rw [ha'def]; exact (mem_shapeSet hw).mpr ⟨j, _, hj, rfl, hsh, hidx⟩
  have hcomp : shapeComp (inj m a') = m := shapeComp_inj m a'
  have hbody : shapeBody (inj m a') = a' := shapeBody_inj m a'
  have htag : shapeTag a' = j := by rw [ha'def]; exact shapeTag_inj j _
  have hfields : shapeFields ((Fsss m).getD j []).length a' = shadowOf nP (ksF m j) fs := by
    rw [ha'def, ← hlen, ← shadowOf_length nP (ksF m j) fs]
    exact shapeFields_inj j _ [pt]
  refine ⟨inj m a', mem_blockShapeSet.mpr ⟨a', ha', rfl⟩, ?_⟩
  -- the recursive slots at the real prefix, at their TARGET components
  have hslot : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length,
      ((tgtsss m).getD j []).getD i 0 < k ∧
      SlotFit (uf (((tgtsss m).getD j []).getD i 0)) w ρp
        (Idss (((tgtsss m).getD j []).getD i 0)) (((tlsss m).getD j []).getD i [])
        (((Eisss m).getD j []).getD i []) (fs.take i) ∧
      fs.getD i pt ∈ˢ slotSet w (uf (((tgtsss m).getD j []).getD i 0)) (consList (fs.take i) ρp)
        (((tlsss m).getD j []).getD i []) (((Eisss m).getD j []).getD i [])
        (Xs (((tgtsss m).getD j []).getD i 0)) := by
    intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    have := fitsXBI_slot_mem hI ((Fsss m).getD j []) 0 [] fs rfl (hfitX j hj) hfs i
      (by rw [hlen]; exact hik) (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append] at this
    rw [projS_ndMkTowerSet_zero this.1] at this
    exact this
  -- the shadow prefix against the real prefix
  have hrecAt : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length,
      recAt nP (ksF m j) (nP + i) := by
    intro i hi
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    rw [hrss m hm j hjn] at hri
    exact (recAt_iff_rsOf (by rw [(hC m hm j hjn).hks]; exact hik)).mpr hri
  have hQ : ∀ i, ∀ q, (recAt nP (ksF m j) q ∧ q < nP + i) → q < nP + i := fun _ _ h => h.2
  have hlenT : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length,
      (fs.take i).length = i := by
    intro i hi
    rw [List.length_take, hlen]; exact Nat.min_eq_left (Nat.le_of_lt (mem_recIdx.mp hi).1)
  have hag : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length,
      AgreeOff (exclP (fun q => recAt nP (ksF m j) q ∧ q < nP + i) (nP + i))
        (consList (fs.take i) ρp) (consList ((shadowOf nP (ksF m j) fs).take i) ρp) := by
    intro i hi
    have := agreeOff_shadow (shadowRel_shadowOf nP (ksF m j) (fs.take i)) ρp
    rw [hlenT i hi, ← shadowOf_take] at this
    exact this
  have hspine : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length, ∀ bs : List V,
      SpineFit (consList ((shadowOf nP (ksF m j) fs).take i) ρp)
          ((((tlsss m).getD j []).getD i []).map (·.2.2)) bs ↔
      SpineFit (consList (fs.take i) ρp)
          ((((tlsss m).getD j []).getD i []).map (·.2.2)) bs := fun i hi bs =>
    (spineFit_congr_exclP _ bs (hQ i) (hag i hi)
      (nbT_mapS (hC m hm j hjn).toS (mem_recIdx.mp hi).1 (hrecAt i hi))).symm
  have hEmap : ∀ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length, ∀ bs : List V,
      bs.length = (((tlsss m).getD j []).getD i []).length →
      ((((Eisss m).getD j []).getD i []).map
          (interp V (consList bs (consList ((shadowOf nP (ksF m j) fs).take i) ρp))))
        = (((Eisss m).getD j []).getD i []).map
            (interp V (consList bs (consList (fs.take i) ρp))) := by
    intro i hi bs hbs
    apply List.map_congr_left
    intro E hE
    have hnb := (hC m hm j hjn).nbE i (mem_recIdx.mp hi).1 (hrecAt i hi) E hE
    rw [← hbs] at hnb
    exact (interp_congr_noBVar E hnb (agreeOff_exclP_consList bs (hQ i) (hag i hi))).symm
  -- the function on the positions: the recursive slots' spine folds
  let G : V → V := fun p =>
    (projList ((((tlsss m).getD j []).getD (natIdx (sfst p)) [])).length (ssnd p)).foldl
      SetTheory.app (fs.getD (natIdx (sfst p)) pt)
  have hpos : ∀ p, p ∈ˢ blockPosSet w ρp rsss tlsss Fsss (inj m a') ↔
      ∃ i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length, ∃ q,
        q ∈ˢ spineSet w ρp (((tlsss m).getD j []).getD i [])
          ((shadowOf nP (ksF m j) fs).take i) ∧ p = kpair (vnat i) q := by
    intro p
    unfold blockPosSet posSet
    rw [hcomp, hbody, htag, hfields, mem_sigmaPairs]
    constructor
    · rintro ⟨q, hq, r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := mem_recTags.mp hq
      rw [natIdx_vnat] at hr
      exact ⟨i, hi, r, hr, rfl⟩
    · rintro ⟨i, hi, r, hr, rfl⟩
      refine ⟨vnat i, mem_recTags.mpr ⟨i, hi, rfl⟩, r, ?_, rfl⟩
      rw [natIdx_vnat]; exact hr
  have htgtM : ∀ i (q : V), blockPosTgtM tgtsss (inj m a') (kpair (vnat i) q)
      = ((tgtsss m).getD j []).getD i 0 := by
    intro i q
    unfold blockPosTgtM
    rw [hcomp, hbody, htag, sfst_kpair, natIdx_vnat]
  refine ⟨graph G (blockPosSet w ρp rsss tlsss Fsss (inj m a')), ?_, ?_⟩
  · -- the values land in the TARGET component at the call's index tuple
    refine graph_mem_piSet fun p hp => ?_
    obtain ⟨i, hi, q, hq, rfl⟩ := (hpos p).mp hp
    unfold spineSet at hq
    have hbs := (towerSet_elim_teleOfFields hw hq).1
    rw [List.length_map] at hbs
    have hbsR := (hspine i hi _).mp hbs
    have hlenbs : (projList ((((tlsss m).getD j []).getD i [])).length q).length
        = (((tlsss m).getD j []).getD i []).length := by
      rw [hbs.length_eq, List.length_map]
    have hmem := slotSet_fold_mem (hfam _ (hslot i hi).1) (hslot i hi).2.2 hbsR
    show G (kpair (vnat i) q) ∈ˢ SetTheory.app (Xs (blockPosTgtM tgtsss (inj m a') _))
      (blockPosTgtI uf ρp tgtsss tlsss Eisss Fsss (inj m a') (kpair (vnat i) q))
    rw [htgtM i q]
    unfold blockPosTgtI posTgt
    rw [htgtM i q, hcomp, hbody, htag, hfields]
    simp only [G, sfst_kpair, ssnd_kpair, natIdx_vnat]
    rw [hEmap i hi _ hlenbs]
    exact hmem
  · -- the element is the builder's value
    unfold blockMkShape mkShape
    rw [hbody, htag, hfields]
    have hL : fs = (List.range ((Fsss m).getD j []).length).map fun i =>
        if ((rsss m).getD j []).getD i false then
          lamTower w (consList ((shadowOf nP (ksF m j) fs).take i) ρp)
            (((tlsss m).getD j []).getD i []) fun σ =>
              app (graph G (blockPosSet w ρp rsss tlsss Fsss (inj m a')))
                (kpair (vnat i)
                  (mkTower (frameIdx ((((tlsss m).getD j []).getD i [])).length σ)))
        else (shadowOf nP (ksF m j) fs).getD i pt := by
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      rw [List.getElem_map, List.getElem_range]
      have hfsi : fs[i] = fs.getD i pt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
      rw [hfsi]
      by_cases hri : ((rsss m).getD j []).getD i false = true
      · rw [if_pos hri]
        have hi : i ∈ recIdx ((rsss m).getD j []) ((Fsss m).getD j []).length :=
          mem_recIdx.mpr ⟨by omega, hri⟩
        have hstep1 : lamTower w (consList ((shadowOf nP (ksF m j) fs).take i) ρp)
              (((tlsss m).getD j []).getD i [])
              (fun σ => app (graph G (blockPosSet w ρp rsss tlsss Fsss (inj m a')))
                (kpair (vnat i)
                  (mkTower (frameIdx ((((tlsss m).getD j []).getD i [])).length σ))))
            = lamTower w (consList (fs.take i) ρp) (((tlsss m).getD j []).getD i [])
              (fun σ => app (graph G (blockPosSet w ρp rsss tlsss Fsss (inj m a')))
                (kpair (vnat i)
                  (mkTower (frameIdx ((((tlsss m).getD j []).getD i [])).length σ)))) := by
          refine lamTower_congr_exclP _ (hQ i) (agreeOff_symm (hag i hi)) ?_ fun bs hbs => ?_
          · intro q d hq
            exact (hC m hm j hjn).nbT i (by omega) (hrecAt i hi) q d hq
          · have hlenbs : bs.length = (((tlsss m).getD j []).getD i []).length := by
              rw [hbs.length_eq, List.length_map]
            rw [← hlenbs, frameIdx_consList', frameIdx_consList']
        have hstep2 : lamTower w (consList (fs.take i) ρp) (((tlsss m).getD j []).getD i [])
              (fun σ => app (graph G (blockPosSet w ρp rsss tlsss Fsss (inj m a')))
                (kpair (vnat i)
                  (mkTower (frameIdx ((((tlsss m).getD j []).getD i [])).length σ))))
            = lamTower w (consList (fs.take i) ρp) (((tlsss m).getD j []).getD i [])
              (fun σ => (frameIdx ((((tlsss m).getD j []).getD i [])).length σ).foldl
                SetTheory.app (fs.getD i pt)) := by
          refine lamTower_congr_leaves fun bs hbs => ?_
          have hlenbs : bs.length = (((tlsss m).getD j []).getD i []).length := by
            rw [hbs.length_eq, List.length_map]
          rw [← hlenbs, frameIdx_consList']
          have hpmem : kpair (vnat i) (mkTower bs)
              ∈ˢ blockPosSet w ρp rsss tlsss Fsss (inj m a') := by
            refine (hpos _).mpr ⟨i, hi, mkTower bs, ?_, rfl⟩
            unfold spineSet
            exact mkTower_mem hw (fitsS_teleOfFields.mpr ((hspine i hi bs).mpr hbs))
          rw [app_graph hpmem]
          simp only [G, sfst_kpair, ssnd_kpair, natIdx_vnat]
          rw [projList_mkTower _ bs hlenbs]
        rw [hstep1, hstep2]
        have := (hslot i hi).2.2
        unfold slotSet at this
        exact (piTele_eta hw this).symm
      · rw [if_neg hri, shadowOf_getD h1]
        rw [if_neg]
        intro hr
        exact hri (by
          rw [hrss m hm j hjn]
          exact (recAt_iff_rsOf (by rw [(hC m hm j hjn).hks]; omega)).mp hr)
    exact congrArg (fun L => inj j (mkTower (L ++ [pt]))) hL

/-! ## The witness -/

include hI in
/-- **A closed tuple exists for every block** (positive sort): the
block's tuple functor is a container — shapes the shadow tuples tagged
by (component, constructor), positions the recursive fields' spines,
targets the calls' member-and-index-tuple pairs, the builder the
curried slots — so `blockPhi_closed_container` applies. -/
theorem blockClosed_of :
    ∃ L, IsClosedTuple w k (blockIdx uf ρp Idss)
      (blockPhi k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss) L := by
  have hfitX : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ m, m < k →
      ∀ t, t ∈ˢ idxSet (uf m) ρp (Idss m) → ∀ j, j < (Fsss m).length →
        SlotsFitXB k w ρp uf Idss ((rsss m).getD j []) ((tgtsss m).getD j [])
          ((tlsss m).getD j []) ((Eisss m).getD j []) Y t 0 [] ((Fsss m).getD j []) := by
    intro Y hY m hm t ht j hj
    have hjn : j < nOf m := by rw [← hlenF m hm]; exact hj
    rw [hrss m hm j hjn]
    exact (blockChain_of hI hm hY ht (hC m hm j hjn)).2
  exact blockPhi_closed_container hw
    (blockShapeSet w nP ρp uf Idss ksF Fsss Esss)
    (blockPosSet w ρp rsss tlsss Fsss)
    (blockPosTgtM tgtsss)
    (blockPosTgtI uf ρp tgtsss tlsss Eisss Fsss)
    (blockMkShape w ρp rsss tlsss Fsss)
    (fun m hm _ _ => blockShapeSet_mem hw hlenF hC hm _)
    (fun m hm _ a _ ha => blockPosSet_mem hw hlenF hrss hC hm ha)
    (fun m hm _ a p _ ha hp => blockPosTgt_mem hw hlenF hrss hC hm ha hp)
    (fun m hm _ a g _ ha hg => blockMkShape_mem hw hlenF hrss hC hm ha hg)
    (fun Xs hXs m hm t ht x hx =>
      blockStepV_elim_container hw hI hlenF hrss hC hXs hm ht
        (fun j hj => (hfitX (ndMkTowerSet Xs 0 k) (ndMkTowerSet_mem_famsSpaceB hXs) m hm t ht j hj))
        hx)

end Block

end ConLeche.Model
