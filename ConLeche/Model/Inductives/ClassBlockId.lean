module

public import ConLeche.Model.Inductives.ClassBlock
import ConLeche.Model.Inductives.ClassCrestFit
public import ConLeche.Model.Inductives.ClassHFits

public section

/-!
# The block's identification: every node's crest at its filler (P2d, DESIGN CLASSCHECK / P2D4)

A container class's node identifies its container's recorded fit at a
valuation with its crest's fit at the valuation FILLED
(`ClassBlock.fill`).  The block states, per container class `c`, what
that takes, at the level of positions (`ClassBlockId`):

* the coherent value of a coherent class `d` for the reader `c`
  (`cohVal`): `d`'s container's carrier at `d`'s key read with `c`'s
  stage classes abstracted (`cohFr c d`, reading only `c`'s stage
  positions);
* `hfrd`: `d`'s own frame at a valuation holding `c`'s earlier coherent
  reads coherently is that key frame (P1 between the two restrictions,
  `restrict_read_eq`);
* `hidZ`: at every valuation holding `c`'s coherent reads coherently and
  its stage positions at their representatives, the crest's fit is the
  recorded fit (I2/I3 at the completion, `classCrest_hfits_iff`).

From these: the filler holds every coherent read at its coherent value
(`fill_coh`, by induction along the fill order — each read's own frame is
filled before it), and the node's identification (`ident`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Name ClassInfo)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {μ : ConLeche.CheckMode}
  {mp : EnvModelM V μ env} {φ : Name → Nat}

namespace ClassBlock

variable (B : ClassBlock mp φ)

/-- `c`'s stage positions: its free positions and its group. -/
@[expose] def Stage (c t : Nat) : Prop := (B.node c).F t ∨ (B.node c).G t

/-- **The coherent value of `d` for the reader `c`**: `d`'s container's
carrier at the key frame `cohFr c d`. -/
@[expose] noncomputable def cohVal (cohFr : Nat → Nat → (Nat → V) → Nat → V) (c d : Nat)
    (Z : Nat → V) : V :=
  (B.node d).D.carrier (B.node d).ψ (cohFr c d Z) ((B.node d).e d)

end ClassBlock

/-- **The block's identification data** (see the module docstring). -/
structure ClassBlockId (B : ClassBlock mp φ) where
  /-- a node's crests, read: node, group position, constructor -/
  crest : Nat → Nat → Nat → List (Nat × Nat × AnnotTerm) × AnnotTerm
  /-- the key frame of `d` read with `c`'s stage classes abstracted -/
  cohFr : Nat → Nat → (Nat → V) → Nat → V
  hcohFr : ∀ (c d : Nat) (Z Z' : Nat → V), (∀ t, t < B.nh → B.Stage c t → Z t = Z' t) →
    cohFr c d Z = cohFr c d Z'
  hflRank : ∀ (c d : Nat), d ∈ B.fl c → B.rank d < B.rank c
  hflPos : ∀ (c d : Nat), d ∈ B.fl c → d < B.nh ∧ ¬ B.Stage c d ∧ (B.node d).G d
  hfrd : ∀ (c i d : Nat), (B.fl c)[i]? = some d → ∀ (v v0 : Nat → V),
    InTupleSpace B.w B.nh B.Is v → InTupleSpace B.w B.nh B.Is v0 →
    (∀ t, t < B.nh → B.Stage c t → v t = v0 t) →
    (∀ i' d', i' < i → (B.fl c)[i']? = some d' → v d' = B.cohVal cohFr c d' v0) →
    (B.node d).fr v = cohFr c d v0
  hrepOff : ∀ (c t : Nat), ¬ B.Stage c t → B.rep c t = t
  hrepIdem : ∀ (c t : Nat), B.rep c (B.rep c t) = B.rep c t
  hrepStage : ∀ (c t : Nat), t < B.nh → B.Stage c t → B.Stage c (B.rep c t)
  hfrRep : ∀ (c : Nat) (Z Z' : Nat → V),
    (∀ t, t < B.nh → (B.node c).F t → B.rep c t = t → Z t = Z' t) →
    (B.node c).fr Z = (B.node c).fr Z'
  hsRep : ∀ (c m : Nat), m < (B.node c).D.N → B.rep c ((B.node c).s m) = (B.node c).s m
  hidZ : ∀ (c : Nat) (Z : Nat → V), InTupleSpace B.w B.nh B.Is Z →
    (∀ d ∈ B.fl c, Z d = B.cohVal cohFr c d Z) →
    (∀ t, t < B.nh → B.Stage c t → Z t = Z (B.rep c t)) →
    ∀ g, g < B.nh → (B.node c).G g → ∀ t, t ∈ˢ B.Is g → ∀ j fs,
      CrestFitAt (B.Dv.frame φ B.ρp Z) (crest c g j).1 (crest c g j).2 t fs ↔
        (B.node c).D.HFits (B.node c).ψ ((B.node c).fr Z) ((B.node c).thr Z) t ((B.node c).e g) j fs

namespace ClassBlock

variable (B : ClassBlock mp φ)

/-- **A class spliced in at its position**: the valuation elsewhere, at
its position its node's carrier at the valuation. -/
theorem sys_T_apply {d : Nat} {v : Nat → V} (hv : InTupleSpace B.w B.nh B.Is v) (hd : d < B.nh)
    (hG : (B.node d).G d) (t : Nat) :
    B.sys.T d v t = if t = d then (B.node d).D.carrier (B.node d).ψ ((B.node d).fr v) ((B.node d).e d)
      else v t := by
  have hΨ : B.sys.Ψ d = (B.node d).op := by
    funext v; unfold ClassSys.Ψ; simp [sys, ClassSys.fillL]
  rw [ClassSys.T_eq, hΨ]
  show mixT (fun t => t = d) v (ccar B.w B.nh B.Is (B.node d).G (B.node d).F (ClassNode.emptyT B.Is)
    (B.node d).op v) t = _
  unfold mixT
  by_cases ht : t = d
  · subst ht
    simp only [if_true]
    exact (B.node t).ccar_eq _ hv t hd hG
  · simp only [if_neg ht]

/-- The stage positions read through representatives are a valuation. -/
theorem norm_maps (c : Nat) : MapsTuple B.w B.nh B.Is (B.norm c) := (B.norm_ok c).1

/-- **A class spliced in keeps the valuation space.** -/
theorem sys_T_maps (d : Nat) : MapsTuple B.w B.nh B.Is (B.sys.T d) := by
  intro v hv t ht
  rw [ClassSys.T_eq]
  unfold cfixP mixT
  split
  · exact lfpTuple_mem _ _ _ _ t ht
  · exact hv t ht

theorem fillL_maps (c : Nat) :
    ∀ L : List Nat, MapsTuple B.w B.nh B.Is (ClassSys.fillL
      (fun d => if _h : B.rank d < B.rank c then B.sys.T d else fun v => v) L)
  | [] => fun _ hv => hv
  | d :: L => fun v hv => by
    show InTupleSpace _ _ _ (ClassSys.fillL _ L
      ((fun d => if _h : B.rank d < B.rank c then B.sys.T d else fun v => v) d v))
    refine fillL_maps c L _ ?_
    by_cases h : B.rank d < B.rank c
    · simp only [dif_pos h]; exact B.sys_T_maps d v hv
    · simp only [dif_neg h]; exact hv

/-- **The filler keeps the valuation space.** -/
theorem fill_maps (c : Nat) : MapsTuple B.w B.nh B.Is (B.fill c) :=
  fun X hX => B.fillL_maps c _ _ (B.norm_maps c X hX)

variable {B} (J : ClassBlockId B)

/-- **The filler along the fill order** (the induction): from a valuation
agreeing with `v0` at `c`'s stage positions and holding the first `i`
coherent reads coherently, the rest of the fill order holds every
coherent read coherently and keeps the stage positions. -/
theorem fill_coh_go (c : Nat) (v0 : Nat → V) (hv0 : InTupleSpace B.w B.nh B.Is v0) :
    ∀ n i, (B.fl c).length - i = n → ∀ v, InTupleSpace B.w B.nh B.Is v →
      (∀ t, t < B.nh → B.Stage c t → v t = v0 t) →
      (∀ i' d', i' < i → (B.fl c)[i']? = some d' → v d' = B.cohVal J.cohFr c d' v0) →
      let v' := ClassSys.fillL (fun d => if _h : B.rank d < B.rank c then B.sys.T d else fun v => v)
        ((B.fl c).drop i) v
      (∀ t, t < B.nh → B.Stage c t → v' t = v0 t) ∧
        ∀ i' d', i' < (B.fl c).length → (B.fl c)[i']? = some d' → v' d' = B.cohVal J.cohFr c d' v0
  | 0, i, hn, v, _, hst, hcoh => by
    have hi : (B.fl c).length ≤ i := by omega
    simp only [List.drop_eq_nil_of_le hi, ClassSys.fillL]
    refine ⟨hst, fun i' d' hi' hd' => hcoh i' d' (by omega) hd'⟩
  | n + 1, i, hn, v, hv, hst, hcoh => by
    have hi : i < (B.fl c).length := by omega
    obtain ⟨d, hd⟩ : ∃ d, (B.fl c)[i]? = some d := ⟨_, List.getElem?_eq_getElem hi⟩
    have hdmem : d ∈ B.fl c := List.mem_of_getElem? hd
    obtain ⟨hdn, hdS, hdG⟩ := J.hflPos c d hdmem
    have hdrop : (B.fl c).drop i = d :: (B.fl c).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi]
      congr 1
      exact (Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hd))
    simp only [hdrop, ClassSys.fillL, dif_pos (J.hflRank c d hdmem)]
    have hT := B.sys_T_apply hv hdn hdG
    have hval : B.sys.T d v d = B.cohVal J.cohFr c d v0 := by
      rw [hT, if_pos rfl, J.hfrd c i d hd v v0 hv hv0 hst hcoh]
      rfl
    refine fill_coh_go c v0 hv0 n (i + 1) (by omega) _ (B.sys_T_maps d v hv) (fun t ht hS => ?_)
      (fun i' d' hi' hd' => ?_)
    · rw [hT, if_neg (fun (h : t = d) => hdS (h ▸ hS))]
      exact hst t ht hS
    · by_cases hdd : d' = d
      · subst hdd; exact hval
      · rw [hT, if_neg hdd]
        refine hcoh i' d' ?_ hd'
        rcases Nat.lt_or_ge i' i with h | h
        · exact h
        · have : i' = i := by omega
          subst this
          rw [hd] at hd'
          exact absurd (Option.some.inj hd').symm hdd

/-- **The filler holds every coherent read coherently** and keeps the
stage positions of the valuation read through their representatives. -/
theorem fill_coh (c : Nat) {X : Nat → V} (hX : InTupleSpace B.w B.nh B.Is X) :
    (∀ t, t < B.nh → B.Stage c t → B.fill c X t = B.norm c X t) ∧
      ∀ d ∈ B.fl c, B.fill c X d = B.cohVal J.cohFr c d (B.norm c X) := by
  have h := fill_coh_go J c (B.norm c X) (B.norm_maps c X hX) _ 0 rfl (B.norm c X)
    (B.norm_maps c X hX) (fun _ _ _ => rfl) (fun _ _ h _ => absurd h (Nat.not_lt_zero _))
  simp only [List.drop_zero] at h
  refine ⟨h.1, fun d hd => ?_⟩
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hd
  exact h.2 i d hi (by rw [List.getElem?_eq_getElem hi, hdi])

/-- **The node's identification at its filler.** -/
@[expose] noncomputable def ident (c : Nat) : (B.node c).Ident where
  fill := B.fill c
  P := fun Z g t j fs => CrestFitAt (B.Dv.frame φ B.ρp Z) (J.crest c g j).1 (J.crest c g j).2 t fs
  hid := by
    intro X hX g hg hG t ht j fs
    obtain ⟨hst, hcoh⟩ := fill_coh J c hX
    have hZ := B.fill_maps c X hX
    have hnorm : ∀ t, t < B.nh → B.Stage c t → B.fill c X t = B.fill c X (B.rep c t) := by
      intro t ht hS
      have hr := (B.hrep c t ht).1
      rw [hst t ht hS, hst _ hr (J.hrepStage c t ht hS)]
      simp only [norm, J.hrepIdem]
    have hcoh' : ∀ d ∈ B.fl c, B.fill c X d = B.cohVal J.cohFr c d (B.fill c X) := by
      intro d hd
      rw [hcoh d hd]
      unfold cohVal
      rw [J.hcohFr c d (B.norm c X) (B.fill c X) fun t ht hS => (hst t ht hS).symm]
    have hid := J.hidZ c _ hZ hcoh' hnorm g hg hG t ht j fs
    have hfr : (B.node c).fr (B.fill c X) = (B.node c).fr X := by
      refine J.hfrRep c _ _ fun t ht hF hrt => ?_
      rw [hst t ht (Or.inl hF)]
      simp only [norm, hrt]
    have hthr : (B.node c).thr (B.fill c X) = (B.node c).thr X := by
      unfold ClassNode.thr
      refine thruT_congr fun m hm => ?_
      obtain ⟨h1, h2, -⟩ := (B.node c).hs m hm
      rw [hst _ h1 (Or.inr h2)]
      simp only [norm, J.hsRep c m hm]
    rw [← hfr, ← hthr]
    exact hid.symm

/-- **The crests' fits grow with the valuation**, when every crest is
positive along the space's hole order (T4). -/
theorem ident_mono
    (hpos : ∀ c g j, PiPosThen (ResultIdxConst 0) (J.crest c g j).1.length (B.Dv.tupRel φ B.ρp)
      (mkPisAV (J.crest c g j).1 (J.crest c g j).2))
    (c : Nat) {Z Z' : Nat → V} (hZ : InTupleSpace B.w B.nh B.Is Z)
    (hZ' : InTupleSpace B.w B.nh B.Is Z') (hle : TupleLe B.nh B.Is Z Z') {g t : Nat} {tt : V}
    {fs : List V} (h : (ident J c).P Z g tt t fs) : (ident J c).P Z' g tt t fs :=
  crestFitAt_mono (hpos c g t) ⟨Z, Z', hZ, hZ', hle, rfl, rfl⟩ h

/-- **THE CLASS FACTS, for every container class** of the block: its
operator and itself spliced in are good; its container's carrier grows
with its free positions and is accessible in the valuation (at a positive
level); its container's fit grows with the valuation (the class kit's
`fitMono`) — given every crest positive (T4 mono) and every node's
crest fit accessible (T4 acc). -/
theorem facts
    (hpos : ∀ c g j, PiPosThen (ResultIdxConst 0) (J.crest c g j).1.length (B.Dv.tupRel φ B.ρp)
      (mkPisAV (J.crest c g j).1 (J.crest c g j).2))
    (hacc : ∀ c, B.w ≠ 0 → ∃ A, A ∈ˢ (univ B.w : V) ∧ AccPred B.w B.nh B.Is (ident J c).Pel A)
    (c : Nat) :
    OpOk B.w B.nh B.Is (B.node c).op ∧ OpOk B.w B.nh B.Is (B.sys.T c) ∧
    (∀ u u', InTupleSpace B.w B.nh B.Is u → InTupleSpace B.w B.nh B.Is u' →
      (∀ m, m < B.nh → (B.node c).F m → FamLe (B.Is m) (u m) (u' m)) →
      ∀ g, g < B.nh → (B.node c).G g →
        FamLe (B.Is g) ((B.node c).D.carrier (B.node c).ψ ((B.node c).fr u) ((B.node c).e g))
          ((B.node c).D.carrier (B.node c).ψ ((B.node c).fr u') ((B.node c).e g))) ∧
    (B.w ≠ 0 → ∃ A, A ∈ˢ (univ B.w : V) ∧
      AccTuple B.w B.nh B.Is B.nh B.Is (ccar B.w B.nh B.Is (B.node c).G (B.node c).F
        (ClassNode.emptyT B.Is) (B.node c).op) A ∧
      ∀ u, InTupleSpace B.w B.nh B.Is u → ∀ g, g < B.nh → (B.node c).G g →
        ccar B.w B.nh B.Is (B.node c).G (B.node c).F (ClassNode.emptyT B.Is) (B.node c).op u g
          = (B.node c).D.carrier (B.node c).ψ ((B.node c).fr u) ((B.node c).e g)) ∧
    (∀ X X', InTupleSpace B.w B.nh B.Is X → InTupleSpace B.w B.nh B.Is X' →
      TupleLe B.nh B.Is X X' → ∀ g, g < B.nh → (B.node c).G g → ∀ t, t ∈ˢ B.Is g → ∀ j fs,
      (B.node c).D.HFits (B.node c).ψ ((B.node c).fr X) ((B.node c).thr X) t ((B.node c).e g) j fs →
      (B.node c).D.HFits (B.node c).ψ ((B.node c).fr X') ((B.node c).thr X') t ((B.node c).e g) j fs) := by
  have hall := B.good (fun c => ident J c) (fun _ => rfl)
    (fun c Z Z' hZ hZ' hle g _ _ t _ j fs h => ident_mono J hpos c hZ hZ' hle h) hacc
  obtain ⟨hok, hT⟩ := hall c
  refine ⟨hok, hT, fun u u' hu hu' hle => (B.node c).carrier_mono hok B.emptyT_mem hu hu' hle,
    fun hw => (B.node c).carrier_acc hok hw B.emptyT_mem, ?_⟩
  intro X X' hX hX' hle g hg hG t ht j fs hf
  have hfill : OpOk B.w B.nh B.Is (ident J c).fill :=
    B.fill_ok c fun d _ => (hall d).2
  exact (ident J c).hfits_mono hfill
    (fun Z Z' hZ hZ' hle' g' _ _ t' _ j' fs' h => ident_mono J hpos c hZ hZ' hle' h)
    hX hX' hle hg hG ht hf

end ClassBlock

end ConLeche.Model
