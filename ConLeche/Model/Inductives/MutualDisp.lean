module

public import ConLeche.Semantics.Tower.MutualLeafI
public import ConLeche.Model.Inductives.SumRecFrames
public import ConLeche.Semantics.Tower.FixRecI
import ConLeche.Model.Inductives.StructFrames
public section

/-!
# The mutual block's motive dispatch (task #278)

Member `m`'s recursor is the AUXILIARY family's recursor
(`nativeRecAVI`, the fixpoint route's leaf at the tag index) at ONE
motive: the **dispatch** of the block's `k` motives on the tag,

    Mot M⃗ := tag.rec (λ (i : tag), Π (x : aux ⟨i⟩), Sort ℓ) M_1 … M_k

— the TAG family's recursor at the motive `λ i, aux ⟨i⟩ → Sort ℓ` with
the block's motives as its minors, exactly the in-process modeller's
construction, spelled with the fixpoint route's own case split
(`caseRecAVI` with no inductive hypotheses) at a K-frame
`(p⃗, Mv, M'_1 … M'_k)` introduced by a λ-tower and immediately applied
to the tag motive and the block's motives (a β-redex in the leaf; the
K-frame is where `SumRecCase`'s arithmetic lives, and no restatement
is needed).  Its laws: at a tag-`m` element `inj m ⟨ı⃗⟩` it reads
`M_m ı⃗ x` (`caseRec_factsI`'s iota), it inhabits the auxiliary motive
space `Π (i : tag) (x : aux ⟨i⟩), Sort ℓ`, and it is graded.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The spelled pieces -/

/-- The tag recursor's elimination level: the sort of `aux ⟨i⟩ → Sort ℓ`. -/
@[expose] def dispLevel (w ℓ : Nat) : Nat := Nat.max w (ℓ + 1)

theorem dispLevel_ne_zero (w ℓ : Nat) : dispLevel w ℓ ≠ 0 := by
  unfold dispLevel
  show max w (ℓ + 1) ≠ 0
  omega

/-- The auxiliary family at the 1-tuple of an index term `i`, `d`
binders below the parameter frame. -/
@[expose] def auxAtAV (W w d : Nat) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) (i : AnnotTerm) : AnnotTerm :=
  .app ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
    (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN d 0) [i])

/-- The tag motive at the parameter frame: `λ (i : tag), Π (x : aux ⟨i⟩), Sort ℓ`. -/
@[expose] def tagMotAV (ℓ W w : Nat) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  .lam (dispLevel w ℓ + 1) (tagTyAV W Idss)
    (.pi w (ℓ + 1) (auxAtAV W w 1 Idss rss tlss Eiss' Fss Ess' (.bvar 0)) (.sort ℓ))

/-- The tag motive's type: `Π (i : tag), Sort ℓ'`. -/
@[expose] def tagMotTyAV (ℓ W w : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  .pi W (dispLevel w ℓ + 1) (tagTyAV W Idss) (.sort (dispLevel w ℓ))

/-- Tag minor `m'`'s type at its K-frame position (below the motive
variable and `m'` earlier minors): `Π ı⃗_{m'}, Mv (inj m' ⟨ı⃗_{m'}⟩)`. -/
@[expose] def tagMinorTyAV (ℓ W w m' : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  let Ids := Idss.getD m' []
  mkPisAV ((liftFields (1 + m') 0 Ids).map fun F => (W, dispLevel w ℓ, F))
    (.app (.bvar (Ids.length + m'))
      (tagTupleAV W m' (1 + m' + Ids.length) Idss (teleVarsAV Ids.length)))

/-- The dispatch's body at depth `2` below the K-frame `(p⃗, Mv, M'⃗)`
(the binders `i, x`): the case split on the tag applied to the payload
and to `x`. -/
@[expose] def dispBodyAV (ℓ W : Nat) (k : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  .app
    (.app (caseRecAVI (dispLevel W ℓ) W (rChains (k + 1) 0 Idss (List.replicate k []))
        (fun j => (Idss.getD j []).length) (fun _ _ => []) k 0 k 2 0 (.fst (.bvar 1)))
      (.snd (.bvar 1)))
    (.bvar 0)

/-- The dispatch tower at the parameter frame:
`λ Mv M'_1 … M'_k (i : tag) (x : aux ⟨i⟩), body`. -/
@[expose] def dispTowerAV (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  mkLamsAV ((dispLevel w ℓ + 1, tagMotTyAV ℓ W w Idss) ::
      (List.range k).map fun m' => (dispLevel w ℓ + 1, tagMinorTyAV ℓ W w m' Idss))
    (.lam (ℓ + 1) ((tagTyAV W Idss).liftN (k + 1) 0)
      (.lam (ℓ + 1) (auxAtAV W w (k + 2) Idss rss tlss Eiss' Fss Ess' (.bvar 0))
        (dispBodyAV ℓ W k Idss)))

/-- **The motive dispatch** at a frame `D` binders below the parameter
frame whose `k` motives sit at `bvar (mOff + k - 1 - m')`: the tower,
lifted, applied to the tag motive (lifted) and the frame's motives. -/
@[expose] def motDispAV (ℓ W w D mOff k : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN ((dispTowerAV ℓ W w k Idss rss tlss Eiss' Fss Ess').liftN D 0)
    ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN D 0 ::
      (List.range k).map fun m' => AnnotTerm.bvar (mOff + k - 1 - m'))

/-! ## The semantic pieces -/

/-- The auxiliary fibre at a tag element. -/
@[expose] noncomputable def auxFib (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (i : V) : V :=
  SetTheory.app (auxFamI W w ρp Idss rss tlss Eiss' Fss Ess') (auxTup W i)

/-- The tag motive's value: the fibre's function space into `Sort ℓ`,
at every tag element. -/
@[expose] noncomputable def tagMotV (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : V :=
  lamR (dispLevel w ℓ + 1) (tagSet W ρp Idss) fun i =>
    piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) fun _ => (univ ℓ : V)

/-- Member `m`'s motive space at the parameter frame: the nested product
over its index telescope into the functions from its fibre into
`Sort ℓ`. -/
@[expose] noncomputable def memberMotSp (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m : Nat) : V :=
  piTele (ℓ + 1) (teleOfFields ρp (Idss.getD m []))
    (fun is => piR (ℓ + 1)
      (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' (inj m (mkTower (is ++ [pt]))))
      fun _ => (univ ℓ : V)) []

/-- The auxiliary motive space at the parameter frame. -/
@[expose] noncomputable def auxMotSp (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : V :=
  piR (ℓ + 1) (tagSet W ρp Idss) fun i =>
    piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) fun _ => (univ ℓ : V)

/-- The hypotheses of the dispatch at a frame `σ` `D` binders below the
parameter frame `ρp`: the tag and the auxiliary chains graded at `ρp`,
the members' index counts, and every motive (at `σ (mOff + k - 1 - m')`)
in its member's space. -/
structure MotDispHyp (ℓ W w D mOff k : Nat) (ρp σ : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : Prop where
  hfr : shiftE D 0 σ = ρp
  hT : TagOk W ρp Idss
  hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess'
  hk : Idss.length = k
  hM : ∀ m', m' < k → σ (mOff + k - 1 - m') ∈ˢ memberMotSp ℓ W w ρp Idss rss tlss Eiss' Fss Ess' m'

section Facts

variable {ℓ W w D mOff k : Nat} {ρp σ : Nat → V} {Idss : List (List AnnotTerm)}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}

/-! ### The auxiliary fibre at an index term -/

/-- The auxiliary family at the parameter frame is in the family space. -/
theorem auxFamI_mem_space (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    auxFamI W w ρp Idss rss tlss Eiss' Fss Ess'
      ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) :=
  (fixBodyAVI_facts (auxIds_idxOk hT) hok).2.1

/-- A tag-set element's 1-tuple is in the auxiliary index set. -/
theorem auxTup_mem (hT : TagOk W ρp Idss) {i : V} (hi : i ∈ˢ tagSet W ρp Idss) :
    auxTup W i ∈ˢ idxSet W ρp (auxIds W Idss) := by
  refine tupW_mem ⟨?_, trivial⟩
  rw [(tagTyAV_facts hT).1]; exact hi

/-- The auxiliary fibre at a tag element is in the block's universe. -/
theorem auxFib_univ (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {i : V} (hi : i ∈ˢ tagSet W ρp Idss) :
    auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i ∈ˢ (univ w : V) :=
  famSpace_app (by rw [← lfpFamSpace_eq]; exact auxFamI_mem_space hT hok) (auxTup_mem hT hi)

/-- **The auxiliary family at an index term** whose value is a tag
element, `d` binders below the parameter frame: its value is the
fibre, in the block's universe, and it is graded. -/
theorem auxAtAV_facts (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {d : Nat} {τ : Nat → V} (hfr : shiftE d 0 τ = ρp) {i : AnnotTerm}
    (hiok : WellDenoted V τ i) (hi : interp V τ i ∈ˢ tagSet W ρp Idss) :
    interp V τ (auxAtAV W w d Idss rss tlss Eiss' Fss Ess' i)
        = auxFib W w ρp Idss rss tlss Eiss' Fss Ess' (interp V τ i) ∧
      interp V τ (auxAtAV W w d Idss rss tlss Eiss' Fss Ess' i) ∈ˢ (univ w : V) ∧
      WellDenoted V τ (auxAtAV W w d Idss rss tlss Eiss' Fss Ess' i) := by
  have hI : IdxOk W ρp (auxIds W Idss) := auxIds_idxOk hT
  have hbody := fixBodyAVI_facts hI hok
  have hfv : interp V τ ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
      = interp V ρp (auxBodyAV W w Idss rss tlss Eiss' Fss Ess') := by
    rw [interp_liftN, hfr]
  have hfok : WellDenoted V τ ((auxBodyAV W w Idss rss tlss Eiss' Fss Ess').liftN d 0) := by
    rw [WellDenoted_liftN, hfr]; exact hbody.2.2
  have htv : interp V τ ((tuplerAV W (auxIds W Idss)).liftN d 0)
      = interp V ρp (tuplerAV W (auxIds W Idss)) := by rw [interp_liftN, hfr]
  have htok : WellDenoted V τ ((tuplerAV W (auxIds W Idss)).liftN d 0) := by
    rw [WellDenoted_liftN, hfr]; exact tuplerAV_wellDenoted hI
  have hsp1 : SpineFit ρp (auxIds W Idss) [interp V τ i] := by
    refine ⟨?_, trivial⟩
    rw [(tagTyAV_facts hT).1]; exact hi
  have hchain : AppChainOk (interp V τ ((tuplerAV W (auxIds W Idss)).liftN d 0))
      ([i].map (interp V τ)) := by
    rw [htv, List.map_singleton]
    exact appChainOk_of_mkPisAV (ds := tuplerData W (auxIds W Idss)) (b := mkTowerGo W (auxIds W Idss))
      (C := (idxTyAV W (auxIds W Idss)).liftN (auxIds W Idss).length 0)
      (fun _ hd => by obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd; exact Iff.rfl)
      (tuplerAV_under hI) (tuplerAV_mem hI) (by rw [tuplerData_doms]; exact hsp1)
  have htup := mkAppN_wellDenoted_of_chain htok (fun a ha => by
      rw [List.mem_singleton] at ha; subst ha; exact hiok) hchain
  have htupv : interp V τ (AnnotTerm.mkAppN ((tuplerAV W (auxIds W Idss)).liftN d 0) [i])
      = auxTup W (interp V τ i) := by
    rw [htup.2, List.map_singleton, htv]
    exact tuplerAV_fold hI hsp1
  have hmemT := auxTup_mem hT hi
  have hfam := auxFamI_mem_space hT hok
  have hval : interp V τ (auxAtAV W w d Idss rss tlss Eiss' Fss Ess' i)
      = auxFib W w ρp Idss rss tlss Eiss' Fss Ess' (interp V τ i) := by
    unfold auxAtAV auxFib
    rw [interp_app, htupv, hfv]
    unfold auxBodyAV auxFamI
    rw [hbody.1]
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]; exact auxFib_univ hT hok hi
  · unfold auxAtAV
    rw [WellDenoted_app]
    refine ⟨hfok, htup.1, w + 1, idxSet W ρp (auxIds W Idss), fun _ => (univ w : V), ?_, ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩
    · rw [hfv]; unfold auxBodyAV; rw [hbody.1]; exact hfam
    · rw [htupv]; exact hmemT

/-! ### The tag motive -/

/-- **The tag motive**: its value, its membership in `Π (i : tag), Sort ℓ'`,
and its grading, at any frame `d` below the parameter frame. -/
theorem tagMotAV_facts (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {d : Nat} {τ : Nat → V} (hfr : shiftE d 0 τ = ρp) :
    interp V τ ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
        = tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' ∧
      interp V τ ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
        ∈ˢ interp V τ ((tagMotTyAV ℓ W w Idss).liftN d 0) ∧
      WellDenoted V τ ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN d 0) := by
  rw [interp_liftN, WellDenoted_liftN, interp_liftN, hfr]
  have hTv := tagTyAV_facts hT
  -- the body under `i`
  have hbody : ∀ i, i ∈ˢ tagSet W ρp Idss →
      interp V (cons i ρp) (.pi w (ℓ + 1) (auxAtAV W w 1 Idss rss tlss Eiss' Fss Ess' (.bvar 0)) (.sort ℓ))
        = piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) (fun _ => (univ ℓ : V)) ∧
      WellDenoted V (cons i ρp)
        (.pi w (ℓ + 1) (auxAtAV W w 1 Idss rss tlss Eiss' Fss Ess' (.bvar 0)) (.sort ℓ)) := by
    intro i hi
    have hfr1 : shiftE 1 0 (cons i ρp) = ρp := by
      rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
    have h := auxAtAV_facts hT hok hfr1 (i := .bvar 0) trivial (by rw [interp_bvar, cons_zero]; exact hi)
    rw [interp_bvar, cons_zero] at h
    refine ⟨?_, ?_⟩
    · rw [interp_pi, h.1]; rfl
    · rw [WellDenoted_pi]
      exact ⟨h.2.2, fun _ _ => trivial⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold tagMotAV tagMotV
    rw [interp_lam, hTv.1]
    exact lamR_congr fun i hi => (hbody i hi).1
  · unfold tagMotAV tagMotTyAV
    rw [interp_lam, interp_pi, hTv.1]
    refine lamR_mem fun i hi => ?_
    rw [(hbody i hi).1]
    exact piR_mem_univ (auxFib_univ hT hok hi) (fun _ _ => univ_mem_univ ℓ)
  · unfold tagMotAV
    rw [WellDenoted_lam, hTv.1]
    refine ⟨hTv.2.2, fun i hi => (hbody i hi).2, fun _ => univ (dispLevel w ℓ), fun i hi => ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    rw [(hbody i hi).1]
    exact piR_mem_univ (auxFib_univ hT hok hi) (fun _ _ => univ_mem_univ ℓ)

/-! ### The tag block's K-frame hypotheses -/

/-- The block's motives' values at the frame, in member order. -/
@[expose] def motVals (σ : Nat → V) (mOff k : Nat) : List V :=
  (List.range k).map fun m' => σ (mOff + k - 1 - m')

/-- The tag recursor's K-frame: the parameter frame, the tag motive,
the block's motives as the minors. -/
@[expose] noncomputable def tagKFrame (ℓ W w mOff k : Nat) (ρp σ : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : Nat → V :=
  consList (motVals σ mOff k) (cons (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') ρp)

omit [SetTheory V] in
theorem motVals_length (σ : Nat → V) (mOff k : Nat) : (motVals σ mOff k).length = k := by
  simp [motVals]

theorem motVals_getD (σ : Nat → V) (mOff k : Nat) {j : Nat} (hj : j < k) :
    (motVals σ mOff k).getD j pt = σ (mOff + k - 1 - j) := by
  unfold motVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- Lifting by nothing is the identity on a chain. -/
theorem liftFields_zero' : ∀ (k : Nat) (Fs : List AnnotTerm), liftFields 0 k Fs = Fs
  | _, [] => rfl
  | k, F :: Fs => by
    rw [liftFields_cons, AnnotTerm.liftN_zero, liftFields_zero' (k + 1) Fs]

/-- The unit-restricted chains are the restricted chains at no index
and no lift. -/
theorem rChains_zero_uChains (Idss : List (List AnnotTerm)) (k : Nat) (hk : Idss.length = k) :
    rChains 0 0 Idss (List.replicate k []) = uChains Idss := by
  apply List.ext_getElem?
  intro j
  rw [rChains_getElem?, uChains_getElem?]
  cases hj : Idss[j]? with
  | none =>
    have : (List.replicate k ([] : List AnnotTerm))[j]? = none := by
      rw [List.getElem?_eq_none]
      rw [List.length_replicate, ← hk]
      exact (List.getElem?_eq_none_iff.mp hj)
    rw [this]; rfl
  | some Fs =>
    have hjl : j < k := by rw [← hk]; exact (List.getElem?_eq_some_iff.mp hj).1
    rw [List.getElem?_replicate, if_pos hjl]
    simp only [Option.map_some]
    unfold rChain idxEqsAt
    rw [liftFields_zero']
    rfl

/-- A minor space with an explicit conclusion equals the nested
product over the same telescope when the two conclusions agree at
fitting tuples (both bits nonzero). -/
theorem minorSpI_eq_piTele {ℓ' v : Nat} (hℓ : ℓ' ≠ 0) (hv : v ≠ 0) {c : List V → V} {B : List V → V} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V} {acc : List V},
      (∀ as : List V, SpineFit ρ Fs as → c (acc ++ as) = B (acc ++ as)) →
      minorSpI ℓ' c Fs ρ acc = piTele v (teleOfFields ρ Fs) B acc
  | [], ρ, acc, h => by
    have := h [] trivial
    simp only [List.append_nil] at this
    simpa [minorSpI, piTele] using this
  | F :: Fs, ρ, acc, h => by
    simp only [minorSpI, teleOfFields_cons, piTele]
    rw [piR_congr_bit (v := ℓ') (v' := v) (iff_of_false hℓ hv)]
    apply piR_congr
    intro a ha
    refine minorSpI_eq_piTele hℓ hv ?_
    intro as hsp
    have := h (a :: as) ⟨ha, hsp⟩
    rwa [List.append_cons] at this

section Disp

variable (h : MotDispHyp ℓ W w D mOff k ρp σ Idss rss tlss Eiss' Fss Ess')
include h

omit h in
/-- The K-frame's parameter frame is `ρp`. -/
theorem tagKFrame_frP :
    frP k 0 (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess') = ρp := by
  unfold tagKFrame
  have := kframe_frP (V := V) (ρp := ρp) (M := tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess')
    (ms := motVals σ mOff k) (is := []) (n := k) (nIdx := 0) rfl (motVals_length σ mOff k)
  simpa using this

omit h in
/-- The K-frame's motive is the tag motive. -/
theorem tagKFrame_frM :
    frM k 0 (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess')
      = tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' := by
  unfold tagKFrame
  have := kframe_frM (V := V) (ρp := ρp) (M := tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess')
    (ms := motVals σ mOff k) (is := []) (n := k) (nIdx := 0) rfl (motVals_length σ mOff k)
  simpa using this

omit h in
/-- The K-frame's minors are the block's motives. -/
theorem tagKFrame_frMs {j : Nat} (hj : j < k) :
    frMs k 0 (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess') j = σ (mOff + k - 1 - j) := by
  unfold tagKFrame
  have := kframe_frMs (V := V) (ρp := ρp) (M := tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess')
    (ms := motVals σ mOff k) (is := []) (n := k) (nIdx := 0) rfl (motVals_length σ mOff k) hj
  rw [← motVals_getD σ mOff k hj]
  simpa using this

omit h in
/-- The tag motive at a member's tagged tuple is the fibre's function
space into `Sort ℓ`. -/
theorem tagMotV_app {i : V} (hi : i ∈ˢ tagSet W ρp Idss) :
    SetTheory.app (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') i
      = piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) fun _ => (univ ℓ : V) := by
  unfold tagMotV
  exact app_lamR_pos (Nat.succ_ne_zero _) hi

/-- The tag motive is in `Π (i : tag), Sort ℓ'`. -/
theorem tagMotV_mem :
    tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess'
      ∈ˢ piR (dispLevel w ℓ + 1) (tagSet W ρp Idss) fun _ => (univ (dispLevel w ℓ) : V) := by
  unfold tagMotV
  refine lamR_mem fun i hi => ?_
  exact piR_mem_univ (auxFib_univ h.hT h.hok hi) (fun _ _ => univ_mem_univ ℓ)

/-- **The tag block's recursor hypotheses** at the K-frame: the sum
route's core (the chains graded, the motive in its space, the frame's
tuple the empty one, the carrier the tagged union) and the minors —
the block's motives — in their member spaces read as the tag
recursor's minor spaces. -/
theorem tagRecHyp :
    RecHypI (dispLevel w ℓ) W (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess')
      Idss (List.replicate k []) [] (fun _ => tagSet W ρp Idss) (fun _ _ => []) := by
  have hfrP := tagKFrame_frP (ℓ := ℓ) (W := W) (w := w) (mOff := mOff) (k := k) (ρp := ρp) (σ := σ)
    (Idss := Idss) (rss := rss) (tlss := tlss) (Eiss' := Eiss') (Fss := Fss) (Ess' := Ess')
  have hfrM := tagKFrame_frM (ℓ := ℓ) (W := W) (w := w) (mOff := mOff) (k := k) (ρp := ρp) (σ := σ)
    (Idss := Idss) (rss := rss) (tlss := tlss) (Eiss' := Eiss') (Fss := Fss) (Ess' := Ess')
  have hW := h.hT.1
  have hlenE : (List.replicate k ([] : List AnnotTerm)).length = Idss.length := by
    rw [List.length_replicate, h.hk]
  have hEs : ∀ j, j < Idss.length → ((List.replicate k ([] : List AnnotTerm)).getD j []).length = 0 := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by rw [← h.hk]; exact hj)]
    rfl
  refine ⟨⟨?_, hEs, hlenE, ?_, ?_, ?_⟩, ?_, fun h0 => absurd h0 (dispLevel_ne_zero w ℓ)⟩
  · -- the restricted chains at the K-frame are graded
    simp only [List.length_nil, Nat.zero_add]
    rw [h.hk]
    intro chain hchain
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hchain
    rw [rChains_getElem?] at hj
    cases hIj : Idss[j]? with
    | none => rw [hIj] at hj; exact nomatch hj
    | some Fs =>
      have hjl : j < k := by rw [← h.hk]; exact (List.getElem?_eq_some_iff.mp hIj).1
      rw [hIj, List.getElem?_replicate, if_pos hjl] at hj
      obtain rfl := Option.some.inj hj
      have hFs : FieldsOkB W (shiftE (k + 1) 0 (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess')) Fs := by
        have hp : shiftE (k + 1) 0 (tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess') = ρp := by
          unfold frP at hfrP; rw [Nat.zero_add] at hfrP; exact hfrP
        rw [hp]
        exact (h.hT.2 Fs (List.mem_of_getElem? hIj)).1
      exact FieldsOkB_rChain (V := V) (w := W) (d := k + 1) (nIdx := 0) (Fs := Fs)
        (Es := ([] : List AnnotTerm)) rfl hFs (fun _ _ E hE => nomatch hE)
  · -- the motive
    simp only [List.length_nil, teleOfFields_nil, piTele]
    rw [h.hk, hfrM]
    exact tagMotV_mem h
  · -- the frame's (empty) index tuple fits
    trivial
  · -- the carrier at the frame is the tagged union of the restricted chains
    simp only [List.length_nil, Nat.zero_add]
    rw [h.hk]
    unfold tagSet
    congr 1
    rw [← rChains_zero_uChains Idss k h.hk]
    refine sumFibre_rChains_congr (w := W) (d := 0) (d' := k + 1) (σ := ρp)
      (σ' := tagKFrame ℓ W w mOff k ρp σ Idss rss tlss Eiss' Fss Ess') hEs hlenE ?_ rfl
    rw [shiftE_zero_zero]
    unfold frP at hfrP
    rw [Nat.zero_add] at hfrP
    exact hfrP.symm
  · -- the minors
    simp only [List.length_nil]
    rw [h.hk]
    intro j hjk
    rw [tagKFrame_frMs hjk, hfrP, hfrM]
    have hM := h.hM j hjk
    unfold memberMotSp at hM
    obtain ⟨Ids, hIds⟩ : ∃ Ids, Idss[j]? = some Ids :=
      ⟨_, List.getElem?_eq_getElem (by rw [h.hk]; exact hjk)⟩
    have hg : Idss.getD j [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
    rw [hg] at hM ⊢
    rw [minorSpI_eq_piTele (dispLevel_ne_zero w ℓ) (Nat.succ_ne_zero ℓ)
      (B := fun is => piR (ℓ + 1)
        (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' (inj j (mkTower (is ++ [pt]))))
        fun _ => (univ ℓ : V))]
    · exact hM
    · intro fs hsp
      show ihSpL _ (concI W ρp _ ((List.replicate k ([] : List AnnotTerm)).getD j []) j fs) [] = _
      have hEj : (List.replicate k ([] : List AnnotTerm)).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hjk]; rfl
      rw [hEj]
      show concI W ρp _ [] j fs = _
      unfold concI ctorValI idxValsAt
      rw [List.map_nil, List.foldl_nil, if_neg hW, List.nil_append]
      exact tagMotV_app (tagTuple_mem h.hT hIds hsp)

end Disp

end Facts

end ConLeche.Model
