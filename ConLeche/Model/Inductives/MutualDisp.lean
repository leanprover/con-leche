module

public import ConLeche.Semantics.Tower.MutualLeafI
public import ConLeche.Model.Inductives.SumRecFrames
import ConLeche.Semantics.Tower.FixRecI
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
  .app ((auxBodyAV [] W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
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

/-- The dispatch's body one binder (`i : tag`) below the K-frame
`(p⃗, Mv, M'⃗)`: the case split on the tag applied to the payload. -/
@[expose] def dispBodyAV (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  .app
    (caseRecAVI [] (dispLevel w ℓ) W (rChains (k + 1) 0 Idss (List.replicate k []))
      (fun j => (Idss.getD j []).length) (fun _ _ => []) k 0 k 1 0 (.fst (.bvar 0)))
    (.snd (.bvar 0))

/-- The tag recursor's binder data: the tag motive, then the `k` minors. -/
@[expose] def dispDs (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) : List (Nat × Nat × AnnotTerm) :=
  (W, dispLevel w ℓ, tagMotTyAV ℓ W w Idss) ::
    (List.range k).map fun m' => (W, dispLevel w ℓ, tagMinorTyAV ℓ W w m' Idss)

/-- The tag recursor's residual at the K-frame: `λ (i : tag), body`. -/
@[expose] def dispLamAV (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  .lam (dispLevel w ℓ) ((tagTyAV W Idss).liftN (k + 1) 0) (dispBodyAV ℓ W w k Idss)

/-- The residual's type at the K-frame: `Π (i : tag), Mv i`. -/
@[expose] def dispResTyAV (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  .pi W (dispLevel w ℓ) ((tagTyAV W Idss).liftN (k + 1) 0) (.app (.bvar (k + 1)) (.bvar 0))

/-- **The tag recursor** at the parameter frame:
`λ Mv M'_1 … M'_k (i : tag), body` — a constant-bit λ-tower over the
binder data, so its laws are `mkLamsC`'s. -/
@[expose] def dispTowerAV (ℓ W w k : Nat) (Idss : List (List AnnotTerm)) : AnnotTerm :=
  mkLamsC (dispLevel w ℓ) (dispDs ℓ W w k Idss) (dispLamAV ℓ W w k Idss)

/-- **The motive dispatch** at a frame `D` binders below the parameter
frame whose `k` motives sit at `bvar (mOff + k - 1 - m')`: the tag
recursor applied to the tag motive and the block's motives. -/
@[expose] def motDispAV (ℓ W w D mOff k : Nat) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN ((dispTowerAV ℓ W w k Idss).liftN D 0)
    ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN D 0 ::
      (List.range k).map fun m' => AnnotTerm.bvar (mOff + k - 1 - m'))

/-! ## The semantic pieces -/

/-- The auxiliary fibre at a tag element. -/
@[expose] noncomputable def auxFib (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (i : V) : V :=
  SetTheory.app (auxFamI [] W w ρp Idss rss tlss Eiss' Fss Ess') (auxTup W i)

/-- The tag motive's value: the fibre's function space into `Sort ℓ`,
at every tag element. -/
@[expose] noncomputable def tagMotV (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : V :=
  lamR (dispLevel w ℓ + 1) (tagSet W ρp Idss) fun i =>
    piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) fun _ => (univ ℓ : V)

/-- The tag motive space `Π (i : tag), Sort ℓ'`. -/
@[expose] noncomputable def tagMotSp (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm)) : V :=
  piR (dispLevel w ℓ + 1) (tagSet W ρp Idss) fun _ => (univ (dispLevel w ℓ) : V)

/-- Tag minor `m`'s space at a tag motive `Mv`: `Π ı⃗_m, Mv (inj m ⟨ı⃗⟩)`. -/
@[expose] noncomputable def tagMinorSp (ℓ w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (Mv : V) (m : Nat) : V :=
  piTele (dispLevel w ℓ) (teleOfFields ρp (Idss.getD m []))
    (fun is => SetTheory.app Mv (inj m (mkTower (is ++ [pt])))) []

/-- Member `m`'s motive space at the parameter frame: the tag minor
space at the tag motive (`memberMotSp_eq`: the nested product over its
index telescope into the functions from its fibre into `Sort ℓ`). -/
@[expose] noncomputable def memberMotSp (ℓ W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m : Nat) : V :=
  tagMinorSp ℓ w ρp Idss (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') m

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

/-- The tag recursor's K-frame hypotheses: a motive in the tag motive
space and `k` minors (member order) in their spaces at it. -/
structure TagFrameHyp (ℓ W w k : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (Mv : V) (ms : List V) : Prop where
  hT : TagOk W ρp Idss
  hMv : Mv ∈ˢ tagMotSp ℓ W w ρp Idss
  hk : Idss.length = k
  hlen : ms.length = k
  hms : ∀ j, j < k → ms.getD j pt ∈ˢ tagMinorSp ℓ w ρp Idss Mv j

/-- The tag recursor's K-frame: the parameter frame, the tag motive,
the minors. -/
@[expose] noncomputable def tagKFrame (ρp : Nat → V) (Mv : V) (ms : List V) : Nat → V :=
  consList ms (cons Mv ρp)

section Facts

variable {ℓ W w D mOff k : Nat} {ρp σ : Nat → V} {Idss : List (List AnnotTerm)}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}

/-! ### The auxiliary fibre at an index term -/

/-- The auxiliary family at the parameter frame is in the family space. -/
theorem auxFamI_mem_space (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    auxFamI [] W w ρp Idss rss tlss Eiss' Fss Ess'
      ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) :=
  (fixBodyAVI_facts (tbl := []) (auxIds_idxOk hT) hok (offOk_nil _ _ _)).2.1

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
  have hbody := fixBodyAVI_facts (tbl := []) hI hok (offOk_nil _ _ _)
  have hfv : interp V τ ((auxBodyAV [] W w Idss rss tlss Eiss' Fss Ess').liftN d 0)
      = interp V ρp (auxBodyAV [] W w Idss rss tlss Eiss' Fss Ess') := by
    rw [interp_liftN, hfr]
  have hfok : WellDenoted V τ ((auxBodyAV [] W w Idss rss tlss Eiss' Fss Ess').liftN d 0) := by
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

/-! ### The tag motive's type and the minor spaces -/

/-- The tag motive's type reads the tag motive space. -/
theorem tagMotTyAV_facts (hT : TagOk W ρp Idss) :
    interp V ρp (tagMotTyAV ℓ W w Idss) = tagMotSp ℓ W w ρp Idss ∧
      WellDenoted V ρp (tagMotTyAV ℓ W w Idss) := by
  have hTv := tagTyAV_facts hT
  unfold tagMotTyAV tagMotSp
  refine ⟨?_, ?_⟩
  · rw [interp_pi, hTv.1]; rfl
  · rw [WellDenoted_pi]
    exact ⟨hTv.2.2, fun _ _ => trivial⟩

/-- The tag motive at a tag element is the fibre's function space into
`Sort ℓ`. -/
theorem tagMotV_app {i : V} (hi : i ∈ˢ tagSet W ρp Idss) :
    SetTheory.app (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') i
      = piR (ℓ + 1) (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i) fun _ => (univ ℓ : V) := by
  unfold tagMotV
  exact app_lamR_pos (Nat.succ_ne_zero _) hi

/-- The tag motive is in the tag motive space. -/
theorem tagMotV_mem (hT : TagOk W ρp Idss)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' ∈ˢ tagMotSp ℓ W w ρp Idss := by
  unfold tagMotV tagMotSp
  refine lamR_mem fun i hi => ?_
  exact piR_mem_univ (auxFib_univ hT hok hi) (fun _ _ => univ_mem_univ ℓ)

/-- Nested products over one telescope agree when their bodies agree
at fitting tuples (both bits nonzero). -/
theorem piTele_congr_fit {v v' : Nat} (hv : v ≠ 0) (hv' : v' ≠ 0) {B B' : List V → V} :
    ∀ {n : Nat} {T : TeleS V n} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) = B' (acc ++ as)) →
      piTele v T B acc = piTele v' T B' acc
  | _, .nil, acc, h => by
    have := h [] trivial
    simpa [piTele] using this
  | _, .cons A T, acc, h => by
    simp only [piTele]
    rw [piR_congr_bit (v := v) (v' := v') (iff_of_false hv hv')]
    apply piR_congr
    intro a ha
    refine piTele_congr_fit hv hv' fun as hfit => ?_
    have := h (a :: as) ⟨ha, hfit⟩
    rwa [List.append_cons] at this

/-- **Member `m`'s motive space** is the nested product over its index
telescope into the functions from its fibre into `Sort ℓ`. -/
theorem memberMotSp_eq (hT : TagOk W ρp Idss) {m : Nat} (hm : m < Idss.length) :
    memberMotSp ℓ W w ρp Idss rss tlss Eiss' Fss Ess' m
      = piTele (ℓ + 1) (teleOfFields ρp (Idss.getD m []))
          (fun is => piR (ℓ + 1)
            (auxFib W w ρp Idss rss tlss Eiss' Fss Ess' (inj m (mkTower (is ++ [pt]))))
            fun _ => (univ ℓ : V)) [] := by
  obtain ⟨Ids, hIds⟩ : ∃ Ids, Idss[m]? = some Ids := ⟨_, List.getElem?_eq_getElem hm⟩
  have hg : Idss.getD m [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
  unfold memberMotSp tagMinorSp
  rw [hg]
  refine piTele_congr_fit (dispLevel_ne_zero w ℓ) (Nat.succ_ne_zero ℓ) fun as hfit => ?_
  rw [List.nil_append]
  exact tagMotV_app (tagTuple_mem hT hIds (fitsS_teleOfFields.mp hfit))

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

/-- The nested product over a lifted chain at a deeper frame is the
product over the chain at the retracted frame (`piTele_liftTele2`'s
shape for `liftFields`, at any cutoff). -/
theorem piTele_liftFields {v n : Nat} {B : List V → V} :
    ∀ (Fs : List AnnotTerm) (k : Nat) (τ : Nat → V) (acc : List V),
      piTele v (teleOfFields τ (liftFields n k Fs)) B acc
        = piTele v (teleOfFields (shiftE n k τ) Fs) B acc
  | [], _, _, _ => rfl
  | F :: Fs, k, τ, acc => by
    rw [liftFields_cons]
    simp only [teleOfFields, piTele]
    rw [interp_liftN]
    refine piR_congr fun a _ => ?_
    rw [piTele_liftFields Fs (k + 1) (cons a τ) (acc ++ [a]), cons_shiftE]

/-! ### The K-frame's slots -/

variable {Mv : V} {ms : List V}

/-- The block's motives' values at the frame, in member order. -/
@[expose] def motVals (σ : Nat → V) (mOff k : Nat) : List V :=
  (List.range k).map fun m' => σ (mOff + k - 1 - m')

omit [SetTheory V] in
theorem motVals_length (σ : Nat → V) (mOff k : Nat) : (motVals σ mOff k).length = k := by
  simp [motVals]

theorem motVals_getD (σ : Nat → V) (mOff k : Nat) {j : Nat} (hj : j < k) :
    (motVals σ mOff k).getD j pt = σ (mOff + k - 1 - j) := by
  unfold motVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

omit [SetTheory V] in
/-- The frame `1 + m'` binders below the parameter frame, at `m'` minors. -/
theorem minorFrame_shift (hlen : ms.length = m') :
    shiftE (1 + m') 0 (consList ms (cons Mv ρp)) = ρp := by
  rw [show 1 + m' = ms.length + 1 by omega, shiftE_consList_add, shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- At `m'` minors the motive sits at `bvar m'`. -/
theorem minorFrame_motive (hlen : ms.length = m') : consList ms (cons Mv ρp) m' = Mv := by
  have := consList_apply_add ms (cons Mv ρp) 0
  rw [Nat.zero_add] at this
  rw [← hlen, this, cons_zero]

theorem getD_snoc_lt {a : V} {j : Nat} (hj : j < ms.length) :
    (ms ++ [a]).getD j pt = ms.getD j pt := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD]

theorem getD_snoc_self {a : V} : (ms ++ [a]).getD ms.length pt = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

omit [SetTheory V] in
theorem tagKFrame_frP (hlen : ms.length = k) : frP k 0 (tagKFrame ρp Mv ms) = ρp :=
  kframe_frP' (is := []) rfl hlen

omit [SetTheory V] in
theorem tagKFrame_shift (hlen : ms.length = k) : shiftE (k + 1) 0 (tagKFrame ρp Mv ms) = ρp := by
  have := tagKFrame_frP (ρp := ρp) (Mv := Mv) hlen
  unfold frP at this
  rwa [Nat.zero_add] at this

omit [SetTheory V] in
theorem tagKFrame_frM (hlen : ms.length = k) : frM k 0 (tagKFrame ρp Mv ms) = Mv :=
  kframe_frM' (is := []) rfl hlen

theorem tagKFrame_frMs (hlen : ms.length = k) {j : Nat} (hj : j < k) :
    frMs k 0 (tagKFrame ρp Mv ms) j = ms.getD j pt := by
  unfold tagKFrame frMs
  rw [Nat.zero_add, consList_getD_lt ms _ _ (by omega), hlen,
    show k - 1 - (k - 1 - j) = j by omega]

/-! ### The minor types -/

/-- **Tag minor `m'`'s type** at a frame `1 + m'` binders below the
parameter frame with the tag motive at `bvar m'`: it reads the minor
space at the motive, and it is graded. -/
theorem tagMinorTyAV_facts (hT : TagOk W ρp Idss) (hMv : Mv ∈ˢ tagMotSp ℓ W w ρp Idss)
    {m' : Nat} (hm' : m' < Idss.length) {τ : Nat → V} (hfr : shiftE (1 + m') 0 τ = ρp)
    (hτ : τ m' = Mv) :
    interp V τ (tagMinorTyAV ℓ W w m' Idss) = tagMinorSp ℓ w ρp Idss Mv m' ∧
      WellDenoted V τ (tagMinorTyAV ℓ W w m' Idss) := by
  obtain ⟨Ids, hIds⟩ : ∃ Ids, Idss[m']? = some Ids := ⟨_, List.getElem?_eq_getElem hm'⟩
  have hg : Idss.getD m' [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
  have hIok : IdxOk W ρp Ids := hT.2 Ids (List.mem_of_getElem? hIds)
  unfold tagMinorTyAV tagMinorSp
  simp only [hg]
  have hdoms : ((liftFields (1 + m') 0 Ids).map fun F => (W, dispLevel w ℓ, F)).map (·.2.2)
      = liftFields (1 + m') 0 Ids := by simp [Function.comp_def]
  -- the body under a fitting index spine
  have hbase : ∀ as, SpineFit τ (liftFields (1 + m') 0 Ids) as →
      interp V (consList as τ) (.app (.bvar (Ids.length + m'))
          (tagTupleAV W m' (1 + m' + Ids.length) Idss (teleVarsAV Ids.length)))
        = SetTheory.app Mv (inj m' (mkTower (as ++ [pt]))) ∧
      WellDenoted V (consList as τ) (.app (.bvar (Ids.length + m'))
          (tagTupleAV W m' (1 + m' + Ids.length) Idss (teleVarsAV Ids.length))) := by
    intro as hsp
    have hlen : as.length = Ids.length := by rw [hsp.length_eq, liftFields_length]
    have hsp' : SpineFit ρp Ids as := by
      rw [← hfr]; exact (spineFit_liftFields _).mp hsp
    have hfr' : shiftE (1 + m' + Ids.length) 0 (consList as τ) = ρp := by
      rw [show 1 + m' + Ids.length = as.length + (1 + m') by omega, shiftE_consList_add, hfr]
    have hMv' : interp V (consList as τ) (.bvar (Ids.length + m')) = Mv := by
      rw [interp_bvar, show Ids.length + m' = m' + as.length by omega, consList_apply_add, hτ]
    have hvok : ∀ E ∈ teleVarsAV Ids.length, WellDenoted V (consList as τ) E := by
      intro E hE
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hE
      trivial
    have hvars : (teleVarsAV Ids.length).map (interp V (consList as τ)) = as := by
      rw [teleVarsAV_interp, ← hlen, frameIdx_consList']
    have htup := tagTupleAV_facts hT hIds hfr' hvok (by rw [hvars]; exact hsp')
    rw [hvars] at htup
    refine ⟨?_, ?_⟩
    · rw [interp_app, hMv', htup.1]
    · rw [WellDenoted_app]
      refine ⟨trivial, htup.2, dispLevel w ℓ + 1, tagSet W ρp Idss, fun _ => (univ (dispLevel w ℓ) : V),
        ?_, ?_, fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
      · rw [hMv']; exact hMv
      · rw [htup.1]; exact tagTuple_mem hT hIds hsp'
  refine ⟨?_, ?_⟩
  · rw [ConLeche.Model.interp_mkPisAV_piTele (v := dispLevel w ℓ)
      (B := fun is => SetTheory.app Mv (inj m' (mkTower (is ++ [pt])))) (acc := [])]
    · rw [hdoms, piTele_liftFields, hfr, hg]
    · intro d hd
      obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd
      exact Iff.rfl
    · intro as hsp
      rw [hdoms] at hsp
      rw [List.nil_append]
      exact (hbase as hsp).1
  · refine WellDenoted_mkPisAV_of (w := W) ?_ ?_
    · rw [hdoms, FieldsOkB_liftFields, hfr]; exact hIok.1
    · intro as hsp
      rw [hdoms] at hsp
      exact (hbase as hsp).2

/-! ### The tag recursor at its K-frame -/

section Disp

variable (h : TagFrameHyp ℓ W w k ρp Idss Mv ms)
include h

/-- **The tag block's recursor hypotheses** at the K-frame: the sum
route's core (the chains graded, the motive in its space, the frame's
tuple the empty one, the carrier the tagged union) and the minors in
their spaces read as the tag recursor's minor spaces. -/
theorem tagRecHyp :
    RecHypI [] (fun jc => jc) (dispLevel w ℓ) W (tagKFrame ρp Mv ms)
      Idss (List.replicate k []) [] (fun _ => tagSet W ρp Idss) (fun _ _ => []) := by
  have hfrP := tagKFrame_frP (ρp := ρp) (Mv := Mv) h.hlen
  have hfrM := tagKFrame_frM (ρp := ρp) (Mv := Mv) h.hlen
  have hshift := tagKFrame_shift (ρp := ρp) (Mv := Mv) h.hlen
  have hW := h.hT.1
  have hlenE : (List.replicate k ([] : List AnnotTerm)).length = Idss.length := by
    rw [List.length_replicate, h.hk]
  have hEs : ∀ j, j < Idss.length → ((List.replicate k ([] : List AnnotTerm)).getD j []).length = 0 := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by rw [← h.hk]; exact hj)]
    rfl
  refine ⟨⟨?_, hEs, hlenE, ?_, ?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_,
    fun h0 => absurd h0 (dispLevel_ne_zero w ℓ)⟩
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
      have hFs : FieldsOkB W (shiftE (k + 1) 0 (tagKFrame ρp Mv ms)) Fs := by
        rw [hshift]
        exact (h.hT.2 Fs (List.mem_of_getElem? hIj)).1
      exact FieldsOkB_rChain (V := V) (w := W) (d := k + 1) (nIdx := 0) (Fs := Fs)
        (Es := ([] : List AnnotTerm)) rfl hFs (fun _ _ E hE => nomatch hE)
  · -- the motive
    simp only [List.length_nil, teleOfFields_nil, piTele]
    rw [h.hk, hfrM]
    exact h.hMv
  · -- the frame's (empty) index tuple fits
    trivial
  · -- the carrier at the frame is the tagged union of the restricted chains
    simp only [List.length_nil, Nat.zero_add]
    rw [h.hk]
    unfold tagSet
    congr 1
    rw [← rChains_zero_uChains Idss k h.hk]
    refine sumFibre_rChains_congr (w := W) (d := 0) (d' := k + 1) (σ := ρp)
      (σ' := tagKFrame ρp Mv ms) hEs hlenE ?_ rfl
    rw [shiftE_zero_zero]
    exact hshift.symm
  · -- the minors
    simp only [List.length_nil]
    rw [h.hk]
    intro j hjk
    rw [tagKFrame_frMs h.hlen hjk, hfrP, hfrM]
    have hM := h.hms j hjk
    unfold tagMinorSp at hM
    obtain ⟨Ids, hIds⟩ : ∃ Ids, Idss[j]? = some Ids :=
      ⟨_, List.getElem?_eq_getElem (by rw [h.hk]; exact hjk)⟩
    have hg : Idss.getD j [] = Ids := by rw [List.getD_eq_getElem?_getD, hIds]; rfl
    rw [hg] at hM ⊢
    rw [minorSpI_eq_piTele (dispLevel_ne_zero w ℓ) (dispLevel_ne_zero w ℓ)
      (B := fun is => SetTheory.app Mv (inj j (mkTower (is ++ [pt]))))]
    · exact hM
    · intro fs hsp
      show ihSpL _ (concI [] W ρp _ ((List.replicate k ([] : List AnnotTerm)).getD j []) j fs) [] = _
      have hEj : (List.replicate k ([] : List AnnotTerm)).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hjk]; rfl
      rw [hEj]
      show concI [] W ρp _ [] j fs = _
      unfold concI ctorValI idxValsAt
      rw [List.map_nil, List.foldl_nil, if_neg hW, List.nil_append, locOf_nil]

omit h in
/-- A term whose value is in the tagged union is graded (graph regime)
through the carrier's own `sigmaSet`. -/
theorem major_sigma (hW : W ≠ 0) {ρ₀ τ : Nat → V} {Fss' : List (List AnnotTerm)}
    (hok : SumFieldsOkB W ρ₀ Fss') {e : AnnotTerm}
    (he : interp V τ e ∈ˢ sumSet W (sumFibre W ρ₀ Fss')) :
    ∃ u v A Bf, interp V τ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ (univ u : V) ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V) := by
  refine ⟨W, W, omega, natFibre (sumFibre W ρ₀ Fss'), ?_, omega_mem_univ_pos hW, ?_⟩
  · rw [show Nat.max W W = W from Nat.max_self W]
    exact he
  · intro k hk
    obtain ⟨i', rfl, hfib⟩ := natFibre_of_mem (sumFibre W ρ₀ Fss') hk
    rw [hfib]
    unfold sumFibre
    cases hi' : Fss'[i']? with
    | none => exact empty_mem_univ W
    | some Fs =>
      exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? hi')).toBound hW)

/-- **The dispatch's body** at a tag element `i = inj m ⟨ı⃗⟩`, at the
frame `(i)` below the K-frame: its value is minor `m` at `ı⃗`, it is
in `Mv i`, and it is graded. -/
theorem dispBody_facts {i : V} (hi : i ∈ˢ tagSet W ρp Idss) :
    (∃ (m : Nat) (y : V), m < k ∧ i = inj m y ∧
      interp V (cons i (tagKFrame ρp Mv ms)) (dispBodyAV ℓ W w k Idss)
        = ((List.range (Idss.getD m []).length).map fun l => projS l y).foldl
            SetTheory.app (ms.getD m pt)) ∧
    interp V (cons i (tagKFrame ρp Mv ms)) (dispBodyAV ℓ W w k Idss) ∈ˢ SetTheory.app Mv i ∧
    WellDenoted V (cons i (tagKFrame ρp Mv ms)) (dispBodyAV ℓ W w k Idss) := by
  have hW := h.hT.1
  have hℓ' := dispLevel_ne_zero w ℓ
  have hyp := tagRecHyp h
  have hfrM := tagKFrame_frM (ρp := ρp) (Mv := Mv) h.hlen
  have hfrMs := fun {j} (hj : j < k) => tagKFrame_frMs (ρp := ρp) (Mv := Mv) h.hlen hj
  have hok := hyp.toRecHypCore.hok
  have hfam := hyp.toRecHypCore.hfam
  generalize hρ₀ : tagKFrame ρp Mv ms = ρ₀ at hyp hfrM hfrMs hok hfam ⊢
  have hk := h.hk
  subst hk
  simp only [List.length_nil, Nat.zero_add] at hfam hok
  -- the carrier at the K-frame
  have hi' : i ∈ˢ sumSet W (sumFibre W ρ₀ (rChains (Idss.length + 1) 0 Idss
      (List.replicate Idss.length []))) := by
    rw [← hfam]; exact hi
  obtain ⟨m, y, hy, rfl⟩ := sumSet_elim hW hi'
  have hm : m < Idss.length := by
    refine Nat.lt_of_not_le fun hge => ?_
    rw [sumFibre_of_ge (by rw [rChains_length, List.length_replicate]; exact Nat.le_trans (Nat.min_le_left _ _) hge)] at hy
    exact not_mem_empty y hy
  -- the frame below the K-frame
  have hfr : RecFrameS 1 ρ₀ (cons (inj m y) ρ₀) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have hih : ∀ (D' j' : Nat) (σ' : Nat → V), RecFrameS D' ρ₀ σ' → j' < Idss.length →
      IhArgsOk W ρ₀ σ' Idss (List.replicate Idss.length []) [] (fun _ _ => []) (fun _ _ => [])
        (fun _ _ => []) D' j' := by
    intro D' j' σ' _ _ y' _
    exact ⟨rfl, rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩
  have hcase := caseRec_factsI hW hyp hih Idss.length (D := 1) (j := 0)
    (σ := cons (inj m y) ρ₀) (k := .fst (.bvar 0)) hfr (Nat.zero_add _)
  simp only [List.length_nil, Nat.zero_add] at hcase
  -- the tag and the payload at the frame
  have htag : interp V (cons (inj m y) ρ₀) (.fst (.bvar 0)) = vnat m := by
    rw [interp_fst, interp_bvar, cons_zero, sfst_inj]
  have hpay : interp V (cons (inj m y) ρ₀) (.snd (.bvar 0)) = y := by
    rw [interp_snd, interp_bvar, cons_zero, ssnd_inj]
  have hkω : interp V (cons (inj m y) ρ₀) (.fst (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega m
  obtain ⟨hmem, hiota⟩ := hcase.1 hkω
  rw [htag, motSem_vnat, Nat.zero_add] at hmem
  have hval := hiota m htag hm
  -- the motive at the frame's (empty) tuple is the tag motive
  have hMi : frMi Idss.length 0 ρ₀ = Mv := by
    unfold frMi
    simp only [frameIdx, List.range_zero, List.map_nil, List.foldl_nil]
    exact hfrM
  rw [hMi] at hmem
  -- the case split applied to the payload
  have hbase : SetTheory.app (interp V (cons (inj m y) ρ₀)
        (caseRecAVI [] (dispLevel w ℓ) W (rChains (Idss.length + 1) 0 Idss (List.replicate Idss.length []))
          (fun j => (Idss.getD j []).length) (fun _ _ => []) Idss.length 0 Idss.length 1 0
          (.fst (.bvar 0)))) y
      = ((List.range (Idss.getD m []).length).map fun l => projS l y).foldl SetTheory.app
          (ms.getD m pt) := by
    rw [hval]
    unfold baseSemI
    rw [app_lamR_pos hℓ' hy, List.append_nil, hfrMs hm]
  have hbaseMem : SetTheory.app (interp V (cons (inj m y) ρ₀)
        (caseRecAVI [] (dispLevel w ℓ) W (rChains (Idss.length + 1) 0 Idss (List.replicate Idss.length []))
          (fun j => (Idss.getD j []).length) (fun _ _ => []) Idss.length 0 Idss.length 1 0
          (.fst (.bvar 0)))) y
      ∈ˢ SetTheory.app Mv (inj m y) := by
    have := app_mem_piR_pos hℓ' hmem hy
    rwa [injW_pos hW] at this
  refine ⟨⟨m, y, hm, rfl, ?_⟩, ?_, ?_⟩
  · unfold dispBodyAV
    rw [interp_app, hpay, hbase]
  · unfold dispBodyAV
    rw [interp_app, hpay]
    exact hbaseMem
  · have hok0 : WellDenoted V (cons (inj m y) ρ₀) (.fst (.bvar 0)) := by
      rw [WellDenoted_fst]
      exact ⟨trivial, major_sigma hW hok (by rw [interp_bvar, cons_zero]; exact hi')⟩
    have hok1 : WellDenoted V (cons (inj m y) ρ₀) (.snd (.bvar 0)) := by
      rw [WellDenoted_snd]
      exact ⟨trivial, major_sigma hW hok (by rw [interp_bvar, cons_zero]; exact hi')⟩
    unfold dispBodyAV
    rw [WellDenoted_app]
    refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, dispLevel w ℓ, _, _, hmem, ?_,
      fun h0 => absurd h0 hℓ'⟩
    rw [hpay]; exact hy

/-- **The residual** `λ (i : tag), body` at the K-frame: graded, and in
`Π (i : tag), Mv i` — `UnderTowerOk`'s base. -/
theorem dispLam_facts :
    UnderTowerOk (dispLevel w ℓ) (tagKFrame ρp Mv ms) (dispLamAV ℓ W w k Idss)
      (dispResTyAV ℓ W w k Idss) [] := by
  have hℓ' := dispLevel_ne_zero w ℓ
  have hshift := tagKFrame_shift (ρp := ρp) (Mv := Mv) h.hlen
  have hM : ∀ i, cons i (tagKFrame ρp Mv ms) (k + 1) = Mv := by
    intro i
    have := tagKFrame_frM (ρp := ρp) (Mv := Mv) h.hlen
    unfold frM at this
    rw [Nat.zero_add] at this
    rw [cons_succ, this]
  have hTv := tagTyAV_facts h.hT
  have htag : interp V (tagKFrame ρp Mv ms) ((tagTyAV W Idss).liftN (k + 1) 0) = tagSet W ρp Idss := by
    rw [interp_liftN, hshift, hTv.1]
  have htagok : WellDenoted V (tagKFrame ρp Mv ms) ((tagTyAV W Idss).liftN (k + 1) 0) := by
    rw [WellDenoted_liftN, hshift]; exact hTv.2.2
  refine ⟨?_, ?_, fun h0 => absurd h0 hℓ'⟩
  · unfold dispLamAV
    rw [WellDenoted_lam, htag]
    exact ⟨htagok, fun i hi => (dispBody_facts h hi).2.2, fun i => SetTheory.app Mv i,
      fun i hi => (dispBody_facts h hi).2.1, fun h0 => absurd h0 hℓ'⟩
  · unfold dispLamAV dispResTyAV
    rw [interp_lam, interp_pi, htag]
    refine lamR_mem fun i hi => ?_
    rw [interp_app, interp_bvar, interp_bvar, cons_zero, hM]
    exact (dispBody_facts h hi).2.1

end Disp

/-! ### The tag recursor's tower -/

/-- The tower's binder bits all agree with the tower's bit. -/
theorem dispDs_bits : ∀ d ∈ dispDs ℓ W w k Idss, (dispLevel w ℓ = 0 ↔ d.2.1 = 0) := by
  intro d hd
  unfold dispDs at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact Iff.rfl
  · obtain ⟨m', -, rfl⟩ := List.mem_map.mp hd
    exact Iff.rfl

/-- The tower's premise along the minors: at `m'` minors in their spaces,
the remaining binders and the residual are hereditarily graded. -/
theorem dispTower_under_go (hT : TagOk W ρp Idss) (hMv : Mv ∈ˢ tagMotSp ℓ W w ρp Idss)
    (hk : Idss.length = k) :
    ∀ (r m' : Nat) (ms : List V), m' + r = k → ms.length = m' →
      (∀ j, j < m' → ms.getD j pt ∈ˢ tagMinorSp ℓ w ρp Idss Mv j) →
      UnderTowerOk (dispLevel w ℓ) (consList ms (cons Mv ρp)) (dispLamAV ℓ W w k Idss)
        (dispResTyAV ℓ W w k Idss)
        ((List.range' m' r).map fun j => (W, dispLevel w ℓ, tagMinorTyAV ℓ W w j Idss))
  | 0, m', ms, hr, hlen, hms => by
    rw [List.range'_zero, List.map_nil]
    exact dispLam_facts ⟨hT, hMv, hk, by omega, fun j hj => hms j (by omega)⟩
  | r + 1, m', ms, hr, hlen, hms => by
    rw [List.range'_succ, List.map_cons]
    have hty := tagMinorTyAV_facts hT hMv (m' := m') (by omega) (minorFrame_shift hlen)
      (minorFrame_motive hlen)
    simp only [UnderTowerOk]
    refine ⟨hty.2, fun a ha => ?_⟩
    rw [hty.1] at ha
    have := dispTower_under_go hT hMv hk r (m' + 1) (ms ++ [a]) (by omega) (by simp [hlen]) ?_
    · rwa [consList_append, consList_cons, consList_nil] at this
    · intro j hj
      rcases Nat.lt_or_ge j m' with hlt | hge
      · rw [getD_snoc_lt (by omega)]; exact hms j hlt
      · have hjm : j = m' := by omega
        rw [hjm, ← hlen, getD_snoc_self, hlen]
        exact ha

/-- **The tower's premise** at the parameter frame. -/
theorem dispTower_under (hT : TagOk W ρp Idss) (hk : Idss.length = k) :
    UnderTowerOk (dispLevel w ℓ) ρp (dispLamAV ℓ W w k Idss) (dispResTyAV ℓ W w k Idss)
      (dispDs ℓ W w k Idss) := by
  unfold dispDs
  simp only [UnderTowerOk]
  refine ⟨(tagMotTyAV_facts hT).2, fun Mv hMv => ?_⟩
  rw [(tagMotTyAV_facts hT).1] at hMv
  have := dispTower_under_go hT hMv hk k 0 [] (Nat.zero_add k) rfl
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  rwa [consList_nil, ← List.range_eq_range'] at this

/-- **The tag recursor** inhabits its Π-tower's reading and is graded. -/
theorem dispTower_facts (hT : TagOk W ρp Idss) (hk : Idss.length = k) :
    interp V ρp (dispTowerAV ℓ W w k Idss)
        ∈ˢ interp V ρp (mkPisAV (dispDs ℓ W w k Idss) (dispResTyAV ℓ W w k Idss)) ∧
      WellDenoted V ρp (dispTowerAV ℓ W w k Idss) :=
  ⟨mkLamsC_mem dispDs_bits (dispTower_under hT hk),
    mkLamsC_wellDenoted dispDs_bits (dispTower_under hT hk)⟩

/-- Minor values in their spaces fit the minor types along the spine. -/
theorem minors_spineFit_go (hT : TagOk W ρp Idss) (hMv : Mv ∈ˢ tagMotSp ℓ W w ρp Idss)
    (hk : Idss.length = k) (val : Nat → V)
    (hval : ∀ j, j < k → val j ∈ˢ tagMinorSp ℓ w ρp Idss Mv j) :
    ∀ (r m' : Nat) (ms : List V), m' + r = k → ms.length = m' →
      (∀ j, j < m' → ms.getD j pt = val j) →
      SpineFit (consList ms (cons Mv ρp))
        ((List.range' m' r).map fun j => tagMinorTyAV ℓ W w j Idss) ((List.range' m' r).map val)
  | 0, _, _, _, _, _ => by
    rw [List.range'_zero, List.map_nil, List.map_nil]; trivial
  | r + 1, m', ms, hr, hlen, hms => by
    rw [List.range'_succ, List.map_cons, List.map_cons]
    have hty := tagMinorTyAV_facts hT hMv (m' := m') (by omega) (minorFrame_shift hlen)
      (minorFrame_motive hlen)
    simp only [SpineFit]
    refine ⟨by rw [hty.1]; exact hval m' (by omega), ?_⟩
    have := minors_spineFit_go hT hMv hk val hval r (m' + 1) (ms ++ [val m']) (by omega)
      (by simp [hlen]) ?_
    · rwa [consList_append, consList_cons, consList_nil] at this
    · intro j hj
      rcases Nat.lt_or_ge j m' with hlt | hge
      · rw [getD_snoc_lt (by omega)]; exact hms j hlt
      · have hjm : j = m' := by omega
        subst hjm
        rw [← hlen, getD_snoc_self]

/-! ### The motive dispatch -/

/-- **The motive dispatch's laws** at a frame satisfying `MotDispHyp`:
at a tag-`m` element `inj m ⟨ı⃗⟩` and a fibre element `x` it reads
`M_m ı⃗ x`, it inhabits the auxiliary motive space, and it is graded. -/
theorem motDispAV_facts (h : MotDispHyp ℓ W w D mOff k ρp σ Idss rss tlss Eiss' Fss Ess') :
    (∀ (i x : V), i ∈ˢ tagSet W ρp Idss → x ∈ˢ auxFib W w ρp Idss rss tlss Eiss' Fss Ess' i →
      ∃ (m : Nat) (y : V), m < k ∧ i = inj m y ∧
        SetTheory.app (SetTheory.app
            (interp V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess')) i) x
          = SetTheory.app (((List.range (Idss.getD m []).length).map fun l => projS l y).foldl
              SetTheory.app (σ (mOff + k - 1 - m))) x) ∧
    interp V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess')
      ∈ˢ auxMotSp ℓ W w ρp Idss rss tlss Eiss' Fss Ess' ∧
    WellDenoted V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess') := by
  have hℓ' := dispLevel_ne_zero w ℓ
  have hMot := tagMotAV_facts (ℓ := ℓ) h.hT h.hok h.hfr
  have hMv : tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' ∈ˢ tagMotSp ℓ W w ρp Idss :=
    tagMotV_mem h.hT h.hok
  -- the arguments' values
  have hargs : (((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN D 0 ::
        (List.range k).map fun m' => AnnotTerm.bvar (mOff + k - 1 - m')).map (interp V σ))
      = tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' :: motVals σ mOff k := by
    rw [List.map_cons, hMot.1, List.map_map]
    rfl
  -- the tower at the frame is the tower at the parameter frame
  have htow : interp V σ ((dispTowerAV ℓ W w k Idss).liftN D 0)
      = interp V ρp (dispTowerAV ℓ W w k Idss) := by
    rw [interp_liftN, h.hfr]
  have htowok : WellDenoted V σ ((dispTowerAV ℓ W w k Idss).liftN D 0) := by
    rw [WellDenoted_liftN, h.hfr]; exact (dispTower_facts h.hT h.hk).2
  -- the spine fits the binder data
  have hsp : SpineFit ρp ((dispDs ℓ W w k Idss).map (·.2.2))
      (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess' :: motVals σ mOff k) := by
    unfold dispDs
    rw [List.map_cons]
    simp only [SpineFit]
    refine ⟨by rw [(tagMotTyAV_facts h.hT).1]; exact hMv, ?_⟩
    have := minors_spineFit_go h.hT hMv h.hk (fun m' => σ (mOff + k - 1 - m'))
      (fun j hj => h.hM j hj) k 0 [] (Nat.zero_add k) rfl (fun j hj => absurd hj (Nat.not_lt_zero j))
    rw [consList_nil, ← List.range_eq_range'] at this
    rw [List.map_map]
    exact this
  have hchain : AppChainOk (interp V σ ((dispTowerAV ℓ W w k Idss).liftN D 0))
      ((((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN D 0 ::
        (List.range k).map fun m' => AnnotTerm.bvar (mOff + k - 1 - m')).map (interp V σ))) := by
    rw [hargs, htow]
    exact appChainOk_of_mkPisAV (m := dispLevel w ℓ) dispDs_bits (dispTower_under h.hT h.hk)
      (dispTower_facts h.hT h.hk).1 hsp
  have hargsok : ∀ a ∈ ((tagMotAV ℓ W w Idss rss tlss Eiss' Fss Ess').liftN D 0 ::
      (List.range k).map fun m' => AnnotTerm.bvar (mOff + k - 1 - m')), WellDenoted V σ a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hMot.2.2
    · obtain ⟨m', -, rfl⟩ := List.mem_map.mp ha
      trivial
  have hall := mkAppN_wellDenoted_of_chain htowok hargsok hchain
  -- the value: the residual at the K-frame
  have hval : interp V σ (motDispAV ℓ W w D mOff k Idss rss tlss Eiss' Fss Ess')
      = interp V (tagKFrame ρp (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') (motVals σ mOff k))
          (dispLamAV ℓ W w k Idss) := by
    unfold motDispAV
    rw [hall.2, hargs, htow]
    unfold dispTowerAV mkLamsC
    rw [mkLamsAV_fold (fun d hd => by obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd; exact hℓ')
      (by rw [List.map_map]; exact hsp)]
    rfl
  have hfh : TagFrameHyp ℓ W w k ρp Idss (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess')
      (motVals σ mOff k) :=
    ⟨h.hT, hMv, h.hk, motVals_length σ mOff k,
      fun j hj => by rw [motVals_getD σ mOff k hj]; exact h.hM j hj⟩
  have hlamv : interp V (tagKFrame ρp (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess') (motVals σ mOff k))
        (dispLamAV ℓ W w k Idss)
      = lamR (dispLevel w ℓ) (tagSet W ρp Idss) fun i =>
          interp V (cons i (tagKFrame ρp (tagMotV ℓ W w ρp Idss rss tlss Eiss' Fss Ess')
            (motVals σ mOff k))) (dispBodyAV ℓ W w k Idss) := by
    unfold dispLamAV
    rw [interp_lam, interp_liftN, tagKFrame_shift (motVals_length σ mOff k), (tagTyAV_facts h.hT).1]
  refine ⟨?_, ?_, hall.1⟩
  · intro i x hi _
    obtain ⟨m, y, hm, rfl, hv⟩ := (dispBody_facts hfh hi).1
    refine ⟨m, y, hm, rfl, ?_⟩
    rw [hval, hlamv, app_lamR_pos hℓ' hi, hv, motVals_getD σ mOff k hm]
  · rw [hval, hlamv]
    unfold auxMotSp
    refine lamR_mem_zero_agree (iff_of_false hℓ' (Nat.succ_ne_zero ℓ)) fun i hi => ?_
    have := (dispBody_facts hfh hi).2.1
    rwa [tagMotV_app hi] at this

end Facts

end ConLeche.Model
