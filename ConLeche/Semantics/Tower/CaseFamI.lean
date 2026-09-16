module

public import ConLeche.Semantics.Tower.MutualTagI
public import ConLeche.Semantics.Tower.FixRecCoreI

@[expose] public section

/-!
# The cased family functor: member-local element tags (task #315, DESIGN §U.15)

The mutual route (`MutualLeafI.lean`) models a `k`-member block as ONE
least fixed point over the tagged union of the members' index tuples,
and the functor it inherits from the fixpoint route (`fixFunAVI`,
`FixLeafI.lean`) sums, at EVERY index tuple, over the ONE global list
of constructor chains: an element's tag is then the constructor's
position in the whole block, so member `m`'s first constructor carries
the tag `offs m` rather than `0`.

The **cased** functor keeps the one global chain list but sums, at an
index tuple whose member is `m`, only over the SUFFIX of that list
from member `m`'s first constructor on (`caseChains`): an element's
tag is then its position WITHIN its member, which is what the
uniform constructor and recursor spellings need.  The member is read
off the tuple itself — an index tuple of the auxiliary family is
`mkTower [inj m ⟨ı⃗_m⟩]`, so its member is `natIdx (sfst (sfst t))`
(`caseTag`) — and the sum body is selected by the sum route's numeral
case split (`caseAVAt`, `SumCase.lean`) on the spelled discriminant
`.fst (.fst (.bvar 0))`.

This module: the cased functor's spelling (`caseFunAVI`,
`caseBodyAVI`), its semantics (`caseStepI`, `caseFamFI`, `caseFunVI`,
`caseFamI`), and the laws — the tag decomposition, the readings and
gradings, monotonicity, the stage's introduction and elimination, and
the fixed-point equation.  The premises are the fixpoint route's own
(`FixChainsOkI`, `XChainsOk` at the auxiliary index telescope) plus
the tag's grading (`TagOk`) and the member count (`Idss.length = k`);
the closed family is NOT derived here — `caseFamI_app_eq` takes it as
a hypothesis.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The cased chains and the member tag -/

/-- Member `m`'s chain suffix: the global X-chains from its first
constructor on (`offs m`). -/
def caseChains (W : Nat) (Idss : List (List AnnotTerm)) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m : Nat) :
    List (List AnnotTerm) :=
  (chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss Ess').drop (offs m)

/-- The suffix's entry `j` is the global entry `offs m + j`. -/
theorem caseChains_getElem? (W : Nat) (Idss : List (List AnnotTerm)) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) (m j : Nat) :
    (caseChains W Idss offs rss tlss Eiss' Fss Ess' m)[j]?
      = if offs m + j < Fss.length then
          some (chainXI W (auxIds W Idss) 1 (rss.getD (offs m + j) [])
            (tlss.getD (offs m + j) []) (Eiss'.getD (offs m + j) [])
            (Fss.getD (offs m + j) []) (Ess'.getD (offs m + j) []))
        else none := by
  unfold caseChains
  rw [List.getElem?_drop, chainsXI_getElem?]

/-- The auxiliary family's index telescope has exactly one domain. -/
theorem auxIds_length (W : Nat) (Idss : List (List AnnotTerm)) :
    (auxIds W Idss).length = 1 := rfl

/-- **The index tuple's member tag**: the numeral of the tagged
tuple's tag, `natIdx (sfst (sfst t))`. -/
noncomputable def caseTag (t : V) : Nat := natIdx (sfst (sfst t))

/-! ## The cased spelling -/

/-- The cased sum bodies: member `m`'s tagged sum over its own chain
suffix, one per member of the block. -/
def caseBodies (W w : Nat) (Idss : List (List AnnotTerm)) (k : Nat) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) :
    List AnnotTerm :=
  (List.range k).map fun m => sumBodyAV w (caseChains W Idss offs rss tlss Eiss' Fss Ess' m)

/-- **The cased functor's λ**: `λ X t`, the case split on the tuple's
member `fst (fst t)` selecting that member's own tagged sum. -/
def caseFunAVI (W w : Nat) (Idss : List (List AnnotTerm)) (k : Nat) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  .lam (Nat.max W (w + 1)) (famTyAV W w (auxIds W Idss))
    (.lam (w + 1) ((idxTyAV W (auxIds W Idss)).liftN 1 0)
      (caseAVAt w (caseBodies W w Idss k offs rss tlss Eiss' Fss Ess') 0 (.fst (.fst (.bvar 0)))))

/-- The cased family: `lfpFam.{W,w} I F` at the parameter frame. -/
def caseBodyAVI (W w : Nat) (Idss : List (List AnnotTerm)) (k : Nat) (offs : Nat → Nat)
    (rss : List (List Bool)) (tlss : List (List (List (Nat × Nat × AnnotTerm))))
    (Eiss' : List (List (List AnnotTerm))) (Fss Ess' : List (List AnnotTerm)) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .lfpFam [W, w])
    [idxTyAV W (auxIds W Idss), caseFunAVI W w Idss k offs rss tlss Eiss' Fss Ess']

/-! ## The cased semantic functor -/

/-- The cased functor's fibre at `(X, t)`: the tagged sum over the
tuple's OWN member's chain suffix. -/
noncomputable def caseStepI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) (X t : V) : V :=
  sumSet w (sumFibre w (cons t (cons X ρp))
    (caseChains W Idss offs rss tlss Eiss' Fss Ess' (caseTag t)))

/-- The cased functor on families (as a set-level function of `X`). -/
noncomputable def caseFamFI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) (X : V) : V :=
  lamR (w + 1) (idxSet W ρp (auxIds W Idss)) fun t =>
    caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t

/-- The cased functor as a set. -/
noncomputable def caseFunVI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : V :=
  lamR (Nat.max W (w + 1)) (lfpFamSpace V w (idxSet W ρp (auxIds W Idss)))
    fun X => caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' X

/-- The cased least pre-fixed family. -/
noncomputable def caseFamI (W w : Nat) (ρp : Nat → V) (Idss : List (List AnnotTerm))
    (offs : Nat → Nat) (rss : List (List Bool))
    (tlss : List (List (List (Nat × Nat × AnnotTerm)))) (Eiss' : List (List (List AnnotTerm)))
    (Fss Ess' : List (List AnnotTerm)) : V :=
  lfpFamSet w (idxSet W ρp (auxIds W Idss)) (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess')

section Facts

variable {W w k : Nat} {ρp : Nat → V} {Idss : List (List AnnotTerm)} {offs : Nat → Nat}
  {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss' : List (List (List AnnotTerm))} {Fss Ess' : List (List AnnotTerm)}

/-! ### The member tag -/

/-- The auxiliary index set is the Σ-set over the tag set. -/
theorem idxSet_auxIds_eq (hT : TagOk W ρp Idss) :
    idxSet W ρp (auxIds W Idss)
      = sigmaSet W (tagSet W ρp Idss) (fun _ => (unitSet : V)) := by
  show towerSet W (teleOfFields ρp (auxIds W Idss)) = _
  show sigmaSet W (interp V ρp (tagTyAV W Idss))
      (fun a => towerSet W (teleOfFields (cons a ρp) ([] : List AnnotTerm))) = _
  rw [(tagTyAV_facts hT).1]
  rfl

/-- Every tag fibre of the tag set lives in the block's universe. -/
theorem natFibre_uChains_univ (hT : TagOk W ρp Idss) {kk : V} (hk : kk ∈ˢ (omega : V)) :
    natFibre (sumFibre W ρp (uChains Idss)) kk ∈ˢ (univ W : V) := by
  obtain ⟨i, -, hfib⟩ := natFibre_of_mem (sumFibre W ρp (uChains Idss)) hk
  rw [hfib]
  unfold sumFibre
  cases h : (uChains Idss)[i]? with
  | none => exact empty_mem_univ W
  | some Fs =>
    exact towerSet_univ_teleOfFields ((hT.sumOk Fs (List.mem_of_getElem? h)).toBound hT.1)

/-- **The index tuple, decomposed**: it is the 1-tower of its member's
tagged index tuple, and `caseTag` reads that member back. -/
theorem caseTag_of_mem (hT : TagOk W ρp Idss) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    ∃ m is, m < Idss.length ∧ SpineFit ρp (Idss.getD m []) is ∧
      t = mkTower [inj m (mkTower (is ++ [pt]))] ∧ caseTag t = m := by
  have hx : t ∈ˢ towerSet W (teleOfFields ρp (auxIds W Idss)) := ht
  obtain ⟨hsp, heta⟩ := towerSet_elim_teleOfFields hT.1 hx
  rw [auxIds_length] at hsp heta
  have hpl : projList 1 t = [sfst t] := rfl
  rw [hpl] at hsp heta
  have htag : sfst t ∈ˢ tagSet W ρp Idss := by
    have h1 : sfst t ∈ˢ interp V ρp (tagTyAV W Idss) := hsp.1
    rwa [(tagTyAV_facts hT).1] at h1
  obtain ⟨m, a, ha, hinj⟩ := sumSet_elim hT.1 htag
  have hm : m < Idss.length := by
    rcases Nat.lt_or_ge m Idss.length with h | h
    · exact h
    · rw [sumFibre_of_ge (by rw [uChains, List.length_map]; exact h)] at ha
      exact absurd ha (not_mem_empty a)
  have hg : Idss[m]? = some (Idss.getD m []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    rfl
  rw [sumFibre_of_getElem? (by rw [uChains_getElem?, hg]; rfl)] at ha
  obtain ⟨hspI, -, -, hae⟩ := restricted_member_elim hT.1 ha
  have htg : caseTag t = m := by
    unfold caseTag
    rw [hinj, sfst_inj, natIdx_vnat]
  refine ⟨m, projList (Idss.getD m []).length a, hm, hspI, ?_, htg⟩
  rw [heta, hinj, ← hae]

/-- The spelled discriminant reads the tuple's outer tag. -/
theorem caseDisc_interp (ρp : Nat → V) (t X : V) :
    interp V (cons t (cons X ρp)) (.fst (.fst (.bvar 0))) = sfst (sfst t) := rfl

/-- **The discriminant's two facts** at an index tuple: it reads to
the member's numeral, and it is graded (the `.fst` clause twice — the
index set is a Σ-set over the tag set, the tag set a Σ-set over `ω`). -/
theorem caseDisc_facts (hT : TagOk W ρp Idss) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) (X : V) :
    interp V (cons t (cons X ρp)) (.fst (.fst (.bvar 0))) = vnat (caseTag t) ∧
      WellDenoted V (cons t (cons X ρp)) (.fst (.fst (.bvar 0))) := by
  obtain ⟨m, is, -, -, hte, htg⟩ := caseTag_of_mem hT ht
  have htag : sfst t ∈ˢ tagSet W ρp Idss := by
    have hx : t ∈ˢ towerSet W (teleOfFields ρp (auxIds W Idss)) := ht
    obtain ⟨hsp, -⟩ := towerSet_elim_teleOfFields hT.1 hx
    rw [auxIds_length] at hsp
    have hpl : projList 1 t = [sfst t] := rfl
    rw [hpl] at hsp
    have h1 : sfst t ∈ˢ interp V ρp (tagTyAV W Idss) := hsp.1
    rwa [(tagTyAV_facts hT).1] at h1
  have hmax : Nat.max W W = W := Nat.max_self W
  have hsf : sfst t = inj m (mkTower (is ++ [pt])) := by
    rw [hte]
    show sfst (spair (inj m (mkTower (is ++ [pt]))) pt) = _
    rw [sfst_spair]
  have hval : interp V (cons t (cons X ρp)) (.fst (.fst (.bvar 0))) = vnat (caseTag t) := by
    rw [caseDisc_interp, htg, hsf, sfst_inj]
  refine ⟨hval, ?_⟩
  have hidx : t ∈ˢ sigmaSet (Nat.max W W) (tagSet W ρp Idss) (fun _ => (unitSet : V)) := by
    rw [hmax, ← idxSet_auxIds_eq hT]
    exact ht
  have hinner : WellDenoted V (cons t (cons X ρp)) (.fst (.bvar 0)) := by
    rw [WellDenoted_fst]
    exact ⟨trivial, W, W, tagSet W ρp Idss, fun _ => (unitSet : V), hidx,
      (tagTyAV_facts hT).2.1, fun _ _ => unitSet_mem_univ W⟩
  have htag' : sfst t ∈ˢ sigmaSet (Nat.max W W) omega
      (natFibre (sumFibre W ρp (uChains Idss))) := by
    rw [hmax]
    exact htag
  rw [WellDenoted_fst]
  exact ⟨hinner, W, W, omega, natFibre (sumFibre W ρp (uChains Idss)), htag',
    omega_mem_univ_pos hT.1, fun _ hkk => natFibre_uChains_univ hT hkk⟩

/-! ### The cased functor's readings -/

/-- The suffix's chains are graded, from the global premise. -/
theorem caseChains_okB (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss))) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) (m : Nat) :
    SumFieldsOkB w (cons t (cons X ρp)) (caseChains W Idss offs rss tlss Eiss' Fss Ess' m) :=
  fun Fs hFs => hok X hX t ht Fs (List.mem_of_mem_drop hFs)

/-- **The cased fibre's formation.** -/
theorem caseStepI_univ (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss))) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB (caseChains_okB hok hX ht (caseTag t))

theorem caseFamFI_mem (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss))) :
    caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' X
      ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) :=
  lamR_mem fun _ ht => caseStepI_univ hok hX ht

theorem caseFamFI_app {X t : V} (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    SetTheory.app (caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' X) t
      = caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t :=
  app_lamR_pos (a := t) (Nat.succ_ne_zero w) ht

theorem caseFunVI_mem (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess'
      ∈ˢ lfpFamFunSpace V W w (idxSet W ρp (auxIds W Idss)) :=
  lamR_mem fun _ hX => caseFamFI_mem hok hX

theorem caseFunVI_app {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss))) :
    SetTheory.app (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess') X
      = caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' X :=
  app_lamR_pos (max_succ_ne_zero W w) hX

/-- A range-indexed selection reads the selected spelling. -/
theorem selFibre_range {σ : Nat → V} {i : Nat} (hi : i < k) (g : Nat → AnnotTerm) :
    selFibre σ ((List.range k).map g) i = interp V σ (g i) := by
  unfold selFibre
  rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- **The cased body at one tuple**: it reads to the cased fibre and
is graded. -/
theorem caseBody_facts (hT : TagOk W ρp Idss) (hk : Idss.length = k)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess')
    {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss))) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    interp V (cons t (cons X ρp))
        (caseAVAt w (caseBodies W w Idss k offs rss tlss Eiss' Fss Ess') 0
          (.fst (.fst (.bvar 0))))
      = caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t ∧
    WellDenoted V (cons t (cons X ρp))
      (caseAVAt w (caseBodies W w Idss k offs rss tlss Eiss' Fss Ess') 0
        (.fst (.fst (.bvar 0)))) := by
  obtain ⟨hdv, hdok⟩ := caseDisc_facts hT ht X
  obtain ⟨m, -, hmlt, -, -, htg⟩ := caseTag_of_mem hT ht
  have hmk : caseTag t < k := by rw [htg, ← hk]; exact hmlt
  have hbody : ∀ T ∈ caseBodies W w Idss k offs rss tlss Eiss' Fss Ess',
      interp V (cons t (cons X ρp)) T ∈ˢ (univ w : V) ∧
        WellDenoted V (cons t (cons X ρp)) T := by
    intro T hTm
    obtain ⟨m', -, rfl⟩ := List.mem_map.mp hTm
    refine ⟨?_, sumBodyAV_wellDenoted (caseChains_okB hok hX ht m')⟩
    rw [sumBodyAV_interp (caseChains_okB hok hX ht m')]
    exact sumSet_univ_of_okB (caseChains_okB hok hX ht m')
  have hfacts := caseAVAt_facts (w := w)
    (Ts := caseBodies W w Idss k offs rss tlss Eiss' Fss Ess') (d := 0)
    (k := (.fst (.fst (.bvar 0)) : AnnotTerm)) (σ := cons t (cons X ρp))
    (by rw [shiftE_zero_zero]; exact fun T hTm => (hbody T hTm).1)
    (by rw [shiftE_zero_zero]; exact fun T hTm => (hbody T hTm).2)
    hdok (by rw [hdv]; exact vnat_mem_omega (caseTag t))
  rw [shiftE_zero_zero] at hfacts
  refine ⟨?_, hfacts.2.2⟩
  rw [hfacts.2.1 (caseTag t) hdv, caseBodies, selFibre_range hmk,
    sumBodyAV_interp (caseChains_okB hok hX ht (caseTag t))]
  rfl

/-- The frame under the cased functor's two binders. -/
theorem caseIdxTy_lift1 (hT : TagOk W ρp Idss) (X : V) :
    interp V (cons X ρp) ((idxTyAV W (auxIds W Idss)).liftN 1 0)
        = idxSet W ρp (auxIds W Idss) ∧
      WellDenoted V (cons X ρp) ((idxTyAV W (auxIds W Idss)).liftN 1 0) :=
  idxTyAV_lift1 (auxIds_idxOk hT) X

/-- **The cased functor's λ**: its value and its grading. -/
theorem caseFunAVI_facts (hT : TagOk W ρp Idss) (hk : Idss.length = k)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    interp V ρp (caseFunAVI W w Idss k offs rss tlss Eiss' Fss Ess')
        = caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess' ∧
      WellDenoted V ρp (caseFunAVI W w Idss k offs rss tlss Eiss' Fss Ess') := by
  have hI : IdxOk W ρp (auxIds W Idss) := auxIds_idxOk hT
  obtain ⟨hfv, -, hfok⟩ := famTyAV_facts (w := w) hI
  refine ⟨?_, ?_⟩
  · unfold caseFunAVI caseFunVI
    rw [interp_lam, hfv]
    refine lamR_congr fun X hX => ?_
    unfold caseFamFI
    rw [interp_lam, (caseIdxTy_lift1 hT X).1]
    refine lamR_congr fun t ht => ?_
    exact (caseBody_facts hT hk hok hX ht).1
  · unfold caseFunAVI
    rw [WellDenoted_lam]
    refine ⟨hfok, fun X hX => ?_,
      fun _ => lfpFamSpace V w (idxSet W ρp (auxIds W Idss)), fun X hX => ?_,
      fun h => absurd h (max_succ_ne_zero W w)⟩
    · rw [hfv] at hX
      rw [WellDenoted_lam]
      refine ⟨(caseIdxTy_lift1 hT X).2, fun t ht => ?_, fun _ => (univ w : V), fun t ht => ?_,
        fun h => absurd h (Nat.succ_ne_zero w)⟩
      · rw [(caseIdxTy_lift1 hT X).1] at ht
        exact (caseBody_facts hT hk hok hX ht).2
      · rw [(caseIdxTy_lift1 hT X).1] at ht
        rw [(caseBody_facts hT hk hok hX ht).1]
        exact caseStepI_univ hok hX ht
    · rw [hfv] at hX
      rw [interp_lam, (caseIdxTy_lift1 hT X).1]
      refine lamR_mem fun t ht => ?_
      rw [(caseBody_facts hT hk hok hX ht).1]
      exact caseStepI_univ hok hX ht

/-- **The cased family**: its value, its membership, its grading. -/
theorem caseBodyAVI_facts (hT : TagOk W ρp Idss) (hk : Idss.length = k)
    (hok : FixChainsOkI W w ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    interp V ρp (caseBodyAVI W w Idss k offs rss tlss Eiss' Fss Ess')
        = caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess' ∧
      caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess'
        ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)) ∧
      WellDenoted V ρp (caseBodyAVI W w Idss k offs rss tlss Eiss' Fss Ess') := by
  have hI : IdxOk W ρp (auxIds W Idss) := auxIds_idxOk hT
  obtain ⟨hiv, hiu, hiok⟩ := idxTyAV_facts hI
  obtain ⟨hfv, hfok⟩ := caseFunAVI_facts hT hk hok
  have hc : interp V ρp (.const .lfpFam [W, w]) = lfpFamV V W w := rfl
  refine ⟨?_, lfpFamSet_mem_space V w _ _, ?_⟩
  · show SetTheory.app (SetTheory.app (interp V ρp (.const .lfpFam [W, w]))
      (interp V ρp (idxTyAV W (auxIds W Idss))))
        (interp V ρp (caseFunAVI W w Idss k offs rss tlss Eiss' Fss Ess')) = _
    rw [hc, hiv, hfv]
    exact lfpFamV_app V hiu (caseFunVI_mem hok)
  · show WellDenoted V ρp (.app (.app (.const .lfpFam [W, w]) _) _)
    rw [WellDenoted_app]
    refine ⟨?_, hfok, Nat.max W (w + 1), lfpFamFunSpace V W w (idxSet W ρp (auxIds W Idss)),
      fun _ => lfpFamSpace V w (idxSet W ρp (auxIds W Idss)), ?_, ?_,
      fun h => absurd h (max_succ_ne_zero W w)⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, hiok, Nat.max W (w + 1), univ W,
        fun I => piR (Nat.max W (w + 1)) (lfpFamFunSpace V W w I) fun _ => lfpFamSpace V w I,
        lfpFamV_mem V W w, by rw [hiv]; exact hiu, fun h => absurd h (max_succ_ne_zero W w)⟩
    · show SetTheory.app (interp V ρp (.const .lfpFam [W, w]))
        (interp V ρp (idxTyAV W (auxIds W Idss))) ∈ˢ _
      rw [hc, hiv]
      exact app_mem_piR_pos (max_succ_ne_zero W w) (lfpFamV_mem V W w) hiu
    · rw [hfv]; exact caseFunVI_mem hok

/-! ### Monotonicity -/

/-- **The cased functor is monotone** in the family: each suffix chain
`j` is the global chain `offs (caseTag t) + j`. -/
theorem caseStepI_mono (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess') {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)))
    (hXY : FamLe (idxSet W ρp (auxIds W Idss)) X Y) {t : V}
    (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t
      ⊆ˢ caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' Y t := by
  unfold caseStepI
  refine sumSet_mono fun j => ?_
  unfold sumFibre
  by_cases hj : offs (caseTag t) + j < Fss.length
  · rw [caseChains_getElem?, if_pos hj]
    show towerSet w (teleOfFields (cons t (cons X ρp))
        (chainXI W (auxIds W Idss) 1 (rss.getD (offs (caseTag t) + j) [])
          (tlss.getD (offs (caseTag t) + j) [])
          (Eiss'.getD (offs (caseTag t) + j) [])
          (Fss.getD (offs (caseTag t) + j) [])
          (Ess'.getD (offs (caseTag t) + j) [])))
      ⊆ˢ towerSet w (teleOfFields (cons t (cons Y ρp))
        (chainXI W (auxIds W Idss) 1 (rss.getD (offs (caseTag t) + j) [])
          (tlss.getD (offs (caseTag t) + j) [])
          (Eiss'.getD (offs (caseTag t) + j) [])
          (Fss.getD (offs (caseTag t) + j) [])
          (Ess'.getD (offs (caseTag t) + j) [])))
    refine towerSet_mono ?_
    unfold chainXI
    exact chainXIGo_tele_sub h.hI hX hXY (Fss.getD (offs (caseTag t) + j) []) 0 [] rfl
      (h.hfit X hX t ht (offs (caseTag t) + j) hj) (by simp)
  · rw [caseChains_getElem?, if_neg hj]
    exact Subset.refl _

theorem caseFamFI_le (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess') {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet W ρp (auxIds W Idss)))
    (hXY : FamLe (idxSet W ρp (auxIds W Idss)) X Y) :
    FamLe (idxSet W ρp (auxIds W Idss))
      (caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' X)
      (caseFamFI W w ρp Idss offs rss tlss Eiss' Fss Ess' Y) := by
  intro t ht
  rw [caseFamFI_app ht, caseFamFI_app ht]
  exact caseStepI_mono h hX hXY ht

theorem caseFunVI_mono (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess') :
    MonoFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess') := by
  intro X Y hX hY hXY
  rw [← lfpFamSpace_eq] at hX hY
  rw [caseFunVI_app hX, caseFunVI_app hY]
  exact caseFamFI_le h hX hXY

theorem caseFunVI_maps (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess') :
    MapsFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess') := by
  intro X hX
  rw [← lfpFamSpace_eq] at hX ⊢
  rw [caseFunVI_app hX]
  exact caseFamFI_mem h.hok hX

/-! ### The stage's introduction and elimination -/

/-- **Stage introduction** (graph regime): a fitting, equation-
satisfying tuple of member-local chain `j` injects into the cased
fibre at its OWN tag `j`. -/
theorem caseStepI_intro (hw : w ≠ 0) {X t : V} {j : Nat} {fs : List V}
    (hJ : offs (caseTag t) + j < Fss.length)
    (hsp : SpineFit (cons t (cons X ρp))
      (chainXIGo W (auxIds W Idss) (rss.getD (offs (caseTag t) + j) [])
        (tlss.getD (offs (caseTag t) + j) [])
        (Eiss'.getD (offs (caseTag t) + j) [])
        (Fss.getD (offs (caseTag t) + j) []) 0) fs)
    (heq : EqAll (consList fs (cons t (cons X ρp)))
      (eqsXI 1 (Fss.getD (offs (caseTag t) + j) []).length
        (Ess'.getD (offs (caseTag t) + j) []))) :
    inj j (mkTower (fs ++ [pt]))
      ∈ˢ caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t := by
  unfold caseStepI
  refine inj_mem hw ?_
  rw [sumFibre_of_getElem? (by rw [caseChains_getElem?, if_pos hJ])]
  refine mkTower_mem_teleOfFields hw ?_
  unfold chainXI
  exact spineFit_append_idxEq.mpr ⟨fs, rfl, hsp, heq⟩

/-- **Stage elimination** (graph regime): a member of the cased fibre
is the injection, at a MEMBER-LOCAL tag `j`, of a point-terminated
tuple fitting the global chain `offs (caseTag t) + j`. -/
theorem caseStepI_elim (hw : w ≠ 0) {X t x : V}
    (hx : x ∈ˢ caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess' X t) :
    ∃ j fs, x = inj j (mkTower (fs ++ [pt])) ∧
      offs (caseTag t) + j < Fss.length ∧
      fs.length = (Fss.getD (offs (caseTag t) + j) []).length ∧
      SpineFit (cons t (cons X ρp))
        (chainXIGo W (auxIds W Idss) (rss.getD (offs (caseTag t) + j) [])
          (tlss.getD (offs (caseTag t) + j) [])
          (Eiss'.getD (offs (caseTag t) + j) [])
          (Fss.getD (offs (caseTag t) + j) []) 0) fs ∧
      EqAll (consList fs (cons t (cons X ρp)))
        (eqsXI 1 (Fss.getD (offs (caseTag t) + j) []).length
          (Ess'.getD (offs (caseTag t) + j) [])) := by
  unfold caseStepI at hx
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw hx
  unfold sumFibre at ha
  by_cases hj : offs (caseTag t) + j < Fss.length
  · rw [caseChains_getElem?, if_pos hj] at ha
    obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
    unfold chainXI at hfit heta
    obtain ⟨fs, hfs, hsp, hall⟩ := spineFit_append_idxEq.mp hfit
    have hlen : fs.length = (Fss.getD (offs (caseTag t) + j) []).length := by
      have hl := hsp.length_eq
      rwa [chainXIGo_length] at hl
    refine ⟨j, fs, ?_, hj, hlen, hsp, hall⟩
    rw [heta, hfs]
  · rw [caseChains_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-- **Stage elimination** (squash regime). -/
theorem caseStepI_zero_elim {X t x : V}
    (hx : x ∈ˢ caseStepI W 0 ρp Idss offs rss tlss Eiss' Fss Ess' X t) :
    x = pt ∧ ∃ j fs, offs (caseTag t) + j < Fss.length ∧
      fs.length = (Fss.getD (offs (caseTag t) + j) []).length ∧
      SpineFit (cons t (cons X ρp))
        (chainXIGo W (auxIds W Idss) (rss.getD (offs (caseTag t) + j) [])
          (tlss.getD (offs (caseTag t) + j) [])
          (Eiss'.getD (offs (caseTag t) + j) [])
          (Fss.getD (offs (caseTag t) + j) []) 0) fs ∧
      EqAll (consList fs (cons t (cons X ρp)))
        (eqsXI 1 (Fss.getD (offs (caseTag t) + j) []).length
          (Ess'.getD (offs (caseTag t) + j) [])) := by
  unfold caseStepI at hx
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
  refine ⟨rfl, ?_⟩
  unfold sumFibre at ha
  by_cases hj : offs (caseTag t) + j < Fss.length
  · rw [caseChains_getElem?, if_pos hj] at ha
    obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
    have hfit' := fitsS_teleOfFields.mp hfit
    unfold chainXI at hfit'
    obtain ⟨fs, -, hsp, hall⟩ := spineFit_append_idxEq.mp hfit'
    have hlen : fs.length = (Fss.getD (offs (caseTag t) + j) []).length := by
      have hl := hsp.length_eq
      rwa [chainXIGo_length] at hl
    exact ⟨j, fs, hj, hlen, hsp, hall⟩
  · rw [caseChains_getElem?, if_neg hj] at ha
    exact absurd ha (not_mem_empty _)

/-! ### The fixed point -/

/-- **The fixed-point equation**, fibrewise, with the closed family as
an explicit hypothesis (it is not derived here). -/
theorem caseFamI_app_eq (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess')
    (hcl : ∃ L, IsClosedFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess') L)
    {t : V} (ht : t ∈ˢ idxSet W ρp (auxIds W Idss)) :
    caseStepI W w ρp Idss offs rss tlss Eiss' Fss Ess'
        (caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess') t
      = SetTheory.app (caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess') t := by
  have heq := app_lfpFamSet_eq hcl (caseFunVI_mono h) (caseFunVI_maps h) ht
  unfold caseFamI at heq ⊢
  rwa [caseFunVI_app (lfpFamSet_mem_space V w _ _), caseFamFI_app ht] at heq

/-! ### The tagged tuple's tag, the chain suffixes, and the sum reading -/

/-- **The tagged tuple's member tag**: the 1-tower over member `m`'s
tagged index tuple is tagged `m` (the graph regime — `W ≠ 0`). -/
theorem caseTag_tupW (hW : W ≠ 0) (m : Nat) (x : V) :
    caseTag (tupW W [inj m x]) = m := by
  unfold caseTag
  rw [tupW_pos hW]
  show natIdx (sfst (sfst (spair (inj m x) pt))) = m
  rw [sfst_spair, sfst_inj, natIdx_vnat]

/-- The restricted chains of a suffix are the suffix of the restricted
chains: entry `j` of the dropped lists is entry `o + j` of the whole. -/
theorem rChains_drop_getElem? (d n o j : Nat) (Fss₀ Ess₀ : List (List AnnotTerm)) :
    (rChains d n (Fss₀.drop o) (Ess₀.drop o))[j]? = (rChains d n Fss₀ Ess₀)[o + j]? := by
  rw [rChains_getElem?, rChains_getElem?, List.getElem?_drop, List.getElem?_drop]

/-- **The top family `t ↦ {pt}` is closed** at a `Prop`-valued block
(every fibre at `w = 0` is a subset of `{pt}`) — the cased twin of
`fixFunVI_closed_zero`. -/
theorem caseFunVI_closed_zero
    (hok : FixChainsOkI W 0 ρp (auxIds W Idss) 1 rss tlss Eiss' Fss Ess') :
    ∃ L, IsClosedFam 0 (idxSet W ρp (auxIds W Idss))
      (caseFunVI W 0 ρp Idss offs rss tlss Eiss' Fss Ess') L := by
  have htop : graph (fun _ => unitSet) (idxSet W ρp (auxIds W Idss))
      ∈ˢ lfpFamSpace V 0 (idxSet W ρp (auxIds W Idss)) := by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun _ _ => by rw [univ_zero]; exact mem_univZero.mpr (Subset.refl _)
  refine ⟨graph (fun _ => unitSet) (idxSet W ρp (auxIds W Idss)),
    by rw [← lfpFamSpace_eq]; exact htop, ?_⟩
  rw [caseFunVI_app htop]
  intro t ht x hx
  rw [caseFamFI_app ht] at hx
  rw [app_graph ht]
  have hu := caseStepI_univ (offs := offs) hok htop ht
  rw [univ_zero] at hu
  exact mem_univZero.mp hu x hx

/-- **The carrier's fibre at a member's tagged index tuple** is the
indexed sum route's restricted tagged union over that MEMBER's own
chain suffix — the cased twin of `fixFamI_app_eq_sum`, with the
element tags shifted down by `offs m`. -/
theorem caseFamI_app_eq_sum (hW : W ≠ 0)
    (h : XChainsOk W w ρp (auxIds W Idss) rss tlss Eiss' Fss Ess')
    (hcl : ∃ L, IsClosedFam w (idxSet W ρp (auxIds W Idss))
      (caseFunVI W w ρp Idss offs rss tlss Eiss' Fss Ess') L)
    {Fss' : List (List AnnotTerm)}
    (hreal : ChainsRealI (caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess') W w ρp
      (auxIds W Idss) rss tlss Eiss' Fss Fss' Ess')
    {m : Nat} {x : V} (hsp : SpineFit ρp (auxIds W Idss) [inj m x]) :
    SetTheory.app (caseFamI W w ρp Idss offs rss tlss Eiss' Fss Ess') (tupW W [inj m x])
      = sumSet w (sumFibre w (consList [inj m x] ρp)
        (rChains 1 1 (Fss'.drop (offs m)) (Ess'.drop (offs m)))) := by
  rw [← caseFamI_app_eq h hcl (tupW_mem hsp)]
  unfold caseStepI
  rw [caseTag_tupW hW]
  refine sumSet_congr fun j => ?_
  obtain ⟨hl₀, hlE, hEs, hlen, hc⟩ := hreal
  unfold sumFibre
  by_cases hj : offs m + j < Fss'.length
  · have hjF : offs m + j < Fss.length := by omega
    have hjE : offs m + j < Ess'.length := by omega
    rw [caseChains_getElem?, if_pos hjF, rChains_drop_getElem?, rChains_getElem?,
      List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjE]
    show towerSet w (teleOfFields (cons (tupW W [inj m x]) (cons _ ρp))
        (chainXI W (auxIds W Idss) 1 (rss.getD (offs m + j) []) (tlss.getD (offs m + j) [])
          (Eiss'.getD (offs m + j) []) (Fss.getD (offs m + j) []) (Ess'.getD (offs m + j) [])))
      = towerSet w (teleOfFields (consList [inj m x] ρp)
        (rChain 1 1 Fss'[offs m + j] Ess'[offs m + j]))
    have hg1 : Fss'[offs m + j] = Fss'.getD (offs m + j) [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    have hg2 : Ess'[offs m + j] = Ess'.getD (offs m + j) [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjE, Option.getD_some]
    rw [hg1, hg2]
    unfold chainXI rChain
    have heq := towerSet_chainXI_eq (w := w) (nF := (Fss.getD (offs m + j) []).length) h.hI hsp
      (hEs (offs m + j) hj) (Fss.getD (offs m + j) []) (Fss'.getD (offs m + j) []) 0 [] rfl
      (hc (offs m + j) hj)
      (by simp only [List.length_nil, Nat.zero_add]; exact (hlen (offs m + j) hj).symm)
    rw [auxIds_length] at heq
    rw [← hlen (offs m + j) hj]
    simpa only [consList_nil] using heq
  · have hjF : ¬ offs m + j < Fss.length := by omega
    rw [caseChains_getElem?, if_neg hjF, rChains_drop_getElem?, rChains_getElem?,
      List.getElem?_eq_none (by omega : Fss'.length ≤ offs m + j)]

open ConLeche.Term in
/-- **The cased family's leaf is closed**: bounded at the parameter
frame when the index telescope is and every global X-chain is bounded
under the functor's two binders — the cased twin of `fixBodyAVI_below`
(each member's sum runs over a SUFFIX of the global chains). -/
theorem caseBodyAVI_below {nP : Nat} (hIds : FieldsBelow nP (auxIds W Idss))
    (hchains : ∀ chain ∈ chainsXI W (auxIds W Idss) 1 rss tlss Eiss' Fss Ess',
      FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (caseBodyAVI W w Idss k offs rss tlss Eiss' Fss Ess').erase := by
  unfold caseBodyAVI
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
  rcases ha with rfl | rfl | hx
  · exact towerBodyAV_below hIds
  · unfold caseFunAVI famTyAV
    simp only [AnnotTerm.erase_lam, AnnotTerm.erase_pi, AnnotTerm.erase_sort, Term.bvarsBelow]
    refine ⟨⟨towerBodyAV_below hIds, trivial⟩, ?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 (towerBodyAV W (auxIds W Idss)).erase nP 0
        (towerBodyAV_below hIds)
    · have hsel := caseAVAt_below (w := w) (K := nP + 2)
        (Ts := caseBodies W w Idss k offs rss tlss Eiss' Fss Ess') (d := 0)
        (kx := (.fst (.fst (.bvar 0)) : AnnotTerm))
        (fun T hT => by
          obtain ⟨m, -, rfl⟩ := List.mem_map.mp hT
          exact sumBodyAV_below fun Fs hFs => hchains Fs (List.mem_of_mem_drop hFs))
        (show Term.bvarsBelow (nP + 2 + 0) (AnnotTerm.erase (.fst (.fst (.bvar 0))))
          from show (0 : Nat) < nP + 2 + 0 by omega)
      rwa [Nat.add_zero] at hsel
  · exact nomatch hx

end Facts

end ConLeche.Semantics
