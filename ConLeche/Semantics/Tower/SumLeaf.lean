module

public import ConLeche.Semantics.Tower.SumCase

@[expose] public section

/-!
# The tagged sum carrier, spelled (task #175 sum-types, stage S2)

The carrier body of a direct sum: the `.psigma [w, w]` node over the
tag domain `Nat` whose fibre is the numeral case split
(`caseAVAt`) over the constructors' tuple-tower bodies
(`towerBodyAV w Fs_i`), reading to the tier's `sumSet w (sumFibre …)`
(`ConLeche/SetModel/TaggedSum.lean`).  At `w = 0` the `.psigma` spelling
cannot serve (its pinned valuation reads the tag domain in `univ 0`),
so — as the structure route's `sqBodyAV` — the squash carrier is spelt
classically, `¬ ∀ k : Nat, ¬ (case k)`, whose bit-`0` products truncate
whatever their domains are; both spellings read to the ONE semantic
carrier, and `sigmaSet`'s zero test makes the two regimes one
statement (`sumBodyAV_interp`).

The type-former leaf `sumTyAV` is the λ-tower over the parameter
domains with this body, exactly as `structTyAV`; its laws consume one
hereditary premise, `ParamsOkS` — `ParamsOkT` with the per-constructor
chain grading `SumFieldsOkB` at the base.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The semantic fibres -/

/-- The `i`-th constructor's tower at the parameter frame, `empty`
beyond the constructor count. -/
noncomputable def sumFibre (w : Nat) (ρ : Nat → V) (Fss : List (List AnnotTerm)) (i : Nat) : V :=
  match Fss[i]? with
  | some Fs => towerSet w (teleOfFields ρ Fs)
  | none => empty

theorem sumFibre_of_getElem? {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)} {i : Nat}
    {Fs : List AnnotTerm} (h : Fss[i]? = some Fs) :
    sumFibre w ρ Fss i = towerSet w (teleOfFields ρ Fs) := by
  unfold sumFibre; rw [h]

theorem sumFibre_of_ge {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)} {i : Nat}
    (h : Fss.length ≤ i) : sumFibre w ρ Fss i = empty := by
  unfold sumFibre; rw [List.getElem?_eq_none h]

/-- Per-constructor hereditary grading: every constructor's chain is
`FieldsOkB`. -/
def SumFieldsOkB (w : Nat) (ρ : Nat → V) (Fss : List (List AnnotTerm)) : Prop :=
  ∀ Fs ∈ Fss, FieldsOkB w ρ Fs

theorem SumFieldsOkB.bound {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (h : SumFieldsOkB w ρ Fss) : ∀ Fs ∈ Fss, w ≠ 0 → FieldsBound w ρ Fs :=
  fun Fs hFs hw => (h Fs hFs).toBound hw

/-- The selector over the tower bodies picks the semantic fibres. -/
theorem selFibre_towers {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hb : ∀ Fs ∈ Fss, w ≠ 0 → FieldsBound w ρ Fs) (i : Nat) :
    selFibre ρ (Fss.map (towerBodyAV w)) i = sumFibre w ρ Fss i := by
  unfold selFibre sumFibre
  rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : Fss[i]? with
  | none => rfl
  | some Fs =>
    simp only [Option.map_some, Option.getD_some, Function.comp_def]
    exact towerBodyAV_interp (hb Fs (List.mem_of_getElem? h))

/-- The tower bodies are bounded and graded from the chains'. -/
theorem towers_facts {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) :
    (∀ T ∈ Fss.map (towerBodyAV w), interp V ρ T ∈ˢ (univ w : V)) ∧
    (∀ T ∈ Fss.map (towerBodyAV w), WellDenoted V ρ T) := by
  constructor
  · intro T hT
    obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
    rw [towerBodyAV_interp (fun hw => (hok Fs hFs).toBound hw)]
    exact towerSet_univ_of_okB (fun hw => (hok Fs hFs).toBound hw)
  · intro T hT
    obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
    exact towerBodyAV_wellDenoted (hok Fs hFs)

/-- The fibre selector at ANY scrutinee: at a frame `d + 1` binders
below the parameter frame, a graded scrutinee in `ω` selects the fibre
function at its value (task #279 D-1: the mutual reduction's scrutinee
is the flat tag computed from the member and the local tag). -/
theorem case_sel {w : Nat} {ρp τ : Nat → V} {d : Nat} (hsh : shiftE (d + 1) 0 τ = ρp)
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρp Fss) {k' : AnnotTerm}
    (hokk : WellDenoted V τ k') (hk : interp V τ k' ∈ˢ (omega : V)) :
    interp V τ (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) k')
        = natFibre (sumFibre w ρp Fss) (interp V τ k') ∧
      interp V τ (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) k') ∈ˢ (univ w : V) ∧
      WellDenoted V τ (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) k') := by
  obtain ⟨hT, hokT⟩ := towers_facts hok
  have h := caseAVAt_facts (w := w) (Ts := Fss.map (towerBodyAV w)) (d := d + 1) (k := k')
    (σ := τ) (by rw [hsh]; exact hT) (by rw [hsh]; exact hokT) hokk hk
  rw [hsh] at h
  refine ⟨?_, h.1, h.2.2⟩
  obtain ⟨i, hi, hfib⟩ := natFibre_of_mem (sumFibre w ρp Fss) hk
  rw [hfib, h.2.1 i hi, selFibre_towers hok.bound]

/-- The case split at a tag frame `d + 1` binders below the parameter
frame reads to the fibre function. -/
theorem case_fibre_at {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρp Fss) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))
        = natFibre (sumFibre w ρp Fss) k ∧
      interp V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))
        ∈ˢ (univ w : V) ∧
      WellDenoted V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)) := by
  have hsh' : shiftE (d + 1) 0 (cons k σ) = ρp := by rw [shiftE_succ_cons, hsh]
  have h := case_sel hsh' hok (k' := .bvar 0) trivial (by rw [interp_bvar]; exact hk)
  rw [interp_bvar] at h
  exact h

/-- The case split at the tag frame reads to the fibre function. -/
theorem case_fibre {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0))
        = natFibre (sumFibre w ρ Fss) k ∧
      interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0))
        ∈ˢ (univ w : V) ∧
      WellDenoted V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)) :=
  case_fibre_at (d := 0) (shiftE_zero_zero ρ) hok hk

/-! ## The carrier body -/

/-- The body's fibre-selector scrutinee (task #279 D-1, DESIGN §M.60):
the flat position computed from the member of the index tuple one
binder out (`.bvar 1`, read by `.fst (.fst _)`) and the local tag
(`.bvar 0`); the local tag itself at the empty table. -/
def bodyScrutAV (tbl : List (List Nat)) (n : Nat) : AnnotTerm :=
  flatTagAV tbl n (.fst (.fst (.bvar 1))) (.bvar 0)

theorem vnat_natIdx_of_mem {x : V} (hx : x ∈ˢ (omega : V)) : vnat (natIdx x) = x := by
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hx
  rw [natIdx_vnat]

/-- The scrutinee's facts at the tag frame `cons k ρ`: it reads the
flat position `tagOf tbl n (ρ 0) (natIdx k)`, in `ω`, graded — the
tuple `ρ 0` a tag tuple when the table is nonempty. -/
theorem bodyScrutAV_facts {tbl : List (List Nat)} {n : Nat} {ρ : Nat → V}
    (hoff : tbl ≠ [] → TagTuple (ρ 0)) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k ρ) (bodyScrutAV tbl n) = vnat (tagOf tbl n (ρ 0) (natIdx k)) ∧
    interp V (cons k ρ) (bodyScrutAV tbl n) ∈ˢ (omega : V) ∧
    WellDenoted V (cons k ρ) (bodyScrutAV tbl n) := by
  cases htbl : tbl with
  | nil =>
    show interp V (cons k ρ) (.bvar 0) = vnat (natIdx k) ∧ interp V (cons k ρ) (.bvar 0) ∈ˢ _ ∧
      WellDenoted V (cons k ρ) (.bvar 0)
    rw [interp_bvar, cons_zero, vnat_natIdx_of_mem hk]
    exact ⟨rfl, hk, trivial⟩
  | cons r rs =>
    have htt : TagTuple (ρ 0) := hoff (by rw [htbl]; exact List.cons_ne_nil r rs)
    have hff := fst_fst_facts (σ := cons k ρ) (e := .bvar 1) trivial (by rw [interp_bvar]; exact htt)
    rw [interp_bvar] at hff
    show interp V (cons k ρ) (flatTagAV (r :: rs) n (.fst (.fst (.bvar 1))) (.bvar 0)) = _ ∧ _ ∧ _
    have h := flatTagAV_facts (tbl := r :: rs) (List.cons_ne_nil r rs) (dead := n)
      (mem := .fst (.fst (.bvar 1))) (k := .bvar 0) (σ := cons k ρ) (m := memTag (ρ 0))
      (i := natIdx k)
      (by
        rw [hff.1]
        show sfst (sfst (ρ 0)) = vnat (memTag (ρ 0))
        unfold memTag
        rw [vnat_natIdx_of_mem htt.2.2]) hff.2.2
      (by rw [interp_bvar, cons_zero, vnat_natIdx_of_mem hk]) trivial
    exact h

/-- The carrier body, graph regime. -/
def sumBodyAVPos (tbl : List (List Nat)) (w : Nat) (Fss : List (List AnnotTerm)) : AnnotTerm :=
  .app (.app (.const .psigma [w, w]) natAV)
    (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length)))

/-- The carrier body, squash regime: `¬ ∀ k : Nat, ¬ (case k)`. -/
def sqSumBodyAV (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) : AnnotTerm :=
  negAV (.pi 1 0 natAV (negAV (caseAVAt 0 (Fss.map (towerBodyAV 0)) 1 (bodyScrutAV tbl Fss.length))))

/-- The carrier body, both regimes.  The table `tbl` is the mutual
reduction's member-local tag table (DESIGN §M.60); `[]` (every other
route) is the flat body. -/
def sumBodyAV (tbl : List (List Nat)) (w : Nat) (Fss : List (List AnnotTerm)) : AnnotTerm :=
  if w = 0 then sqSumBodyAV tbl Fss else sumBodyAVPos tbl w Fss

theorem sumBodyAV_zero (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) :
    sumBodyAV tbl 0 Fss = sqSumBodyAV tbl Fss := if_pos rfl

theorem sumBodyAV_pos {w : Nat} (hw : w ≠ 0) (tbl : List (List Nat)) (Fss : List (List AnnotTerm)) :
    sumBodyAV tbl w Fss = sumBodyAVPos tbl w Fss := if_neg hw

/-- `ω` sits in every positive universe. -/
theorem omega_mem_univ_pos {w : Nat} (hw : w ≠ 0) : (omega : V) ∈ˢ univ w := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact omega_mem_univ_succ w'

/-- **The retagged fibre function**: the body's `jc`-th fibre is the
flat chain `tagOf tbl n t jc`'s at the tuple `t`. -/
noncomputable def sumFibreT (tbl : List (List Nat)) (w : Nat) (ρ : Nat → V)
    (Fss : List (List AnnotTerm)) (jc : Nat) : V :=
  sumFibre w ρ Fss (tagOf tbl Fss.length (ρ 0) jc)

@[simp] theorem sumFibreT_nil (w : Nat) (ρ : Nat → V) (Fss : List (List AnnotTerm)) :
    sumFibreT [] w ρ Fss = sumFibre w ρ Fss := by
  funext jc; rfl

/-- The body's fibre λ, at the tag frame: the case split reads the
retagged fibre function. -/
theorem body_case_facts {tbl : List (List Nat)} {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length))
        = natFibre (sumFibreT tbl w ρ Fss) k ∧
      interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length))
        ∈ˢ (univ w : V) ∧
      WellDenoted V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length)) := by
  obtain ⟨hsv, hsω, hsok⟩ := bodyScrutAV_facts (n := Fss.length) hoff hk
  have hsh : shiftE (0 + 1) 0 (cons k ρ) = ρ := by rw [shiftE_succ_cons, shiftE_zero_zero]
  have h := case_sel (d := 0) hsh hok hsok hsω
  refine ⟨?_, h.2.1, h.2.2⟩
  rw [h.1, hsv, natFibre_vnat]
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
  rw [natFibre_vnat]
  unfold sumFibreT
  rw [natIdx_vnat]

/-- The squash body reads to the squash carrier. -/
theorem sqSumBodyAV_interp {tbl : List (List Nat)} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB 0 ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    interp V ρ (sqSumBodyAV tbl Fss) = sumSet 0 (sumFibreT tbl 0 ρ Fss) := by
  unfold sqSumBodyAV sumSet
  rw [interp_negAV, sigmaSet_zero]
  refine truthVal_congr ?_
  rw [interp_pi, piR_zero, exists_mem_truthVal]
  have hin : ∀ k : V, k ∈ˢ (omega : V) →
      ((∃ y, y ∈ˢ interp V (cons k ρ)
          (negAV (caseAVAt 0 (Fss.map (towerBodyAV 0)) 1 (bodyScrutAV tbl Fss.length))))
        ↔ ¬ ∃ z, z ∈ˢ natFibre (sumFibreT tbl 0 ρ Fss) k) := by
    intro k hk
    rw [interp_negAV, (body_case_facts hok hoff hk).1, exists_mem_truthVal]
  constructor
  · intro h
    exact Classical.byContradiction fun hno =>
      h fun k hk => (hin k hk).mpr fun hz => hno ⟨k, hk, hz⟩
  · rintro ⟨k, hk, y, hy⟩ hall
    exact (hin k hk).mp (hall k hk) ⟨y, hy⟩

/-- The graph body reads to the graph carrier. -/
theorem sumBodyAVPos_interp {tbl : List (List Nat)} {w : Nat} (hw : w ≠ 0) {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    interp V ρ (sumBodyAVPos tbl w Fss) = sumSet w (sumFibreT tbl w ρ Fss) := by
  have hbv : bval V .psigma [w, w] = psigmaV V w w := rfl
  have hB : (lamR (w + 1) omega fun k =>
        interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length)))
      ∈ˢ psigmaFibreSpace V w omega :=
    lamR_mem fun k hk => (body_case_facts hok hoff hk).2.1
  show SetTheory.app (SetTheory.app (bval V .psigma [w, w]) omega)
      (lamR (w + 1) omega fun k =>
        interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (bodyScrutAV tbl Fss.length)))
    = sumSet w (sumFibreT tbl w ρ Fss)
  rw [hbv, psigmaV_app V (omega_mem_univ_pos hw) hB, show Nat.max w w = w from Nat.max_self w]
  unfold sumSet
  exact sigma_congr fun k hk => by
    rw [app_lamR_pos (Nat.succ_ne_zero w) hk, (body_case_facts hok hoff hk).1]

/-- **The carrier body reads to the tier's carrier**, both regimes. -/
theorem sumBodyAV_interp {tbl : List (List Nat)} {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    interp V ρ (sumBodyAV tbl w Fss) = sumSet w (sumFibreT tbl w ρ Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_interp hok hoff
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_interp hw hok hoff

/-- The retagged carrier's formation, both regimes. -/
theorem sumSetT_univ_of_okB {tbl : List (List Nat)} {w : Nat} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρ Fss) :
    sumSet w (sumFibreT tbl w ρ Fss) ∈ˢ (univ w : V) := by
  by_cases hw : w = 0
  · subst hw; rw [univ_zero]; exact sumSet_zero_mem_univZero _
  · refine sumSet_mem_univ hw fun i => ?_
    unfold sumFibreT sumFibre
    cases h : Fss[tagOf tbl Fss.length (ρ 0) i]? with
    | none => exact empty_mem_univ w
    | some Fs => exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? h)).toBound hw)

/-- The carrier's formation, both regimes (the flat instance). -/
theorem sumSet_univ_of_okB {w : Nat} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB w ρ Fss) :
    sumSet w (sumFibre w ρ Fss) ∈ˢ (univ w : V) := by
  have := sumSetT_univ_of_okB (tbl := []) hok
  rwa [sumFibreT_nil] at this

/-- The squash body is graded. -/
theorem sqSumBodyAV_wellDenoted {tbl : List (List Nat)} {ρ : Nat → V} {Fss : List (List AnnotTerm)}
    (hok : SumFieldsOkB 0 ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    WellDenoted V ρ (sqSumBodyAV tbl Fss) := by
  unfold sqSumBodyAV negAV
  rw [WellDenoted_pi]
  refine ⟨?_, fun _ _ => by simp⟩
  rw [WellDenoted_pi]
  refine ⟨trivial, fun k hk => ?_⟩
  rw [WellDenoted_pi]
  exact ⟨(body_case_facts hok hoff hk).2.2, fun _ _ => by simp⟩

/-- The graph body is graded: the two `.psigma` slots from
`psigmaV_ww_mem`, the fibre λ from the selector's facts. -/
theorem sumBodyAVPos_wellDenoted {tbl : List (List Nat)} {w : Nat} (hw : w ≠ 0) {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    WellDenoted V ρ (sumBodyAVPos tbl w Fss) := by
  have hbv : interp V ρ (.const .psigma [w, w]) = psigmaV V w w := rfl
  have hvac : ¬ w + 1 = 0 := Nat.succ_ne_zero w
  have hA : (omega : V) ∈ˢ univ w := omega_mem_univ_pos hw
  unfold sumBodyAVPos
  rw [WellDenoted_app]
  refine ⟨?_, ?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, trivial, w + 1, univ w,
      fun A => piR (w + 1) (psigmaFibreSpace V w A) fun _ => (univ w : V),
      hbv ▸ psigmaV_ww_mem w, hA, fun h => absurd h hvac⟩
  · rw [WellDenoted_lam]
    exact ⟨trivial, fun k hk => (body_case_facts hok hoff hk).2.2,
      fun _ => (univ w : V), fun k hk => (body_case_facts hok hoff hk).2.1, fun h => absurd h hvac⟩
  · refine ⟨w + 1, psigmaFibreSpace V w omega, fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h hvac⟩
    · show SetTheory.app (interp V ρ (.const .psigma [w, w])) omega ∈ˢ _
      rw [hbv]
      exact app_mem_piR_pos hvac (psigmaV_ww_mem w) hA
    · exact lamR_mem fun k hk => (body_case_facts hok hoff hk).2.1

/-- **The carrier body is graded**, both regimes. -/
theorem sumBodyAV_wellDenoted {tbl : List (List Nat)} {w : Nat} {ρ : Nat → V}
    {Fss : List (List AnnotTerm)} (hok : SumFieldsOkB w ρ Fss) (hoff : tbl ≠ [] → TagTuple (ρ 0)) :
    WellDenoted V ρ (sumBodyAV tbl w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_wellDenoted hok hoff
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_wellDenoted hw hok hoff

/-- The flat body's premise is vacuous. -/
theorem noOff (ρ : Nat → V) : ([] : List (List Nat)) ≠ [] → TagTuple (ρ 0) :=
  fun h => absurd rfl h

/-! ## The type-former leaf -/

/-- The type-former leaf of a direct sum: the λ-tower over the
parameter domains (bits `w + 1`) with the sum carrier body. -/
def sumTyAV (w : Nat) (pps : List (Nat × Nat × AnnotTerm)) (Fss : List (List AnnotTerm)) :
    AnnotTerm :=
  mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (sumBodyAV [] w Fss)

/-- `ParamsOkS`: the leaf's one hereditary premise — `ParamsOkT` with
the per-constructor chain grading at the base. -/
def ParamsOkS (w : Nat) (ρ : Nat → V) (Fss : List (List AnnotTerm)) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => SumFieldsOkB w ρ Fss
  | d :: pps => d.2.1 ≠ 0 ∧ WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → ParamsOkS w (cons a ρ) Fss pps

/-- **The leaf inhabits its type's reading.** -/
theorem sumTyAV_mem {w : Nat} {Fss : List (List AnnotTerm)} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkS w ρ Fss pps →
      interp V ρ (sumTyAV w pps Fss) ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], ρ, h => by
    show interp V ρ (sumBodyAV [] w Fss) ∈ˢ (univ w : V)
    rw [sumBodyAV_interp h (noOff ρ), sumFibreT_nil]
    exact sumSet_univ_of_okB h
  | d :: pps, ρ, h => by
    show (lamR (w + 1) (interp V ρ d.2.2)
        fun a => interp V (cons a ρ)
          (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (sumBodyAV [] w Fss)))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamR_mem_zero_agree (iff_of_false (Nat.succ_ne_zero w) h.1)
      (fun a ha => sumTyAV_mem (h.2.2 a ha))

/-- **The leaf is graded.** -/
theorem sumTyAV_wellDenoted {w : Nat} {Fss : List (List AnnotTerm)} :
    ∀ {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      ParamsOkS w ρ Fss pps → WellDenoted V ρ (sumTyAV w pps Fss)
  | [], ρ, h => sumBodyAV_wellDenoted h (noOff ρ)
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam (w + 1) d.2.2
      (mkLamsAV (pps.map fun d => (w + 1, d.2.2)) (sumBodyAV [] w Fss)))
    rw [WellDenoted_lam]
    exact ⟨h.2.1, fun a ha => sumTyAV_wellDenoted (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => sumTyAV_mem (h.2.2 a ha),
       fun h0 => absurd h0 (Nat.succ_ne_zero w)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter spine
the leaf computes the instantiated carrier. -/
theorem sumTyAV_fold {w : Nat} {Fss : List (List AnnotTerm)}
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ (pps.map (·.2.2)) as)
    (hok : SumFieldsOkB w (consList as ρ) Fss) :
    as.foldl SetTheory.app (interp V ρ (sumTyAV w pps Fss))
      = sumSet w (sumFibre w (consList as ρ) Fss) := by
  have hsp' : SpineFit ρ ((pps.map fun d => (w + 1, d.2.2)).map (·.2)) as := by
    rwa [List.map_map]
  rw [sumTyAV,
    mkLamsAV_fold (fun d hd => by
      obtain ⟨d', -, rfl⟩ := List.mem_map.mp hd
      exact Nat.succ_ne_zero w) hsp',
    sumBodyAV_interp hok (noOff _), sumFibreT_nil]

end ConLeche.Semantics
