import Setlec.Semantics.Tower.SumRecCase

/-!
# The sum recursor leaf (task #175 sum-types, stage S4b)

`directSumRecAV ℓ w rds Fss = mkLamsC ℓ rds (sumRecBodyAV ℓ w Fss)` —
the constant-bit λ-tower (bit `ℓ`) over the recursor type reading's
binder data (parameters, motive, one minor per constructor, major),
whose body is the case recursor (`caseRecAV`, stage `0`, depth
`n + 2`) on the major's tag applied to the major's payload:

    sumRecBodyAV = (caseRec 0 (t.0)) (t.1)        t = bvar 0

`sumRecBody_facts` gives the body's grading and its membership in
`M t` at every carrier member (the graph regime through the case
recursor's stage-`0` motive, the squash regime through the minors'
inhabitation), and `sumRecBody_iota` the iota: at `t = inj j
(mkTower f⃗)` the body is minor `j` folded along `f⃗`.  The leaf's ONE
hereditary premise is `RecPreS` — the parameter walk ending in
`RecBaseS`: the chains graded, the motive entry the product over the
carrier into `Sort ℓ`, the minor entries the minor spaces
(`RecTailS`, a chain walk), the major entry the carrier — and
`underTowerOk_of_recPreS` turns it into the tower's premise.
-/

namespace Setlec.Semantics
open Setlec.SetModel

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The recursor body at depth `n + 2`. -/
def sumRecBodyAV (ℓ w : Nat) (Fss : List (List AVExpr)) : AVExpr :=
  .app (caseRecAV ℓ w Fss Fss.length (Fss.length + 2) 0 (.proj 0 (.bvar 0)))
    (.proj 1 (.bvar 0))

/-- The recursor leaf. -/
def directSumRecAV (ℓ w : Nat) (rds : List (Nat × Nat × AVExpr)) (Fss : List (List AVExpr)) :
    AVExpr :=
  mkLamsC ℓ rds (sumRecBodyAV ℓ w Fss)

/-! ## The major's projections -/

/-- The major's tag and payload nodes are graded: in the graph regime
through the carrier's own `sigmaSet`, at squash through the trivial
pair type (the major is the point). -/
theorem major_proj_ok2 {w : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)}
    (hok : SumFieldsOkB w ρp Fss) (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρp Fss)) {i : Nat}
    (hi : i < 2) : AnnotOk2 V σ (.proj i (.bvar 0)) := by
  rw [AnnotOk2_proj]
  refine ⟨trivial, hi, ?_⟩
  by_cases hw : w = 0
  · subst hw
    obtain ⟨hpt, -⟩ := sumSet_zero_elim ht
    refine ⟨0, 0, unitSet, fun _ => unitSet, ?_, unitSet_mem_univ 0, fun _ _ => unitSet_mem_univ 0⟩
    rw [interp2_bvar, hpt, show Nat.max 0 0 = 0 from rfl]
    exact pt_mem_sigma pt_mem_unitSet pt_mem_unitSet
  · refine ⟨w, w, omega, natFibre (sumFibre w ρp Fss), ?_, omega_mem_univ_pos hw, ?_⟩
    · rw [interp2_bvar, show Nat.max w w = w from Nat.max_self w]
      exact ht
    · intro k hk
      obtain ⟨i', rfl, hfib⟩ := natFibre_of_mem (sumFibre w ρp Fss) hk
      rw [hfib]
      unfold sumFibre
      cases hi' : Fss[i']? with
      | none => exact empty_mem_univ w
      | some Fs =>
        exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? hi')).toBound hw)

/-! ## The body -/

/-- **The recursor body's facts** at a carrier member: graded, and in
the motive at the major. -/
theorem sumRecBody_facts {ℓ w : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hfr : RecFrameS Fss.length (Fss.length + 2) ρp M ms σ)
    (hyp : RecHypS ℓ w ρp Fss M ms) (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρp Fss)) :
    AnnotOk2 V σ (sumRecBodyAV ℓ w Fss) ∧
    interp2 V σ (sumRecBodyAV ℓ w Fss) ∈ˢ SetTheory.app M (σ 0) := by
  have hcase := caseRec_facts (n := Fss.length) rfl hyp Fss.length (D := Fss.length + 2) (j := 0)
    (σ := σ) (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
  have hok0 := major_proj_ok2 hyp.hok ht (i := 0) (by omega)
  have hok1 := major_proj_ok2 hyp.hok ht (i := 1) (by omega)
  by_cases hw : w = 0
  · -- squash: no constructors (vacuous) or a zero elimination level
    subst hw
    obtain ⟨hpt, i, a, ha⟩ := sumSet_zero_elim ht
    rcases hyp.hwl rfl with hn | h0
    · -- no constructors: the fibres are empty
      exfalso
      rw [sumFibre_of_ge (by omega)] at ha
      exact not_mem_empty a ha
    · have hi : i < Fss.length := by
        rcases Nat.lt_or_ge i Fss.length with h | h
        · exact h
        · exfalso
          rw [sumFibre_of_ge h] at ha
          exact not_mem_empty a ha
      have hn : 0 < Fss.length := by omega
      obtain ⟨r, hr⟩ : ∃ r, Fss.length = r + 1 := ⟨Fss.length - 1, by omega⟩
      have hhead : interp2 V σ (caseRecAV ℓ 0 Fss Fss.length (Fss.length + 2) 0 (.proj 0 (.bvar 0)))
          = pt := by
        rw [hr]; exact caseRec_zero h0 Fss r _ 0 _ σ
      have hokcase := hcase.2 hok0 (fun hl => absurd h0 hl)
      refine ⟨?_, ?_⟩
      · exact (mkAppN_ok2_of_pt_head (args := [.proj 1 (.bvar 0)]) hokcase hhead
          (fun a' ha' => by rw [List.mem_singleton.mp ha']; exact hok1)).1
      · show SetTheory.app (interp2 V σ (caseRecAV ℓ 0 Fss Fss.length (Fss.length + 2) 0
          (.proj 0 (.bvar 0)))) (interp2 V σ (.proj 1 (.bvar 0))) ∈ˢ _
        rw [hhead, app_pt, hpt]
        -- the motive at the point is inhabited by the `i`-th minor's inhabitation
        have hiF : Fss[i]? = some (Fss.getD i []) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
        rw [sumFibre_of_getElem? hiF] at ha
        obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
        obtain ⟨v, hv⟩ := minorSpC_zero_inhab (h0 ▸ hyp.hms i hi) (fitsS_teleOfFields.mp hfit)
        have hv' : v = pt := eq_pt_of_mem_univZero (hyp.hM0 h0 _) hv
        subst hv'
        simpa [ctorVal] using hv
  · -- graph: the major is an injection
    obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht
    have htag : interp2 V σ (.proj 0 (.bvar 0)) = vnat i := by
      rw [interp2_proj, if_pos rfl, interp2_bvar, hta, sfst_inj]
    have hpay : interp2 V σ (.proj 1 (.bvar 0)) = a := by
      rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, hta, ssnd_inj]
    have hkω : interp2 V σ (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
      rw [htag]; exact vnat_mem_omega i
    obtain ⟨hmem, -⟩ := hcase.1 hkω
    rw [htag, motSem_vnat, Nat.zero_add] at hmem
    have hB0 : ℓ = 0 → ∀ y, y ∈ˢ sumFibre w ρp Fss i →
        SetTheory.app M (injW w i y) ∈ˢ (univZero : V) :=
      fun h0 y _ => hyp.hM0 h0 _
    refine ⟨?_, ?_⟩
    · show AnnotOk2 V σ (.app _ _)
      rw [AnnotOk2_app]
      refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, ℓ, sumFibre w ρp Fss i, _, hmem, ?_, hB0⟩
      rw [hpay]; exact ha
    · show SetTheory.app (interp2 V σ (caseRecAV ℓ w Fss Fss.length (Fss.length + 2) 0
        (.proj 0 (.bvar 0)))) (interp2 V σ (.proj 1 (.bvar 0))) ∈ˢ _
      rw [hpay]
      have := app_mem_piR hmem ha hB0
      rwa [injW_pos hw, ← hta] at this

theorem foldl_app_pt_sum : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt_sum ts

/-- **The body's iota**: at the injection of constructor `j`'s tupler
the body is minor `j` folded along the fields. -/
theorem sumRecBody_iota {ℓ w : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)}
    {M : V} {ms : Nat → V} (hfr : RecFrameS Fss.length (Fss.length + 2) ρp M ms σ)
    (hyp : RecHypS ℓ w ρp Fss M ms) {j : Nat} (hj : j < Fss.length) {bs : List V}
    (hlen : bs.length = (Fss.getD j []).length) (hmaj : σ 0 = inj j (mkTower bs))
    (hbs : mkTower bs ∈ˢ sumFibre w ρp Fss j) :
    interp2 V σ (sumRecBodyAV ℓ w Fss) = bs.foldl SetTheory.app (ms j) := by
  have hcase := caseRec_facts (n := Fss.length) rfl hyp Fss.length (D := Fss.length + 2) (j := 0)
    (σ := σ) (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
  have htag : interp2 V σ (.proj 0 (.bvar 0)) = vnat j := by
    rw [interp2_proj, if_pos rfl, interp2_bvar, hmaj, sfst_inj]
  have hpay : interp2 V σ (.proj 1 (.bvar 0)) = mkTower bs := by
    rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, hmaj, ssnd_inj]
  have hkω : interp2 V σ (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega j
  have hsel := (hcase.1 hkω).2 j htag hj
  rw [Nat.zero_add] at hsel
  show SetTheory.app (interp2 V σ (caseRecAV ℓ w Fss Fss.length (Fss.length + 2) 0
    (.proj 0 (.bvar 0)))) (interp2 V σ (.proj 1 (.bvar 0))) = _
  rw [hsel, hpay]
  unfold baseSem
  by_cases h0 : ℓ = 0
  · rw [h0, lamR_zero, app_pt, hyp.minor_pt h0 hj]
    exact (foldl_app_pt_sum bs).symm
  · rw [app_lamR_pos h0 hbs, map_range_projS_mkTower hlen]

/-! ## The hereditary premise -/

/-- The minor entries' chain, ending in the major entry: at the frame
under the motive and the earlier minors, the `j`-th minor entry is
graded and reads to minor `j`'s space; at the end the major entry is
graded and reads to the carrier. -/
def RecTailS (ℓ w : Nat) (ρp : Nat → V) (Fss : List (List AVExpr)) (M : V)
    (dt : Nat × Nat × AVExpr) : List (Nat × Nat × AVExpr) → Nat → (Nat → V) → Prop
  | [], _, σ => AnnotOk2 V σ dt.2.2 ∧ interp2 V σ dt.2.2 = sumSet w (sumFibre w ρp Fss)
  | d :: dms, j, σ => AnnotOk2 V σ d.2.2 ∧
      interp2 V σ d.2.2 = minorSpC ℓ M (ctorVal w j) (Fss.getD j []) ρp [] ∧
      ∀ m, m ∈ˢ interp2 V σ d.2.2 → RecTailS ℓ w ρp Fss M dt dms (j + 1) (cons m σ)

/-- The recursor's post-parameter phase facts. -/
structure RecBaseS (ℓ w : Nat) (ρp : Nat → V) (Fss : List (List AVExpr))
    (dM : Nat × Nat × AVExpr) (dms : List (Nat × Nat × AVExpr)) (dt : Nat × Nat × AVExpr) :
    Prop where
  hok : SumFieldsOkB w ρp Fss
  hwl : w = 0 → Fss.length = 0 ∨ ℓ = 0
  hlen : dms.length = Fss.length
  okM : AnnotOk2 V ρp dM.2.2
  eqM : interp2 V ρp dM.2.2 = piR (ℓ + 1) (sumSet w (sumFibre w ρp Fss)) fun _ => (univ ℓ : V)
  tail : ∀ M, M ∈ˢ interp2 V ρp dM.2.2 → RecTailS ℓ w ρp Fss M dt dms 0 (cons M ρp)

/-- `RecPreS`: the parameter walk ending in `RecBaseS`. -/
def RecPreS (ℓ w : Nat) (ρ : Nat → V) (Fss : List (List AVExpr))
    (dM : Nat × Nat × AVExpr) (dms : List (Nat × Nat × AVExpr)) (dt : Nat × Nat × AVExpr) :
    List (Nat × Nat × AVExpr) → Prop
  | [] => RecBaseS ℓ w ρ Fss dM dms dt
  | d :: pds => AnnotOk2 V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp2 V ρ d.2.2 → RecPreS ℓ w (cons a ρ) Fss dM dms dt pds

/-- The minor chain's frame: `j` minors consed over the motive over
the parameter frame. -/
structure TailFrame (ρp : Nat → V) (M : V) (j : Nat) (σ : Nat → V) : Prop where
  sh : shiftE (j + 1) 0 σ = ρp
  hM : σ j = M

omit [SetTheory V] in
theorem TailFrame.push {ρp : Nat → V} {M : V} {j : Nat} {σ : Nat → V}
    (h : TailFrame ρp M j σ) (m : V) : TailFrame ρp M (j + 1) (cons m σ) where
  sh := by rw [shiftE_succ_cons, h.sh]
  hM := by show cons m σ (j + 1) = M; rw [cons_succ, h.hM]

/-- The walk down the minor chain, ending at the major: the tower's
premise over the minor and major entries. -/
theorem underTowerOk_of_recTail {ℓ w : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {dt : Nat × Nat × AVExpr} (hok : SumFieldsOkB w ρp Fss)
    (hwl : w = 0 → Fss.length = 0 ∨ ℓ = 0)
    (hM : M ∈ˢ piR (ℓ + 1) (sumSet w (sumFibre w ρp Fss)) fun _ => (univ ℓ : V)) :
    ∀ {dms : List (Nat × Nat × AVExpr)} {j : Nat} {σ : Nat → V},
      j + dms.length = Fss.length → TailFrame ρp M j σ →
      (∀ j', j' < j → σ (j - 1 - j') ∈ˢ minorSpC ℓ M (ctorVal w j') (Fss.getD j' []) ρp []) →
      RecTailS ℓ w ρp Fss M dt dms j σ →
      UnderTowerOk ℓ σ (sumRecBodyAV ℓ w Fss) (.app (.bvar (Fss.length + 1)) (.bvar 0))
        (dms ++ [dt])
  | [], j, σ, hj, hfr, hms, htail => by
    simp only [List.length_nil, Nat.add_zero] at hj
    subst hj
    refine ⟨htail.1, fun t ht => ?_⟩
    rw [htail.2] at ht
    -- the body's frame
    have hfrS : RecFrameS Fss.length (Fss.length + 2) ρp M
        (fun j' => σ (Fss.length - 1 - j')) (cons t σ) :=
      { sh := by rw [shiftE_succ_cons, hfr.sh]
        hD := Nat.le_refl _
        hM := by
          show cons t σ (Fss.length + 2 - 1) = M
          rw [show Fss.length + 2 - 1 = Fss.length + 1 from rfl, cons_succ, hfr.hM]
        hm := by
          intro j' hj'
          show cons t σ (Fss.length + 2 - 2 - j') = σ (Fss.length - 1 - j')
          rw [show Fss.length + 2 - 2 - j' = (Fss.length - 1 - j') + 1 from by omega, cons_succ] }
    have hyp : RecHypS ℓ w ρp Fss M (fun j' => σ (Fss.length - 1 - j')) :=
      ⟨hok, hM, fun j' hj' => hms j' hj', hwl⟩
    have ht' : cons t σ 0 ∈ˢ sumSet w (sumFibre w ρp Fss) := ht
    have hfacts := sumRecBody_facts hfrS hyp ht'
    refine ⟨hfacts.1, ?_, ?_⟩
    · show interp2 V (cons t σ) (sumRecBodyAV ℓ w Fss)
        ∈ˢ SetTheory.app (cons t σ (Fss.length + 1)) (cons t σ 0)
      rw [cons_succ, hfr.hM]
      exact hfacts.2
    · intro h0
      show SetTheory.app (cons t σ (Fss.length + 1)) (cons t σ 0) ∈ˢ _
      rw [cons_succ, hfr.hM, cons_zero]
      exact hyp.hM0 h0 t
  | d :: dms, j, σ, hj, hfr, hms, htail => by
    refine ⟨htail.1, fun m hm => ?_⟩
    refine underTowerOk_of_recTail hok hwl hM (dms := dms) (j := j + 1) (σ := cons m σ)
      (by simp only [List.length_cons] at hj; omega) (hfr.push m) ?_ (htail.2.2 m hm)
    intro j' hj'
    rcases Nat.lt_or_ge j' j with hlt | hge
    · show cons m σ (j + 1 - 1 - j') ∈ˢ _
      rw [show j + 1 - 1 - j' = (j - 1 - j') + 1 from by omega, cons_succ]
      exact hms j' hlt
    · have hjj : j' = j := by omega
      rw [hjj]
      show cons m σ (j + 1 - 1 - j) ∈ˢ _
      rw [show j + 1 - 1 - j = 0 from by omega, cons_zero, ← htail.2.1]
      exact hm

/-- **The recursor leaf's `UnderTowerOk`** from `RecPreS`. -/
theorem underTowerOk_of_recPreS {ℓ w : Nat} {Fss : List (List AVExpr)}
    {dM : Nat × Nat × AVExpr} {dms : List (Nat × Nat × AVExpr)} {dt : Nat × Nat × AVExpr} :
    ∀ {pds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      RecPreS ℓ w ρ Fss dM dms dt pds →
      UnderTowerOk ℓ ρ (sumRecBodyAV ℓ w Fss) (.app (.bvar (Fss.length + 1)) (.bvar 0))
        (pds ++ [dM] ++ dms ++ [dt])
  | d :: pds, ρ, h =>
    ⟨h.1, fun a ha => underTowerOk_of_recPreS (h.2 a ha)⟩
  | [], ρp, h => by
    refine ⟨h.okM, fun M hM => ?_⟩
    rw [h.eqM] at hM
    have hfr : TailFrame ρp M 0 (cons M ρp) :=
      { sh := by rw [show (0 : Nat) + 1 = 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
        hM := rfl }
    have := underTowerOk_of_recTail h.hok h.hwl hM (dms := dms) (j := 0) (σ := cons M ρp)
      (by rw [h.hlen, Nat.zero_add]) hfr (fun j' hj' => absurd hj' (Nat.not_lt_zero _))
      (h.tail M (h.eqM ▸ hM))
    simpa using this

/-- **The recursor leaf inhabits its type's reading.** -/
theorem directSumRecAV_mem {ℓ w : Nat} {Fss : List (List AVExpr)} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM : Nat × Nat × AVExpr} {dms : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPreS ℓ w ρ Fss dM dms dt pds) :
    interp2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss)
      ∈ˢ interp2 V ρ (mkPisAV (pds ++ [dM] ++ dms ++ [dt])
          (.app (.bvar (Fss.length + 1)) (.bvar 0))) :=
  mkLamsC_mem hz (underTowerOk_of_recPreS hpre)

/-- **The recursor leaf is graded.** -/
theorem directSumRecAV_ok2 {ℓ w : Nat} {Fss : List (List AVExpr)} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM : Nat × Nat × AVExpr} {dms : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPreS ℓ w ρ Fss dM dms dt pds) :
    AnnotOk2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss) :=
  mkLamsC_ok2 hz (underTowerOk_of_recPreS hpre)

end Setlec.Semantics
