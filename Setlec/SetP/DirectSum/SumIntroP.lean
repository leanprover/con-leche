import Setlec.SetP.Direct.DirectIntroP
import Setlec.Semantics.Tower.SumWire

/-!
# The sum leaves' bit validity and P packages (task #175 sum-types)

`AnnotValidV` for the three sum leaves.  The case split and the
injection carry no `.pi` node (hereditary plumbing); the squash
carrier's and the recursor's motive `.pi` nodes carry the genuine
clause — a zero codomain bit over a truth value — discharged from
`piR_zero_mem_univZero` (the squash carrier) and from the motive's
own applications being truth values at a zero elimination level (the
recursor, `RecHypS.hM0`).  The recursor's validity is one more
induction on the remaining constructor count (`caseRec_validV`), and
the tail walk `underTowerValid_of_recTailS` mirrors the membership
walk of `SumRec.lean`.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The case split -/

theorem numeralAV_validV (i : Nat) (σ : Nat → V) : AnnotValidV V σ (numeralAV i) := by
  induction i with
  | zero => trivial
  | succ i ih =>
    show AnnotValidV V σ (.app (.const .natSucc []) (numeralAV i))
    rw [AnnotValidV_app]
    exact ⟨trivial, ih⟩

theorem succsAV_validV : ∀ (j : Nat) {kx : AVExpr} {σ : Nat → V},
    AnnotValidV V σ kx → AnnotValidV V σ (succsAV j kx)
  | 0, _, _, h => h
  | j + 1, kx, σ, h => by
    show AnnotValidV V σ (.app (.const .natSucc []) (succsAV j kx))
    rw [AnnotValidV_app]
    exact ⟨trivial, succsAV_validV j h⟩

theorem natRecAV_validV {u : Nat} {M z s kx : AVExpr} {σ : Nat → V}
    (hM : AnnotValidV V σ M) (hz : AnnotValidV V σ z) (hs : AnnotValidV V σ s)
    (hk : AnnotValidV V σ kx) : AnnotValidV V σ (natRecAV u M z s kx) := by
  show AnnotValidV V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) kx)
  simp only [AnnotValidV_app, AnnotValidV_const]
  exact ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

theorem natSortMotiveAV_validV (w : Nat) (σ : Nat → V) :
    AnnotValidV V σ (natSortMotiveAV w) := by
  show AnnotValidV V σ (.lam (w + 1) natAV (.sort w))
  rw [AnnotValidV_lam]
  exact ⟨trivial, fun _ _ => trivial⟩

/-- The selector is bit-valid from the spellings' validity at the
retracted environment (hereditary; no `.pi` node). -/
theorem caseAVAt_validV {w : Nat} :
    ∀ {Ts : List AVExpr} {d : Nat} {kx : AVExpr} {σ : Nat → V},
      (∀ T ∈ Ts, AnnotValidV V (shiftE d 0 σ) T) → AnnotValidV V σ kx →
      AnnotValidV V σ (caseAVAt w Ts d kx)
  | [], _, _, _, _, _ => trivial
  | T :: Ts, d, kx, σ, hT, hk => by
    refine natRecAV_validV (natSortMotiveAV_validV w σ) ?_ ?_ hk
    · rw [AnnotValidV_liftN]; exact hT T List.mem_cons_self
    · rw [AnnotValidV_lam]
      refine ⟨trivial, fun b _ => ?_⟩
      rw [AnnotValidV_lam]
      refine ⟨trivial, fun a _ => ?_⟩
      refine caseAVAt_validV (Ts := Ts) (d := d + 2) (kx := .bvar 1) (σ := cons a (cons b σ))
        ?_ trivial
      rw [shiftE_step]
      exact fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')

/-! ## The carrier -/

/-- Per-constructor hereditary validity. -/
def SumFieldsValid (ρ : Nat → V) (Fss : List (List AVExpr)) : Prop :=
  ∀ Fs ∈ Fss, FieldsValid ρ Fs

theorem towers_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AVExpr)}
    (hv : SumFieldsValid ρ Fss) : ∀ T ∈ Fss.map (towerBodyAV w), AnnotValidV V ρ T := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_validV (hv Fs hFs)

theorem case_validV_at {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AVExpr)} (hv : SumFieldsValid ρp Fss) (k : V) :
    AnnotValidV V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)) := by
  refine caseAVAt_validV ?_ trivial
  rw [shiftE_succ_cons, hsh]
  exact towers_validV hv

theorem sumBodyAVPos_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AVExpr)}
    (hv : SumFieldsValid ρ Fss) : AnnotValidV V ρ (sumBodyAVPos w Fss) := by
  unfold sumBodyAVPos
  rw [AnnotValidV_app, AnnotValidV_app, AnnotValidV_lam]
  exact ⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at (shiftE_zero_zero ρ) hv k⟩

theorem sqSumBodyAV_validV {ρ : Nat → V} {Fss : List (List AVExpr)}
    (hv : SumFieldsValid ρ Fss) : AnnotValidV V ρ (sqSumBodyAV Fss) := by
  unfold sqSumBodyAV negAV
  rw [AnnotValidV_pi]
  refine ⟨?_, fun _ _ => by simp, fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩
  rw [AnnotValidV_pi]
  refine ⟨trivial, fun k _ => ?_, fun _ k _ => piR_zero_mem_univZero⟩
  rw [AnnotValidV_pi]
  exact ⟨case_validV_at (shiftE_zero_zero ρ) hv k, fun _ _ => by simp,
    fun _ _ _ => by rw [← univ_zero]; exact empty_mem_univ 0⟩

theorem sumBodyAV_validV {w : Nat} {ρ : Nat → V} {Fss : List (List AVExpr)}
    (hv : SumFieldsValid ρ Fss) : AnnotValidV V ρ (sumBodyAV w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_validV hv
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_validV hv

/-- The type-former leaf's P currency. -/
theorem directSumTyAV_okP {w : Nat} {Fss : List (List AVExpr)}
    {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hok : ParamsOkS w ρ Fss pps)
    (hval : UnderTowerValid ρ (sumBodyAV w Fss) pps) :
    AnnotOkP V ρ (directSumTyAV w pps Fss) :=
  ⟨directSumTyAV_ok2 hok, mkLamsC_validV hval⟩

/-! ## The constructor -/

theorem sumInjAtAV_validV {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List AVExpr)} (hv : SumFieldsValid ρp Fss) {tag payload : AVExpr}
    (ht : AnnotValidV V σ tag) (hp : AnnotValidV V σ payload) :
    AnnotValidV V σ (sumInjAtAV w Fss d tag payload) := by
  show AnnotValidV V σ (.app (.app (.app (.app (.const .psigmaMk [w, w]) natAV)
    (.lam (w + 1) natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))) tag) payload)
  simp only [AnnotValidV_app, AnnotValidV_const, AnnotValidV_lam]
  exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, fun k _ => case_validV_at hsh hv k⟩, ht⟩, hp⟩

/-- The constructor's body is bit-valid at a fitting field frame. -/
theorem sumInj_validV_at_fields {w j : Nat} {ρp : Nat → V} {Fs : List AVExpr}
    {Fss : List (List AVExpr)} {bs : List V}
    (hv : SumFieldsValid ρp Fss) (hvF : FieldsValid ρp Fs)
    (hb : w ≠ 0 → FieldsBound w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    AnnotValidV V (consList bs ρp)
      (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGo w Fs)) := by
  have hlen : bs.length = Fs.length := hsp.length_eq
  have hsh : shiftE Fs.length 0 (consList bs ρp) = ρp := by rw [← hlen]; exact shiftE_consList bs ρp
  exact sumInjAtAV_validV hsh hv (numeralAV_validV j _) (mkTowerGo_validV hvF hb hsp)

/-- The constructor leaf's P currency. -/
theorem directSumMkAV_okP {w j : Nat} {bodyC : AVExpr} {ρ : Nat → V}
    {Fss : List (List AVExpr)} {pds fds : List (Nat × Nat × AVExpr)}
    (hz : ∀ d ∈ pds ++ fds, (w = 0 ↔ d.2.1 = 0))
    (hpre : MkPreS w j ρ (fds.map (·.2.2)) Fss bodyC pds)
    (hval : UnderTowerValid ρ
      (sumInjAtAV w Fss (fds.map (·.2.2)).length (numeralAV j) (mkTowerGo w (fds.map (·.2.2))))
      (pds ++ fds)) :
    AnnotOkP V ρ (directSumMkAV w j (pds ++ fds) (fds.map (·.2.2)) Fss) :=
  ⟨directSumMkAV_ok2 hz hpre, mkLamsC_validV hval⟩

/-! ## The recursor -/

theorem major_proj_validV (i : Nat) (σ : Nat → V) : AnnotValidV V σ (.proj i (.bvar 0)) := by
  rw [AnnotValidV_proj]; trivial

/-- The stage motive body is bit-valid at a tag in `ω`: its `.pi`
node's zero clause is the motive's application being a truth value. -/
theorem motiveBody_validV {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hfr : RecFrameS n D ρp M ms σ) (hyp : RecHypS ℓ w ρp Fss M ms)
    (hv : SumFieldsValid ρp Fss) (j : Nat) {k : V} (hk : k ∈ˢ (omega : V)) :
    AnnotValidV V (cons k σ) (caseMotiveBodyAV ℓ w Fss D j) := by
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
  obtain ⟨hread, -⟩ := motiveBody_facts hfr hyp j hk
  have hsh1 : shiftE (D + 1) 0 (cons (vnat i) σ) = ρp := hfr.sh1 _
  show AnnotValidV V (cons (vnat i) σ) (.pi w ℓ _ _)
  rw [AnnotValidV_pi]
  refine ⟨?_, fun y _ => ?_, fun h0 y hy => ?_⟩
  · refine caseAVAt_validV ?_ trivial
    rw [hsh1]
    exact fun T hT => towers_validV hv T (List.mem_of_mem_drop hT)
  · rw [AnnotValidV_app]
    refine ⟨trivial, sumInjAtAV_validV (by rw [shiftE_step, hfr.sh]) hv
      (succsAV_validV j trivial) trivial⟩
  · -- the zero clause: the motive's application is a truth value
    have hpi := hread
    rw [motSem_vnat] at hpi
    -- read the codomain off the product's fibre
    show interp2 V (cons y (cons (vnat i) σ))
      (.app (.bvar (D + 1)) (sumInjAtAV w Fss (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))
      ∈ˢ (univZero : V)
    rw [interp2_app, interp2_bvar, hfr.tag2]
    exact hyp.hM0 h0 _

theorem motive_validV {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hfr : RecFrameS n D ρp M ms σ) (hyp : RecHypS ℓ w ρp Fss M ms)
    (hv : SumFieldsValid ρp Fss) (j : Nat) :
    AnnotValidV V σ (caseMotiveAV ℓ w Fss D j) := by
  show AnnotValidV V σ (.lam (imaxN w ℓ + 1) natAV (caseMotiveBodyAV ℓ w Fss D j))
  rw [AnnotValidV_lam]
  exact ⟨trivial, fun k hk => motiveBody_validV hfr hyp hv j hk⟩

theorem base_validV {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hfr : RecFrameS n D ρp M ms σ) (hv : SumFieldsValid ρp Fss) (j : Nat) :
    AnnotValidV V σ (caseBaseAV ℓ w Fss D j) := by
  show AnnotValidV V σ (.lam ℓ _ _)
  rw [AnnotValidV_lam]
  refine ⟨?_, fun y _ => ?_⟩
  · rw [AnnotValidV_liftN, hfr.sh]
    by_cases hj : j < Fss.length
    · have hjF : Fss[j]? = some (Fss.getD j []) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      exact towerBodyAV_validV (hv _ (List.mem_of_getElem? hjF))
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact towerBodyAV_validV trivial
  · exact mkAppN_validV trivial fun a ha => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
      exact projAV_validV trivial

/-- The case recursor is bit-valid. -/
theorem caseRec_validV {ℓ w n : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hyp : RecHypS ℓ w ρp Fss M ms) (hv : SumFieldsValid ρp Fss) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {kx : AVExpr},
      RecFrameS n D ρp M ms σ → AnnotValidV V σ kx →
      AnnotValidV V σ (caseRecAV ℓ w Fss r D j kx)
  | 0, _, _, σ, _, _, _ => by
    show AnnotValidV V σ (.lam ℓ (.const .empty [w]) .prf)
    rw [AnnotValidV_lam]
    exact ⟨trivial, fun _ _ => trivial⟩
  | r + 1, D, j, σ, kx, hfr, hk => by
    refine natRecAV_validV (motive_validV hfr hyp hv j) (base_validV hfr hv j) ?_ hk
    rw [AnnotValidV_lam]
    refine ⟨trivial, fun b hb => ?_⟩
    rw [AnnotValidV_lam]
    refine ⟨motiveBody_validV hfr hyp hv j hb, fun a _ => ?_⟩
    exact caseRec_validV hyp hv r (hfr.step a b) trivial

theorem sumRecBody_validV {ℓ w : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hfr : RecFrameS Fss.length (Fss.length + 2) ρp M ms σ)
    (hyp : RecHypS ℓ w ρp Fss M ms) (hv : SumFieldsValid ρp Fss) :
    AnnotValidV V σ (sumRecBodyAV ℓ w Fss) := by
  show AnnotValidV V σ (.app _ _)
  rw [AnnotValidV_app]
  exact ⟨caseRec_validV hyp hv Fss.length hfr (major_proj_validV 0 σ), major_proj_validV 1 σ⟩

/-- The validity walk down the minor chain (the twin of
`underTowerOk_of_recTail`). -/
theorem underTowerValid_of_recTailS {ℓ w : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {dt : Nat × Nat × AVExpr} (hok : SumFieldsOkB w ρp Fss) (hv : SumFieldsValid ρp Fss)
    (hwl : w = 0 → Fss.length = 0 ∨ ℓ = 0)
    (hM : M ∈ˢ piR (ℓ + 1) (sumSet w (sumFibre w ρp Fss)) fun _ => (univ ℓ : V)) :
    ∀ {dms : List (Nat × Nat × AVExpr)} {j : Nat} {σ : Nat → V},
      j + dms.length = Fss.length → TailFrame ρp M j σ →
      (∀ j', j' < j → σ (j - 1 - j') ∈ˢ minorSpC ℓ M (ctorVal w j') (Fss.getD j' []) ρp []) →
      RecTailS ℓ w ρp Fss M dt dms j σ →
      (∀ d ∈ dms, ∀ σ' : Nat → V, AnnotValidV V σ' d.2.2) →
      (∀ σ' : Nat → V, AnnotValidV V σ' dt.2.2) →
      UnderTowerValid σ (sumRecBodyAV ℓ w Fss) (dms ++ [dt])
  | [], j, σ, hj, hfr, hms, htail, _, hvt => by
    simp only [List.length_nil, Nat.add_zero] at hj
    subst hj
    refine ⟨hvt σ, fun t ht => ?_⟩
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
    exact sumRecBody_validV hfrS hyp hv
  | d :: dms, j, σ, hj, hfr, hms, htail, hvd, hvt => by
    refine ⟨hvd d List.mem_cons_self σ, fun m hm => ?_⟩
    refine underTowerValid_of_recTailS hok hv hwl hM (dms := dms) (j := j + 1) (σ := cons m σ)
      (by simp only [List.length_cons] at hj; omega) (hfr.push m) ?_ (htail.2.2 m hm)
      (fun d' hd' => hvd d' (List.mem_cons_of_mem _ hd')) hvt
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

/-- The recursor leaf's validity premise from `RecPreS` plus the
entries' validity (every entry is valid at every environment: the
readings of stored types, `AnnotOkP`). -/
theorem underTowerValid_of_recPreS {ℓ w : Nat} {Fss : List (List AVExpr)}
    {dM : Nat × Nat × AVExpr} {dms : List (Nat × Nat × AVExpr)} {dt : Nat × Nat × AVExpr}
    (hvFss : ∀ ρ : Nat → V, SumFieldsOkB w ρ Fss → SumFieldsValid ρ Fss)
    (hvd : ∀ d ∈ dms, ∀ σ' : Nat → V, AnnotValidV V σ' d.2.2)
    (hvt : ∀ σ' : Nat → V, AnnotValidV V σ' dt.2.2)
    (hvM : ∀ σ' : Nat → V, AnnotValidV V σ' dM.2.2) :
    ∀ {pds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      RecPreS ℓ w ρ Fss dM dms dt pds →
      (∀ d ∈ pds, ∀ σ' : Nat → V, AnnotValidV V σ' d.2.2) →
      UnderTowerValid ρ (sumRecBodyAV ℓ w Fss) (pds ++ [dM] ++ dms ++ [dt])
  | d :: pds, ρ, h, hvp =>
    ⟨hvp d List.mem_cons_self ρ, fun a ha =>
      underTowerValid_of_recPreS hvFss hvd hvt hvM (h.2 a ha)
        (fun d' hd' => hvp d' (List.mem_cons_of_mem _ hd'))⟩
  | [], ρp, h, _ => by
    refine ⟨hvM ρp, fun M hM => ?_⟩
    rw [h.eqM] at hM
    have hfr : TailFrame ρp M 0 (cons M ρp) :=
      { sh := by rw [show (0 : Nat) + 1 = 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
        hM := rfl }
    have := underTowerValid_of_recTailS h.hok (hvFss ρp h.hok) h.hwl hM (dms := dms) (j := 0)
      (σ := cons M ρp) (by rw [h.hlen, Nat.zero_add]) hfr
      (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) (h.tail M (h.eqM ▸ hM)) hvd hvt
    simpa using this

/-- The recursor leaf's P currency. -/
theorem directSumRecAV_okP {ℓ w : Nat} {Fss : List (List AVExpr)} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM : Nat × Nat × AVExpr} {dms : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPreS ℓ w ρ Fss dM dms dt pds)
    (hval : UnderTowerValid ρ (sumRecBodyAV ℓ w Fss) (pds ++ [dM] ++ dms ++ [dt])) :
    AnnotOkP V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss) :=
  ⟨directSumRecAV_ok2 hz hpre, mkLamsC_validV hval⟩

end Setlec.SetP
