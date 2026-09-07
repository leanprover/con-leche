import Lech.SetP.DirectSum.SumRecFramesP
import Lech.SetP.Direct.DirectRecLawCoreP

/-!
# The sum recursor's walks and rule law (task #175 sum-types, indexed)

From the frames' `RecBaseS`: the recursor leaf's hereditary premises
(`sumRecWalks` — `RecPreS` along the parameters, and the validity
walk along the whole frame, whose base needs the body's validity at a
full frame, read off the frame's spine by `sumRecSpine_facts`), the
leaf's P currency and membership (`sumRecLeafFacts`), and the rule
law at the readings (`sumRecLawCore`): the recursor leaf applied to a
spine ending in constructor `j`'s leaf at fitting arguments is the
rule's right-hand side at the parameters, motive, minors and fields —
both sides fold to minor `j` at the fields (the body's iota,
`sumRecBody_iota` in the graph regime; `sumRecBody_iota_sq` at a
squash instantiation with a nonzero elimination level, where the
elimination restriction leaves one constructor and the sources are
the fields); at a zero elimination level both sides are the point.
The index pin (`IotaIndexPinP`, the kernel's `iotaIndexOk`) supplies
the equation of the constructor's index values with the recursor
application's index arguments.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Kit -/

omit [SetTheory V] in
/-- Shifting past a consed spine recovers the frame. -/
theorem shiftE_consList_zero : ∀ (as : List V) (σ : Nat → V),
    shiftE as.length 0 (consList as σ) = σ := by
  intro as σ
  rw [shiftE_zero]
  funext i
  exact consList_apply_add as σ i

/-- A constant-bit tower at bit zero is the point. -/
theorem interp2_mkLamsC_zero {b : AVExpr} : ∀ {ds : List (Nat × Nat × AVExpr)} (ρ : Nat → V),
    ds ≠ [] → interp2 V ρ (mkLamsC 0 ds b) = (pt : V)
  | [], _, h => absurd rfl h
  | d :: ds, ρ, _ => by
    show interp2 V ρ (mkLamsAV ((0, d.2.2) :: ds.map fun d => (0, d.2.2)) b) = pt
    exact mkLamsAV_zero_head _ _ _ _

/-- A λ-tower whose head bit is zero is the point. -/
theorem interp2_mkLamsAV_zero_of_bits {b : AVExpr} :
    ∀ {lds : List (Nat × AVExpr)} (ρ : Nat → V), lds ≠ [] →
      (∀ d ∈ lds, d.1 = 0) → interp2 V ρ (mkLamsAV lds b) = (pt : V)
  | [], _, h, _ => absurd rfl h
  | (b₀, A) :: lds, ρ, _, hb => by
    have h0 : b₀ = 0 := hb (b₀, A) List.mem_cons_self
    subst h0
    exact mkLamsAV_zero_head _ _ _ _

/-- A fitting spine over a singleton chain. -/
theorem spineFit_singleton_inv {D : AVExpr} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ [D] as) : ∃ a, as = [a] ∧ a ∈ˢ interp2 V ρ D := by
  match as, h with
  | [], h => exact h.elim
  | [a], h => exact ⟨a, rfl, h.1⟩
  | _ :: _ :: _, h => exact h.2.elim

/-! ## The chains along a spine -/

/-- Along a spine fitting the index entries, the K-frame's facts. -/
theorem recIdxS_spine {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : List V → V} {srcs : List (List (Option Nat))} {dt : Nat × Nat × AVExpr} :
    ∀ {dis : List (Nat × Nat × AVExpr)} {σ : Nat → V} {is : List V},
      RecIdxS ℓ w Fss Ess Ids famAt srcs dt dis σ → SpineFit σ (dis.map (·.2.2)) is →
      AnnotOk2 V (consList is σ) dt.2.2 ∧
        interp2 V (consList is σ) dt.2.2
          = sumSet w (sumFibre w (consList is σ)
              (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) ∧
        RecHypS ℓ w (consList is σ) Fss Ess Ids famAt ∧
        SqHypS ℓ w (consList is σ) Fss Ess Ids srcs
  | [], _, [], h, _ => h
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | d :: dis, σ, i :: is, h, hsp => by
    obtain ⟨-, hrec⟩ := h
    obtain ⟨hi, hsp'⟩ := hsp
    rw [consList_cons]
    exact recIdxS_spine (hrec i hi) hsp'

/-- Along a spine fitting the minor entries, the index chain. -/
theorem recTailS_spine {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : List V → V} {srcs : List (List (Option Nat))} {dis : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr} :
    ∀ {dms : List (Nat × Nat × AVExpr)} {σ : Nat → V} {ms : List V},
      RecTailS ℓ w Fss Ess Ids famAt srcs dis dt dms σ → SpineFit σ (dms.map (·.2.2)) ms →
      RecIdxS ℓ w Fss Ess Ids famAt srcs dt dis (consList ms σ)
  | [], _, [], h, _ => h
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | d :: dms, σ, m :: ms, h, hsp => by
    obtain ⟨-, hrec⟩ := h
    obtain ⟨hm, hsp'⟩ := hsp
    rw [consList_cons]
    exact recTailS_spine (hrec m hm) hsp'

/-! ## A full frame's facts -/

/-- **A spine fitting the recursor's data** splits as parameters,
motive, minors, indices, major, and yields the recursor leaf's
semantic premises at the K-frame. -/
theorem sumRecSpine_facts {ℓ w nP n nIdx : Nat} {pds dms dis : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hlenI : dis.length = nIdx)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss Ess Ids (famAt ρp) srcs dM dms dis dt)
    {ρ : Nat → V} {vals : List V}
    (hsp : SpineFit ρ ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)) vals) :
    ∃ (bs₁ ms is : List V) (M t : V), vals = bs₁ ++ [M] ++ ms ++ is ++ [t] ∧
      bs₁.length = nP ∧ ms.length = n ∧ is.length = nIdx ∧
      Sat2 V ((pds.map (·.2.2)).reverse) (consList bs₁ ρ) ∧
      RecBaseS ℓ w (consList bs₁ ρ) Fss Ess Ids (famAt (consList bs₁ ρ)) srcs dM dms dis dt ∧
      consList vals ρ = cons t (consList is (consList ms (cons M (consList bs₁ ρ)))) ∧
      RecHypS ℓ w (consList is (consList ms (cons M (consList bs₁ ρ)))) Fss Ess Ids
        (famAt (consList bs₁ ρ)) ∧
      SqHypS ℓ w (consList is (consList ms (cons M (consList bs₁ ρ)))) Fss Ess Ids srcs ∧
      t ∈ˢ sumSet w (sumFibre w (consList is (consList ms (cons M (consList bs₁ ρ))))
        (rChains (nIdx + n + 1) nIdx Fss Ess)) := by
  simp only [List.map_append, List.map_cons, List.map_nil] at hsp
  obtain ⟨v₁, vt, rfl, hsp₁, hspt⟩ := spineFit_append_inv hsp
  obtain ⟨v₂, vi, rfl, hsp₂, hspi⟩ := spineFit_append_inv hsp₁
  obtain ⟨v₃, vm, rfl, hsp₃, hspm⟩ := spineFit_append_inv hsp₂
  obtain ⟨bs₁, vM, rfl, hspP, hspM⟩ := spineFit_append_inv hsp₃
  obtain ⟨M, rfl, hM⟩ := spineFit_singleton_inv hspM
  obtain ⟨t, rfl, ht⟩ := spineFit_singleton_inv hspt
  have hlen₁ : bs₁.length = nP := by rw [hspP.length_eq]; simp [hlenP]
  have hlenm : vm.length = n := by rw [hspm.length_eq]; simp [hlenM]
  have hleni : vi.length = nIdx := by rw [hspi.length_eq]; simp [hlenI]
  have hsatP : Sat2 V ((pds.map (·.2.2)).reverse) (consList bs₁ ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hspP
    rwa [List.append_nil] at this
  have hB := hbase _ hsatP
  have hMσ : consList [M] (consList bs₁ ρ) = cons M (consList bs₁ ρ) := rfl
  rw [consList_append, hMσ] at hspm
  rw [consList_append, consList_append, hMσ] at hspi
  rw [consList_append, consList_append, consList_append, hMσ] at ht
  have htail := hB.tail M hM
  have hidx := recTailS_spine htail hspm
  obtain ⟨-, hteq, hyp, hsq⟩ := recIdxS_spine hidx hspi
  rw [hteq, hIds, hFss] at ht
  refine ⟨bs₁, vm, vi, M, t, rfl, hlen₁, hlenm, hleni, hsatP, hB, ?_, hyp, hsq, ht⟩
  rw [consList_append, consList_append, consList_append, consList_append, hMσ]
  rfl

/-! ## The walks -/

/-- The body's validity at a frame satisfying the whole context. -/
theorem sumRecBodyValid_of_sat {ℓ w nP n nIdx : Nat} {pds dms dis : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hlenI : dis.length = nIdx)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss Ess Ids (famAt ρp) srcs dM dms dis dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      ∀ j, j < n → ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        ∀ E ∈ Ess.getD j [], AnnotValidV V (consList bs ρp) E)
    (σ : Nat → V)
    (hsat : Sat2 V ((((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse)) σ) :
    AnnotValidV V σ (sumRecBodyAV ℓ w Fss Ess srcs nIdx) := by
  have hsp := spineFit_of_sat2 (Δ₀ := []) (Ds := (pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2))
    (by rw [List.append_nil]; exact hsat)
  have hσ0 : consList (((List.range ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).length).reverse).map σ)
      (fun j => σ (j + ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).length)) = σ :=
    consList_range_reverse _ σ
  generalize hρ' : (fun j => σ (j + ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).length)) = ρ'
    at hsp hσ0
  obtain ⟨bs₁, ms, is, M, t, hvals, hlenB, hlenMs, hlenIs, hsatP, -, hσ', hyp, -, -⟩ :=
    sumRecSpine_facts hlenP hlenM hlenI hFss hIds hbase hsp
  rw [hσ0] at hσ'
  have hfr : RecFrameS 1 (consList is (consList ms (cons M (consList bs₁ ρ')))) σ := by
    show shiftE 1 0 σ = _
    rw [hσ', shiftE_one_cons]
  have hsh : shiftE (Ids.length + Fss.length + 1) 0 (consList is (consList ms (cons M (consList bs₁ ρ'))))
      = consList bs₁ ρ' := by
    have := kframe_frP (ρp := consList bs₁ ρ') (M := M) (n := n) (nIdx := nIdx) hlenIs hlenMs
    unfold frP at this
    rwa [hIds, hFss]
  obtain ⟨hv, hE⟩ := hvFss _ hsatP
  have hv' : SumFieldsValid (consList is (consList ms (cons M (consList bs₁ ρ'))))
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) := by
    refine rChains_validV ?_ ?_
    · rw [hsh]; exact hv
    · rw [hsh]
      intro j hj bs hsp E hE'
      exact hE j (by rw [← hFss]; exact hj) bs hsp E hE'
  rw [← hIds]
  exact sumRecBody_validV hfr hyp hv'

/-- **The recursor leaf's hereditary premises**: `RecPreS` along the
parameters, and validity along the whole frame. -/
theorem sumRecWalks {ℓ w nP n nIdx : Nat} {pds dms dis : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hlenI : dis.length = nIdx)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (okΓ : ∀ i, i < nP + n + nIdx + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).drop (nP + n + nIdx + 2 - i)) ρ →
      AnnotOkP V ρ ((((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).getD (nP + n + nIdx + 2 - 1 - i) default))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss Ess Ids (famAt ρp) srcs dM dms dis dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      ∀ j, j < n → ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        ∀ E ∈ Ess.getD j [], AnnotValidV V (consList bs ρp) E) :
    ∀ ρ : Nat → V,
      RecPreS ℓ w ρ Fss Ess Ids famAt srcs dM dms dis dt pds ∧
      UnderTowerValid ρ (sumRecBodyAV ℓ w Fss Ess srcs nIdx) (pds ++ [dM] ++ dms ++ dis ++ [dt]) := by
  intro ρ
  have hlenR : (pds ++ [dM] ++ dms ++ dis ++ [dt]).length = nP + n + nIdx + 2 := by
    rw [rds_length, hlenP, hlenM, hlenI]
  have hΓlen : (((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).length = nP + n + nIdx + 2 := by
    rw [List.length_reverse, List.length_map, hlenR]
  have hdrop : (((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).drop (n + nIdx + 2)
      = (pds.map (·.2.2)).reverse := by
    rw [← hlenM, ← hlenI]; exact rds_drop_params
  have hΓplen : ((pds.map (·.2.2)).reverse).length = nP := by simp [hlenP]
  constructor
  · -- `RecPreS` along the parameters
    have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
        Sat2 V (((pds.map (·.2.2)).reverse).drop (nP - i)) ρ →
        AnnotOkP V ρ (((pds.map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
      intro i hi ρ hρ
      have := okΓ i (by omega) ρ (by
        rw [show nP + n + nIdx + 2 - i = (n + nIdx + 2) + (nP - i) from by omega, ← List.drop_drop, hdrop]
        exact hρ)
      rwa [show nP + n + nIdx + 2 - 1 - i = (n + nIdx + 2) + (nP - 1 - i) from by omega, ← getD_drop', hdrop]
        at this
    have hent : ∀ i, i < nP → ∃ q, pds[i]? = some q ∧
        q.2.2 = ((pds.map (·.2.2)).reverse).getD (nP - 1 - i) default := by
      intro i hi
      have hil : i < pds.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds' => RecPreS ℓ w ρ Fss Ess Ids famAt srcs dM dms dis dt pds')
      hΓplen hlenP hent okΓp (fun ρ hρ => hbase ρ hρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw
  · -- validity along the whole frame
    have hent : ∀ i, i < nP + n + nIdx + 2 → ∃ q, (pds ++ [dM] ++ dms ++ dis ++ [dt])[i]? = some q ∧
        q.2.2 = (((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).getD (nP + n + nIdx + 2 - 1 - i) default := by
      intro i hi
      have hil : i < (pds ++ [dM] ++ dms ++ dis ++ [dt]).length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlenR hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (sumRecBodyAV ℓ w Fss Ess srcs nIdx) ds')
      hΓlen hlenR hent okΓ
      (fun ρ hρ => sumRecBodyValid_of_sat hlenP hlenM hlenI hFss hIds hbase hvFss ρ hρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw

/-- **The recursor leaf's P currency and membership**, at every frame. -/
theorem sumRecLeafFacts {ℓ w nP n nIdx : Nat} {pds dms dis : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hlenI : dis.length = nIdx)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ dis ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (okΓ : ∀ i, i < nP + n + nIdx + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).drop (nP + n + nIdx + 2 - i)) ρ →
      AnnotOkP V ρ ((((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).getD (nP + n + nIdx + 2 - 1 - i) default))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss Ess Ids (famAt ρp) srcs dM dms dis dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      ∀ j, j < n → ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        ∀ E ∈ Ess.getD j [], AnnotValidV V (consList bs ρp) E) :
    ∀ ρ : Nat → V,
      AnnotOkP V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs nIdx) ∧
      interp2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs nIdx)
        ∈ˢ interp2 V ρ (mkPisAV (pds ++ [dM] ++ dms ++ dis ++ [dt]) (recConcAV n nIdx)) := by
  intro ρ
  obtain ⟨hpre, hval⟩ := sumRecWalks hlenP hlenM hlenI hFss hIds okΓ hbase hvFss ρ
  have hmem := directSumRecAV_mem hz hpre
  rw [hFss, hIds] at hmem
  rw [← hIds] at hval
  refine ⟨?_, hmem⟩
  have := directSumRecAV_okP hz hpre hval
  rwa [← hIds]

/-! ## The rule law -/

set_option maxHeartbeats 6400000 in
/-- **The sum recursor rule's law at the readings.** -/
theorem sumRecLawCore {ℓ w nP nF nIdx n j : Nat} {pds dms dis ds : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))} {Es : List AVExpr}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hlenI : dis.length = nIdx)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hlenDs : ds.length = nP + nF) (hjn : j < n)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2))) (hEsj : Ess[j]? = some Es)
    (hEs : Es.length = nIdx)
    (hokR : ∀ ρ : Nat → V,
      AnnotOk2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs nIdx))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss Ess Ids (famAt ρp) srcs dM dms dis dt)
    (hokFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp → SumFieldsOkB w ρp Fss)
    {lds : List (Nat × AVExpr)}
    (hldsDom : lds.map (·.2) = ((pds ++ [dM] ++ dms).map (·.2.2)) ++ (liftDoms (n + 1) 0 (ds.drop nP)).map (·.2.2))
    (hldsBits : ∀ d ∈ lds, (ℓ = 0 ↔ d.1 = 0))
    {Ra : AVExpr} (hRa : Ra = mkLamsAV lds (sumRuleCoreAV nF n j))
    (hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra)
    {ρ : Nat → V} {xs ys : List AVExpr} (hxl : xs.length = nP + 1 + n + nIdx) (hyl : ys.length = nP + nF)
    (hspR : SpineFit ρ ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]).map
        (interp2 V ρ)))
    (hspC : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ)))
    (hplain : ∀ i, i < nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default))
    (hpin : ∀ i, i < nIdx →
      interp2 V (consList (ys.map (interp2 V ρ)) ρ) (Es.getD i default)
        = interp2 V ρ (xs.getD (nP + 1 + n + i) default)) :
    interp2 V ρ (AVExpr.mkAppN (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs nIdx)
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP)) ∧
    ((∀ a ∈ xs, AnnotOkP V ρ a) → (∀ b ∈ ys, AnnotOkP V ρ b) →
      AnnotOkP V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  -- the constructor's fit, split at the parameters
  have hdsSplit : ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨as₁, as₂, hys, hsp₁, hsp₂⟩ := spineFit_append_inv hspC
  have hlen₁ : as₁.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlen₂ : as₂.length = nF := by rw [hsp₂.length_eq, hlenFs]
  -- the recursor's fit: parameters, motive, minors, indices, major
  obtain ⟨bs₁, ms, is, M, t, hvals, hlenb₁, hlenm, hleni, hρp, hB, hσ, hyp, hsq, ht⟩ :=
    sumRecSpine_facts hlenP hlenM hlenI hFss hIds hbase hspR
  -- the argument values
  have hvals' := hvals
  rw [List.map_append, List.map_cons, List.map_nil] at hvals'
  have hxsv : xs.map (interp2 V ρ) = bs₁ ++ [M] ++ ms ++ is := List.append_inj_left' hvals' (by simp)
  have htv : interp2 V ρ (AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys)
      = t := by
    have := List.append_inj_right' hvals' (by simp)
    simpa using this
  -- the parameters, identified
  have hparams : as₁ = bs₁ := by
    have h1 : as₁ = (ys.map (interp2 V ρ)).take nP := by
      rw [hys, List.take_left' hlen₁]
    have h2 : bs₁ = (xs.map (interp2 V ρ)).take nP := by
      rw [hxsv, List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]
    rw [h1, h2]
    apply List.ext_getElem
    · simp only [List.length_take, List.length_map, hxl, hyl]; omega
    · intro i h1' h2'
      have hi : i < nP := by simpa [hyl] using h1'
      simp only [List.getElem_take, List.getElem_map]
      have := hplain i hi
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
      simpa using this
  subst hparams
  -- the index values, identified
  have hidxEq : idxValsAt (consList as₁ ρ) Es as₂ = is := by
    apply List.ext_getElem
    · simp [idxValsAt, hEs, hleni]
    · intro i h1 h2
      have hi : i < nIdx := by simpa [idxValsAt, hEs] using h1
      simp only [idxValsAt, List.getElem_map]
      have h := hpin i hi
      rw [hys, consList_append, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
        Option.getD_some] at h
      rw [h]
      have hx : (xs.map (interp2 V ρ))[nP + 1 + n + i]? = is[i]? := by
        rw [hxsv]
        simp only [List.append_assoc]
        rw [List.getElem?_append_right (by simp [hlenb₁]; omega),
          List.getElem?_append_right (by simp [hlenb₁]; omega),
          List.getElem?_append_right (by simp [hlenb₁, hlenm]; omega)]
        congr 1
        simp [hlenb₁, hlenm]
        omega
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some,
        List.getElem?_eq_getElem (by omega)] at hx
      exact Option.some.inj hx
  -- the constructor leaf's value
  have hleafC' : directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)
      = directSumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) (uChains Fss) := by
    rw [List.take_append_drop]
  have hokU : SumFieldsOkB w (consList as₁ ρ) (uChains Fss) := SumFieldsOkB_uChains (hokFss _ hρp)
  have hjU : (uChains Fss)[j]? = some ((ds.drop nP).map (·.2.2) ++ [idxEqAV []]) := by
    rw [uChains_getElem?, hFsj]; rfl
  have hmkv : t = if w = 0 then (pt : V) else inj j (mkTower (as₂ ++ [pt])) := by
    rw [← htv, interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hys,
      hleafC']
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, directSumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [directSumMkAV_fold hw hsp₁ hsp₂ hokU hjU, if_neg hw]
  -- the right-hand side's fit
  have hys₂ : (ys.map (interp2 V ρ)).drop nP = as₂ := by rw [hys, List.drop_left' hlen₁]
  have hxs₁ : (xs.take (nP + 1 + n)).map (interp2 V ρ) = as₁ ++ [M] ++ ms := by
    rw [List.map_take, hxsv, List.take_append_of_le_length (by simp [hlenb₁, hlenm]; omega),
      List.take_of_length_le (by simp [hlenb₁, hlenm]; omega)]
  have hfit : SpineFit ρ (lds.map (·.2)) ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp2 V ρ)) := by
    rw [hldsDom, List.map_append (f := interp2 V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁]
    refine SpineFit.append ?_ ?_
    · have h := hspR
      rw [hvals] at h
      simp only [List.map_append, List.map_cons, List.map_nil] at h ⊢
      obtain ⟨v₁, vt, hv, h₁, -⟩ := spineFit_append_inv h
      obtain ⟨v₂, vi, hv', h₂, -⟩ := spineFit_append_inv h₁
      have hv₂ : v₂ = as₁ ++ [M] ++ ms := by
        have hl : v₂.length = (as₁ ++ [M] ++ ms).length := by
          rw [h₂.length_eq]; simp [hlenm]; omega
        have hv'' : v₂ ++ (vi ++ vt) = as₁ ++ [M] ++ ms ++ (is ++ [t]) := by
          rw [← List.append_assoc, ← hv', ← hv, List.append_assoc]
        exact List.append_inj_left hv'' hl
      rw [hv₂] at h₂
      exact h₂
    · rw [spineFit_liftDoms, List.append_assoc, consList_append,
        show n + 1 = ([M] ++ ms).length from by simp [hlenm], shiftE_consList_zero]
      exact hsp₂
  -- the minor at the rule's core
  have hcore : interp2 V (consList ((xs.take (nP + 1 + n) ++ ys.drop nP).map (interp2 V ρ)) ρ)
      (sumRuleCoreAV nF n j) = as₂.foldl SetTheory.app (ms.getD j pt) := by
    rw [List.map_append (f := interp2 V ρ) (l₁ := xs.take (nP + 1 + n)) (l₂ := ys.drop nP),
      List.map_drop, hys₂, hxs₁, consList_append]
    unfold sumRuleCoreAV
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V (consList as₂ (consList (as₁ ++ [M] ++ ms) ρ)))
      (g := SetTheory.app),
      show fieldBvars nF = (List.range nF).map (fun k => AVExpr.bvar (nF - 1 - k)) from rfl,
      map_fieldBvars_interp hlen₂, interp2_bvar,
      show nF + n - 1 - j = (n - 1 - j) + as₂.length from by omega, consList_apply_add,
      consList_append, consList_apply_lt ms _ (n - 1 - j) (by omega),
      show ms.length - 1 - (n - 1 - j) = j from by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
  -- the right-hand side: the rule's fold
  have hRHS : interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))
      = as₂.foldl SetTheory.app (ms.getD j pt) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hRa,
      mkLamsAV_fold_graded (by rw [← hRa]; exact (hokRa ρ).1) hfit, hcore]
  -- the left-hand side: the recursor leaf's fold
  have hLHS : interp2 V ρ (AVExpr.mkAppN (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs nIdx)
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) (uChains Fss)) ys]))
      = interp2 V (consList (as₁ ++ [M] ++ ms ++ is ++ [t]) ρ) (sumRecBodyAV ℓ w Fss Ess srcs nIdx) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app),
      List.map_append, List.map_cons, List.map_nil, hxsv, htv]
    unfold directSumRecAV mkLamsC
    have hsp : SpineFit ρ (((pds ++ [dM] ++ dms ++ dis ++ [dt]).map fun d => (ℓ, d.2.2)).map (·.2))
        (as₁ ++ [M] ++ ms ++ is ++ [t]) := by
      rw [List.map_map]
      show SpineFit ρ ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)) _
      rw [← hvals]; exact hspR
    rw [mkLamsAV_fold_graded (hokR ρ) hsp]
  -- the K-frame
  have hσ' := hσ
  rw [List.map_append, List.map_cons, List.map_nil, hxsv, htv] at hσ'
  have hfr : RecFrameS 1 (consList is (consList ms (cons M (consList as₁ ρ))))
      (consList (as₁ ++ [M] ++ ms ++ is ++ [t]) ρ) := by
    show shiftE 1 0 _ = _
    rw [hσ', shiftE_one_cons]
  have hFsjD : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
    rw [List.getD_eq_getElem?_getD, hFsj]; rfl
  have hEsjD : Ess.getD j [] = Es := by
    rw [List.getD_eq_getElem?_getD, hEsj]; rfl
  have hfrP : frP Fss.length Ids.length (consList is (consList ms (cons M (consList as₁ ρ))))
      = consList as₁ ρ :=
    kframe_frP (by rw [hIds]; exact hleni) (by rw [hFss]; exact hlenm)
  have hfrIdx : frameIdx Ids.length (consList is (consList ms (cons M (consList as₁ ρ)))) = is :=
    kframe_frameIdx (by rw [hIds]; exact hleni)
  have hfrMs : ∀ j', j' < Fss.length →
      frMs Fss.length Ids.length (consList is (consList ms (cons M (consList as₁ ρ)))) j'
        = ms.getD j' pt := fun j' hj' =>
    kframe_frMs (by rw [hIds]; exact hleni) (by rw [hFss]; exact hlenm) hj'
  refine ⟨?_, ?_⟩
  · by_cases hℓ0 : ℓ = 0
    · -- both sides are the point
      subst hℓ0
      have hmpt : ms.getD j pt = pt := by
        rw [← hfrMs j (by rw [hFss]; exact hjn)]
        exact hyp.minor_pt rfl (by rw [hFss]; exact hjn)
      rw [hRHS, hmpt, foldl_app_pt_sum, interp2_mkAppN,
        ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app)]
      unfold directSumRecAV
      rw [interp2_mkLamsC_zero ρ (by simp), foldl_app_pt_sum]
    · rw [hLHS, hRHS]
      have hmaj : consList (as₁ ++ [M] ++ ms ++ is ++ [t]) ρ 0 = t := consList_apply_last _ _ _
      have hEs' : Es.length = Ids.length := by rw [hIds]; exact hEs
      rcases Nat.eq_zero_or_pos w with hw0 | hwpos
      · -- the squash regime at a nonzero elimination level: one constructor
        subst hw0
        have hn1 : Fss.length ≤ 1 := hsq.hwl rfl hℓ0
        have hj0 : j = 0 := by rw [hFss] at hn1; omega
        subst hj0
        have hidxK : idxValsAt (frP Fss.length Ids.length (consList is (consList ms (cons M (consList as₁ ρ)))))
            (Ess.getD 0 []) as₂
            = frameIdx Ids.length (consList is (consList ms (cons M (consList as₁ ρ)))) := by
          rw [hfrP, hfrIdx, hEsjD]; exact hidxEq
        have := sumRecBody_iota_sq hℓ0 hfr hsq (by rw [hFss]; omega)
          (by rw [hfrP, hFsjD]; exact hsp₂) hidxK
        rw [← hIds, this, hfrMs 0 (by rw [hFss]; omega)]
      · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
        have hmaj' : consList (as₁ ++ [M] ++ ms ++ is ++ [t]) ρ 0 = inj j (mkTower (as₂ ++ [pt])) := by
          rw [hmaj, hmkv, if_neg hw]
        have hbs : mkTower (as₂ ++ [pt]) ∈ˢ sumFibre w (consList is (consList ms (cons M (consList as₁ ρ))))
            (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j := by
          have hchain : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)[j]?
              = some (rChain (Ids.length + Fss.length + 1) Ids.length ((ds.drop nP).map (·.2.2)) Es) := by
            rw [rChains_getElem?, hFsj, hEsj]
          rw [sumFibre_of_getElem? hchain]
          unfold rChain
          have hsh : shiftE (Ids.length + Fss.length + 1) 0 (consList is (consList ms (cons M (consList as₁ ρ))))
              = consList as₁ ρ := by
            have := hfrP; unfold frP at this; rwa [Nat.add_comm Ids.length] at this
          have := restricted_member_intro (w := w)
            (Fs := liftFields (Ids.length + Fss.length + 1) 0 ((ds.drop nP).map (·.2.2)))
            ((spineFit_liftFields _).mpr (hsh ▸ hsp₂))
            ((EqAll_idxEqsAt (d := Ids.length + Fss.length + 1) (nIdx := Ids.length)
                (nF := ((ds.drop nP).map (·.2.2)).length) hEs' (by rw [hlen₂, hlenFs])).mpr
              (by rw [hsh, hfrIdx]; exact hidxEq))
          rw [if_neg hw] at this
          exact this
        have := sumRecBody_iota (srcs := srcs) hw hfr hyp (by rw [hFss]; exact hjn)
          (by rw [hFsjD, hlen₂, hlenFs]) hmaj' hbs
        rw [← hIds, this, hfrMs j (by rw [hFss]; exact hjn)]
  · intro hxs_ok hys_ok
    refine mkAppN_okP_of_lam (hokRa ρ) ?_ (by rw [← hRa]; exact (hokRa ρ).1)
      (Or.inr (by rw [hRa])) hfit
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hxs_ok a (List.mem_of_mem_take h)
    · exact hys_ok a (List.mem_of_mem_drop h)

end Lech.SetP
