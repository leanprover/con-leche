import Setlec.SetP.DirectSum.SumRecFramesP
import Setlec.SetP.Direct.DirectRecLawCoreP

/-!
# The sum recursor's walks and rule law (task #175 sum-types)

From the frames' `RecBaseS`: the recursor leaf's hereditary premises
(`sumRecWalks` — `RecPreS` along the parameters, and the validity
walk along the whole frame, whose base needs the body's validity at a
full frame, read off the frame's spine by `sumRecSpine_facts`), the
leaf's P currency and membership (`sumRecLeafFacts`), and the rule
law at the readings (`sumRecLawCore`): the recursor leaf applied to a
spine ending in constructor `j`'s leaf at fitting arguments is the
rule's right-hand side at the parameters, motive, minors and fields —
both sides fold to minor `j` at the fields (the body's iota,
`sumRecBody_iota`); at a zero elimination level both sides are the
point.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
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

/-! ## The minor chain along a spine -/

/-- Along a spine fitting the minor entries, the values lie in their
minor spaces, and at the end the major entry reads to the carrier. -/
theorem recTailS_spine {ℓ w : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {dt : Nat × Nat × AVExpr} :
    ∀ {dms : List (Nat × Nat × AVExpr)} {j : Nat} {σ : Nat → V} {ms : List V},
      RecTailS ℓ w ρp Fss M dt dms j σ → SpineFit σ (dms.map (·.2.2)) ms →
      (∀ k, k < dms.length →
        ms.getD k pt ∈ˢ minorSpC ℓ M (ctorVal w (j + k)) (Fss.getD (j + k) []) ρp []) ∧
      (AnnotOk2 V (consList ms σ) dt.2.2 ∧
        interp2 V (consList ms σ) dt.2.2 = sumSet w (sumFibre w ρp Fss))
  | [], _, _, [], h, _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero _), h⟩
  | [], _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, hsp => hsp.elim
  | d :: dms, j, σ, m :: ms, h, hsp => by
    obtain ⟨-, hread, hrec⟩ := h
    obtain ⟨hm, hsp'⟩ := hsp
    obtain ⟨ih1, ih2⟩ := recTailS_spine (hrec m hm) hsp'
    refine ⟨fun k hk => ?_, ih2⟩
    cases k with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [← hread]; exact hm
    | succ k =>
      simp only [List.getD_cons_succ]
      rw [show j + (k + 1) = j + 1 + k from by omega]
      exact ih1 k (by simpa using hk)

/-! ## A full frame's facts -/

/-- **A spine fitting the recursor's data** splits as parameters,
motive, minors, major, and yields the recursor leaf's semantic
premises at the parameter frame. -/
theorem sumRecSpine_facts {ℓ w nP n : Nat} {pds dms : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss : List (List AVExpr)}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hFss : Fss.length = n)
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss dM dms dt)
    {ρ : Nat → V} {vals : List V}
    (hsp : SpineFit ρ ((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)) vals) :
    ∃ (bs₁ ms : List V) (M t : V), vals = bs₁ ++ [M] ++ ms ++ [t] ∧
      bs₁.length = nP ∧ ms.length = n ∧
      Sat2 V ((pds.map (·.2.2)).reverse) (consList bs₁ ρ) ∧
      RecBaseS ℓ w (consList bs₁ ρ) Fss dM dms dt ∧
      RecFrameS n (n + 2) (consList bs₁ ρ) M (fun k => ms.getD k pt) (consList vals ρ) ∧
      RecHypS ℓ w (consList bs₁ ρ) Fss M (fun k => ms.getD k pt) ∧
      t ∈ˢ sumSet w (sumFibre w (consList bs₁ ρ) Fss) := by
  simp only [List.map_append, List.map_cons, List.map_nil] at hsp
  obtain ⟨v₁, vt, rfl, hsp₁, hspt⟩ := spineFit_append_inv hsp
  obtain ⟨v₂, vm, rfl, hsp₂, hspm⟩ := spineFit_append_inv hsp₁
  obtain ⟨bs₁, vM, rfl, hspP, hspM⟩ := spineFit_append_inv hsp₂
  obtain ⟨M, rfl, hM⟩ := spineFit_singleton_inv hspM
  obtain ⟨t, rfl, ht⟩ := spineFit_singleton_inv hspt
  have hlen₁ : bs₁.length = nP := by rw [hspP.length_eq]; simp [hlenP]
  have hlenm : vm.length = n := by rw [hspm.length_eq]; simp [hlenM]
  have hsatP : Sat2 V ((pds.map (·.2.2)).reverse) (consList bs₁ ρ) := by
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) hspP
    rwa [List.append_nil] at this
  have hB := hbase _ hsatP
  have hM' : M ∈ˢ piR (ℓ + 1) (sumSet w (sumFibre w (consList bs₁ ρ) Fss)) fun _ => (univ ℓ : V) := by
    rw [← hB.eqM]; exact hM
  have hMσ : consList [M] (consList bs₁ ρ) = cons M (consList bs₁ ρ) := rfl
  rw [consList_append, hMσ] at hspm
  rw [consList_append, consList_append, hMσ] at ht
  have htail := hB.tail M (hB.eqM ▸ hM')
  obtain ⟨hms, -, hteq⟩ := recTailS_spine htail hspm
  rw [hteq] at ht
  refine ⟨bs₁, vm, M, t, rfl, hlen₁, hlenm, hsatP, hB, ?_, ⟨hB.hok, hM', ?_, hB.hwl⟩, ht⟩
  · -- the frame
    have hσ : consList (bs₁ ++ [M] ++ vm ++ [t]) ρ
        = consList (vm ++ [t]) (cons M (consList bs₁ ρ)) := by
      rw [consList_append, consList_append, consList_append, hMσ, consList_append vm [t]]
    rw [hσ]
    refine ⟨?_, Nat.le_refl _, ?_, ?_⟩
    · rw [shiftE_zero]
      funext i
      show consList (vm ++ [t]) (cons M (consList bs₁ ρ)) (i + (n + 2)) = _
      rw [show i + (n + 2) = (i + 1) + (vm ++ [t]).length from by simp [hlenm]; omega,
        consList_apply_add]
      rfl
    · show consList (vm ++ [t]) (cons M (consList bs₁ ρ)) (n + 2 - 1) = M
      rw [show n + 2 - 1 = 0 + (vm ++ [t]).length from by simp [hlenm], consList_apply_add]
      rfl
    · intro k hk
      show consList (vm ++ [t]) (cons M (consList bs₁ ρ)) (n + 2 - 2 - k) = vm.getD k pt
      rw [consList_apply_lt _ _ _ (by simp [hlenm]; omega),
        show (vm ++ [t]).length - 1 - (n + 2 - 2 - k) = k from by simp [hlenm]; omega,
        List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
  · intro k hk
    have := hms k (by omega)
    rwa [Nat.zero_add] at this

/-! ## The walks -/

/-- The body's validity at a frame satisfying the whole context. -/
theorem sumRecBodyValid_of_sat {ℓ w nP n : Nat} {pds dms : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss : List (List AVExpr)}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hFss : Fss.length = n)
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss dM dms dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp → SumFieldsValid ρp Fss)
    (σ : Nat → V)
    (hsat : Sat2 V ((((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse)) σ) :
    AnnotValidV V σ (sumRecBodyAV ℓ w Fss) := by
  have hsp := spineFit_of_sat2 (Δ₀ := []) (Ds := (pds ++ [dM] ++ dms ++ [dt]).map (·.2.2))
    (by rw [List.append_nil]; exact hsat)
  obtain ⟨bs₁, ms, M, t, hvals, -, -, hsatP, -, hfr, hyp, -⟩ :=
    sumRecSpine_facts hlenP hlenM hFss hbase hsp
  have hσ : consList (((List.range ((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).length).reverse).map σ)
      (fun j => σ (j + ((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).length)) = σ :=
    consList_range_reverse _ σ
  rw [hσ] at hfr
  rw [← hFss] at hfr
  exact sumRecBody_validV hfr hyp (hvFss _ hsatP)

/-- **The recursor leaf's hereditary premises**: `RecPreS` along the
parameters, and validity along the whole frame. -/
theorem sumRecWalks {ℓ w nP n : Nat} {pds dms : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss : List (List AVExpr)}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hFss : Fss.length = n)
    (okΓ : ∀ i, i < nP + n + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).drop (nP + n + 2 - i)) ρ →
      AnnotOkP V ρ ((((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).getD (nP + n + 2 - 1 - i) default))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss dM dms dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp → SumFieldsValid ρp Fss) :
    ∀ ρ : Nat → V,
      RecPreS ℓ w ρ Fss dM dms dt pds ∧
      UnderTowerValid ρ (sumRecBodyAV ℓ w Fss) (pds ++ [dM] ++ dms ++ [dt]) := by
  intro ρ
  have hlenR : (pds ++ [dM] ++ dms ++ [dt]).length = nP + n + 2 := by
    rw [rds_length, hlenP, hlenM]
  have hΓlen : (((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).length = nP + n + 2 := by
    rw [List.length_reverse, List.length_map, hlenR]
  have hdrop : (((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).drop (n + 2)
      = (pds.map (·.2.2)).reverse := by
    rw [← hlenM]; exact rds_drop_params
  have hΓplen : ((pds.map (·.2.2)).reverse).length = nP := by simp [hlenP]
  constructor
  · -- `RecPreS` along the parameters
    have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
        Sat2 V (((pds.map (·.2.2)).reverse).drop (nP - i)) ρ →
        AnnotOkP V ρ (((pds.map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
      intro i hi ρ hρ
      have := okΓ i (by omega) ρ (by
        rw [show nP + n + 2 - i = (n + 2) + (nP - i) from by omega, ← List.drop_drop, hdrop]
        exact hρ)
      rwa [show nP + n + 2 - 1 - i = (n + 2) + (nP - 1 - i) from by omega, ← getD_drop', hdrop]
        at this
    have hent : ∀ i, i < nP → ∃ q, pds[i]? = some q ∧
        q.2.2 = ((pds.map (·.2.2)).reverse).getD (nP - 1 - i) default := by
      intro i hi
      have hil : i < pds.length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds' => RecPreS ℓ w ρ Fss dM dms dt pds')
      hΓplen hlenP hent okΓp (fun ρ hρ => hbase ρ hρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw
  · -- validity along the whole frame
    have hent : ∀ i, i < nP + n + 2 → ∃ q, (pds ++ [dM] ++ dms ++ [dt])[i]? = some q ∧
        q.2.2 = (((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).getD (nP + n + 2 - 1 - i) default := by
      intro i hi
      have hil : i < (pds ++ [dM] ++ dms ++ [dt]).length := by omega
      exact ⟨_, List.getElem?_eq_getElem hil,
        by rw [getD_reverse_of_peel hlenR hi (List.getElem?_eq_getElem hil)]⟩
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (sumRecBodyAV ℓ w Fss) ds')
      hΓlen hlenR hent okΓ
      (fun ρ hρ => sumRecBodyValid_of_sat hlenP hlenM hFss hbase hvFss ρ hρ)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    rw [List.drop_zero] at hw
    exact hw

/-- **The recursor leaf's P currency and membership**, at every frame. -/
theorem sumRecLeafFacts {ℓ w nP n : Nat} {pds dms : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss : List (List AVExpr)}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hFss : Fss.length = n)
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (okΓ : ∀ i, i < nP + n + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).drop (nP + n + 2 - i)) ρ →
      AnnotOkP V ρ ((((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)).reverse).getD (nP + n + 2 - 1 - i) default))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss dM dms dt)
    (hvFss : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp → SumFieldsValid ρp Fss) :
    ∀ ρ : Nat → V,
      AnnotOkP V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss) ∧
      interp2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss)
        ∈ˢ interp2 V ρ (mkPisAV (pds ++ [dM] ++ dms ++ [dt]) (.app (.bvar (Fss.length + 1)) (.bvar 0))) := by
  intro ρ
  obtain ⟨hpre, hval⟩ := sumRecWalks hlenP hlenM hFss okΓ hbase hvFss ρ
  exact ⟨directSumRecAV_okP hz hpre hval, directSumRecAV_mem hz hpre⟩

/-! ## The rule law -/

set_option maxHeartbeats 6400000 in
/-- **The sum recursor rule's law at the readings.** -/
theorem sumRecLawCore {ℓ w nP nF n j : Nat} {pds dms ds : List (Nat × Nat × AVExpr)}
    {dM dt : Nat × Nat × AVExpr} {Fss : List (List AVExpr)}
    (hlenP : pds.length = nP) (hlenM : dms.length = n) (hFss : Fss.length = n)
    (hlenDs : ds.length = nP + nF) (hjn : j < n)
    (hFsj : Fss[j]? = some ((ds.drop nP).map (·.2.2)))
    (hokR : ∀ ρ : Nat → V, AnnotOk2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss))
    (hbase : ∀ ρp : Nat → V, Sat2 V ((pds.map (·.2.2)).reverse) ρp →
      RecBaseS ℓ w ρp Fss dM dms dt)
    {lds : List (Nat × AVExpr)}
    (hldsDom : lds.map (·.2) = ((pds ++ [dM] ++ dms).map (·.2.2)) ++ (liftDoms (n + 1) 0 (ds.drop nP)).map (·.2.2))
    (hldsBits : ∀ d ∈ lds, (ℓ = 0 ↔ d.1 = 0))
    {Ra : AVExpr} (hRa : Ra = mkLamsAV lds (sumRuleCoreAV nF n j))
    (hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra)
    {ρ : Nat → V} {xs ys : List AVExpr} (hxl : xs.length = nP + 1 + n) (hyl : ys.length = nP + nF)
    (hspR : SpineFit ρ ((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) Fss) ys]).map (interp2 V ρ)))
    (hspC : SpineFit ρ (ds.map (·.2.2)) (ys.map (interp2 V ρ)))
    (hplain : ∀ i, i < nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default)) :
    interp2 V ρ (AVExpr.mkAppN (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss)
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) Fss) ys]))
      = interp2 V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP)) ∧
    ((∀ a ∈ xs, AnnotOkP V ρ a) → (∀ b ∈ ys, AnnotOkP V ρ b) →
      AnnotOkP V ρ (AVExpr.mkAppN Ra (xs.take (nP + 1 + n) ++ ys.drop nP))) := by
  have hlenFs : (((ds.drop nP).map (·.2.2))).length = nF := by simp [hlenDs]
  have hxtake : xs.take (nP + 1 + n) = xs := List.take_of_length_le (by omega)
  rw [hxtake]
  -- the constructor's fit, split at the parameters
  have hdsSplit : ds.map (·.2.2) = (ds.take nP).map (·.2.2) ++ (ds.drop nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  rw [hdsSplit] at hspC
  obtain ⟨as₁, as₂, hys, hsp₁, hsp₂⟩ := spineFit_append_inv hspC
  have hlen₁ : as₁.length = nP := by rw [hsp₁.length_eq]; simp [hlenDs]
  have hlen₂ : as₂.length = nF := by rw [hsp₂.length_eq, hlenFs]
  -- the recursor's fit: parameters, motive, minors, major
  obtain ⟨bs₁, ms, M, t, hvals, hlenb₁, hlenm, hρp, hB, hfr, hyp, ht⟩ :=
    sumRecSpine_facts hlenP hlenM hFss hbase hspR
  -- the argument values
  have hvals' := hvals
  rw [List.map_append, List.map_cons, List.map_nil] at hvals'
  have hxsv : xs.map (interp2 V ρ) = bs₁ ++ [M] ++ ms := List.append_inj_left' hvals' (by simp)
  have htv : interp2 V ρ (AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) Fss) ys)
      = t := by
    have := List.append_inj_right' hvals' (by simp)
    simpa using this
  -- the parameters, identified
  have hparams : as₁ = bs₁ := by
    have h1 : as₁ = (ys.map (interp2 V ρ)).take nP := by
      rw [hys, List.take_left' hlen₁]
    have h2 : bs₁ = (xs.map (interp2 V ρ)).take nP := by
      rw [hxsv, List.append_assoc, List.take_append_of_le_length (by omega),
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
  -- the constructor leaf's value
  have hleafC' : directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) Fss
      = directSumMkAV w j (ds.take nP ++ ds.drop nP) ((ds.drop nP).map (·.2.2)) Fss := by
    rw [List.take_append_drop]
  have hmkv : t = if w = 0 then (pt : V) else inj j (mkTower as₂) := by
    rw [← htv, interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hys,
      hleafC']
    rcases Nat.eq_zero_or_pos w with hw0 | hwpos
    · rw [hw0, directSumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
    · have hw : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
      rw [directSumMkAV_fold hw hsp₁ hsp₂ hB.hok hFsj, if_neg hw]
  -- the right-hand side's fit
  have hys₂ : (ys.map (interp2 V ρ)).drop nP = as₂ := by rw [hys, List.drop_left' hlen₁]
  have hfit : SpineFit ρ (lds.map (·.2)) ((xs ++ ys.drop nP).map (interp2 V ρ)) := by
    rw [hldsDom, List.map_append (f := interp2 V ρ) (l₁ := xs) (l₂ := ys.drop nP), List.map_drop, hys₂, hxsv]
    refine SpineFit.append ?_ ?_
    · have h := hspR
      rw [hvals] at h
      simp only [List.map_append, List.map_cons, List.map_nil] at h ⊢
      obtain ⟨v₁, vt, hv, h₁, -⟩ := spineFit_append_inv h
      have hv₁ : v₁ = as₁ ++ [M] ++ ms := by
        have hl : v₁.length = (as₁ ++ [M] ++ ms).length := by
          rw [h₁.length_eq]; simp [hlenb₁, hlenm]; omega
        exact (List.append_inj_left hv hl.symm).symm
      rw [hv₁] at h₁
      exact h₁
    · rw [spineFit_liftDoms, List.append_assoc, consList_append,
        show n + 1 = ([M] ++ ms).length from by simp [hlenm], shiftE_consList_zero]
      exact hsp₂
  -- the minor at the rule's core
  have hcore : interp2 V (consList ((xs ++ ys.drop nP).map (interp2 V ρ)) ρ) (sumRuleCoreAV nF n j)
      = as₂.foldl SetTheory.app (ms.getD j pt) := by
    rw [List.map_append (f := interp2 V ρ) (l₁ := xs) (l₂ := ys.drop nP), List.map_drop, hys₂, hxsv, consList_append]
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
  have hRHS : interp2 V ρ (AVExpr.mkAppN Ra (xs ++ ys.drop nP))
      = as₂.foldl SetTheory.app (ms.getD j pt) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app), hRa,
      mkLamsAV_fold_graded (by rw [← hRa]; exact (hokRa ρ).1) hfit, hcore]
  -- the left-hand side: the recursor leaf's fold
  have hLHS : interp2 V ρ (AVExpr.mkAppN (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ [dt]) Fss)
        (xs ++ [AVExpr.mkAppN (directSumMkAV w j ds ((ds.drop nP).map (·.2.2)) Fss) ys]))
      = interp2 V (consList (as₁ ++ [M] ++ ms ++ [t]) ρ) (sumRecBodyAV ℓ w Fss) := by
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app),
      List.map_append, List.map_cons, List.map_nil, hxsv, htv]
    unfold directSumRecAV mkLamsC
    have hsp : SpineFit ρ (((pds ++ [dM] ++ dms ++ [dt]).map fun d => (ℓ, d.2.2)).map (·.2))
        (as₁ ++ [M] ++ ms ++ [t]) := by
      rw [List.map_map]
      show SpineFit ρ ((pds ++ [dM] ++ dms ++ [dt]).map (·.2.2)) _
      rw [← hvals]; exact hspR
    rw [mkLamsAV_fold_graded (hokR ρ) hsp]
  refine ⟨?_, ?_⟩
  · by_cases hℓ0 : ℓ = 0
    · -- both sides are the point
      subst hℓ0
      have hmpt : ms.getD j pt = pt := hyp.minor_pt rfl (by rw [hFss]; exact hjn)
      rw [hRHS, hmpt, foldl_app_pt_sum, interp2_mkAppN,
        ← List.foldl_map (f := interp2 V ρ) (g := SetTheory.app)]
      unfold directSumRecAV
      rw [interp2_mkLamsC_zero ρ (by simp), foldl_app_pt_sum]
    · -- the graph regime: the body's iota
      rw [hLHS, hRHS]
      have hw : w ≠ 0 := by
        intro hw0
        rcases hyp.hwl hw0 with h | h
        · rw [hFss] at h; omega
        · exact hℓ0 h
      rw [hvals] at hfr
      rw [hmkv, if_neg hw] at hfr ht ⊢
      have hFsj' : Fss.getD j [] = (ds.drop nP).map (·.2.2) := by
        rw [List.getD_eq_getElem?_getD, hFsj]; rfl
      rw [← hFss] at hfr
      refine sumRecBody_iota hfr hyp (by rw [hFss]; exact hjn) (by rw [hFsj', hlenFs, hlen₂]) ?_ ?_
      · rw [consList_apply_last]
      · rw [sumFibre_of_getElem? hFsj]
        exact mkTower_mem_teleOfFields hw hsp₂
  · intro hxs_ok hys_ok
    refine mkAppN_okP_of_lam (hokRa ρ) ?_ (by rw [← hRa]; exact (hokRa ρ).1)
      (Or.inr (by rw [hRa])) hfit
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hxs_ok a h
    · exact hys_ok a (List.mem_of_mem_drop h)

end Setlec.SetP
