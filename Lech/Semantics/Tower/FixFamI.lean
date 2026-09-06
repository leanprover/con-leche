import Lech.Semantics.Tower.FixLeafI
import Lech.Semantics.Tower.SumRecCase

/-!
# The recursive family's functor: readings and laws (task #188, indexed)

The X-chain's entries at the **X-frame** `(ρp, X, t, f₀ … f_{i-1})`
(`FixLeafI.lean`): an ordinary entry reads the domain at the parameter
frame below the fields (`interp2_chainXI_ord`), a recursive entry
reads `X ⟨e⃗_i⟩` — the family at the tuple of the index expressions'
values (`recSlot_facts`, through the tupler's fold; graded through the
tupler's Π-tower chain, `appChainOk_of_mkPisAV`), and the terminator
reads the index equation against the tuple's projections
(`EqAll_eqsXI`).  On top of these the functor's laws: monotonicity in
the family (`chainXIGo_tele_sub`, `fixStepI_mono`), the ω-iterate
family as a closed member (`famU`), the fixed point (`fixFamI_eq`), the
carrier as the ω-iterate (`fixFamI_eq_famU`), and the identification
of the fibre at `⟨ı⃗⟩` with the indexed sum route's restricted tagged
union (`fixFamI_app_eq_sum`).
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory SetTheory.Tower

universe w

variable {V : Type w} [SetTheory V]

/-! ## The X-frame kit -/

omit [SetTheory V] in
theorem shiftE_Xframe (ρp : Nat → V) (as : List V) (t X : V) :
    shiftE (as.length + 2) 0 (consList as (cons t (cons X ρp))) = ρp := by
  rw [shiftE_consList_add, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons, shiftE_succ_cons,
    shiftE_zero_zero]

omit [SetTheory V] in
theorem Xframe_X (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) (as.length + 1) = X := by
  have := consList_apply_add as (cons t (cons X ρp)) 1
  rw [Nat.add_comm] at this
  exact this

omit [SetTheory V] in
theorem Xframe_t (ρp : Nat → V) (as : List V) (t X : V) :
    consList as (cons t (cons X ρp)) as.length = t := by
  have := consList_apply_add as (cons t (cons X ρp)) 0
  rw [Nat.zero_add] at this
  exact this

/-- An ordinary entry of the X-chain reads the domain at the parameter
frame under the fields. -/
theorem interp2_chainXI_ord {ρp : Nat → V} (F : AVExpr) (as : List V) (t X : V) :
    interp2 V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      = interp2 V (consList as ρp) F := by
  rw [interp2_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons,
    shiftE_succ_cons, shiftE_zero_zero]

theorem AnnotOk2_chainXI_ord {ρp : Nat → V} (F : AVExpr) (as : List V) (t X : V) :
    AnnotOk2 V (consList as (cons t (cons X ρp))) (F.liftN 2 as.length)
      ↔ AnnotOk2 V (consList as ρp) F := by
  rw [AnnotOk2_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl, shiftE_succ_cons,
    shiftE_succ_cons, shiftE_zero_zero]

/-! ## The recursive slot -/

/-- The application chain along a Π-tower's binder data is graded. -/
theorem appChainOk_of_mkPisAV {m : Nat} {b C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b C ds →
      f ∈ˢ interp2 V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as → AppChainOk f as
  | [], _, _, [], _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, hu, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp2 V ρ d.2.2)
        (fun x => interp2 V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp2 V ρ d.2.2 →
        interp2 V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro h0 x hx
      exact underTowerOk_res_univZero ((hz d (.head _)).mpr h0)
        (fun d' hd' => hz d' (.tail _ hd')) (hu.2 x hx)
    intro l hl
    cases l with
    | zero =>
      refine ⟨d.2.1, interp2 V ρ d.2.2, fun x => interp2 V (cons x ρ) (mkPisAV ds C), ?_, ?_, hB0⟩
      · simpa using hf'
      · simpa using hsp.1
    | succ l =>
      have ih := appChainOk_of_mkPisAV (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a)
        (as := as) (fun d' hd' => hz d' (.tail _ hd')) (hu.2 a hsp.1)
        (app_mem_piR hf' hsp.1 hB0) hsp.2 l (by simpa using hl)
      obtain ⟨v, A, B, h1, h2, h3⟩ := ih
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2

section Slot

variable {u w : Nat} {ρp : Nat → V} {Ids : List AVExpr}

/-- The tupler applied to index expressions at the X-frame: its value
(the tuple of the expressions' values) and its grading. -/
theorem tuplerApp_facts (hI : IdxOk u ρp Ids) (as : List V) (t X : V) {Es : List AVExpr}
    (hEok : ∀ E ∈ Es, AnnotOk2 V (consList as ρp) E)
    (hsp : SpineFit ρp Ids (Es.map (interp2 V (consList as ρp)))) :
    interp2 V (consList as (cons t (cons X ρp)))
        (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length)))
      = tupW u (Es.map (interp2 V (consList as ρp))) ∧
    AnnotOk2 V (consList as (cons t (cons X ρp)))
      (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length))) := by
  have hfv : interp2 V (consList as (cons t (cons X ρp))) ((tuplerAV u Ids).liftN (as.length + 2) 0)
      = interp2 V ρp (tuplerAV u Ids) := by
    rw [interp2_liftN, shiftE_Xframe]
  have hfok : AnnotOk2 V (consList as (cons t (cons X ρp))) ((tuplerAV u Ids).liftN (as.length + 2) 0) := by
    rw [AnnotOk2_liftN, shiftE_Xframe]; exact tuplerAV_ok2 hI
  have hargs : (Es.map (·.liftN 2 as.length)).map (interp2 V (consList as (cons t (cons X ρp))))
      = Es.map (interp2 V (consList as ρp)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro E _
    exact interp2_chainXI_ord E as t X
  have hargsok : ∀ a ∈ Es.map (·.liftN 2 as.length), AnnotOk2 V (consList as (cons t (cons X ρp))) a := by
    intro a ha
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
    exact (AnnotOk2_chainXI_ord E as t X).mpr (hEok E hE)
  have hchain : AppChainOk (interp2 V (consList as (cons t (cons X ρp)))
      ((tuplerAV u Ids).liftN (as.length + 2) 0))
      ((Es.map (·.liftN 2 as.length)).map (interp2 V (consList as (cons t (cons X ρp))))) := by
    rw [hfv, hargs]
    exact appChainOk_of_mkPisAV (ds := tuplerData u Ids) (b := mkTowerGo u Ids)
      (C := (idxTyAV u Ids).liftN Ids.length 0)
      (fun _ hd => by obtain ⟨F, -, rfl⟩ := List.mem_map.mp hd; exact Iff.rfl)
      (tuplerAV_under hI) (tuplerAV_mem hI) (by rw [tuplerData_doms]; exact hsp)
  have h := mkAppN_ok2_of_chain hfok hargsok hchain
  refine ⟨?_, h.1⟩
  rw [h.2, hargs, hfv]
  exact tuplerAV_fold hI hsp

/-- **The recursive slot** `X ⟨e⃗⟩` at the X-frame: its value, its
grading, its bound. -/
theorem recSlot_facts (hI : IdxOk u ρp Ids) {X : V} (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids))
    (as : List V) (t : V) {Es : List AVExpr}
    (hEok : ∀ E ∈ Es, AnnotOk2 V (consList as ρp) E)
    (hsp : SpineFit ρp Ids (Es.map (interp2 V (consList as ρp)))) :
    interp2 V (consList as (cons t (cons X ρp)))
        (.app (.bvar (as.length + 1))
          (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length))))
      = SetTheory.app X (tupW u (Es.map (interp2 V (consList as ρp)))) ∧
    AnnotOk2 V (consList as (cons t (cons X ρp)))
      (.app (.bvar (as.length + 1))
        (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0) (Es.map (·.liftN 2 as.length)))) ∧
    SetTheory.app X (tupW u (Es.map (interp2 V (consList as ρp)))) ∈ˢ (univ w : V) := by
  obtain ⟨htv, htok⟩ := tuplerApp_facts (X := X) (t := t) hI as hEok hsp
  have hXm : X ∈ˢ piR (w + 1) (idxSet u ρp Ids) fun _ => (univ w : V) := hX
  refine ⟨?_, ?_, ?_⟩
  · rw [interp2_app, interp2_bvar, Xframe_X, htv]
  · rw [AnnotOk2_app]
    refine ⟨trivial, htok, w + 1, idxSet u ρp Ids, fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h (Nat.succ_ne_zero w)⟩
    · rw [interp2_bvar, Xframe_X]; exact hXm
    · rw [htv]; exact tupW_mem hsp
  · exact app_mem_piR_pos (Nat.succ_ne_zero w) hXm (tupW_mem hsp)

/-! ## The terminator -/

/-- At index level `0` every index value is the point. -/
theorem spineFit_pt_of_bound0 {ρ : Nat → V} :
    ∀ {Fs : List AVExpr} {as : List V}, FieldsBound 0 ρ Fs → SpineFit ρ Fs as →
      ∀ l, l < as.length → as.getD l pt = pt
  | [], [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, hsp, _, _ => hsp.elim
  | _ :: _, [], _, hsp, _, _ => hsp.elim
  | F :: Fs, a :: as, hb, hsp, l, hl => by
    cases l with
    | zero =>
      have h0 : interp2 V ρ F ∈ˢ (univZero : V) := by
        have := hb.1; rwa [univ_zero] at this
      exact eq_pt_of_mem_univZero h0 hsp.1
    | succ l =>
      exact spineFit_pt_of_bound0 (hb.2 a hsp.1) hsp.2 l (by simpa using hl)

/-- The terminator's sides are graded at the X-frame. -/
theorem eqsXI_ok2 (hI : IdxOk u ρp Ids) {X t : V} (ht : t ∈ˢ idxSet u ρp Ids) {bs : List V}
    {nF : Nat} (hlen : bs.length = nF) {Es : List AVExpr}
    (hEok : ∀ E ∈ Es, AnnotOk2 V (consList bs ρp) E) (hEs : Es.length = Ids.length) :
    EqsOk2 (consList bs (cons t (cons X ρp))) (eqsXI Ids.length nF Es) := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < Ids.length := List.mem_range.mp hl
  refine ⟨?_, ?_⟩
  · show AnnotOk2 V _ ((Es.getD l default).liftN 2 nF)
    subst hlen
    exact (AnnotOk2_chainXI_ord _ bs t X).mpr (hEok _ (getD_mem_of_lt (by omega)))
  · show AnnotOk2 V _ (projAV l (.bvar nF))
    subst hlen
    refine projAV_ok2_tower (w := u) (Fs := Ids) (ρ := ρp) (by simp) ?_ hI.2 hl'
    rw [interp2_bvar, Xframe_t]
    exact ht

/-- **The terminator's reading** at a tuple: the index expressions'
values are the tuple's components. -/
theorem EqAll_eqsXI (hI : IdxOk u ρp Ids) {X : V} {is : List V} (hsp : SpineFit ρp Ids is)
    {bs : List V} {nF : Nat} (hlen : bs.length = nF) {Es : List AVExpr} :
    EqAll (consList bs (cons (tupW u is) (cons X ρp))) (eqsXI Ids.length nF Es) ↔
      ∀ l, l < Ids.length → interp2 V (consList bs ρp) (Es.getD l default) = is.getD l pt := by
  have hislen : is.length = Ids.length := hsp.length_eq
  have hproj : ∀ l, l < Ids.length →
      interp2 V (consList bs (cons (tupW u is) (cons X ρp))) (projAV l (.bvar nF)) = is.getD l pt := by
    intro l hl
    subst hlen
    rw [projAV_interp, interp2_bvar, Xframe_t]
    by_cases hu : u = 0
    · subst hu
      rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
    · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
  unfold EqAll eqsXI
  constructor
  · intro h l hl
    have := h ((Es.getD l default).liftN 2 nF, projAV l (.bvar nF))
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
    simp only at this
    subst hlen
    rwa [interp2_chainXI_ord, hproj l hl] at this
  · intro h e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    simp only
    subst hlen
    rw [interp2_chainXI_ord, hproj l (List.mem_range.mp hl)]
    exact h l (List.mem_range.mp hl)

/-- The sum route's terminator at the index frame, in the same
pointwise form. -/
theorem EqAll_idxEqsAt' {is : List V} (hislen : is.length = Ids.length) {bs : List V} {nF : Nat}
    (hlen : bs.length = nF) {Es : List AVExpr} (hEs : Es.length = Ids.length) :
    EqAll (consList bs (consList is ρp)) (idxEqsAt Ids.length Ids.length nF Es) ↔
      ∀ l, l < Ids.length → interp2 V (consList bs ρp) (Es.getD l default) = is.getD l pt := by
  rw [EqAll_idxEqsAt hEs hlen]
  have hsh : shiftE Ids.length 0 (consList is ρp) = ρp := by
    rw [← hislen]; exact shiftE_consList is ρp
  have hfr : frameIdx Ids.length (consList is ρp) = is := by
    rw [← hislen]; exact frameIdx_consList' is ρp
  rw [hsh, hfr]
  unfold idxValsAt
  constructor
  · intro h l hl
    have hl' : l < Es.length := by omega
    have := congrArg (fun L => L.getD l pt) h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl',
      Option.map_some, Option.getD_some] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl', Option.getD_some,
      List.getD_eq_getElem?_getD]
    exact this
  · intro h
    apply List.ext_getElem
    · rw [List.length_map]; omega
    · intro l h1 h2
      rw [List.getElem_map]
      have := h l (by rw [List.length_map] at h1; omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map] at h1; omega),
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
        Option.getD_some] at this
      exact this

end Slot

end Lech.Semantics
