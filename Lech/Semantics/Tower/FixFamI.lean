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

/-- **The terminator's reading**, pointwise: the index expressions'
values equal the tuple's projections (no premise: the sides read off
the frame directly). -/
theorem EqAll_eqsXI_gen {X t : V} {bs : List V} {nF : Nat} (hlen : bs.length = nF)
    {n : Nat} {Es : List AVExpr} :
    EqAll (consList bs (cons t (cons X ρp))) (eqsXI n nF Es) ↔
      ∀ l, l < n → interp2 V (consList bs ρp) (Es.getD l default) = projS l t := by
  have hproj : ∀ l, interp2 V (consList bs (cons t (cons X ρp))) (projAV l (.bvar nF)) = projS l t := by
    intro l
    subst hlen
    rw [projAV_interp, interp2_bvar, Xframe_t]
  unfold EqAll eqsXI
  constructor
  · intro h l hl
    have := h ((Es.getD l default).liftN 2 nF, projAV l (.bvar nF))
      (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
    simp only at this
    subst hlen
    rwa [interp2_chainXI_ord, hproj l] at this
  · intro h e he
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    simp only
    subst hlen
    rw [interp2_chainXI_ord, hproj l]
    exact h l (List.mem_range.mp hl)

/-- The terminator's value does not depend on the family slot. -/
theorem interp2_termXI {X Y t : V} {bs : List V} {nF : Nat} (hlen : bs.length = nF)
    {n : Nat} {Es : List AVExpr} :
    interp2 V (consList bs (cons t (cons X ρp))) (idxEqAV (eqsXI n nF Es))
      = interp2 V (consList bs (cons t (cons Y ρp))) (idxEqAV (eqsXI n nF Es)) := by
  rw [idxEqAV_interp, idxEqAV_interp]
  congr 1
  exact propext ((EqAll_eqsXI_gen hlen).trans (EqAll_eqsXI_gen hlen).symm)

/-- **The terminator's reading** at a tuple: the index expressions'
values are the tuple's components. -/
theorem EqAll_eqsXI (hI : IdxOk u ρp Ids) {X : V} {is : List V} (hsp : SpineFit ρp Ids is)
    {bs : List V} {nF : Nat} (hlen : bs.length = nF) {Es : List AVExpr} :
    EqAll (consList bs (cons (tupW u is) (cons X ρp))) (eqsXI Ids.length nF Es) ↔
      ∀ l, l < Ids.length → interp2 V (consList bs ρp) (Es.getD l default) = is.getD l pt := by
  rw [EqAll_eqsXI_gen hlen]
  have hislen : is.length = Ids.length := hsp.length_eq
  have hproj : ∀ l, l < Ids.length → projS l (tupW u is) = is.getD l pt := by
    intro l hl
    by_cases hu : u = 0
    · subst hu
      rw [tupW_zero, projS_pt, spineFit_pt_of_bound0 hI.2 hsp l (by omega)]
    · rw [tupW_pos hu, projS_mkTower l is (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
  constructor
  · intro h l hl; rw [← hproj l hl]; exact h l hl
  · intro h l hl; rw [hproj l hl]; exact h l hl

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

/-! ## The functor's laws -/

section Fam

variable {u w : Nat} {ρp : Nat → V} {Ids : List AVExpr} {rss : List (List Bool)}
  {Eiss : List (List (List AVExpr))} {Fss Ess : List (List AVExpr)}

/-- The X-chain entry at position `i` (the head of `chainXIGo` there). -/
def xEntry (u : Nat) (Ids : List AVExpr) (rs : List Bool) (Eis : List (List AVExpr)) (F : AVExpr)
    (i : Nat) : AVExpr :=
  if rs.getD i false then
    .app (.bvar (i + 1))
      (AVExpr.mkAppN ((tuplerAV u Ids).liftN (i + 2) 0) ((Eis.getD i []).map (·.liftN 2 i)))
  else F.liftN 2 i

omit [SetTheory V] in
theorem chainXIGo_cons (rs : List Bool) (Eis : List (List AVExpr)) (F : AVExpr) (Fs : List AVExpr)
    (i : Nat) :
    chainXIGo u Ids rs Eis (F :: Fs) i = xEntry u Ids rs Eis F i :: chainXIGo u Ids rs Eis Fs (i + 1) :=
  rfl

omit [SetTheory V] in
theorem chainXIGo_length (rs : List Bool) (Eis : List (List AVExpr)) :
    ∀ (Fs : List AVExpr) (i : Nat), (chainXIGo u Ids rs Eis Fs i).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, i => by simp [chainXIGo, chainXIGo_length rs Eis Fs (i + 1)]

/-- The recursive slots' fit, hereditarily along the X-chain at
`(X, t)`: at each recursive position the index expressions are graded
at the parameter frame under the prefix and their values fit the index
telescope. -/
def SlotsFitX (u : Nat) (ρp : Nat → V) (Ids : List AVExpr) (rs : List Bool)
    (Eis : List (List AVExpr)) (X t : V) : Nat → List V → List AVExpr → Prop
  | _, _, [] => True
  | i, as, F :: Fs =>
    (rs.getD i false = true →
      (∀ E ∈ Eis.getD i [], AnnotOk2 V (consList as ρp) E) ∧
      SpineFit ρp Ids ((Eis.getD i []).map (interp2 V (consList as ρp)))) ∧
    ∀ a, a ∈ˢ interp2 V (consList as (cons t (cons X ρp))) (xEntry u Ids rs Eis F i) →
      SlotsFitX u ρp Ids rs Eis X t (i + 1) (as ++ [a]) Fs

/-- **The functor's full premise**: the index telescope graded, the
X-chains graded at every family and tuple, the recursive slots
fitting there. -/
structure XChainsOk (u w : Nat) (ρp : Nat → V) (Ids : List AVExpr) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (Fss Ess : List (List AVExpr)) : Prop where
  hI : IdxOk u ρp Ids
  hok : FixChainsOkI u w ρp Ids Ids.length rss Eiss Fss Ess
  hfit : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
    ∀ j, j < Fss.length →
      SlotsFitX u ρp Ids (rss.getD j []) (Eiss.getD j []) X t 0 [] (Fss.getD j [])

theorem lfpFamSpace_eq (w : Nat) (I : V) : lfpFamSpace V w I = famSpace w I :=
  piR_pos (Nat.succ_ne_zero w)

/-- A recursive entry reads the family at the tuple (no membership of
the family needed for the value). -/
theorem xEntry_rec (hI : IdxOk u ρp Ids) {X : V}
    {rs : List Bool} {Eis : List (List AVExpr)} (F : AVExpr) (as : List V) (t : V)
    (hri : rs.getD as.length false = true)
    (hEok : ∀ E ∈ Eis.getD as.length [], AnnotOk2 V (consList as ρp) E)
    (hsp : SpineFit ρp Ids ((Eis.getD as.length []).map (interp2 V (consList as ρp)))) :
    interp2 V (consList as (cons t (cons X ρp))) (xEntry u Ids rs Eis F as.length)
      = SetTheory.app X (tupW u ((Eis.getD as.length []).map (interp2 V (consList as ρp)))) := by
  unfold xEntry
  rw [if_pos hri, interp2_app, interp2_bvar, Xframe_X, (tuplerApp_facts (X := X) (t := t) hI as hEok hsp).1]

omit [SetTheory V] in
theorem consList_snoc' (a : V) (as : List V) (ρ : Nat → V) :
    cons a (consList as ρ) = consList (as ++ [a]) ρ := by
  rw [consList_append]; rfl

omit [SetTheory V] in
theorem length_snoc' (a : V) (as : List V) : (as ++ [a]).length = as.length + 1 := by simp

/-- An ordinary entry reads the domain. -/
theorem xEntry_ord {X : V} {rs : List Bool} {Eis : List (List AVExpr)} (F : AVExpr) (as : List V)
    (t : V) (hri : rs.getD as.length false = false) :
    interp2 V (consList as (cons t (cons X ρp))) (xEntry u Ids rs Eis F as.length)
      = interp2 V (consList as ρp) F := by
  unfold xEntry
  rw [if_neg (by rw [hri]; exact Bool.false_ne_true)]
  exact interp2_chainXI_ord F as t X

/-- **Monotonicity of the X-chain telescope** in the family. -/
theorem chainXIGo_tele_sub (hI : IdxOk u ρp Ids) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y)
    {rs : List Bool} {Eis : List (List AVExpr)} {t : V} {n nF : Nat} {Es : List AVExpr} :
    ∀ (Fs : List AVExpr) (i : Nat) (as : List V), as.length = i →
      SlotsFitX u ρp Ids rs Eis X t i as Fs → as.length + Fs.length = nF →
      TeleS.Sub
        (teleOfFields (consList as (cons t (cons X ρp)))
          (chainXIGo u Ids rs Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
        (teleOfFields (consList as (cons t (cons Y ρp)))
          (chainXIGo u Ids rs Eis Fs i ++ [idxEqAV (eqsXI n nF Es)]))
  | [], i, as, hi, _, hnF => by
    simp only [chainXIGo, List.nil_append, teleOfFields]
    rw [interp2_termXI (X := X) (Y := Y) (by simpa using hnF)]
    exact .cons (Subset.refl _) fun _ _ => .nil
  | F :: Fs, i, as, hi, hfit, hnF => by
    subst hi
    rw [chainXIGo_cons, List.cons_append]
    simp only [teleOfFields]
    refine .cons ?_ fun a ha => ?_
    · by_cases hri : rs.getD as.length false = true
      · obtain ⟨hEok, hsp⟩ := hfit.1 hri
        rw [xEntry_rec hI (X := X) F as t hri hEok hsp, xEntry_rec hI (X := Y) F as t hri hEok hsp]
        exact hXY _ (tupW_mem hsp)
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri', xEntry_ord F as t hri']
        exact Subset.refl _
    · rw [consList_snoc', consList_snoc']
      exact chainXIGo_tele_sub hI hX hXY Fs (as.length + 1) (as ++ [a]) (length_snoc' a as)
        (hfit.2 a ha) (by simp at hnF ⊢; omega)

/-- The fit predicate restricts along a smaller family. -/
theorem slotsFitX_mono (hI : IdxOk u ρp Ids) {X X' : V} (hX'X : FamLe (idxSet u ρp Ids) X' X)
    {rs : List Bool} {Eis : List (List AVExpr)} {t : V} :
    ∀ (Fs : List AVExpr) (i : Nat) (as : List V), as.length = i →
      SlotsFitX u ρp Ids rs Eis X t i as Fs → SlotsFitX u ρp Ids rs Eis X' t i as Fs
  | [], _, _, _, _ => trivial
  | F :: Fs, i, as, hi, hfit => by
    subst hi
    refine ⟨hfit.1, fun a ha => ?_⟩
    have ha' : a ∈ˢ interp2 V (consList as (cons t (cons X ρp))) (xEntry u Ids rs Eis F as.length) := by
      by_cases hri : rs.getD as.length false = true
      · obtain ⟨hEok, hsp⟩ := hfit.1 hri
        rw [xEntry_rec hI (X := X') F as t hri hEok hsp] at ha
        rw [xEntry_rec hI (X := X) F as t hri hEok hsp]
        exact hX'X _ (tupW_mem hsp) a ha
      · have hri' : rs.getD as.length false = false := by simpa using hri
        rw [xEntry_ord F as t hri'] at ha
        rw [xEntry_ord F as t hri']
        exact ha
    exact slotsFitX_mono hI hX'X Fs (as.length + 1) (as ++ [a]) (length_snoc' a as) (hfit.2 a ha')

/-- **The functor is monotone** in the family. -/
theorem fixStepI_mono (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y) {t : V}
    (ht : t ∈ˢ idxSet u ρp Ids) :
    fixStepI u w ρp Ids Ids.length rss Eiss Fss Ess X t
      ⊆ˢ fixStepI u w ρp Ids Ids.length rss Eiss Fss Ess Y t := by
  unfold fixStepI
  refine sumSet_mono fun j => ?_
  unfold sumFibre
  by_cases hj : j < Fss.length
  · rw [chainsXI_getElem?, if_pos hj]
    show towerSet w (teleOfFields (cons t (cons X ρp)) (chainXI u Ids Ids.length (rss.getD j [])
      (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))) ⊆ˢ towerSet w (teleOfFields (cons t (cons Y ρp))
      (chainXI u Ids Ids.length (rss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j [])))
    refine towerSet_mono ?_
    unfold chainXI
    exact chainXIGo_tele_sub h.hI hX hXY (Fss.getD j []) 0 [] rfl (h.hfit X hX t ht j hj) (by simp)
  · rw [chainsXI_getElem?, if_neg hj]
    exact Subset.refl _

theorem famFI_le (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {X Y : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) (hXY : FamLe (idxSet u ρp Ids) X Y) :
    FamLe (idxSet u ρp Ids) (famFI u w ρp Ids Ids.length rss Eiss Fss Ess X)
      (famFI u w ρp Ids Ids.length rss Eiss Fss Ess Y) := by
  intro t ht
  rw [famFI_app ht, famFI_app ht]
  exact fixStepI_mono h hX hXY ht

theorem fixFunVI_mono (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    MonoFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss Eiss Fss Ess) := by
  intro X Y hX hY hXY
  rw [← lfpFamSpace_eq] at hX hY
  rw [fixFunVI_app hX, fixFunVI_app hY]
  exact famFI_le h hX hXY

theorem fixFunVI_maps (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    MapsFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss Eiss Fss Ess) := by
  intro X hX
  rw [← lfpFamSpace_eq] at hX ⊢
  rw [fixFunVI_app hX]
  exact famFI_mem h.hok hX

/-! ## The ω-iterate family -/

/-- The finite iterates of the functor from the empty family. -/
noncomputable def famIter (u w : Nat) (ρp : Nat → V) (Ids : List AVExpr) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (Fss Ess : List (List AVExpr)) : Nat → V
  | 0 => graph (fun _ => empty) (idxSet u ρp Ids)
  | n + 1 => famFI u w ρp Ids Ids.length rss Eiss Fss Ess (famIter u w ρp Ids rss Eiss Fss Ess n)

/-- The ω-iterate family: the fibrewise union of the iterates. -/
noncomputable def famU (u w : Nat) (ρp : Nat → V) (Ids : List AVExpr) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (Fss Ess : List (List AVExpr)) : V :=
  graph (fun t => natUnion fun n => SetTheory.app (famIter u w ρp Ids rss Eiss Fss Ess n) t)
    (idxSet u ρp Ids)

theorem famIter_mem (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    ∀ n, famIter u w ρp Ids rss Eiss Fss Ess n ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)
  | 0 => by
    rw [lfpFamSpace_eq]
    exact graph_mem_famSpace fun _ _ => empty_mem_univ w
  | n + 1 => famFI_mem h.hok (famIter_mem h n)

theorem famIter_le_succ (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    ∀ n, FamLe (idxSet u ρp Ids) (famIter u w ρp Ids rss Eiss Fss Ess n)
      (famIter u w ρp Ids rss Eiss Fss Ess (n + 1))
  | 0 => by
    intro t ht
    show SetTheory.app (graph (fun _ => empty) (idxSet u ρp Ids)) t ⊆ˢ _
    rw [app_graph ht]
    exact empty_subset _
  | n + 1 => famFI_le h (famIter_mem h n) (famIter_le_succ h n)

theorem famIter_mono (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {m n : Nat} (hmn : m ≤ n) :
    FamLe (idxSet u ρp Ids) (famIter u w ρp Ids rss Eiss Fss Ess m)
      (famIter u w ρp Ids rss Eiss Fss Ess n) := by
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this; exact FamLe.refl _ _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | rfl
    · exact FamLe.trans (ih (Nat.le_of_lt_succ hlt)) (famIter_le_succ h n)
    · exact FamLe.refl _ _

theorem famU_app {t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    SetTheory.app (famU u w ρp Ids rss Eiss Fss Ess) t
      = natUnion fun n => SetTheory.app (famIter u w ρp Ids rss Eiss Fss Ess n) t :=
  app_graph ht

theorem famU_mem (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    famU u w ρp Ids rss Eiss Fss Ess ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) := by
  rw [lfpFamSpace_eq]
  refine graph_mem_famSpace fun t ht => natUnion_mem_univ fun n => ?_
  have := famIter_mem h n
  rw [lfpFamSpace_eq] at this
  exact famSpace_app this ht

theorem famIter_le_famU (_h : XChainsOk u w ρp Ids rss Eiss Fss Ess) (n : Nat) :
    FamLe (idxSet u ρp Ids) (famIter u w ρp Ids rss Eiss Fss Ess n)
      (famU u w ρp Ids rss Eiss Fss Ess) := by
  intro t ht x hx
  rw [famU_app ht]
  exact mem_natUnion.mpr ⟨n, hx⟩

/-- **Finitarity**: a tuple fitting the X-chain at the ω-iterate fits
it at some finite stage. -/
theorem fitsXI_iter (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    {rs : List Bool} {Eis : List (List AVExpr)} {n' nF : Nat} {Es : List AVExpr} :
    ∀ (Fs : List AVExpr) (i : Nat) (as bs : List V), as.length = i → as.length + Fs.length = nF →
      SlotsFitX u ρp Ids rs Eis (famU u w ρp Ids rss Eiss Fss Ess) t i as Fs →
      SpineFit (consList as (cons t (cons (famU u w ρp Ids rss Eiss Fss Ess) ρp)))
        (chainXIGo u Ids rs Eis Fs i ++ [idxEqAV (eqsXI n' nF Es)]) bs →
      ∃ n, SpineFit (consList as (cons t (cons (famIter u w ρp Ids rss Eiss Fss Ess n) ρp)))
        (chainXIGo u Ids rs Eis Fs i ++ [idxEqAV (eqsXI n' nF Es)]) bs
  | [], i, as, bs, hi, hnF, _, hf => by
    refine ⟨0, ?_⟩
    simp only [chainXIGo, List.nil_append] at hf ⊢
    cases bs with
    | nil => exact hf
    | cons b bs =>
      obtain ⟨hb, hrest⟩ := hf
      refine ⟨?_, ?_⟩
      · rw [interp2_termXI (X := famIter u w ρp Ids rss Eiss Fss Ess 0)
          (Y := famU u w ρp Ids rss Eiss Fss Ess) (by simpa using hnF)]
        exact hb
      · cases bs with
        | nil => trivial
        | cons _ _ => exact hrest.elim
  | F :: Fs, i, as, bs, hi, hnF, hfit, hf => by
    subst hi
    rw [chainXIGo_cons, List.cons_append] at hf ⊢
    cases bs with
    | nil => exact hf.elim
    | cons b bs =>
      obtain ⟨hb, hrest⟩ := hf
      rw [consList_snoc'] at hrest
      obtain ⟨n₁, hn₁⟩ := fitsXI_iter h ht Fs (as.length + 1) (as ++ [b]) bs (length_snoc' b as)
        (by simp at hnF ⊢; omega) (hfit.2 b hb) hrest
      by_cases hri : rs.getD as.length false = true
      · obtain ⟨hEok, hsp⟩ := hfit.1 hri
        have hb' := hb
        rw [xEntry_rec h.hI F as t hri hEok hsp, famU_app (tupW_mem hsp)] at hb'
        obtain ⟨n₀, hn₀⟩ := mem_natUnion.mp hb'
        refine ⟨max n₀ n₁, ?_, ?_⟩
        · rw [xEntry_rec h.hI F as t hri hEok hsp]
          exact famIter_mono h (Nat.le_max_left n₀ n₁) _ (tupW_mem hsp) b hn₀
        · rw [consList_snoc']
          refine (fitsS_teleOfFields.mp (FitsS.mono ?_ (fitsS_teleOfFields.mpr hn₁)))
          refine chainXIGo_tele_sub h.hI (famIter_mem h n₁) (famIter_mono h (Nat.le_max_right n₀ n₁))
            Fs (as.length + 1) (as ++ [b]) (length_snoc' b as) ?_ (by simp at hnF ⊢; omega)
          exact slotsFitX_mono h.hI (famIter_le_famU h n₁) Fs (as.length + 1) (as ++ [b])
            (length_snoc' b as) (hfit.2 b hb)
      · have hri' : rs.getD as.length false = false := by simpa using hri
        refine ⟨n₁, ?_, ?_⟩
        · rw [xEntry_ord F as t hri'] at hb ⊢; exact hb
        · rw [consList_snoc']; exact hn₁

/-- **The ω-iterate family is closed.** -/
theorem famU_closed (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    FamLe (idxSet u ρp Ids)
      (famFI u w ρp Ids Ids.length rss Eiss Fss Ess (famU u w ρp Ids rss Eiss Fss Ess))
      (famU u w ρp Ids rss Eiss Fss Ess) := by
  intro t ht x hx
  rw [famFI_app ht] at hx
  rw [famU_app ht, mem_natUnion]
  -- a member of the fibre at the ω-iterate: some constructor's tower at a finite stage
  have key : ∀ j, j < Fss.length → ∀ a,
      a ∈ˢ towerSet w (teleOfFields (cons t (cons (famU u w ρp Ids rss Eiss Fss Ess) ρp))
        (chainXI u Ids Ids.length (rss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))) →
      ∃ n, a ∈ˢ towerSet w (teleOfFields (cons t (cons (famIter u w ρp Ids rss Eiss Fss Ess n) ρp))
        (chainXI u Ids Ids.length (rss.getD j []) (Eiss.getD j []) (Fss.getD j []) (Ess.getD j []))) := by
    intro j hj a ha
    have hfit := h.hfit _ (famU_mem h) t ht j hj
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · obtain ⟨rfl, bs, hbs⟩ := towerSet_zero_elim _ ha
      obtain ⟨n, hn⟩ := fitsXI_iter h ht (Fss.getD j []) 0 [] bs rfl (by simp) hfit
        (fitsS_teleOfFields.mp hbs)
      exact ⟨n, pt_mem_tower (fitsS_teleOfFields.mpr hn)⟩
    · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
      obtain ⟨hbs, heta⟩ := towerSet_elim_teleOfFields hw' ha
      obtain ⟨n, hn⟩ := fitsXI_iter h ht (Fss.getD j []) 0 [] _ rfl (by simp) hfit hbs
      refine ⟨n, ?_⟩
      rw [heta]
      exact mkTower_mem hw' (fitsS_teleOfFields.mpr hn)
  -- the fibre's members at a constructor
  have fib : ∀ j a, a ∈ˢ sumFibre w (cons t (cons (famU u w ρp Ids rss Eiss Fss Ess) ρp))
        (chainsXI u Ids Ids.length rss Eiss Fss Ess) j →
      ∃ n, a ∈ˢ sumFibre w (cons t (cons (famIter u w ρp Ids rss Eiss Fss Ess n) ρp))
        (chainsXI u Ids Ids.length rss Eiss Fss Ess) j := by
    intro j a ha
    unfold sumFibre at ha ⊢
    by_cases hj : j < Fss.length
    · rw [chainsXI_getElem?, if_pos hj] at ha ⊢
      obtain ⟨n, hn⟩ := key j hj a ha
      exact ⟨n, hn⟩
    · rw [chainsXI_getElem?, if_neg hj] at ha
      exact absurd ha (not_mem_empty _)
  unfold fixStepI at hx
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim hx
    obtain ⟨n, hn⟩ := fib j a ha
    refine ⟨n + 1, ?_⟩
    show pt ∈ˢ SetTheory.app (famFI u 0 ρp Ids Ids.length rss Eiss Fss Ess _) t
    rw [famFI_app ht]
    exact pt_mem_sumSet_zero (i := j) (a := a) hn
  · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hw
    obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw' hx
    obtain ⟨n, hn⟩ := fib j a ha
    refine ⟨n + 1, ?_⟩
    show inj j a ∈ˢ SetTheory.app (famFI u w ρp Ids Ids.length rss Eiss Fss Ess _) t
    rw [famFI_app ht]
    exact inj_mem hw' hn

/-- **A closed family exists**: the ω-iterate. -/
theorem fixFunVI_closed_exists (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) :
    ∃ L, IsClosedFam w (idxSet u ρp Ids) (fixFunVI u w ρp Ids Ids.length rss Eiss Fss Ess) L := by
  refine ⟨famU u w ρp Ids rss Eiss Fss Ess, ?_, ?_⟩
  · rw [← lfpFamSpace_eq]; exact famU_mem h
  · rw [fixFunVI_app (famU_mem h)]
    exact famU_closed h

/-! ## The carrier's laws -/

theorem fixFamI_mem (u w : Nat) (ρp : Nat → V) (Ids : List AVExpr) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (Fss Ess : List (List AVExpr)) :
    fixFamI u w ρp Ids Ids.length rss Eiss Fss Ess ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) :=
  lfpFamSet_mem_space V w _ _

/-- **The fixed-point equation**, fibrewise: the fibre at `t` is the
functor's fibre at the carrier. -/
theorem fixFamI_app_eq (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    fixStepI u w ρp Ids Ids.length rss Eiss Fss Ess (fixFamI u w ρp Ids Ids.length rss Eiss Fss Ess) t
      = SetTheory.app (fixFamI u w ρp Ids Ids.length rss Eiss Fss Ess) t := by
  have := app_lfpFamSet_eq (fixFunVI_closed_exists h) (fixFunVI_mono h) (fixFunVI_maps h) ht
  unfold fixFamI at this ⊢
  rwa [fixFunVI_app (lfpFamSet_mem_space V w _ _), famFI_app ht] at this

/-- **The carrier is the ω-iterate**, fibrewise. -/
theorem fixFamI_app_eq_famU (h : XChainsOk u w ρp Ids rss Eiss Fss Ess) {t : V} (ht : t ∈ˢ idxSet u ρp Ids) :
    SetTheory.app (fixFamI u w ρp Ids Ids.length rss Eiss Fss Ess) t
      = SetTheory.app (famU u w ρp Ids rss Eiss Fss Ess) t := by
  refine Subset.antisymm ?_ ?_
  · refine lfpFamSet_le ⟨?_, ?_⟩ t ht
    · rw [← lfpFamSpace_eq]; exact famU_mem h
    · rw [fixFunVI_app (famU_mem h)]; exact famU_closed h
  · have hn : ∀ n, FamLe (idxSet u ρp Ids) (famIter u w ρp Ids rss Eiss Fss Ess n)
        (fixFamI u w ρp Ids Ids.length rss Eiss Fss Ess) := by
      intro n
      induction n with
      | zero =>
        intro t ht
        show SetTheory.app (graph (fun _ => empty) (idxSet u ρp Ids)) t ⊆ˢ _
        rw [app_graph ht]
        exact empty_subset _
      | succ n ih =>
        intro t ht
        show SetTheory.app (famFI u w ρp Ids Ids.length rss Eiss Fss Ess _) t ⊆ˢ _
        rw [famFI_app ht, ← fixFamI_app_eq h ht]
        exact fixStepI_mono h (famIter_mem h n) ih ht
    intro x hx
    rw [famU_app ht] at hx
    obtain ⟨n, hxn⟩ := mem_natUnion.mp hx
    exact hn n t ht x hxn

end Fam

end Lech.Semantics
