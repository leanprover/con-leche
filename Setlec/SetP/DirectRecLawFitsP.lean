import Setlec.SetP.DirectRecLawKitP

/-!
# The rule's λ-domains at the full frame (task #175 W4c, P3 module 6, part 17)

`recLawFits`: at any valuation of the full composite frame (parameters,
motive, minor, fields), the frame's values fit the rule right-hand
side's λ-domains.  The checker pins each λ-domain to the frame's own
variable annotation by `isDefEq` **at the full depth**, so the
identification is per position at the full frame — the earlier
positions' fits (the induction) supply the grading of the next
λ-layer's domain (`mkLamsAV_layers_okP`) the defeq claim needs.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- The layers of a P-graded λ-tower are P-graded along any fitting
prefix of a spine. -/
theorem mkLamsAV_layers_okP :
    ∀ {lds : List (Nat × AVExpr)} {b : AVExpr} {ρ : Nat → V} {as : List V} {i : Nat},
      AnnotOkP V ρ (mkLamsAV lds b) → SpineFit ρ ((lds.take i).map (·.2)) as →
      i < lds.length → AnnotOkP V (consList as ρ) ((lds.getD i default).2)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | d :: lds, b, ρ, as, 0, hok, hsp, _ => by
    obtain rfl : as = [] := by
      match as, hsp with
      | [], _ => rfl
    have hok2 := hok.1
    have hokV := hok.2
    simp only [mkLamsAV, AnnotOk2_lam] at hok2
    simp only [mkLamsAV, AnnotValidV_lam] at hokV
    exact ⟨hok2.1, hokV.1⟩
  | d :: lds, b, ρ, [], i + 1, _, hsp, _ => hsp.elim
  | d :: lds, b, ρ, a :: as, i + 1, hok, hsp, hi => by
    simp only [List.take_succ_cons, List.map_cons, SpineFit] at hsp
    have hok2 := hok.1
    have hokV := hok.2
    simp only [mkLamsAV, AnnotOk2_lam] at hok2
    simp only [mkLamsAV, AnnotValidV_lam] at hokV
    obtain ⟨-, hrest, -⟩ := hok2
    obtain ⟨-, hrestv⟩ := hokV
    simp only [consList_cons, List.getD_cons_succ]
    exact mkLamsAV_layers_okP ⟨hrest a hsp.1, hrestv a hsp.1⟩ hsp.2 (by simpa using hi)

/-- The first `i` values of a frame, outermost first. -/
def frameVals (ρ : Nat → V) (D i : Nat) : List V :=
  (List.range i).map fun k => ρ (D - 1 - k)

omit [SetTheory V] in
theorem frameVals_length (ρ : Nat → V) (D i : Nat) : (frameVals ρ D i).length = i := by
  simp [frameVals]

omit [SetTheory V] in
theorem frameVals_succ (ρ : Nat → V) (D i : Nat) :
    frameVals ρ D (i + 1) = frameVals ρ D i ++ [ρ (D - 1 - i)] := by
  simp [frameVals, List.range_succ]

omit [SetTheory V] in
/-- The frame's first `i` values, consed on the frame's tail, are the
frame shifted by `D - i`. -/
theorem consList_frameVals (ρ : Nat → V) {D i : Nat} (hi : i ≤ D) :
    consList (frameVals ρ D i) (fun k => ρ (k + D)) = fun k => ρ (k + (D - i)) := by
  funext k
  rcases Nat.lt_or_ge k i with hk | hk
  · rw [consList_apply_lt _ _ _ (by rw [frameVals_length]; exact hk), frameVals_length]
    simp only [frameVals, List.getElem?_map, List.getElem?_range (show i - 1 - k < i by omega),
      Option.map_some, Option.getD_some]
    congr 1; omega
  · have := consList_apply_add (frameVals ρ D i) (fun k => ρ (k + D)) (k - i)
    rw [frameVals_length, show k - i + i = k from by omega] at this
    rw [this]
    show ρ (k - i + D) = ρ (k + (D - i))
    congr 1; omega

/-- The domains of a λ-peel, by position. -/
theorem lds_entry {lds : List (Nat × AVExpr)} {Γ : List AVExpr} {D : Nat}
    (hΓ : (lds.map (·.2)).reverse = Γ) (hlen : lds.length = D) {i : Nat} (hi : i < D) :
    Γ.getD (D - 1 - i) default = (lds.getD i default).2 := by
  subst hΓ
  have hq : lds[i]? = some (lds.getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp; omega), List.length_map, hlen,
    show D - 1 - (D - 1 - i) = i from by omega, List.getElem?_map, hq]
  rfl

/-! ## The fits -/

set_option maxHeartbeats 6400000 in
/-- **The full frame's values fit the rule's λ-domains.** -/
theorem recLawFits {m : EnvS2Core V env} {F : Nat} (hc : ClaimsAtP μ m φ F)
    {nP nF : Nat} {tyR : Expr} {fvsR : List Expr} {oR : Expr} {Γr : List AVExpr} {Rr : AVExpr}
    (hR : OpenedP m φ (nP + 3) tyR fvsR oR Γr Rr)
    (hidxR : ∀ (i : Nat) (x : Expr), fvsR[i]? = some x → ∃ nm ty, x = Expr.fvar i nm ty)
    (hlenF : fvsR.length = nP + 3)
    {xFvs : List Expr} {minBody : Expr} {Γm : List AVExpr} {Rm : AVExpr}
    (comp : CompOpenedP m φ nP nF fvsR xFvs minBody Γr Γm Rm)
    {rhsA : Expr} (hrhsF : rhsA.hasFvar = false) (hrhsB : rhsA.looseBVarsBounded 0 = true)
    {Ra : AVExpr} (hread : denoteP m.acval env φ 0 rhsA = some Ra)
    (hokRa : ∀ ρ : Nat → V, AnnotOkP V ρ Ra)
    {ldoms : List Expr} {lrest : Expr}
    (hli : Expr.instLamsAt (fvsR.take (nP + 2) ++ xFvs) rhsA = some (ldoms, lrest))
    (hpins : Setlec.DefEqListOk μ F env (nP + 2 + nF)
      ((fvsR.take (nP + 2) ++ xFvs).map Expr.fvarTypeD) ldoms) :
    ∃ (lds : List (Nat × AVExpr)) (C : AVExpr),
      Ra = mkLamsAV lds C ∧ lds.length = nP + 2 + nF ∧
      denoteP m.acval env φ (nP + 2 + nF) lrest = some C ∧
      ∀ ρ'' : Nat → V,
        Sat2 V (compCtx Γm Γr nF (Γr.getD 1 default) nF) ρ'' →
        SpineFit (fun k => ρ'' (k + (nP + 2 + nF))) (lds.map (·.2))
          (frameVals ρ'' (nP + 2 + nF) (nP + 2 + nF)) := by
  -- names
  have hlenT : (fvsR.take (nP + 2)).length = nP + 2 := by simp [hlenF]
  have hlenSp : (fvsR.take (nP + 2) ++ xFvs).length = nP + 2 + nF := by
    rw [List.length_append, hlenT, comp.lenX]
  have hidxX := fun q x hx => (comp.varX q x hx).1
  have hidxSp : ∀ (i : Nat) (x : Expr), (fvsR.take (nP + 2) ++ xFvs)[i]? = some x →
      ∃ nm ty, x = Expr.fvar (0 + i) nm ty := by
    intro i x hx
    rcases Nat.lt_or_ge i (nP + 2) with hi | hi
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hi] at hx
      obtain ⟨nm, ty, h⟩ := hidxR i x hx
      exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
    · rw [List.getElem?_append_right (by omega), hlenT] at hx
      obtain ⟨nm, ty, h⟩ := hidxX _ x hx
      exact ⟨nm, ty, by rw [h]; congr 1; omega⟩
  -- the rule's λ-telescope
  obtain ⟨Γl, C, htele, hΓl, hC, hdomsL⟩ := instLamsAt_denotePTele _ hli hidxSp hread
  rw [hlenSp] at htele hΓl
  rw [Nat.zero_add, hlenSp] at hC
  obtain ⟨lds, rfl, hldsΓ, hlenL⟩ := stripLamsAV_of_lamTeleP htele
  refine ⟨lds, C, rfl, hlenL, hC, ?_⟩
  -- the pins, indexed by position
  have hpin : ∀ i, i < nP + 2 + nF → ∃ a b, (fvsR.take (nP + 2) ++ xFvs)[i]? = some a ∧
      ldoms[i]? = some b ∧
      Setlec.isDefEqCore μ env F (nP + 2 + nF) (Expr.fvarTypeD a) b = .ok true := by
    intro i hi
    have hlenL' : ldoms.length = nP + 2 + nF := by
      rw [instLamsAt_length _ hli, hlenSp]
    obtain ⟨a, ha⟩ : ∃ a, (fvsR.take (nP + 2) ++ xFvs)[i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨b, hb⟩ : ∃ b, ldoms[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨a, b, ha, hb, defEqListOk_index hpins i _ b (by rw [List.getElem?_map, ha]; rfl) hb⟩
  -- the frame
  have hΔlen := compCtx_length comp.lenM hR.len (E := Γr.getD 1 default) (Nat.le_refl nF)
  -- the frame's entries: their readings at their own depth, gradings
  -- under their prefixes, and the variables' scoping
  have hentry : ∀ i, i < nP + 2 + nF → ∃ (x : Expr) (A : AVExpr),
      (fvsR.take (nP + 2) ++ xFvs)[i]? = some x ∧
      Expr.WScoped i (Expr.fvarTypeD x) ∧ (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.fvarTypeD x) ∧
      (∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
        (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs)) ∧
      denoteP m.acval env φ i (Expr.fvarTypeD x) = some A ∧
      (compCtx Γm Γr nF (Γr.getD 1 default) nF)[nP + 2 + nF - 1 - i]? = some A ∧
      (∀ ρ : Nat → V, Sat2 V ((compCtx Γm Γr nF (Γr.getD 1 default) nF).drop (nP + 2 + nF - i)) ρ →
        AnnotOkP V ρ A) := by
    intro i hi
    rcases Nat.lt_or_ge i (nP + 2) with hlt | hge
    · -- a recursor variable
      obtain ⟨x, hx⟩ : ∃ x, fvsR[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨-, hw, hb, hL, hleaf⟩ := hR.var i x hx
      have hd := hR.doms i x hx
      refine ⟨x, _, by rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hlt]; exact hx,
        hw, hb, hL, ?_, hd, ?_, ?_⟩
      · intro l hl
        have hlt' := Expr.fvarLeaves_lt_of_wscoped hw l hl
        obtain ⟨p, hp⟩ := List.getElem?_of_mem (hleaf l hl)
        obtain ⟨nm', ty', hx'⟩ := hidxR p _ hp
        have hp' : l.1 = p := by injection hx'
        exact Or.inl (List.mem_of_getElem?
          (by rw [List.getElem?_take_of_lt (i := p) (j := nP + 2) (by omega)]; exact hp))
      · rcases Nat.lt_or_ge i (nP + 1) with h1 | h1
        · rw [show nP + 3 - 1 - i = nP + 2 - i from by omega]
          exact compCtx_getElem?_rec comp.lenM hR.len (Nat.le_refl _) (by omega)
        · obtain rfl : i = nP + 1 := by omega
          rw [show nP + 3 - 1 - (nP + 1) = 1 from by omega]
          exact compCtx_getElem?_minor comp.lenM (Nat.le_refl _)
      · intro ρ hρ
        rw [compCtx_drop_rec comp.lenM (Nat.le_refl _) (by omega)] at hρ
        exact hR.okΓ i (by omega) ρ hρ
    · -- a field variable
      obtain ⟨j, rfl⟩ : ∃ j, i = nP + 2 + j := ⟨i - (nP + 2), by omega⟩
      have hj : j < nF := by omega
      obtain ⟨x, hx⟩ : ∃ x, xFvs[j]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [comp.lenX]; exact hj)⟩
      obtain ⟨-, hw, hb, hL, hleaf⟩ := comp.varX j x hx
      have hd := comp.domsX j x hx
      refine ⟨x, _, by rw [List.getElem?_append_right (by omega), hlenT,
          show nP + 2 + j - (nP + 2) = j from by omega]; exact hx,
        hw, hb, hL, ?_, hd, ?_, ?_⟩
      · intro l hl
        rcases hleaf l hl with h | h
        · exact Or.inl (mem_take_of_le h (by omega))
        · exact Or.inr h
      · rw [show nP + 2 + nF - 1 - (nP + 2 + j) = nF - 1 - j from by omega]
        exact compCtx_getElem?_field comp.lenM (Nat.le_refl _) hj
      · intro ρ hρ
        rw [show nP + 2 + nF - (nP + 2 + j) = nF - j from by omega,
          compCtx_drop_fields comp.lenM (Nat.le_of_lt hj) (Nat.le_refl _)] at hρ
        exact comp.okΓm _ j hj ρ hρ
  -- a λ-domain's scoping and leaves
  have hspW : ∀ (i : Nat) (a : Expr), (fvsR.take (nP + 2) ++ xFvs)[i]? = some a →
      Expr.WScoped (0 + i + 1) a := by
    intro i a ha
    obtain ⟨x, A, hx, hw, -, -, -, -, -, -⟩ := hentry i (by
      have := (List.getElem?_eq_some_iff.mp ha).1
      omega)
    obtain rfl := Option.some.inj (hx.symm.trans ha)
    obtain ⟨nm, ty, rfl⟩ := hidxSp i _ ha
    simp only [Expr.fvarTypeD] at hw
    simp only [Expr.WScoped]
    exact ⟨by omega, by rw [Nat.zero_add]; exact hw⟩
  have hw0 : Expr.WScoped 0 rhsA := Expr.WScoped.of_not_hasFvar hrhsF
  have hnil : rhsA.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hrhsF
  obtain ⟨hbdoms, -⟩ := instLamsAt_bounded _ hli hrhsB (fun a ha => by
    obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
    obtain ⟨nm, ty, rfl⟩ := hidxSp q a hq
    rfl)
  have hleavesL := instLamsAt_leaves _ hli
  have hleafDom : ∀ l, (∃ x ∈ ldoms, l ∈ x.fvarLeaves) →
      (Expr.fvar l.1 l.2.1 l.2.2 ∈ fvsR.take (nP + 2) ∨ Expr.fvar l.1 l.2.1 l.2.2 ∈ xFvs) ∧
      l.2.2.looseBVarsBounded 0 = true := by
    intro l hl
    rcases hleavesL l (Or.inl hl) with h | ⟨a, ha, hla⟩
    · rw [hnil] at h; exact absurd h List.not_mem_nil
    · obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
      obtain ⟨x, A, hx, -, hb, hL, hleaf, -, -, -⟩ := hentry q (by
        have := (List.getElem?_eq_some_iff.mp hq).1
        omega)
      obtain rfl := Option.some.inj (hx.symm.trans hq)
      obtain ⟨nm, ty, rfl⟩ := hidxSp q _ hq
      simp only [Expr.fvarTypeD] at hb hL hleaf
      simp only [Expr.fvarLeaves, List.mem_cons] at hla
      rcases hla with rfl | hla
      · refine ⟨?_, hb⟩
        rcases List.mem_append.mp ha with h | h
        · exact Or.inl h
        · exact Or.inr h
      · exact ⟨hleaf l hla, hL l hla⟩
  -- the full frame's Sat2, in the induction: the values fit the first
  -- `i` layers
  have hE : ∀ l : Nat × Name × Expr, l.1 = nP + 1 → Γr.getD 1 default = Γr.getD 1 default :=
    fun _ _ => rfl
  suffices key : ∀ i, i ≤ nP + 2 + nF → ∀ ρ'' : Nat → V,
      Sat2 V (compCtx Γm Γr nF (Γr.getD 1 default) nF) ρ'' →
      SpineFit (fun k => ρ'' (k + (nP + 2 + nF))) ((lds.take i).map (·.2))
        (frameVals ρ'' (nP + 2 + nF) i) by
    intro ρ'' hρ''
    have := key (nP + 2 + nF) (Nat.le_refl _) ρ'' hρ''
    rwa [List.take_of_length_le (by rw [hlenL]; exact Nat.le_refl _)] at this
  intro i
  induction i with
  | zero => intro _ ρ'' _; simp [frameVals, SpineFit]
  | succ i ih =>
    intro hi ρ'' hρ''
    have hfit := ih (by omega) ρ'' hρ''
    have hq : lds[i]? = some (lds.getD i default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [List.take_add_one, hq, Option.toList_some, List.map_append,
      List.map_cons, List.map_nil, frameVals_succ]
    refine SpineFit.append hfit ?_
    rw [consList_frameVals ρ'' (by omega)]
    refine ⟨?_, trivial⟩
    -- the pin at position `i`, at this frame
    obtain ⟨a, b, ha, hb, hdeq⟩ := hpin i (by omega)
    obtain ⟨x, A, hx, hwa, hba, hLa, hleafa, hda, hposA, hokA⟩ := hentry i (by omega)
    obtain rfl := Option.some.inj (hx.symm.trans ha)
    have hwb : Expr.WScoped i b := by
      have := instLamsAt_index_WScoped _ (d := 0) hli hw0 hspW i b hb
      rwa [Nat.zero_add] at this
    have hbb : b.looseBVarsBounded 0 = true := hbdoms b (List.mem_of_getElem? hb)
    have hleafb := fun l hl => hleafDom l ⟨b, List.mem_of_getElem? hb, hl⟩
    have hLb : Expr.LeavesBounded b := fun l hl => (hleafb l hl).2
    -- readings at the full depth
    have hdaD : denoteP m.acval env φ (nP + 2 + nF) (Expr.fvarTypeD x)
        = some (A.liftN (nP + 2 + nF - i) 0) := by
      rw [denoteP_lift m.acval_closed hwa (nP + 2 + nF) (by omega), hda]
      rfl
    have hdb : denoteP m.acval env φ i b = some ((lds.getD i default).2) := by
      have := hdomsL i b hb
      rw [Nat.zero_add, hlenSp, lds_entry hldsΓ hlenL (by omega)] at this
      exact this
    have hdbD : denoteP m.acval env φ (nP + 2 + nF) b
        = some (((lds.getD i default).2).liftN (nP + 2 + nF - i) 0) := by
      rw [denoteP_lift m.acval_closed hwb (nP + 2 + nF) (by omega), hdb]
      rfl
    -- the context correlations
    have hCa := comp.ctx (Γr.getD 1 default) (Nat.le_refl nF)
      (Expr.WScoped.mono (by omega) hwa) (fun l hl => ⟨hleafa l hl, fun _ => rfl⟩)
    have hCb := comp.ctx (Γr.getD 1 default) (Nat.le_refl nF)
      (Expr.WScoped.mono (by omega) hwb) (fun l hl => ⟨(hleafb l hl).1, fun _ => rfl⟩)
    -- the gradings under the full frame
    have hshift : ∀ ρ : Nat → V, shiftE (nP + 2 + nF - i) 0 ρ = fun k => ρ (k + (nP + 2 + nF - i)) :=
      fun ρ => shiftE_zero _ ρ
    have hokaD : ∀ ρ : Nat → V, Sat2 V (compCtx Γm Γr nF (Γr.getD 1 default) nF) ρ →
        AnnotOkP V ρ (A.liftN (nP + 2 + nF - i) 0) := by
      intro ρ hρ
      refine (AnnotOkP_liftN V _ _ 0 ρ).mpr ?_
      rw [hshift]
      exact hokA _ (Sat2_drop hρ _)
    have hokbD : ∀ ρ : Nat → V, Sat2 V (compCtx Γm Γr nF (Γr.getD 1 default) nF) ρ →
        AnnotOkP V ρ (((lds.getD i default).2).liftN (nP + 2 + nF - i) 0) := by
      intro ρ hρ
      refine (AnnotOkP_liftN V _ _ 0 ρ).mpr ?_
      rw [hshift, ← consList_frameVals ρ (by omega)]
      exact mkLamsAV_layers_okP (hokRa (fun k => ρ (k + (nP + 2 + nF)))) (ih (by omega) ρ hρ)
        (by omega)
    have heq := hc.defEqRow hdeq (Expr.WScoped.mono (by omega) hwa) hba hLa
      (Expr.WScoped.mono (by omega) hwb) hbb hLb hCa hCb hdaD hdbD hokaD hokbD ρ'' hρ''
    rw [interp2_liftN, interp2_liftN, hshift] at heq
    rw [← heq]
    -- the frame's own membership at position `i`
    have hmem := hρ'' (nP + 2 + nF - 1 - i) A hposA
    have e : (fun j => ρ'' (j + (nP + 2 + nF - 1 - i) + 1)) = fun k => ρ'' (k + (nP + 2 + nF - i)) := by
      funext k; congr 1; omega
    rw [e] at hmem
    exact hmem

end Setlec.SetR.Interp2
