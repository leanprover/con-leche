import Setlec.SetP.DirectCtorFramesP

/-!
# The constructor's cons (task #175 W4c, P3 module 6, part 5)

`stageCtor`: the P step at the constructor's cons.  The leaf is
`directMkAV (resSort.eval ψ) (ds ψ) (Fs ψ)` over the constructor
type's peel; its two hereditary premises (`MkPre`, `UnderTowerValid`)
walk the parameter frame and the full frame from the constructor's
data and frames; the family application at the bottom folds the
former's real leaf along the parameters (`formerFold`), the frames
identified.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.SetR (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

omit [SetTheory V] in
theorem consN_eq_consList : ∀ (ts : List V) (ρ : Nat → V), consN ts ρ = consList ts ρ
  | [], _ => rfl
  | t :: ts, ρ => consN_eq_consList ts (cons t ρ)

omit [SetTheory V] in
/-- The reversed range under a consed spine recovers the spine. -/
theorem range_reverse_map_consList :
    ∀ (as : List V) (ρ : Nat → V),
      (List.range as.length).reverse.map (consList as ρ) = as
  | [], _ => rfl
  | a :: as, ρ => by
    rw [List.length_cons, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have h0 : consList as (cons a ρ) as.length = a := by
      have := consList_apply_add as (cons a ρ) 0
      rw [Nat.zero_add] at this
      rw [this]; rfl
    rw [h0, range_reverse_map_consList as (cons a ρ)]

/-- Two domain lists whose reversed contexts have the same satisfying
valuations fit the same spines. -/
theorem spineFit_iff_of_sat2_iff {Ds₁ Ds₂ : List AVExpr}
    (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat2 V Ds₁.reverse ρ ↔ Sat2 V Ds₂.reverse ρ)
    (ρ : Nat → V) (as : List V) (hl : as.length = Ds₁.length) :
    SpineFit ρ Ds₁ as ↔ SpineFit ρ Ds₂ as := by
  have key : ∀ (Ds₁ Ds₂ : List AVExpr), Ds₁.length = Ds₂.length →
      (∀ ρ : Nat → V, Sat2 V Ds₁.reverse ρ → Sat2 V Ds₂.reverse ρ) →
      ∀ (ρ : Nat → V) (as : List V), as.length = Ds₁.length →
      SpineFit ρ Ds₁ as → SpineFit ρ Ds₂ as := by
    intro Ds₁ Ds₂ hlen hsat ρ as hl h
    have h1 := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ) h
    rw [List.append_nil] at h1
    have h2 := spineFit_of_sat2 (Δ₀ := []) (Ds := Ds₂)
      (by rw [List.append_nil]; exact hsat _ h1)
    have e1 : (fun j => consList as ρ (j + Ds₂.length)) = ρ := by
      funext j; rw [← hlen, ← hl, consList_apply_add]
    have e2 : ((List.range Ds₂.length).reverse.map (consList as ρ)) = as := by
      rw [← hlen, ← hl]; exact range_reverse_map_consList as ρ
    rw [e1, e2] at h2
    exact h2
  exact ⟨key Ds₁ Ds₂ hlen (fun ρ => (hiff ρ).mp) ρ as hl,
    key Ds₂ Ds₁ hlen.symm (fun ρ => (hiff ρ).mpr) ρ as (by rw [hl, hlen])⟩

/-- The reversed constructor context's parameter entries are the
reversed parameter context's. -/
theorem getD_reverse_take {ds : List (Nat × Nat × AVExpr)} {nP nF : Nat}
    (hlen : ds.length = nP + nF) {i : Nat} (hi : i < nP) :
    ((ds.map (·.2.2)).reverse).getD (nP + nF - 1 - i) default
      = (((ds.take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
  have hil : i < ds.length := by omega
  rw [getD_reverse_of_peel hlen (by omega) (List.getElem?_eq_getElem hil),
    getD_reverse_of_peel (List.length_take_of_le (by omega)) hi
      (by rw [List.getElem?_take_of_lt hi]; exact List.getElem?_eq_getElem hil)]

/-! ## The constructor leaf's premises -/

/-- **The constructor leaf's hereditary premises**: `MkPre` along the
parameters and `UnderTowerValid` along the whole frame. -/
theorem ctorWalks {m : EnvS2Core V env} {T : Name} {cvT cvC : ConstantVal}
    {nP nF : Nat} {resSort : Level}
    {pps ds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvT nP resSort pps)
    (hCD : CtorData m T cvC nP nF resSort ds)
    (hleafT : ∀ ψ, m.acval T ψ
      = directTyAV (resSort.eval ψ) (pps ψ) (((ds ψ).drop nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
        FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop nP).map (·.2.2)))
    (ψ : Name → Nat) (ρ : Nat → V) :
    MkPre (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))
        (ctorBodyAV m T nP nF ψ) ((ds ψ).take nP) ∧
      UnderTowerValid ρ (mkTowerGo (resSort.eval ψ) (((ds ψ).drop nP).map (·.2.2)))
        ((ds ψ).take nP ++ (ds ψ).drop nP) := by
  have hlenDs := hCD.len ψ
  have hlenP : ((ds ψ).take nP).length = nP := List.length_take_of_le (by omega)
  let Fs : List AVExpr := ((ds ψ).drop nP).map (·.2.2)
  -- the full frame's gradings
  have hst := stripPisAV_mkPisAV (ds ψ) (ctorBodyAV m T nP nF ψ)
  rw [hlenDs] at hst
  have htele := piTeleP_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleP_graded (V := V) htele (Δ₀ := []) (fun ρ _ => hCD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hΓlen : (((ds ψ).map (·.2.2)).reverse).length = nP + nF := by simp [hlenDs]
  have hΓplen : ((((ds ψ).take nP).map (·.2.2)).reverse).length = nP := by
    rw [List.length_reverse, List.length_map, hlenP]
  -- the parameter frame's gradings, from the full frame's
  have okΓp : ∀ i, i < nP → ∀ ρ : Nat → V,
      Sat2 V (((((ds ψ).take nP).map (·.2.2)).reverse).drop (nP - i)) ρ →
      AnnotOkP V ρ (((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default) := by
    intro i hi ρ hρ
    rw [← getD_reverse_take hlenDs hi]
    refine okΓ i (by omega) ρ ?_
    rw [drop_fields_eq hlenDs i (by omega)]
    exact hρ
  have hentP : ∀ i, i < nP → ∃ q, ((ds ψ).take nP)[i]? = some q ∧
      q.2.2 = ((((ds ψ).take nP).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < ((ds ψ).take nP).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenP hi (List.getElem?_eq_getElem hil)]⟩
  have hent : ∀ i, i < nP + nF → ∃ q, (ds ψ)[i]? = some q ∧
      q.2.2 = (((ds ψ).map (·.2.2)).reverse).getD (nP + nF - 1 - i) default := by
    intro i hi
    have hil : i < (ds ψ).length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenDs hi (List.getElem?_eq_getElem hil)]⟩
  -- the former's hereditary premise at the parameter frame
  have hpok : ∀ ρ₀ : Nat → V, ParamsOkT (resSort.eval ψ) ρ₀
      (((ds ψ).drop nP).map (·.2.2)) (pps ψ) := fun ρ₀ =>
    (formerWalks hFD (fun ψ' ρ' h => hfields ψ' ρ' ((hiff ψ' ρ').mp h)) ψ ρ₀).1
  constructor
  · -- `MkPre` along the parameters
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ pds => MkPre (resSort.eval ψ) ρ Fs (ctorBodyAV m T nP nF ψ) pds)
      hΓplen hlenP hentP okΓp
      (fun ρ hρ => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓplen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    · rw [List.drop_zero] at hw; exact hw
    -- the base: the field chain and the family's fold
    refine ⟨(hfields ψ ρ hρ).1, fun bs hsp => ?_⟩
    -- the parameter values, from the frame
    have hρt : Sat2 V ((pps ψ).map (·.2.2)).reverse ρ := (hiff ψ ρ).mpr hρ
    have hspP := spineFit_of_sat2 (Δ₀ := []) (Ds := (pps ψ).map (·.2.2))
      (by rw [List.append_nil]; exact hρt)
    simp only [List.length_map, hFD.len ψ] at hspP
    have hlenB : bs.length = nF := by
      rw [hsp.length_eq]
      show ((((ds ψ).drop nP).map (·.2.2))).length = nF
      simp [hlenDs]
    -- the body: the family at the parameters
    have hK : VExpr.bvarsBelow 0 (m.acval T ψ).erase := m.cval_closedL T ψ
    have hbody : interp2 V (consList bs ρ) (ctorBodyAV m T nP nF ψ)
        = ((List.range nP).reverse.map ρ).foldl SetTheory.app
            (interp2 V (fun j => ρ (j + nP)) (m.acval T ψ)) := by
      unfold ctorBodyAV paramBvars
      have hlen' : ((List.range nP).reverse.map ρ).length = nP := by simp
      have := interp2_bvarSpine (V := V) ((List.range nP).reverse.map ρ)
        (ρ := fun j => ρ (j + nP)) (σ := consList bs ρ) (K := m.acval T ψ)
        (fun q => nP + nF - 1 - q)
        (fun q hq => by
          rw [consN_eq_consList, consList_range_reverse, hlen',
            show nP + nF - 1 - q = (nP - 1 - q) + bs.length from by omega,
            consList_apply_add])
        (interp2_closed (V := V) hK _ _)
      rw [hlen'] at this
      exact this
    rw [hbody, hleafT, formerFold (hpok _) hspP, consList_range_reverse]
  · -- `UnderTowerValid` along the whole frame
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (mkTowerGo (resSort.eval ψ) Fs) ds')
      hΓlen hlenDs hent okΓ
      (fun ρ' hρ' => ?_)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ)
    · rw [List.take_append_drop]
      rw [List.drop_zero] at hw
      exact hw
    -- the base: the tupler is valid at the full frame, which is a
    -- fitting field spine over a parameter valuation
    rw [reverse_map_take_drop (ds ψ) nP] at hρ'
    have hspF := spineFit_of_sat2 (Δ₀ := (((ds ψ).take nP).map (·.2.2)).reverse)
      (Ds := ((ds ψ).drop nP).map (·.2.2)) hρ'
    have hlenF : (((ds ψ).drop nP).map (·.2.2)).length = nF := by simp [hlenDs]
    rw [hlenF] at hspF
    have hρp : Sat2 V (((ds ψ).take nP).map (·.2.2)).reverse (fun j => ρ' (j + nF)) := by
      have := Sat2_drop hρ' nF
      rw [List.drop_append_of_le_length (by simp [hlenDs]),
        List.drop_eq_nil_of_le (by simp [hlenDs]), List.nil_append] at this
      exact this
    obtain ⟨hokB, hval⟩ := hfields ψ _ hρp
    have := mkTowerGo_validV (w := resSort.eval ψ) hval (fun hw => hokB.toBound hw) hspF
    rwa [consList_range_reverse] at this

end Setlec.SetR.Interp2
