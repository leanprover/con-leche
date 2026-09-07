import Lech.SetP.DirectFix.FixRecPreP
import Lech.SetP.DirectFix.FixIntroP

/-!
# The recursive recursor leaf's facts (task #188)

The sum route's `sumRecLeafFacts` (`SumRecLawP.lean`) for the
recursive route: from the premise `FixPre`, the type's validity and
the block's validity facts at the parameter frames, the recursor leaf
is `AnnotOkP` and inhabits its type's reading at every frame.  The
body's validity at a frame satisfying the binder data comes from the
K-frame package (`FixPre.hK`) and the validity kit (`FixIntroP.lean`);
the tower's validity is the hereditary walk over the opened type's
gradings.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-- **The body's validity** at a frame satisfying the recursor's binder
data. -/
theorem fixRecBodyValid_of_sat {ℓ w u s nP n nIdx : Nat} {Fss₀ Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))}
    {rds : List (Nat × Nat × AVExpr)}
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (hvFss : ∀ ρp : Nat → V, Sat2 V (((rds.take nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      (∀ j, j < n → ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        ∀ E ∈ Ess.getD j [], AnnotValidV V (consList bs ρp) E) ∧
      (∀ j, j < n → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
        ∀ fs : List V, SpineFit ρp (Fss.getD j []) fs →
        ∀ E ∈ (Eiss.getD j []).getD i [], AnnotValidV V (consList (fs.take i) ρp) E))
    (σ : Nat → V) (hsat : Sat2 V (((rds.map (·.2.2)).reverse)) σ) :
    AnnotValidV V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) := by
  have hsp := spineFit_of_sat2 (Δ₀ := []) (Ds := rds.map (·.2.2))
    (by rw [List.append_nil]; exact hsat)
  have hσ0 : consList (((List.range (rds.map (·.2.2)).length).reverse).map σ)
      (fun j => σ (j + (rds.map (·.2.2)).length)) = σ :=
    consList_range_reverse _ σ
  generalize hρ' : (fun j => σ (j + (rds.map (·.2.2)).length)) = ρ' at hsp hσ0
  generalize hvs : ((List.range (rds.map (·.2.2)).length).reverse).map σ = vs at hsp hσ0
  have hlenvs : vs.length = rds.length := by
    rw [← hvs, List.length_map, List.length_reverse, List.length_range, List.length_map]
  have hne : vs ≠ [] := by
    intro hnil
    have := h.hlen
    rw [hnil, List.length_nil] at hlenvs
    omega
  obtain ⟨as, t, rfl⟩ : ∃ as t, vs = as ++ [t] := by
    rcases List.eq_nil_or_concat vs with hnil | ⟨as, t, h⟩
    · exact absurd hnil hne
    · exact ⟨as, t, by rw [h, List.concat_eq_append]⟩
  -- the K-frame package
  obtain ⟨hK, -⟩ := h.hK ρ' as t hsp
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hsp
  have hσ : σ = cons t (consList (as₀ ++ is) ρ') := by
    rw [← hσ0, consList_append, consList_cons, consList_nil]
  have hfr : RecFrameS 1 (consList (as₀ ++ is) ρ') σ := by
    show shiftE 1 0 σ = _
    rw [hσ, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have hfrP := frP_block (Fss := Fss) (Ids := Ids) (ρb := ρ') hl₀ hli
  -- the parameter frame satisfies the parameters
  have hsatP : Sat2 V (((rds.take nP).map (·.2.2)).reverse) (consList (as₀.take nP) ρ') := by
    have hpre := spineFit_prefix (as := as₀.take nP) (bs := as₀.drop nP ++ is ++ [t]) (by
      rw [← List.append_assoc, ← List.append_assoc, List.take_append_drop]; exact hsp)
    rw [List.length_take, show min nP as₀.length = nP from by omega, ← List.map_take] at hpre
    have := sat2_of_spineFit (Δ₀ := []) (Sat2_nil V ρ') hpre
    rwa [List.append_nil] at this
  obtain ⟨hv, hE, hEis⟩ := hvFss _ hsatP
  have hsh : shiftE (Ids.length + Fss.length + 1) 0 (consList (as₀ ++ is) ρ') = consList (as₀.take nP) ρ' := by
    have := hfrP; unfold frP at this; rwa [Nat.add_comm Ids.length] at this
  have hv' : SumFieldsValid (consList (as₀ ++ is) ρ')
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) := by
    refine rChains_validV ?_ ?_
    · rw [hsh]; exact hv
    · rw [hsh]
      intro j hj bs hsp' E hE'
      exact hE j (by rw [← hFss]; exact hj) bs hsp' E hE'
  refine fixRecBody_validV hfr hK.hyp hv' ?_
  intro j hj i hi fs hfs E hE'
  rw [hfrP] at hfs ⊢
  exact hEis j (by rw [← hFss]; exact hj) i hi fs hfs E hE'

/-- **The recursor leaf's P currency and membership**, at every frame. -/
theorem fixRecLeafFacts {ℓ w u s nP n nIdx : Nat} {Fss₀ Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))}
    {rds : List (Nat × Nat × AVExpr)}
    (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss tlss Eiss rds s)
    (hFss : Fss.length = n) (hIds : Ids.length = nIdx)
    (okΓ : ∀ i, i < nP + n + nIdx + 2 → ∀ ρ : Nat → V,
      Sat2 V ((((rds.map (·.2.2)).reverse)).drop (nP + n + nIdx + 2 - i)) ρ →
      AnnotOkP V ρ ((((rds.map (·.2.2)).reverse)).getD (nP + n + nIdx + 2 - 1 - i) default))
    (hokTyV : ∀ ρ : Nat → V, AnnotValidV V ρ (mkPisAV rds (recConcAV n nIdx)))
    (hvFss : ∀ ρp : Nat → V, Sat2 V (((rds.take nP).map (·.2.2)).reverse) ρp →
      SumFieldsValid ρp Fss ∧
      (∀ j, j < n → ∀ bs : List V, SpineFit ρp (Fss.getD j []) bs →
        ∀ E ∈ Ess.getD j [], AnnotValidV V (consList bs ρp) E) ∧
      (∀ j, j < n → ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
        ∀ fs : List V, SpineFit ρp (Fss.getD j []) fs →
        ∀ E ∈ (Eiss.getD j []).getD i [], AnnotValidV V (consList (fs.take i) ρp) E)) :
    ∀ ρ : Nat → V,
      AnnotOkP V ρ (directFixRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s) ∧
      interp2 V ρ (directFixRecAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
        ∈ˢ interp2 V ρ (mkPisAV rds (recConcAV n nIdx)) := by
  intro ρ
  have hlenR : rds.length = nP + n + nIdx + 2 := by have := h.hlen; omega
  have hΓlen : (((rds.map (·.2.2)).reverse)).length = nP + n + nIdx + 2 := by
    rw [List.length_reverse, List.length_map, hlenR]
  have hmem := directFixRecAVI_mem h ρ
  rw [hFss, hIds] at hmem
  refine ⟨⟨directFixRecAVI_ok2 h ρ, ?_⟩, hmem⟩
  -- validity: the tower's validity under every function value
  have hent : ∀ i, i < nP + n + nIdx + 2 → ∃ q, rds[i]? = some q ∧
      q.2.2 = (((rds.map (·.2.2)).reverse)).getD (nP + n + nIdx + 2 - 1 - i) default := by
    intro i hi
    have hil : i < rds.length := by omega
    exact ⟨_, List.getElem?_eq_getElem hil,
      by rw [getD_reverse_of_peel hlenR hi (List.getElem?_eq_getElem hil)]⟩
  have hwalk : ∀ ρ' : Nat → V,
      UnderTowerValid ρ' (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) rds := by
    intro ρ'
    have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds' => UnderTowerValid ρ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss tlss Eiss) ds')
      hΓlen hlenR hent okΓ
      (fun σ hσ => fixRecBodyValid_of_sat h hFss hIds hvFss σ hσ)
      (fun ρ d ds' _ hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ' (by
        rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hΓlen]; exact Nat.le_refl _)]
        exact Sat2_nil V ρ')
    rw [List.drop_zero] at hw
    exact hw
  show AnnotValidV V ρ (fixSelAVI ℓ w nP Fss Ess Ids rss tlss Eiss rds s)
  refine fixSelAVI_validV ?_ fun r _ => hwalk (cons r ρ)
  show AnnotValidV V ρ (mkPisAV rds (recConcAV Fss.length Ids.length))
  rw [hFss, hIds]
  exact hokTyV ρ

end Lech.SetP
