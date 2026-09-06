import Lech.SetP.Direct.DirectRecLamP

/-!
# The recursor rule's kit (task #175 W4c, P3 module 6, part 16)

Syntactic and semantic pieces of the recursor rule's law: the
`checkDefEqList` pins indexed, the rule's λ-peel residual as the
body's instantiation sequence and its value (the minor applied to the
fields), a `TeleFitPA` fit's chain memberships as a `SpineFit`, the
constructor's level assignment agreeing with the recursor's on the
block's parameters, and the minor value at a zero elimination level.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The frame values (from the retired `DirectRecLawFitsP`, task #175 S2) -/

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

/-! ## Fits as spines -/

/-- A fit's chain memberships are a `SpineFit` (the values read at the
fit's own frame `ρ`, the domains walked from `σ`). -/
theorem spineFit_of_chain' :
    ∀ {Ds : List AVExpr} {ws : List AVExpr} {σ ρ : Nat → V},
      ws.length = Ds.length →
      (∀ n, n < Ds.length →
        interp2 V ρ (ws.getD n default)
          ∈ˢ interp2 V (consN ((ws.take n).map (interp2 V ρ)) σ)
            (Ds.reverse.getD (Ds.length - 1 - n) default)) →
      SpineFit σ Ds (ws.map (interp2 V ρ))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | D :: Ds, w :: ws, σ, ρ, hlen, hmem => by
    simp only [List.map_cons, SpineFit]
    have h0 := hmem 0 (by simp)
    simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.length_cons,
      Nat.add_sub_cancel, Nat.sub_zero] at h0
    rw [List.getD_eq_getElem?_getD, List.reverse_cons, List.getElem?_append_right (by simp),
      List.length_reverse, Nat.sub_self] at h0
    refine ⟨h0, ?_⟩
    refine spineFit_of_chain' (by simpa using hlen) ?_
    intro n hn
    have := hmem (n + 1) (by simp; omega)
    simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.length_cons] at this
    rw [List.reverse_cons] at this
    rw [List.getD_eq_getElem?_getD (l := Ds.reverse ++ [D]),
      List.getElem?_append_left (by simp; omega),
      show Ds.length + 1 - 1 - (n + 1) = Ds.length - 1 - n from by omega,
      ← List.getD_eq_getElem?_getD] at this
    exact this

theorem spineFit_of_chain {Ds : List AVExpr} {ws : List AVExpr} {ρ : Nat → V}
    (hlen : ws.length = Ds.length)
    (hmem : ∀ n, n < Ds.length →
      interp2 V ρ (ws.getD n default)
        ∈ˢ interp2 V (chainP V ρ (ws.take n)) (Ds.reverse.getD (Ds.length - 1 - n) default)) :
    SpineFit ρ Ds (ws.map (interp2 V ρ)) :=
  spineFit_of_chain' hlen hmem

/-! ## Level assignments -/

/-- The constructor's level assignment, fixed by the recursor's through
`recFireComparands`, agrees with the recursor's on the block's
parameters. -/
theorem substFn_agree_of_comparand {lps lpsR : List Name} {us usj : List Level}
    (hψ : Level.substFn φ lps usj
      = Level.substFn φ lps (lps.map fun q => Level.subst lpsR us (.param q))) :
    ∀ q ∈ lps, Level.substFn φ lps usj q = Level.substFn φ lpsR us q := by
  intro q hq
  rw [congrFun hψ q]
  have hmap : (lps.map fun q => Level.subst lpsR us (.param q))
      = (lps.map Level.param).map (Level.subst lpsR us) := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, Level.substFn_map_subst (by simp) hq, Level.substFn_map_param]

/-! ## The minor at a zero elimination level -/

/-- At a zero elimination level the minor value is the point: the minor
space is a truth value (the motive's applications are). -/
theorem minor_pt_of_zero {ℓ w : Nat} {M m : V} {Fs : List AVExpr} {ρp : Nat → V} {A : V}
    (h0 : ℓ = 0) (hM : M ∈ˢ piR (ℓ + 1) A (fun _ => (univ ℓ : V)))
    (hm : m ∈ˢ minorSp ℓ w M Fs ρp []) : m = pt := by
  have hM0 : ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V) := by
    intro y
    by_cases hy : y ∈ˢ A
    · have hmem := app_mem_piR_pos (Nat.succ_ne_zero ℓ) hM hy
      rw [h0, univ_zero] at hmem
      exact hmem
    · rw [(mem_piR_pos (Nat.succ_ne_zero ℓ) hM).2.2.1 y hy, ← univ_zero]
      exact empty_mem_univ 0
  exact eq_pt_of_mem_univZero (minorSp_zero_univZero h0 hM0 Fs ρp []) hm

end Lech.SetP
