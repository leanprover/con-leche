import Setlec.SetP.Direct.DirectRecLamP

/-!
# The recursor rule's kit (task #175 W4c, P3 module 6, part 16)

Syntactic and semantic pieces of the recursor rule's law: the
`checkDefEqList` pins indexed, the rule's λ-peel residual as the
body's instantiation sequence and its value (the minor applied to the
fields), a `TeleFitPA` fit's chain memberships as a `SpineFit`, the
constructor's level assignment agreeing with the recursor's on the
block's parameters, and the minor value at a zero elimination level.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## The pins, indexed -/

theorem defEqListOk_index {F d : Nat} :
    ∀ {as bs : List Expr}, Setlec.DefEqListOk μ F env d as bs →
      ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        Setlec.isDefEqCore μ env F d a b = .ok true
  | [], [], _, _, _, _, ha, _ => nomatch ha
  | [], _ :: _, h, _, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _, _ => h.elim
  | a₀ :: as, b₀ :: bs, h, i, a, b, ha, hb => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
      subst ha hb
      exact h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha hb
      exact defEqListOk_index h.2 i a b ha hb

/-! ## The rule's residual -/

/-- The λ-peel's residual at a spine is the stripped body's
instantiation sequence. -/
theorem instLamsAt_rest_of_stripLams :
    ∀ (sp : List Expr) {e : Expr} {bs : List (Name × Expr × BinderMeta)} {body : Expr}
      {ds : List Expr} {rest : Expr},
      e.stripLams sp.length = some (bs, body) →
      Expr.instLamsAt sp e = some (ds, rest) →
      rest = Expr.instSeq sp (sp.length - 1) body
  | [], e, bs, body, ds, rest, hst, h => by
    simp only [List.length_nil, Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hst
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := hst
    obtain ⟨-, rfl⟩ := h
    rfl
  | a :: sp, e, bs, body, ds, rest, hst, h => by
    match e, hst, h with
    | .lam nm dom b mb, hst, h =>
      simp only [List.length_cons, Expr.stripLams] at hst
      cases hst' : Expr.stripLams sp.length b with
      | none => rw [hst'] at hst; exact nomatch hst
      | some q =>
        obtain ⟨bs', body'⟩ := q
        rw [hst'] at hst
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨-, rfl⟩ := hst
        simp only [Expr.instLamsAt] at h
        cases h1 : Expr.instLamsAt sp (b.instantiate1 a) with
        | none => rw [h1] at h; exact nomatch h
        | some q' =>
          obtain ⟨ds', rest'⟩ := q'
          rw [h1] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          -- the instantiated body's peel
          have hsome := Expr.stripLams_instantiate1_isSome (v := a) sp.length (e := b) 0
            (by rw [hst']; rfl)
          obtain ⟨⟨bs'', body''⟩, hst''⟩ := Option.isSome_iff_exists.mp hsome
          obtain ⟨hb, -⟩ := Expr.stripLams_instantiate1_eq (v := a) sp.length 0 hst' hst''
          rw [Nat.zero_add] at hb
          have := instLamsAt_rest_of_stripLams sp hst'' h1
          rw [this, hb]
          simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSeq]
    | .bvar _, hst, _ | .fvar _ _ _, hst, _ | .sort _, hst, _ | .const _ _, hst, _
    | .app _ _, hst, _ | .forallE _ _ _ _, hst, _ | .letE _ _ _ _, hst, _
    | .lit _, hst, _ | .proj _ _ _, hst, _ =>
      simp [Expr.stripLams] at hst

/-- The rule body's instantiation sequence: the minor variable applied
to the field variables. -/
theorem instSeq_directRuleBody {nP nF : Nat} {fvsP xFvs : List Expr}
    (hlenP : fvsP.length = nP + 2) (hlenX : xFvs.length = nF)
    (hbP : ∀ a ∈ fvsP, a.looseBVarsBounded 0 = true)
    (hbX : ∀ a ∈ xFvs, a.looseBVarsBounded 0 = true) :
    Expr.instSeq (fvsP ++ xFvs) (nP + 1 + nF) (Setlec.directRuleBody nF)
      = Expr.mkAppN (fvsP.getD (nP + 1) default) xFvs := by
  have hb : ∀ a ∈ fvsP ++ xFvs, a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hbP a h
    · exact hbX a h
  have hlen : (fvsP ++ xFvs).length = nP + 2 + nF := by
    rw [List.length_append, hlenP, hlenX]
  unfold Setlec.directRuleBody
  rw [Expr.instSeq_mkAppN]
  congr 1
  · have := Expr.instSeq_bvar (fvsP ++ xFvs) (nP + 1 + nF) nF hb (by omega) (by omega)
    rw [show nP + 1 + nF - nF = nP + 1 from by omega,
      List.getElem?_append_left (by omega)] at this
    rw [List.getD_eq_getElem?_getD, this]
    rfl
  · apply List.ext_getElem
    · simp [hlenX]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have hi : i < nF := by simpa using h1
      have := Expr.instSeq_bvar (fvsP ++ xFvs) (nP + 1 + nF) (nF - 1 - i) hb (by omega)
        (by omega)
      rw [show nP + 1 + nF - (nF - 1 - i) = nP + 2 + i from by omega,
        List.getElem?_append_right (by omega), hlenP,
        show nP + 2 + i - (nP + 2) = i from by omega, List.getElem?_eq_getElem h2] at this
      exact (Option.some.inj this).symm

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

end Setlec.SetP
