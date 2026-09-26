module

public import ConLeche.Model.Inductives.StructRecSpine
public section

/-!
# The recursor's frame kit, continued (task #175 W4c, P3 module 6, part 9)

Openings at any depth, per-index scoping of an opening's variables and
of an `instPisAt` residual, frame shifts under a consed spine,
application scoping, the identification of two contexts from entry-wise
agreement (`frameIdent`), the minor space as a Π-tower reading
(`interp_minorSp_of_tele`), and list arithmetic.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Openings at any depth -/

theorem openPisAtFvars_of_stripPis_isSome :
    ∀ (n : Nat) {e : Expr} (d : Nat), (Expr.stripPis n e).isSome = true →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, e, _, _ => ⟨[], e, rfl⟩
  | n + 1, e, d, h => by
    match e, h with
    | .forallE dom body mb, h =>
      simp only [Expr.stripPis, Option.isSome_map] at h
      obtain ⟨fvs, o, ho⟩ := openPisAtFvars_of_stripPis_isSome n (d + 1)
        (Expr.stripPis_instantiate1_isSome (v := .fvar d dom) n 0 h)
      exact ⟨.fvar d dom :: fvs, o, by simp only [openPisAtFvars, ho]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [Expr.stripPis] at h

/-! ## Per-index scoping -/

/-- Each opened variable's annotation is scoped at its own depth. -/
theorem openPisAtFvars_typeWScoped :
    ∀ (n : Nat) {e : Expr} {d : Nat} {fvs : List Expr} {o : Expr},
      openPisAtFvars n e d = some (fvs, o) → Expr.WScoped d e →
      ∀ (i : Nat) (x : Expr), fvs[i]? = some x → Expr.WScoped (d + i) (Expr.fvarTypeD x)
  | 0, _, _, _, _, hop, _, i, x, hx => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact nomatch hx
  | n + 1, e, d, fvs, o, hop, hw, i, x, hx => by
    match e, hop with
    | .forallE dom body mb, hop =>
      simp only [openPisAtFvars] at hop
      split at hop
      · next fvs' o' hop' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hw' : Expr.WScoped d dom ∧ Expr.WScoped d body := by
          simpa only [Expr.WScoped] using hw
        cases i with
        | zero =>
          obtain rfl : Expr.fvar d dom = x := by simpa using hx
          show Expr.WScoped (d + 0) dom
          rw [Nat.add_zero]; exact hw'.1
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          have hb : Expr.WScoped (d + 1) (body.instantiate1 (.fvar d dom)) :=
            Expr.WScoped.instantiate1_gen (v := .fvar d dom) (d := d + 1)
              (by simp only [Expr.WScoped]; exact ⟨by omega, hw'.1⟩) 0
              (Expr.WScoped.mono (by omega) hw'.2)
          have := openPisAtFvars_typeWScoped n hop' hb i x hx
          rw [show d + (i + 1) = d + 1 + i from by omega]
          exact this
      · exact nomatch hop
    | .bvar _, hop | .fvar _ _, hop | .sort _, hop | .const _ _, hop | .app _ _, hop
    | .lam _ _ _, hop | .letE _ _ _, hop | .lit _, hop | .proj _ _ _, hop =>
      simp [openPisAtFvars] at hop

/-! ## Frame shifts under a consed spine -/

omit [SetTheory V] in
theorem shiftE_cons_succ' (n k : Nat) (a : V) (σ : Nat → V) :
    shiftE n (k + 1) (cons a σ) = cons a (shiftE n k σ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ i =>
    simp only [shiftE, cons_succ]
    by_cases h : i < k
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, show i + 1 + n = i + n + 1 from by omega, cons_succ]

/-! ## List arithmetic -/

theorem mkPisAV_append :
    ∀ (l₁ l₂ : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      mkPisAV (l₁ ++ l₂) b = mkPisAV l₁ (mkPisAV l₂ b)
  | [], _, _ => rfl
  | d :: l₁, l₂, b => by simp [mkPisAV, mkPisAV_append l₁ l₂ b]

/-! ## Lifted domains, field spines, and frame arithmetic (from the retired
`StructRecMinorP`, task #175 S2) -/

theorem liftDoms_take (n : Nat) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (k j : Nat),
      (liftDoms n k ds).take j = liftDoms n k (ds.take j)
  | [], _, _ => by simp [liftDoms]
  | _ :: ds, k, 0 => rfl
  | _ :: ds, k, j + 1 => by
    simp only [liftDoms, List.take_succ_cons, liftDoms_take n ds (k + 1) j]

/-- A fit of lifted domains is a fit of the domains at the shifted
frame. -/
theorem spineFit_liftDoms (n : Nat) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {k : Nat} {σ : Nat → V} {as : List V},
      SpineFit σ ((liftDoms n k ds).map (·.2.2)) as ↔
        SpineFit (shiftE n k σ) (ds.map (·.2.2)) as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | d :: ds, k, σ, a :: as => by
    simp only [liftDoms, List.map_cons, SpineFit, interp_liftN]
    rw [← shiftE_cons_succ']
    exact and_congr Iff.rfl (spineFit_liftDoms n)

theorem spineFit_append_inv :
    ∀ {Ds₁ Ds₂ : List AnnotTerm} {ρ : Nat → V} {as : List V},
      SpineFit ρ (Ds₁ ++ Ds₂) as →
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂
  | [], _, ρ, as, h => ⟨[], as, rfl, trivial, h⟩
  | _ :: _, _, _, [], h => h.elim
  | D :: Ds₁, Ds₂, ρ, a :: as, h => by
    obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_inv (Ds₁ := Ds₁) h.2
    exact ⟨a :: as₁, as₂, rfl, ⟨h.1, h1⟩, h2⟩

omit [SetTheory V] in
/-- A consed spine's entries below its length are the spine's, from the
top. -/
theorem consList_apply_lt :
    ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
      consList as σ k = (as[as.length - 1 - k]?).getD (σ 0)
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with h | h
    · rw [consList_apply_lt as (cons a σ) k h, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega,
        List.getElem?_cons_succ, List.getElem?_eq_getElem (by omega), Option.getD_some,
        Option.getD_some]
    · obtain rfl : k = as.length := by simp at hk; omega
      have := consList_apply_add as (cons a σ) 0
      rw [Nat.zero_add] at this
      rw [this, List.length_cons, show as.length + 1 - 1 - as.length = 0 from by omega,
        List.getElem?_cons_zero, Option.getD_some, cons_zero]

end ConLeche.Model
