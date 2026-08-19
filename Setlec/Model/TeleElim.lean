import Setlec.Model.InterpLemmas
import Setlec.Model.AnnotOkLemmas
import Setlec.Model.Subst

/-!
# Eliminating an interpreted `∀`-telescope along a value spine

A checked theorem's statement is a `∀`-telescope over an equation; its
(interpreted) inhabitant, applied along values that fit the telescope's
domains, lands in the interpretation of the fully instantiated body.
With an equation body this yields value-level equalities — the engine
that turns the preprocessor's checked `iota` theorems into the fold
facts the environment invariant demands.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}
variable {cval : ConstVal V}

open SetTheory Expr

/-- Values fitting an opened `∀`-telescope: each value is a member of
the interpretation of the corresponding (progressively instantiated)
domain; `d'`, `ρ'`, `rest` describe the fully opened residual body. -/
inductive TeleFit (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → Expr → List V → Nat → (Nat → V) → Expr → Prop
  | nil {d ρ e} : TeleFit cval env φ d ρ e [] d ρ e
  | cons {d ρ n ty body m x xs d' ρ' rest A} :
      interpExpr V cval env φ d ρ ty = some A →
      x ∈ˢ A →
      TeleFit cval env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty)) xs d' ρ' rest →
      TeleFit cval env φ d ρ (.forallE n ty body m) (x :: xs) d' ρ' rest

/-- Stepping an inhabitant of an interpreted telescope through fitting
values: the applied value inhabits the interpreted residual body, which
stays annotation-truthful. -/
theorem TeleFit.elim :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {xs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit cval env φ d ρ e xs d' ρ' rest →
      ∀ {v P : V}, AnnotOk V cval env φ d ρ e →
        interpExpr V cval env φ d ρ e = some P → v ∈ˢ P →
        ∃ Q, interpExpr V cval env φ d' ρ' rest = some Q ∧
          SpineFold V v xs ∈ˢ Q ∧ AnnotOk V cval env φ d' ρ' rest := by
  intro d ρ e xs d' ρ' rest ht
  induction ht with
  | nil =>
    intro v P hA hi hv
    exact ⟨P, hi, hv, hA⟩
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx ht ih =>
    intro v P hA hi hv
    simp only [AnnotOk] at hA
    obtain ⟨haty, ⟨cod, hcod⟩, hcond⟩ := hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hity hx
    -- the interpreted ∀ is a pi over the interpreted domain
    rw [interpExpr, hcod, hity] at hi
    dsimp only at hi
    obtain rfl := Option.some.inj hi
    -- fibres are inhabited interpretations in the cod universe
    have hfib : ∀ y, y ∈ˢ A →
        ((interpExpr V cval env φ (d + 1) (updV V ρ d y)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
          univ (cod.eval φ) := by
      intro y hy
      obtain ⟨-, hwfact'⟩ := hcond y A hity hy
      obtain ⟨w, hwi, hwu⟩ := hwfact' cod hcod
      rw [hwi]
      exact hwu
    have happ := app_mem hv hx hfib
    obtain ⟨w, hwi, hwu⟩ := hwfact cod hcod
    rw [hwi] at happ
    simp only [Option.getD_some] at happ
    obtain ⟨Q, hQ, hmem, hA'⟩ := ih hbody hwi happ
    exact ⟨Q, hQ, by
      rw [show SpineFold V v (x :: xs) =
        SpineFold V (SetTheory.app v x) xs from rfl]
      exact hmem, hA'⟩

/-- Values fitting a `∀`-telescope along an *expression* spine: each
argument expression interprets to a member of the corresponding domain,
and the telescope is instantiated one argument at a time (mirroring the
iota certificates' walk).  The last index is the fully instantiated
residual body. -/
inductive TeleFitI (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : Expr → List Expr → List V → Expr → Prop
  | nil {e} : TeleFitI cval env φ d ρ e [] [] e
  | cons {n ty body m arg args x xs A rest} :
      interpExpr V cval env φ d ρ ty = some A →
      interpExpr V cval env φ d ρ arg = some x →
      x ∈ˢ A →
      fvarsBelow d body →
      WScoped d arg →
      arg.looseBVarsBounded 0 = true →
      AnnotOk V cval env φ d ρ arg →
      TeleFitI cval env φ d ρ (body.instantiate1 arg) args xs rest →
      TeleFitI cval env φ d ρ (.forallE n ty body m) (arg :: args) (x :: xs)
        rest

/-- Stepping an inhabitant of an interpreted telescope through an
expression-spine fit: the applied value inhabits the interpretation of
the fully instantiated residual, which stays annotation-truthful.
Each step is one `interp_beta` bridge — no depth relocation. -/
theorem TeleFitI.elim :
    ∀ {e rest : Expr} {args : List Expr} {xs : List V},
      TeleFitI cval env φ d ρ e args xs rest →
      ∀ {v P : V}, AnnotOk V cval env φ d ρ e →
        interpExpr V cval env φ d ρ e = some P → v ∈ˢ P →
        ∃ Q, interpExpr V cval env φ d ρ rest = some Q ∧
          SpineFold V v xs ∈ˢ Q ∧ AnnotOk V cval env φ d ρ rest := by
  intro e rest args xs ht
  induction ht with
  | nil =>
    intro v P hA hi hv
    exact ⟨P, hi, hv, hA⟩
  | @cons n ty body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro v P hA hi hv
    simp only [AnnotOk] at hA
    obtain ⟨haty, ⟨cod, hcod⟩, hcond⟩ := hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hity hx
    rw [interpExpr, hcod, hity] at hi
    dsimp only at hi
    obtain rfl := Option.some.inj hi
    have hfib : ∀ y, y ∈ˢ A →
        ((interpExpr V cval env φ (d + 1) (updV V ρ d y)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
          univ (cod.eval φ) := by
      intro y hy
      obtain ⟨-, hwfact'⟩ := hcond y A hity hy
      obtain ⟨w, hwi, hwu⟩ := hwfact' cod hcod
      rw [hwi]
      exact hwu
    have happ := app_mem hv hx hfib
    obtain ⟨w, hwi, hwu⟩ := hwfact cod hcod
    rw [hwi] at happ
    simp only [Option.getD_some] at happ
    -- bridge the opened body back to the instantiated one
    have hibeta : interpExpr V cval env φ d ρ (body.instantiate1 arg) =
        some w := by
      rw [interp_beta (n := n) (ty := ty) hfb hwa hba hiarg 0]
      exact hwi
    have hAbeta : AnnotOk V cval env φ d ρ (body.instantiate1 arg) :=
      AnnotOk_beta hfb hwa hba hiarg hAa 0 hbody
    obtain ⟨Q, hQ, hmem, hA'⟩ := ih hAbeta hibeta happ
    exact ⟨Q, hQ, by
      rw [show SpineFold V v (x :: xs) =
        SpineFold V (SetTheory.app v x) xs from rfl]
      exact hmem, hA'⟩

/-- Weakening an expression-spine fit: a fit over `p`-scoped data holds
at any depth `≥ p` under any valuation agreeing below `p`. -/
theorem TeleFitI.lift {p : Nat} {ρ : Nat → V} :
    ∀ {e : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI cval env φ p ρ e args vs rest →
      WScoped p e →
      ∀ {D : Nat} {ρ2 : Nat → V}, p ≤ D → (∀ i, i < p → ρ2 i = ρ i) →
      TeleFitI cval env φ D ρ2 e args vs rest := by
  intro e args vs rest ht
  induction ht with
  | nil => intro _ D ρ2 _ _; exact TeleFitI.nil
  | @cons n ty body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro hwe D ρ2 hpD hag
    have hwe' : WScoped p ty ∧ WScoped p body := by simpa [WScoped] using hwe
    refine TeleFitI.cons ?_ ?_ hx (fvarsBelow_mono hpD hfb)
      (hwa.mono hpD) hba
      (AnnotOk.lift hwa D hpD ρ ρ2 hag hAa)
      (ih (WScoped.instantiate1_gen hwa 0 hwe'.2) hpD hag)
    · rw [interp_lift hwe'.1 D hpD ρ ρ2 hag]
      exact hity
    · rw [interp_lift hwa D hpD ρ ρ2 hag]
      exact hiarg

/-- Swapping an instantiation argument for an interp-equal one inside
an expression-spine fit (both closed and `d`-scoped): every interp fact
transfers through a double `interp_beta` bridge, and the walk\'s
substitutions are re-associated with `instantiate1_instantiate1`. -/
theorem TeleFitI.arg_swap {d : Nat} {ρ : Nat → V} {a₁ a₂ : Expr} {xv : V}
    (hwa₁ : WScoped d a₁) (hba₁ : a₁.looseBVarsBounded 0 = true)
    (hwa₂ : WScoped d a₂) (hba₂ : a₂.looseBVarsBounded 0 = true)
    (hia₁ : interpExpr V cval env φ d ρ a₁ = some xv)
    (hia₂ : interpExpr V cval env φ d ρ a₂ = some xv) :
    ∀ {args : List Expr} {body : Expr} {k : Nat} {vs : List V} {rest : Expr},
      TeleFitI cval env φ d ρ (body.instantiate1 a₁ k) args vs rest →
      Expr.fvarsBelow d body →
      (body.stripPis args.length).isSome →
      ∃ rest2, TeleFitI cval env φ d ρ (body.instantiate1 a₂ k) args vs rest2
  | [], body, k, vs, rest, hfit, hfb, harity => by
    generalize body.instantiate1 a₁ k = e at hfit
    cases hfit with
    | nil => exact ⟨body.instantiate1 a₂ k, TeleFitI.nil⟩
  | arg :: args, body, k, vs, rest, hfit, hfb, harity => by
    obtain ⟨n, ty₀, b₀, m₀, rfl⟩ :
        ∃ n ty₀ b₀ m₀, body = .forallE n ty₀ b₀ m₀ := by
      match body, harity with
      | .forallE n ty₀ b₀ m₀, _ => exact ⟨n, ty₀, b₀, m₀, rfl⟩
    simp only [Expr.instantiate1] at hfit
    have hfb' : Expr.fvarsBelow d ty₀ ∧ Expr.fvarsBelow d b₀ := by
      simpa [Expr.fvarsBelow] using hfb
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have hity₂ : interpExpr V cval env φ d ρ (ty₀.instantiate1 a₂ k) =
        some A := by
      rw [interp_beta (n := .anonymous) (ty := .sort .zero) hfb'.1 hwa₂ hba₂
        hia₂ k]
      rw [← interp_beta (n := .anonymous) (ty := .sort .zero) hfb'.1 hwa₁ hba₁
        hia₁ k]
      exact hity
    have hsub' : TeleFitI cval env φ d ρ
        ((b₀.instantiate1 arg).instantiate1 a₁ k) args xs rest := by
      rw [instantiate1_instantiate1 hba₁ hbarg b₀ 0 k (Nat.zero_le k)] at hsub
      exact hsub
    have hfbsub : Expr.fvarsBelow d (b₀.instantiate1 arg) :=
      fvarsBelow_instantiate1_gen hwarg.fvarsBelow 0 hfb'.2
    have harity' : ((b₀.instantiate1 arg).stripPis args.length).isSome := by
      simp only [List.length_cons, Expr.stripPis, Option.isSome_map] at harity
      exact stripPis_instantiate1_isSome args.length 0 harity
    obtain ⟨rest2, hsw⟩ := TeleFitI.arg_swap hwa₁ hba₁ hwa₂ hba₂ hia₁ hia₂
      hsub' hfbsub harity'
    have hsw' : TeleFitI cval env φ d ρ
        ((b₀.instantiate1 a₂ (k + 1)).instantiate1 arg) args xs rest2 := by
      rw [instantiate1_instantiate1 hba₂ hbarg b₀ 0 k (Nat.zero_le k)]
      exact hsw
    refine ⟨rest2, ?_⟩
    simp only [Expr.instantiate1]
    exact TeleFitI.cons hity₂ hiarg hx
      (fvarsBelow_instantiate1_gen hwa₂.fvarsBelow (k + 1) hfb'.2)
      hwarg hbarg hAarg hsw'

/-- An expression-spine fit of a genuine `∀`-telescope yields a
value-spine fit: each instantiation argument is exchanged for the
opening variable (which interprets to the same value). -/
theorem TeleFitI.toTeleFit {d : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {ty : Expr} {vs : List V} {rest : Expr},
      TeleFitI cval env φ d ρ ty args vs rest →
      WScoped d ty →
      (ty.stripPis args.length).isSome →
      ∃ d2 ρ2 rest2, TeleFit cval env φ d ρ ty vs d2 ρ2 rest2
  | [], ty, vs, rest, hfit, hwty, harity => by
    cases hfit with
    | nil => exact ⟨d, ρ, ty, TeleFit.nil⟩
  | arg :: args, ty, vs, rest, hfit, hwty, harity => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty = .forallE n dom body m := by
      match ty, harity with
      | .forallE n dom body m, _ => exact ⟨n, dom, body, m, rfl⟩
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have hwty' : WScoped d dom ∧ WScoped d body := by simpa [WScoped] using hwty
    have hagub : ∀ i, i < d → updV V ρ d x i = ρ i := fun i hi => by
      simp only [updV]; rw [if_neg (by omega)]
    have hsub1 : TeleFitI cval env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 arg) args xs rest :=
      TeleFitI.lift hsub (WScoped.instantiate1_gen hwarg 0 hwty'.2)
        (Nat.le_succ d) hagub
    have hiarg1 : interpExpr V cval env φ (d + 1) (updV V ρ d x) arg =
        some x := by
      rw [interp_lift hwarg (d + 1) (Nat.le_succ d) ρ (updV V ρ d x) hagub]
      exact hiarg
    have hifv : interpExpr V cval env φ (d + 1) (updV V ρ d x)
        (.fvar d n dom) = some x := by
      simp [interpExpr, updV]
    have hwfv : WScoped (d + 1) (Expr.fvar d n dom) := by
      simp only [WScoped]
      exact ⟨Nat.lt_succ_self d, hwty'.1⟩
    have harity' : (body.stripPis args.length).isSome := by
      simpa [List.length_cons, Expr.stripPis, Option.isSome_map] using harity
    obtain ⟨rest2, hsw⟩ := TeleFitI.arg_swap (hwarg.mono (Nat.le_succ d))
      hbarg hwfv rfl hiarg1 hifv (k := 0) hsub1
      (fvarsBelow_mono (Nat.le_succ d) hwty'.2.fvarsBelow) harity'
    obtain ⟨d2, ρ2, rest3, hfit'⟩ := TeleFitI.toTeleFit hsw
      (WScoped.instantiate1_gen hwfv 0 (hwty'.2.mono (Nat.le_succ d)))
      (stripPis_instantiate1_isSome args.length 0 harity')
    exact ⟨d2, ρ2, rest3, TeleFit.cons hity hx hfit'⟩

end Setlec
