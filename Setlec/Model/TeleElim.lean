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

/-- Stepping an inhabitant of an interpreted telescope through fitting
values: the applied value inhabits the interpreted residual body, which
stays annotation-truthful. -/
theorem TeleFit.elim :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {xs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e xs d' ρ' rest →
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

/-- Stepping an inhabitant of an interpreted telescope through an
expression-spine fit: the applied value inhabits the interpretation of
the fully instantiated residual, which stays annotation-truthful.
Each step is one `interp_beta` bridge — no depth relocation. -/
theorem TeleFitI.elim :
    ∀ {e rest : Expr} {args : List Expr} {xs : List V},
      TeleFitI V cval env φ d ρ e args xs rest →
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

/-- Shrinking a value-spine fit past one fresh constant and back to an
agreeing valuation: the fit's expressions live entirely in the old
environment. -/
theorem TeleFit.env_shrink {c₀ : ConstantInfo} {env : Env}
    {val' cval : ConstVal V}
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ' : Name → Nat,
      val' n ψ' = cval n ψ') :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V val' (⟨c₀ :: env.consts⟩ : Env) φ d ρ e vs d' ρ' rest →
      e.constsResolve env = true →
      TeleFit V cval env φ d ρ e vs d' ρ' rest := by
  intro d ρ e vs d' ρ' rest ht
  induction ht with
  | nil => intro _; exact TeleFit.nil
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx ht ih =>
    intro hres
    have hres' : ty.constsResolve env = true ∧
        body.constsResolve env = true := by
      simpa [Expr.constsResolve] using hres
    refine TeleFit.cons ?_ hx
      (ih (Expr.constsResolve_instantiate1 hres'.1 0 hres'.2))
    have h1 : interpExpr V val' env φ d ρ ty = some A := by
      rw [← interp_mono (cval := val') hfresh ty d ρ hres'.1]
      exact hity
    rw [← interp_cval_ext hagree ty d ρ]
    exact h1

/-- Weakening an expression-spine fit: a fit over `p`-scoped data holds
at any depth `≥ p` under any valuation agreeing below `p`. -/
theorem TeleFitI.lift {p : Nat} {ρ : Nat → V} :
    ∀ {e : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ p ρ e args vs rest →
      WScoped p e →
      ∀ {D : Nat} {ρ2 : Nat → V}, p ≤ D → (∀ i, i < p → ρ2 i = ρ i) →
      TeleFitI V cval env φ D ρ2 e args vs rest := by
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
      TeleFitI V cval env φ d ρ (body.instantiate1 a₁ k) args vs rest →
      Expr.fvarsBelow d body →
      (body.stripPis args.length).isSome →
      ∃ rest2, TeleFitI V cval env φ d ρ (body.instantiate1 a₂ k) args vs rest2
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
    have hsub' : TeleFitI V cval env φ d ρ
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
    have hsw' : TeleFitI V cval env φ d ρ
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
      TeleFitI V cval env φ d ρ ty args vs rest →
      WScoped d ty →
      (ty.stripPis args.length).isSome →
      ∃ d2 ρ2 rest2, TeleFit V cval env φ d ρ ty vs d2 ρ2 rest2
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
    have hsub1 : TeleFitI V cval env φ (d + 1) (updV V ρ d x)
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

/-- Values fitting a λ-tower along an expression spine (mirror of
`TeleFitI` on the term side); the last index is the fully
instantiated body. -/
inductive TeleFitLam (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : Expr → List Expr → List V → Expr → Prop
  | nil {e} : TeleFitLam cval env φ d ρ e [] [] e
  | cons {n ty body m arg args x xs A rest} :
      interpExpr V cval env φ d ρ ty = some A →
      interpExpr V cval env φ d ρ arg = some x →
      x ∈ˢ A →
      Expr.fvarsBelow d body →
      WScoped d arg →
      arg.looseBVarsBounded 0 = true →
      AnnotOk V cval env φ d ρ arg →
      TeleFitLam cval env φ d ρ (body.instantiate1 arg) args xs rest →
      TeleFitLam cval env φ d ρ (.lam n ty body m) (arg :: args) (x :: xs)
        rest

/-- A type-telescope fit transfers to a λ-tower with the same binder
domains: the walks instantiate the same arguments into syntactically
equal domains. -/
theorem TeleFitI.toLam :
    ∀ {args : List Expr} {ty e : Expr} {vs : List V} {restT : Expr},
      TeleFitI V cval env φ d ρ ty args vs restT →
      Expr.LamPiDomsEq args.length e ty →
      Expr.fvarsBelow d e →
      ∃ restE, TeleFitLam cval env φ d ρ e args vs restE
  | [], ty, e, vs, restT, hfit, hdoms, hfbe => by
    generalize ty = t at hfit
    cases hfit with
    | nil => exact ⟨e, TeleFitLam.nil⟩
  | arg :: args, ty, e, vs, restT, hfit, hdoms, hfbe => by
    obtain ⟨n₁, d₁, b₁, m₁, n₂, d₂, b₂, m₂, rfl, rfl⟩ :
        ∃ n₁ d₁ b₁ m₁ n₂ d₂ b₂ m₂, e = .lam n₁ d₁ b₁ m₁ ∧
          ty = .forallE n₂ d₂ b₂ m₂ := by
      match e, ty, hdoms with
      | .lam n₁ d₁ b₁ m₁, .forallE n₂ d₂ b₂ m₂, _ =>
        exact ⟨n₁, d₁, b₁, m₁, n₂, d₂, b₂, m₂, rfl, rfl⟩
    obtain ⟨hdeq, hdoms'⟩ : d₁ = d₂ ∧ Expr.LamPiDomsEq args.length b₁ b₂ := by
      simpa [Expr.LamPiDomsEq] using hdoms
    subst hdeq
    have hfbe' : Expr.fvarsBelow d d₁ ∧ Expr.fvarsBelow d b₁ := by
      simpa [Expr.fvarsBelow] using hfbe
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨restE, hfitE⟩ := TeleFitI.toLam hsub
      (Expr.LamPiDomsEq.instantiate1 args.length 0 hdoms')
      (fvarsBelow_instantiate1_gen hwarg.fvarsBelow 0 hfbe'.2)
    exact ⟨restE, TeleFitLam.cons hity hiarg hx hfbe'.2 hwarg hbarg hAarg
      hfitE⟩

/-- Folding an interpreted λ-tower over a fitting expression spine:
the result is the interpretation of the fully instantiated body, and
every application stays inside a certified slot.  `app_lam` is
unconditional, so the Prop collapse needs no special treatment. -/
theorem TeleFitLam.fold :
    ∀ {e restE : Expr} {args : List Expr} {vs : List V},
      TeleFitLam cval env φ d ρ e args vs restE →
      AnnotOk V cval env φ d ρ e →
      ∀ {L : V}, interpExpr V cval env φ d ρ e = some L →
      ∃ B, interpExpr V cval env φ d ρ restE = some B ∧
        SpineFold V L vs = B ∧ ChainSlots V L vs := by
  intro e restE args vs ht
  induction ht with
  | nil =>
    intro hA L hi
    exact ⟨L, hi, rfl, trivial⟩
  | @cons n ty body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro hA L hi
    simp only [AnnotOk] at hA
    obtain ⟨hAty, ⟨cod, hcod⟩, hcond⟩ := hA
    rw [interpExpr, hcod, hity] at hi
    dsimp only at hi
    obtain rfl := Option.some.inj hi
    obtain ⟨hbodyA, hwfact⟩ := hcond x A hity hx
    obtain ⟨w, B0, hwi, hwB0, hB0u⟩ := hwfact cod hcod
    -- functional fibres for the beta step and the slot
    have hfibres : ∀ y, y ∈ˢ A → ∃ B, ((interpExpr V cval env φ (d + 1)
        (updV V ρ d y) (body.instantiate1 (.fvar d n ty))).getD
          SetTheory.empty) ∈ˢ B ∧ B ∈ˢ univ (cod.eval φ) := by
      intro y hy
      obtain ⟨-, hwfact2⟩ := hcond y A hity hy
      obtain ⟨w2, B2, hw2, hwB2, hB2u⟩ := hwfact2 cod hcod
      rw [hw2]
      exact ⟨B2, hwB2, hB2u⟩
    obtain ⟨Bf, hBf1, hBf2⟩ := choose_fibres hfibres
    have happlam : SetTheory.app
        (lam (cod.eval φ) A fun y => (interpExpr V cval env φ (d + 1)
          (updV V ρ d y) (body.instantiate1 (.fvar d n ty))).getD
            SetTheory.empty) x =
        (interpExpr V cval env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty :=
      app_lam hx hBf1 hBf2
    have hsubi : interpExpr V cval env φ d ρ (body.instantiate1 arg) =
        some w := by
      rw [interp_beta (n := n) (ty := ty) hfb hwa hba hiarg 0]
      exact hwi
    have hsubA : AnnotOk V cval env φ d ρ (body.instantiate1 arg) :=
      AnnotOk_beta hfb hwa hba hiarg hAa 0 hbodyA
    obtain ⟨B, hBi, hfold, hchain⟩ := ih hsubA hsubi
    refine ⟨B, hBi, ?_, ?_⟩
    · rw [SpineFold_cons, happlam, hwi]
      simpa using hfold
    · refine ⟨⟨cod.eval φ, A, Bf, lam_mem hBf1, hx, hBf2⟩, ?_⟩
      rw [happlam, hwi]
      simpa using hchain

/-- A value-spine fit induces an expression-spine fit at its final
depth, with the opening variables as the argument spine: the two walks
produce syntactically identical subjects. -/
theorem TeleFit.toTeleFitI :
    ∀ {D : Nat} {ρD : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ D ρD e vs d' ρ' rest →
      WScoped D e →
      D ≤ d' ∧ (∀ i, i < D → ρ' i = ρD i) ∧
      ∃ args rest₂, TeleFitI V cval env φ d' ρ' e args vs rest₂ := by
  intro D ρD e vs d' ρ' rest ht
  induction ht with
  | nil =>
    intro _
    exact ⟨Nat.le_refl _, fun _ _ => rfl, [], _, TeleFitI.nil⟩
  | @cons D ρD n ty body m x xs d' ρ' rest A hity hx ht ih =>
    intro hwe
    have hwe' : WScoped D ty ∧ WScoped D body := by simpa [WScoped] using hwe
    have hwopen : WScoped (D + 1) (body.instantiate1 (.fvar D n ty)) := by
      refine WScoped.instantiate1_gen ?_ 0 (hwe'.2.mono (Nat.le_succ D))
      simp only [WScoped]
      exact ⟨Nat.lt_succ_self D, hwe'.1⟩
    obtain ⟨hDd, hagr, args, rest₂, hfit⟩ := ih hwopen
    have hDd' : D ≤ d' := Nat.le_trans (Nat.le_succ D) hDd
    have hagr' : ∀ i, i < D → ρ' i = ρD i := by
      intro i hi
      rw [hagr i (by omega)]
      simp only [updV]
      rw [if_neg (by omega)]
    have hρD : ρ' D = x := by
      rw [hagr D (by omega)]
      simp [updV]
    refine ⟨hDd', hagr', .fvar D n ty :: args, rest₂, ?_⟩
    refine TeleFitI.cons ?_ ?_ hx (fvarsBelow_mono hDd' hwe'.2.fvarsBelow)
      ?_ rfl (by simp [AnnotOk]) hfit
    · rw [interp_lift hwe'.1 d' hDd' ρD ρ' hagr']
      exact hity
    · simp [interpExpr, hρD]
    · simp only [WScoped]
      exact ⟨by omega, hwe'.1⟩

/-- Swapping one argument of an expression-spine fit anywhere in the
spine, for an interp-equal replacement. -/
theorem TeleFitI.arg_swap_list {d : Nat} {ρ : Nat → V} {a₁ a₂ : Expr}
    (hwa₂ : WScoped d a₂) (hba₂ : a₂.looseBVarsBounded 0 = true)
    (hAa₂ : AnnotOk V cval env φ d ρ a₂)
    (hia : interpExpr V cval env φ d ρ a₂ =
      interpExpr V cval env φ d ρ a₁) :
    ∀ {pre : List Expr} {ty : Expr} {post : List Expr} {vs : List V}
      {rest : Expr},
      TeleFitI V cval env φ d ρ ty (pre ++ a₁ :: post) vs rest →
      (ty.stripPis (pre ++ a₁ :: post).length).isSome →
      ∃ rest₂, TeleFitI V cval env φ d ρ ty (pre ++ a₂ :: post) vs rest₂
  | [], ty, post, vs, rest, hfit, harity => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty = .forallE n dom body m := by
      match ty, harity with
      | .forallE n dom body m, _ => exact ⟨n, dom, body, m, rfl⟩
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have hia₂ : interpExpr V cval env φ d ρ a₂ = some x := hia.trans hiarg
    have harity' : (body.stripPis post.length).isSome := by
      simpa [Expr.stripPis, Option.isSome_map] using harity
    obtain ⟨rest₂, hsw⟩ := TeleFitI.arg_swap hwarg hbarg hwa₂ hba₂ hiarg
      hia₂ (k := 0) hsub hfbI harity'
    exact ⟨rest₂, TeleFitI.cons hity hia₂ hx hfbI hwa₂ hba₂ hAa₂ hsw⟩
  | p₀ :: pre, ty, post, vs, rest, hfit, harity => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty = .forallE n dom body m := by
      match ty, harity with
      | .forallE n dom body m, _ => exact ⟨n, dom, body, m, rfl⟩
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have harity' : ((body.instantiate1 p₀).stripPis
        (pre ++ a₁ :: post).length).isSome := by
      refine stripPis_instantiate1_isSome _ 0 ?_
      simpa [Expr.stripPis, Option.isSome_map] using harity
    obtain ⟨rest₂, hsw⟩ := TeleFitI.arg_swap_list hwa₂ hba₂ hAa₂ hia
      hsub harity'
    exact ⟨rest₂, TeleFitI.cons hity hiarg hx hfbI hwarg hbarg hAarg hsw⟩

/-- Related by constant renaming, modulo the positions the
interpretation never reads. -/
def RenEq (f : Name → Name) (e₁ e₂ : Expr) : Prop :=
  Expr.ErasedEq (e₁.renameConsts f) e₂

theorem RenEq.interp {f : Name → Name} (hro : RenameOk cval env f)
    {e₁ e₂ : Expr} (h : RenEq f e₁ e₂) (d : Nat) (ρ : Nat → V) :
    interpExpr V cval env φ d ρ e₂ = interpExpr V cval env φ d ρ e₁ := by
  rw [← interp_erasedEq h d ρ]
  exact interp_renameConsts hro e₁ d ρ

theorem RenEq.forallE_inv {f : Name → Name} {n : Name} {ty body : Expr}
    {m : BinderMeta} {e₂ : Expr}
    (h : RenEq f (.forallE n ty body m) e₂) :
    ∃ n₂ ty₂ body₂, e₂ = .forallE n₂ ty₂ body₂ m ∧
      RenEq f ty ty₂ ∧ RenEq f body body₂ := by
  match e₂, h with
  | .forallE n₂ ty₂ body₂ m₂, h =>
    obtain ⟨rfl, h1, h2⟩ :
        m = m₂ ∧ Expr.ErasedEq (ty.renameConsts f) ty₂ ∧
          Expr.ErasedEq (body.renameConsts f) body₂ := h
    exact ⟨n₂, ty₂, body₂, rfl, h1, h2⟩

theorem RenEq.instantiate1 {f : Name → Name} {e₁ e₂ a₁ a₂ : Expr} {k : Nat}
    (he : RenEq f e₁ e₂) (ha : RenEq f a₁ a₂) :
    RenEq f (e₁.instantiate1 a₁ k) (e₂.instantiate1 a₂ k) := by
  unfold RenEq
  rw [renameConsts_instantiate1_gen]
  exact Expr.ErasedEq.instantiate1 he ha

/-- Pointwise relation on argument spines. -/
inductive ArgsRel (P : Expr → Expr → Prop) : List Expr → List Expr → Prop
  | nil : ArgsRel P [] []
  | cons {a₁ a₂ : Expr} {l₁ l₂ : List Expr} :
      P a₁ a₂ → ArgsRel P l₁ l₂ → ArgsRel P (a₁ :: l₁) (a₂ :: l₂)

/-- A fit's value spine has the arguments' length. -/
theorem TeleFitI.vs_length :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest → vs.length = args.length := by
  intro ty args vs rest h
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => simpa using ih

/-- Transfer an expression-spine fit across a renaming of the telescope
and the arguments: every interpretation fact is renaming-invariant. -/
theorem TeleFitI.ren_transfer {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ {args₁ : List Expr} {ty₁ ty₂ : Expr} {args₂ : List Expr}
      {vs : List V} {rest₁ : Expr},
      TeleFitI V cval env φ d ρ ty₁ args₁ vs rest₁ →
      RenEq f ty₁ ty₂ →
      ArgsRel (fun a₁ a₂ => RenEq f a₁ a₂ ∧ WScoped d a₂ ∧
        a₂.looseBVarsBounded 0 = true ∧
        AnnotOk V cval env φ d ρ a₂) args₁ args₂ →
      ∃ rest₂, TeleFitI V cval env φ d ρ ty₂ args₂ vs rest₂
  | [], ty₁, ty₂, args₂, vs, rest₁, hfit, hty, hargs => by
    generalize ty₁ = t at hfit
    cases hfit with
    | nil =>
      cases hargs with
      | nil => exact ⟨ty₂, TeleFitI.nil⟩
  | a₁ :: args₁, ty₁, ty₂, args₂, vs, rest₁, hfit, hty, hargs => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty₁ = .forallE n dom body m := by
      cases hfit; exact ⟨_, _, _, _, rfl⟩
    obtain ⟨n₂, dom₂, body₂, m₂eq, hdom, hbody⟩ := RenEq.forallE_inv hty
    subst m₂eq
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    cases hargs with
    | cons ha hargs' =>
    obtain ⟨haren, hwa₂, hba₂, hAa₂⟩ := ha
    obtain ⟨rest₂, hsub₂⟩ := TeleFitI.ren_transfer hro hsub
      (RenEq.instantiate1 hbody haren) hargs'
    refine ⟨rest₂, TeleFitI.cons ?_ ?_ hx ?_ hwa₂ hba₂ hAa₂ hsub₂⟩
    · rw [RenEq.interp hro hdom d ρ]
      exact hity
    · rw [RenEq.interp hro haren d ρ]
      exact hiarg
    · exact Expr.fvarsBelow_erasedEq hbody
        (Expr.fvarsBelow_renameConsts hfbI)

/-- Peel the leading arguments off an expression-spine fit. -/
theorem TeleFitI.drop_prefix :
    ∀ {pre : List Expr} {ty : Expr} {post : List Expr} {vs : List V}
      {rest : Expr},
      TeleFitI V cval env φ d ρ ty (pre ++ post) vs rest →
      ∃ ty' vs', TeleFitI V cval env φ d ρ ty' post vs' rest ∧
        vs = vs.take pre.length ++ vs' ∧ vs'.length = post.length
  | [], ty, post, vs, rest, hfit => by
    exact ⟨ty, vs, hfit, by simp, TeleFitI.vs_length hfit⟩
  | p₀ :: pre, ty, post, vs, rest, hfit => by
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨ty', vs', hfit', heq, hlen⟩ := TeleFitI.drop_prefix hsub
    exact ⟨ty', vs', hfit', by simpa using heq, hlen⟩

end Setlec
