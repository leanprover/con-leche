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

/-- An inhabitant of an interpreted telescope, applied through fitting
values, walks a chain of typing slots. -/
theorem TeleFit.chainSlots :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {xs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env φ d ρ e xs d' ρ' rest →
      ∀ {v P : V}, AnnotOk V cval env φ d ρ e →
        interpExpr V cval env φ d ρ e = some P → v ∈ˢ P →
        ChainSlots V v xs := by
  intro d ρ e xs d' ρ' rest ht
  induction ht with
  | nil =>
    intro v P _ _ _
    exact trivial
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx ht ih =>
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
    refine ⟨⟨cod.eval φ, A,
      fun y => (interpExpr V cval env φ (d + 1) (updV V ρ d y)
        (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty,
      hv, hx, hfib⟩, ?_⟩
    have happ := app_mem hv hx hfib
    obtain ⟨w, hwi, hwu⟩ := hwfact cod hcod
    rw [hwi] at happ
    simp only [Option.getD_some] at happ
    exact ih hbody hwi happ

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

/-- The members of an application spine resolve when the whole
expression does. -/
theorem Expr.constsResolve_getAppArgs {env : Env} :
    ∀ {e : Expr}, e.constsResolve env = true →
      ∀ x ∈ e.getAppArgs, x.constsResolve env = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hb x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.constsResolve, Bool.and_eq_true] at hb
    rcases hx with hx | rfl
    · exact ihf hb.1 x hx
    · exact hb.2
  | _ => intro hb x hx; simp [Expr.getAppArgs] at hx

/-- A value-spine fit's residual resolves in any environment its
telescope resolves in (the walk only inserts opening variables typed by
the telescope's own domains). -/
theorem TeleFit.rest_resolve {envR : Env} {env₂ : Env} :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env₂ φ d ρ e vs d' ρ' rest →
      e.constsResolve envR = true →
      rest.constsResolve envR = true := by
  intro d ρ e vs d' ρ' rest ht
  induction ht with
  | nil => intro h; exact h
  | @cons d ρ n ty body m x xs d' ρ' rest A hity hx ht ih =>
    intro hres
    have hres' : ty.constsResolve envR = true ∧
        body.constsResolve envR = true := by
      simpa [Expr.constsResolve] using hres
    exact ih (Expr.constsResolve_instantiate1 hres'.1 0 hres'.2)

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
      ∃ args, TeleFitI V cval env φ d' ρ' e args vs rest ∧
        ∀ a ∈ args, ∃ i n ty, a = .fvar i n ty := by
  intro D ρD e vs d' ρ' rest ht
  induction ht with
  | nil =>
    intro _
    exact ⟨Nat.le_refl _, fun _ _ => rfl, [], TeleFitI.nil,
      fun a ha => by simp at ha⟩
  | @cons D ρD n ty body m x xs d' ρ' rest A hity hx ht ih =>
    intro hwe
    have hwe' : WScoped D ty ∧ WScoped D body := by simpa [WScoped] using hwe
    have hwopen : WScoped (D + 1) (body.instantiate1 (.fvar D n ty)) := by
      refine WScoped.instantiate1_gen ?_ 0 (hwe'.2.mono (Nat.le_succ D))
      simp only [WScoped]
      exact ⟨Nat.lt_succ_self D, hwe'.1⟩
    obtain ⟨hDd, hagr, args, hfit, hfvars⟩ := ih hwopen
    have hDd' : D ≤ d' := Nat.le_trans (Nat.le_succ D) hDd
    have hagr' : ∀ i, i < D → ρ' i = ρD i := by
      intro i hi
      rw [hagr i (by omega)]
      simp only [updV]
      rw [if_neg (by omega)]
    have hρD : ρ' D = x := by
      rw [hagr D (by omega)]
      simp [updV]
    refine ⟨hDd', hagr', .fvar D n ty :: args,
      ?_,
      fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨D, n, ty, rfl⟩
        · exact hfvars a ha⟩
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

/-- The first `k` domains of two `∀`-telescopes are related by the
renaming (their residuals are unconstrained). -/
def PiDomsRenEq (f : Name → Name) : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .forallE _ d₁ b₁ _, e₂ =>
    ∃ n₂ d₂ b₂ m₂, e₂ = .forallE n₂ d₂ b₂ m₂ ∧ RenEq f d₁ d₂ ∧
      PiDomsRenEq f k b₁ b₂
  | _ + 1, _, _ => False

/-- Domain relatedness survives instantiating both sides with related
arguments. -/
theorem PiDomsRenEq.instantiate1 {f : Name → Name} {a₁ a₂ : Expr}
    (ha : RenEq f a₁ a₂) :
    ∀ (k : Nat) {e₁ e₂ : Expr} (j : Nat), PiDomsRenEq f k e₁ e₂ →
      PiDomsRenEq f k (e₁.instantiate1 a₁ j) (e₂.instantiate1 a₂ j) := by
  intro k
  induction k with
  | zero => intro e₁ e₂ j _; trivial
  | succ k ih =>
    intro e₁ e₂ j h
    match e₁, h with
    | .forallE n₁ d₁ b₁ m₁, h =>
      obtain ⟨n₂, d₂, b₂, m₂, rfl, hd, hb⟩ := h
      exact ⟨n₂, d₂.instantiate1 a₂ j, b₂.instantiate1 a₂ (j + 1), m₂, rfl,
        RenEq.instantiate1 hd ha, ih (j + 1) hb⟩

/-- Pointwise domain relatedness assembles the prefix relation. -/
theorem PiDomsRenEq.of_pointwise {f : Name → Name} :
    ∀ (k : Nat) {e₁ e₂ : Expr}
      {bs₁ bs₂ : List (Name × Expr × BinderMeta)} {body₁ body₂ : Expr},
      e₁.stripPis k = some (bs₁, body₁) →
      e₂.stripPis k = some (bs₂, body₂) →
      (∀ (i : Nat) (b₁ b₂ : Name × Expr × BinderMeta),
        bs₁[i]? = some b₁ → bs₂[i]? = some b₂ → RenEq f b₁.2.1 b₂.2.1) →
      PiDomsRenEq f k e₁ e₂ := by
  intro k
  induction k with
  | zero => intro e₁ e₂ bs₁ bs₂ body₁ body₂ _ _ _; trivial
  | succ k ih =>
    intro e₁ e₂ bs₁ bs₂ body₁ body₂ h1 h2 hdoms
    match e₁, e₂, h1, h2 with
    | .forallE n₁ d₁ b₁ m₁, .forallE n₂ d₂ b₂ m₂, h1, h2 =>
      simp only [Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : b₂.stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, -⟩ : (n₁, d₁, m₁) :: p1.1 = bs₁ ∧ p1.2 = body₁ := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, -⟩ : (n₂, d₂, m₂) :: p2.1 = bs₂ ∧ p2.2 = body₂ := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hb2
      refine ⟨n₂, d₂, b₂, m₂, rfl, ?_, ?_⟩
      · exact hdoms 0 (n₁, d₁, m₁) (n₂, d₂, m₂) rfl rfl
      · exact ih hs1 hs2 (fun i c₁ c₂ hc₁ hc₂ =>
          hdoms (i + 1) c₁ c₂ (by simpa using hc₁) (by simpa using hc₂))

/-- Transfer an expression-spine fit across a renaming of the telescope
domains and the arguments: every interpretation fact is
renaming-invariant.  Only the walked prefix of the telescopes needs to
be related. -/
theorem TeleFitI.ren_transfer {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ {args₁ : List Expr} {ty₁ ty₂ : Expr} {args₂ : List Expr}
      {vs : List V} {rest₁ : Expr},
      TeleFitI V cval env φ d ρ ty₁ args₁ vs rest₁ →
      PiDomsRenEq f args₁.length ty₁ ty₂ →
      Expr.fvarsBelow d ty₂ →
      ArgsRel (fun a₁ a₂ => RenEq f a₁ a₂ ∧ WScoped d a₂ ∧
        a₂.looseBVarsBounded 0 = true ∧
        AnnotOk V cval env φ d ρ a₂) args₁ args₂ →
      ∃ rest₂, TeleFitI V cval env φ d ρ ty₂ args₂ vs rest₂
  | [], ty₁, ty₂, args₂, vs, rest₁, hfit, hty, hfb₂, hargs => by
    generalize ty₁ = t at hfit
    cases hfit with
    | nil =>
      cases hargs with
      | nil => exact ⟨ty₂, TeleFitI.nil⟩
  | a₁ :: args₁, ty₁, ty₂, args₂, vs, rest₁, hfit, hty, hfb₂, hargs => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty₁ = .forallE n dom body m := by
      cases hfit; exact ⟨_, _, _, _, rfl⟩
    obtain ⟨n₂, dom₂, body₂, m₂, rfl, hdom, hbody⟩ := hty
    have hfb₂' : Expr.fvarsBelow d dom₂ ∧ Expr.fvarsBelow d body₂ := by
      simpa [Expr.fvarsBelow] using hfb₂
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    cases hargs with
    | cons ha hargs' =>
    obtain ⟨haren, hwa₂, hba₂, hAa₂⟩ := ha
    obtain ⟨rest₂, hsub₂⟩ := TeleFitI.ren_transfer hro hsub
      (PiDomsRenEq.instantiate1 haren args₁.length 0 hbody)
      (fvarsBelow_instantiate1_gen hwa₂.fvarsBelow 0 hfb₂'.2) hargs'
    refine ⟨rest₂, TeleFitI.cons ?_ ?_ hx hfb₂'.2 hwa₂ hba₂ hAa₂ hsub₂⟩
    · rw [RenEq.interp hro hdom d ρ]
      exact hity
    · rw [RenEq.interp hro haren d ρ]
      exact hiarg

/-- Keep only the leading arguments of an expression-spine fit. -/
theorem TeleFitI.take_prefix :
    ∀ {pre post : List Expr} {ty : Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty (pre ++ post) vs rest →
      ∃ mid, TeleFitI V cval env φ d ρ ty pre (vs.take pre.length) mid
  | [], post, ty, vs, rest, hfit => ⟨ty, by simpa using TeleFitI.nil⟩
  | p₀ :: pre, post, ty, vs, rest, hfit => by
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨mid, hfit'⟩ := TeleFitI.take_prefix hsub
    exact ⟨mid, by
      simpa using TeleFitI.cons hity hiarg hx hfbI hwarg hbarg hAarg hfit'⟩

/-- Peel a `∀`-telescope along an argument list. -/
def telescopeInst : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => telescopeInst (b.instantiate1 a) as
  | _, _ :: _ => none

/-- The kernel's telescope-peeling helper is `telescopeInst`. -/
theorem piResidual_eq_telescopeInst :
    ∀ (ty : Expr) (args : List Expr),
      piResidual ty args = telescopeInst ty args
  | _, [] => rfl
  | .forallE _ _ b _, a :: as => piResidual_eq_telescopeInst (b.instantiate1 a) as
  | .sort _, _ :: _ | .bvar _, _ :: _ | .fvar _ _ _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

/-- Argument spines with given interpreted values: each argument is
bvar-closed, `D`-scoped and interprets to the corresponding value. -/
def InstArgs (cval : ConstVal V) (env : Env) (φ : Name → Nat) (D : Nat)
    (ρ : Nat → V) : List Expr → List V → Prop
  | [], [] => True
  | a :: as, v :: vs =>
    (WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
      interpExpr V cval env φ D ρ a = some v) ∧
    InstArgs cval env φ D ρ as vs
  | _, _ => False

theorem InstArgs.length {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs → args.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: as, _ :: vs, h => by
    simpa using InstArgs.length (h.2)

theorem InstArgs.bounded {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs →
      ∀ a ∈ args, a.looseBVarsBounded 0 = true
  | [], [], _ => by simp
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, v :: vs, h => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.2.1
    · exact InstArgs.bounded h.2 x hx

theorem InstArgs.wscoped {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs → ∀ a ∈ args, WScoped D a
  | [], [], _ => by simp
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, v :: vs, h => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1.1
    · exact InstArgs.wscoped h.2 x hx

/-- An expression-spine fit's arguments and values form an `InstArgs`
spine. -/
theorem TeleFitI.toInstArgs {D : Nat} {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ D ρ ty args vs rest →
      InstArgs cval env φ D ρ args vs := by
  intro ty args vs rest h
  induction h with
  | nil => trivial
  | cons hity hiarg hx hfb hwa hba hAa _ ih => exact ⟨⟨hwa, hba, hiarg⟩, ih⟩

/-- `InstArgs` lifts to any higher frame agreeing below the base. -/
theorem InstArgs.lift {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs →
      ∀ {D' : Nat} {ρ' : Nat → V}, D ≤ D' → (∀ i, i < D → ρ' i = ρ i) →
      InstArgs cval env φ D' ρ' args vs
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, h, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | a :: as, v :: vs, h, D', ρ', hle, hag => by
    obtain ⟨⟨hw, hb, hi⟩, h'⟩ := h
    refine ⟨⟨hw.mono hle, hb, ?_⟩, InstArgs.lift h' hle hag⟩
    rw [interp_lift hw D' hle ρ ρ' hag]
    exact hi

/-- For opening-variable spines the level assignment is irrelevant:
`InstArgs` transfers across any two assignments. -/
theorem InstArgs.of_fvars_ext {φ₂ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      (∀ a ∈ args, ∃ i n ty, a = .fvar i n ty) →
      InstArgs cval env φ D ρ args vs →
      InstArgs cval env φ₂ D ρ args vs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, v :: vs, hfv, h => by
    obtain ⟨⟨hw, hb, hi⟩, h'⟩ := h
    obtain ⟨i, n, ty, rfl⟩ := hfv a List.mem_cons_self
    refine ⟨⟨hw, hb, ?_⟩,
      InstArgs.of_fvars_ext (fun y hy => hfv y (List.mem_cons_of_mem _ hy))
        h'⟩
    simpa [interpExpr] using hi

/-- Interpretation of an instantiation sequence is determined by the
argument *values*: two spines with pointwise equal interpretations
yield interp-equal instantiations.  Each head argument is exchanged for
the opening variable through a double `interp_beta` bridge after
commuting it past the remaining (closed) substitutions. -/
theorem interp_instSeq_congr {D : Nat} {ρ : Nat → V} :
    ∀ {args₁ args₂ : List Expr} {vs : List V} {e : Expr},
      InstArgs cval env φ D ρ args₁ vs →
      InstArgs cval env φ D ρ args₂ vs →
      Expr.fvarsBelow D e →
      e.looseBVarsBounded args₁.length = true →
      interpExpr V cval env φ D ρ (instSeq args₁ (args₁.length - 1) e) =
      interpExpr V cval env φ D ρ (instSeq args₂ (args₂.length - 1) e)
  | [], [], [], e, _, _, _, _ => rfl
  | [], _ :: _, vs, e, h₁, h₂, _, _ => by
    match vs, h₁ with
    | [], _ => exact nomatch h₂
  | _ :: _, [], vs, e, h₁, h₂, _, _ => by
    match vs, h₂ with
    | [], _ => exact nomatch h₁
  | a₁ :: as₁, a₂ :: as₂, vs, e, h₁, h₂, hfb, hb => by
    match vs, h₁, h₂ with
    | v :: vs, ⟨⟨hw₁, hb₁, hi₁⟩, h₁'⟩, ⟨⟨hw₂, hb₂, hi₂⟩, h₂'⟩ =>
    have hlen12 : as₁.length = as₂.length := by
      have := InstArgs.length h₁'
      have := InstArgs.length h₂'
      omega
    show interpExpr V cval env φ D ρ
        (instSeq as₁ ((a₁ :: as₁).length - 1 - 1)
          (e.instantiate1 a₁ ((a₁ :: as₁).length - 1))) =
      interpExpr V cval env φ D ρ
        (instSeq as₂ ((a₂ :: as₂).length - 1 - 1)
          (e.instantiate1 a₂ ((a₂ :: as₂).length - 1)))
    simp only [List.length_cons, Nat.succ_sub_one]
    have hfb₁ : Expr.fvarsBelow D (e.instantiate1 a₁ as₁.length) :=
      fvarsBelow_instantiate1_gen hw₁.fvarsBelow _ hfb
    have hbnd₁ : (e.instantiate1 a₁ as₁.length).looseBVarsBounded
        as₁.length = true :=
      looseBVarsBounded_instantiate1_gen hb₁
        (by simpa [List.length_cons] using hb)
    have hIH := interp_instSeq_congr h₁' h₂' hfb₁ hbnd₁
    rw [hIH]
    rw [hlen12]
    have hout₁ := instSeq_instantiate1_out hb₁ as₂ as₂.length e
      (InstArgs.bounded h₂') (Nat.le_refl _)
    have hout₂ := instSeq_instantiate1_out hb₂ as₂ as₂.length e
      (InstArgs.bounded h₂') (Nat.le_refl _)
    rw [Nat.sub_self] at hout₁ hout₂
    rw [hout₁, hout₂]
    have hfbX : Expr.fvarsBelow D (instSeq as₂ (as₂.length - 1) e) :=
      fvarsBelow_instSeq as₂ _
        (fun a ha => (InstArgs.wscoped h₂' a ha).fvarsBelow)
        hfb
    rw [interp_beta (n := .anonymous) (ty := .sort .zero) hfbX hw₁ hb₁ hi₁ 0,
      ← interp_beta (n := .anonymous) (ty := .sort .zero) hfbX hw₂ hb₂ hi₂ 0]

/-- Well-formedness of an expression-spine fit's residual: scoping,
loose-bvar boundedness and annotation truthfulness carry through the
instantiation walk. -/
theorem TeleFitI.rest_wf {d : Nat} {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      WScoped d ty → ty.looseBVarsBounded 0 = true →
      AnnotOk V cval env φ d ρ ty →
      WScoped d rest ∧ rest.looseBVarsBounded 0 = true ∧
        AnnotOk V cval env φ d ρ rest ∧
        ∀ l ∈ rest.fvarLeaves,
          l ∈ ty.fvarLeaves ∨ ∃ a ∈ args, l ∈ a.fvarLeaves := by
  intro ty args vs rest ht
  induction ht with
  | nil => intro hw hb hA; exact ⟨hw, hb, hA, fun l hl => Or.inl hl⟩
  | @cons n ty₀ body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro hw hb hA
    have hw' : WScoped d ty₀ ∧ WScoped d body := by simpa [WScoped] using hw
    have hb' : ty₀.looseBVarsBounded 0 = true ∧
        body.looseBVarsBounded 1 = true := by
      simpa [Expr.looseBVarsBounded] using hb
    simp only [AnnotOk] at hA
    obtain ⟨hAty, ⟨v, hcod⟩, hcond⟩ := hA
    obtain ⟨hAopen, -⟩ := hcond x A hity hx
    obtain ⟨hwR, hbR, hAR, hlR⟩ := ih (WScoped.instantiate1_gen hwa 0 hw'.2)
      (looseBVarsBounded_instantiate1_gen hba (k := 0) hb'.2)
      (AnnotOk_beta hfb hwa hba hiarg hAa 0 hAopen)
    refine ⟨hwR, hbR, hAR, fun l hl => ?_⟩
    rcases hlR l hl with hl' | ⟨a, ha, hla⟩
    · rcases fvarLeaves_instantiate1 body 0 hl' with hb'' | hb''
      · exact Or.inl (by
          simp only [Expr.fvarLeaves, List.mem_append]
          exact Or.inr hb'')
      · exact Or.inr ⟨arg, List.mem_cons_self, hb''⟩
    · exact Or.inr ⟨a, List.mem_cons_of_mem _ ha, hla⟩

/-- Peel the leading arguments off an expression-spine fit. -/
theorem TeleFitI.drop_prefix :
    ∀ {pre : List Expr} {ty : Expr} {post : List Expr} {vs : List V}
      {rest : Expr},
      TeleFitI V cval env φ d ρ ty (pre ++ post) vs rest →
      ∃ ty' vs', telescopeInst ty pre = some ty' ∧
        TeleFitI V cval env φ d ρ ty' post vs' rest ∧
        vs = vs.take pre.length ++ vs' ∧ vs'.length = post.length
  | [], ty, post, vs, rest, hfit => by
    exact ⟨ty, vs, rfl, hfit, by simp, TeleFitI.vs_length hfit⟩
  | p₀ :: pre, ty, post, vs, rest, hfit => by
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨ty', vs', hpeel, hfit', heq, hlen⟩ := TeleFitI.drop_prefix hsub
    exact ⟨ty', vs', hpeel, hfit', by simpa using heq, hlen⟩

/-- An expression-spine fit's residual is the peeled telescope. -/
theorem TeleFitI.rest_eq :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      telescopeInst ty args = some rest := by
  intro ty args vs rest h
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => exact ih

/-- Concatenate two expression-spine fits (the second starting at the
first's residual). -/
theorem TeleFitI.append :
    ∀ {ty : Expr} {args₁ : List Expr} {vs₁ : List V} {mid : Expr}
      {args₂ : List Expr} {vs₂ : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args₁ vs₁ mid →
      TeleFitI V cval env φ d ρ mid args₂ vs₂ rest →
      TeleFitI V cval env φ d ρ ty (args₁ ++ args₂) (vs₁ ++ vs₂) rest := by
  intro ty args₁ vs₁ mid args₂ vs₂ rest h1
  induction h1 with
  | nil => intro h2; exact h2
  | cons hity hiarg hx hfb hwa hba hAa _ ih =>
    intro h2
    exact TeleFitI.cons hity hiarg hx hfb hwa hba hAa (ih h2)

/-- Positional interpretation facts of an expression-spine fit. -/
theorem TeleFitI.arg_facts :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      ∀ (i : Nat) (a : Expr) (v : V), args[i]? = some a → vs[i]? = some v →
        interpExpr V cval env φ d ρ a = some v := by
  intro ty args vs rest h
  induction h with
  | nil => intro i a v ha _; simp at ha
  | @cons n ty body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro i a v ha hv
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hv
      subst ha hv
      exact hiarg
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha hv
      exact ih i a v ha hv

/-- Positional well-formedness facts of an expression-spine fit's
arguments. -/
theorem TeleFitI.arg_wf :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      ∀ (i : Nat) (a : Expr), args[i]? = some a →
        WScoped d a ∧ a.looseBVarsBounded 0 = true ∧
        AnnotOk V cval env φ d ρ a := by
  intro ty args vs rest h
  induction h with
  | nil => intro i a ha; simp at ha
  | @cons n ty body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro i a ha
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      exact ⟨hwa, hba, hAa⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at ha
      exact ih i a ha

/-- Renaming relates every expression to itself modulo erasure when the
renaming only retargets constants that do not occur — in particular any
`fvar` (its annotation is erased). -/
theorem RenEq.fvar_self {f : Name → Name} {i : Nat} {n : Name} {ty : Expr} :
    RenEq f (.fvar i n ty) (.fvar i n ty) := by
  show Expr.ErasedEq (Expr.fvar i n (ty.renameConsts f)) (.fvar i n ty)
  exact rfl

/-- Erasure-equality is a `RenEq` along the identity renaming. -/
theorem RenEq.of_erasedEq {e₁ e₂ : Expr} (h : Expr.ErasedEq e₁ e₂) :
    RenEq (fun n => n) e₁ e₂ := by
  show Expr.ErasedEq (e₁.renameConsts fun n => n) e₂
  rw [renameConsts_id]
  exact h

/-- Pointwise domain agreement assembles the λ/∀ domain relation. -/
theorem LamPiDomsEq.of_pointwise :
    ∀ (k : Nat) {e ty : Expr}
      {lbs pbs : List (Name × Expr × BinderMeta)} {lbody pbody : Expr},
      e.stripLams k = some (lbs, lbody) →
      ty.stripPis k = some (pbs, pbody) →
      (∀ (i : Nat) (b₁ b₂ : Name × Expr × BinderMeta),
        lbs[i]? = some b₁ → pbs[i]? = some b₂ → b₁.2.1 = b₂.2.1) →
      Expr.LamPiDomsEq k e ty := by
  intro k
  induction k with
  | zero => intro e ty lbs pbs lbody pbody _ _ _; trivial
  | succ k ih =>
    intro e ty lbs pbs lbody pbody h1 h2 hdoms
    match e, ty, h1, h2 with
    | .lam n₁ d₁ b₁ m₁, .forallE n₂ d₂ b₂ m₂, h1, h2 =>
      simp only [Expr.stripLams, Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripLams k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : b₂.stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, -⟩ : (n₁, d₁, m₁) :: p1.1 = lbs ∧ p1.2 = lbody := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, -⟩ : (n₂, d₂, m₂) :: p2.1 = pbs ∧ p2.2 = pbody := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hb2
      refine ⟨hdoms 0 (n₁, d₁, m₁) (n₂, d₂, m₂) rfl rfl, ?_⟩
      exact ih hs1 hs2 (fun i c₁ c₂ hc₁ hc₂ =>
        hdoms (i + 1) c₁ c₂ (by simpa using hc₁) (by simpa using hc₂))

/-- Peeling a telescope: the residual's decomposition carries the
accumulated descending-index instantiations. -/
theorem telescopeInst_stripPis :
    ∀ (p : Nat) (args : List Expr) (k : Nat) {ty : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      args.length = p →
      ty.stripPis (p + k) = some (bs, body) →
      ∃ mid, telescopeInst ty args = some mid ∧
        ∃ bs' body', mid.stripPis k = some (bs', body') ∧
          body' = Expr.instSeq args (p + k - 1) body ∧
          ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
            bs[p + i]? = some b → bs'[i]? = some b' →
            b'.2.1 = Expr.instSeq args (p + i - 1) b.2.1 := by
  intro p
  induction p with
  | zero =>
    intro args k ty bs body hlen hstrip
    match args, hlen with
    | [], _ =>
      refine ⟨ty, rfl, bs, body, by simpa using hstrip, rfl, ?_⟩
      intro i b b' hb hb'
      simp only [Nat.zero_add] at hb
      rw [hb] at hb'
      obtain rfl := Option.some.inj hb'
      rfl
  | succ p ih =>
    intro args k ty bs body hlen hstrip
    match args, hlen with
    | a :: as, hlen =>
    have hlen' : as.length = p := by simpa using hlen
    rw [show p + 1 + k = (p + k) + 1 from by omega] at hstrip
    match ty, hstrip with
    | .forallE n d b m, hstrip =>
    simp only [Expr.stripPis] at hstrip
    cases hs0 : b.stripPis (p + k) with
    | none => rw [hs0] at hstrip; exact nomatch hstrip
    | some p0 =>
    rw [hs0] at hstrip
    simp only [Option.map_some, Option.some.injEq] at hstrip
    obtain ⟨hb0, hbody0⟩ : (n, d, m) :: p0.1 = bs ∧ p0.2 = body := by
      cases hstrip; exact ⟨rfl, rfl⟩
    have hlen0 : p0.1.length = p + k := Expr.stripPis_length _ hs0
    cases hs1 : (b.instantiate1 a).stripPis (p + k) with
    | none =>
      exact absurd (Expr.stripPis_instantiate1_isSome (p + k) 0
        (by rw [hs0]; rfl)) (by rw [hs1]; simp)
    | some p1 =>
    obtain ⟨hbody1, hdoms1⟩ := Expr.stripPis_instantiate1_eq (p + k) 0
      hs0 hs1
    obtain ⟨mid, hmid, bs', body', hstrip', hbody', hdoms'⟩ :=
      ih as k hlen' (bs := p1.1) (body := p1.2) hs1
    refine ⟨mid, hmid, bs', body', hstrip', ?_, ?_⟩
    · rw [hbody', hbody1, ← hbody0]
      show Expr.instSeq as (p + k - 1) (p0.2.instantiate1 a (0 + (p + k)))
        = Expr.instSeq (a :: as) (p + 1 + k - 1) p0.2
      show _ = Expr.instSeq as (p + 1 + k - 1 - 1)
        (p0.2.instantiate1 a (p + 1 + k - 1))
      congr 2 <;> omega
    · intro i bb bb' hbb hbb'
      rw [← hb0] at hbb
      have hbb0 : p0.1[p + i]? = some bb ∨ False := by
        left
        simpa [show p + 1 + i = (p + i) + 1 from by omega] using hbb
      obtain hbb0 := hbb0.resolve_right (fun h => h)
      have hlen1 : p1.1.length = p + k := Expr.stripPis_length _ hs1
      by_cases hik : p + i < p + k
      · have hbb1 : ∃ cb, p1.1[p + i]? = some cb := by
          refine ⟨p1.1[p + i]'(by omega), ?_⟩
          simp [List.getElem?_eq_getElem (by omega : p + i < p1.1.length)]
        obtain ⟨cb, hcb⟩ := hbb1
        have hd1 : cb.2.1 = bb.2.1.instantiate1 a (0 + (p + i)) :=
          hdoms1 (p + i) bb cb hbb0 hcb
        rw [hdoms' i cb bb' hcb hbb', hd1]
        show Expr.instSeq as (p + i - 1) (bb.2.1.instantiate1 a (0 + (p + i)))
          = Expr.instSeq as (p + 1 + i - 1 - 1)
            (bb.2.1.instantiate1 a (p + 1 + i - 1))
        congr 2 <;> omega
      · exact absurd hbb0 (by
          rw [List.getElem?_eq_none (by omega : p0.1.length ≤ p + i)]
          simp)

/-- After walking the parameters (constructor side) and the full
prefix (statement side) with the same closed arguments, the two
telescopes' field domains are related by the renaming: the lift slots
are eaten by the motive/minor instantiations, the parameter
instantiations drop past the lift, and the renaming rides along
(erased on the fvar arguments). -/
theorem fields_relation {f : Name → Name} {nP nmM cnF : Nat}
    (hnm : 1 ≤ nmM)
    {ctorTy stmtTy : Expr}
    {cbs sbs : List (Name × Expr × BinderMeta)} {cbody sbody : Expr}
    (hcs : ctorTy.stripPis (nP + cnF) = some (cbs, cbody))
    (hss : stmtTy.stripPis ((nP + nmM) + cnF) = some (sbs, sbody))
    (hpin : ∀ (i : Nat) (cb sb : Name × Expr × BinderMeta),
      cbs[nP + i]? = some cb → sbs[(nP + nmM) + i]? = some sb →
      sb.2.1 = (cb.2.1.liftLooseBVars nmM i).renameConsts f)
    {params extras : List Expr}
    (hplen : params.length = nP) (hxlen : extras.length = nmM)
    (hpb : ∀ a ∈ params, a.looseBVarsBounded 0 = true)
    (hpren : ∀ a ∈ params, Expr.ErasedEq (a.renameConsts f) a)
    {midC midS : Expr}
    (hmidC : telescopeInst ctorTy params = some midC)
    (hmidS : telescopeInst stmtTy (params ++ extras) = some midS) :
    PiDomsRenEq f cnF midC midS := by
  obtain ⟨midC', hmidC', cbs', cbody', hcs', hcbody', hcdoms⟩ :=
    telescopeInst_stripPis nP params cnF hplen hcs
  obtain rfl : midC' = midC := by
    rw [hmidC'] at hmidC
    exact Option.some.inj hmidC
  obtain ⟨midS', hmidS', sbs', sbody', hss', hsbody', hsdoms⟩ :=
    telescopeInst_stripPis (nP + nmM) (params ++ extras) cnF
      (by simp [hplen, hxlen]) hss
  obtain rfl : midS' = midS := by
    rw [hmidS'] at hmidS
    exact Option.some.inj hmidS
  refine PiDomsRenEq.of_pointwise cnF hcs' hss' ?_
  intro i b₁ b₂ hb₁ hb₂
  have hilen : i < cnF := by
    rcases Nat.lt_or_ge i cnF with h | h
    · exact h
    · rw [List.getElem?_eq_none
        (by rw [Expr.stripPis_length _ hcs']; omega)] at hb₁
      exact nomatch hb₁
  have hclen : cbs.length = nP + cnF := Expr.stripPis_length _ hcs
  have hslen : sbs.length = (nP + nmM) + cnF := Expr.stripPis_length _ hss
  obtain ⟨cb, hcb⟩ : ∃ cb, cbs[nP + i]? = some cb :=
    ⟨cbs[nP + i]'(by omega),
     by simp [List.getElem?_eq_getElem (by omega : nP + i < cbs.length)]⟩
  obtain ⟨sb, hsb⟩ : ∃ sb, sbs[(nP + nmM) + i]? = some sb :=
    ⟨sbs[(nP + nmM) + i]'(by omega),
     by simp [List.getElem?_eq_getElem
       (by omega : (nP + nmM) + i < sbs.length)]⟩
  have h1 : b₁.2.1 = Expr.instSeq params (nP + i - 1) cb.2.1 :=
    hcdoms i cb b₁ hcb hb₁
  have h2 : b₂.2.1 = Expr.instSeq (params ++ extras)
      ((nP + nmM) + i - 1) sb.2.1 :=
    hsdoms i sb b₂ hsb hb₂
  have h3 : sb.2.1 = (cb.2.1.liftLooseBVars nmM i).renameConsts f :=
    hpin i cb sb hcb hsb
  show RenEq f b₁.2.1 b₂.2.1
  rw [h1, h2, h3]
  show Expr.ErasedEq
    ((Expr.instSeq params (nP + i - 1) cb.2.1).renameConsts f)
    (Expr.instSeq (params ++ extras) (nP + nmM + i - 1)
      ((cb.2.1.liftLooseBVars nmM i).renameConsts f))
  rw [renameConsts_liftLooseBVars]
  rw [Expr.instSeq_append]
  rw [Expr.instSeq_liftLooseBVars params (nP + nmM + i - 1) hpb
    (by rw [hplen]; omega)]
  rw [show nP + nmM + i - 1 - nmM = nP + i - 1 from by omega]
  rw [show nP + nmM + i - 1 - params.length = i + extras.length - 1 from by
    rw [hplen, hxlen]; omega]
  rw [← hxlen]
  rw [Expr.instSeq_lift_eat extras]
  exact instSeq_renameConsts params (nP + i - 1) hpren

/-- Peel a λ-tower along an argument list. -/
def telescopeInstLam : Expr → List Expr → Option Expr
  | e, [] => some e
  | .lam _ _ b _, a :: as => telescopeInstLam (b.instantiate1 a) as
  | _, _ :: _ => none

/-- A λ-spine fit's residual is the peeled tower. -/
theorem TeleFitLam.rest_eq :
    ∀ {e : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitLam cval env φ d ρ e args vs rest →
      telescopeInstLam e args = some rest := by
  intro e args vs rest h
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => exact ih

/-- Peeling a λ-tower: the residual body carries the accumulated
descending-index instantiations. -/
theorem telescopeInstLam_body :
    ∀ (p : Nat) (args : List Expr) {e : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      args.length = p →
      e.stripLams p = some (bs, body) →
      telescopeInstLam e args = some (Expr.instSeq args (p - 1) body) := by
  intro p
  induction p with
  | zero =>
    intro args e bs body hlen hstrip
    match args, hlen with
    | [], _ =>
      simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at hstrip
      obtain ⟨-, rfl⟩ := hstrip
      rfl
  | succ p ih =>
    intro args e bs body hlen hstrip
    match args, hlen with
    | a :: as, hlen =>
    have hlen' : as.length = p := by simpa using hlen
    match e, hstrip with
    | .lam n d b m, hstrip =>
    simp only [Expr.stripLams] at hstrip
    cases hs0 : b.stripLams p with
    | none => rw [hs0] at hstrip; exact nomatch hstrip
    | some p0 =>
    rw [hs0] at hstrip
    simp only [Option.map_some, Option.some.injEq] at hstrip
    obtain ⟨-, hbody0⟩ : (n, d, m) :: p0.1 = bs ∧ p0.2 = body := by
      cases hstrip; exact ⟨rfl, rfl⟩
    cases hs1 : (b.instantiate1 a).stripLams p with
    | none =>
      exact absurd (Expr.stripLams_instantiate1_isSome p 0
        (by rw [hs0]; rfl)) (by rw [hs1]; simp)
    | some p1 =>
    obtain ⟨hbody1, -⟩ := Expr.stripLams_instantiate1_eq p 0 hs0 hs1
    show telescopeInstLam (b.instantiate1 a) as = _
    rw [ih as hlen' (bs := p1.1) (body := p1.2) (by rw [hs1])]
    rw [hbody1, ← hbody0]
    show some (Expr.instSeq as (p - 1) (p0.2.instantiate1 a (0 + p))) =
      some (Expr.instSeq as (p + 1 - 1 - 1)
        (p0.2.instantiate1 a (p + 1 - 1)))
    congr 3 <;> omega

/-- The first `k` λ-domains are related by the renaming to the
`∀`-telescope's domains. -/
def LamPiDomsRenEq (f : Name → Name) : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .lam _ d₁ b₁ _, e₂ =>
    ∃ n₂ d₂ b₂ m₂, e₂ = .forallE n₂ d₂ b₂ m₂ ∧ RenEq f d₁ d₂ ∧
      LamPiDomsRenEq f k b₁ b₂
  | _ + 1, _, _ => False

/-- Pointwise domain relatedness assembles the λ/∀ renaming
relation. -/
theorem LamPiDomsRenEq.of_pointwise {f : Name → Name} :
    ∀ (k : Nat) {e ty : Expr}
      {lbs pbs : List (Name × Expr × BinderMeta)} {lbody pbody : Expr},
      e.stripLams k = some (lbs, lbody) →
      ty.stripPis k = some (pbs, pbody) →
      (∀ (i : Nat) (b₁ b₂ : Name × Expr × BinderMeta),
        lbs[i]? = some b₁ → pbs[i]? = some b₂ → RenEq f b₁.2.1 b₂.2.1) →
      LamPiDomsRenEq f k e ty := by
  intro k
  induction k with
  | zero => intro e ty lbs pbs lbody pbody _ _ _; trivial
  | succ k ih =>
    intro e ty lbs pbs lbody pbody h1 h2 hdoms
    match e, ty, h1, h2 with
    | .lam n₁ d₁ b₁ m₁, .forallE n₂ d₂ b₂ m₂, h1, h2 =>
      simp only [Expr.stripLams, Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripLams k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : b₂.stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, -⟩ : (n₁, d₁, m₁) :: p1.1 = lbs ∧ p1.2 = lbody := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, -⟩ : (n₂, d₂, m₂) :: p2.1 = pbs ∧ p2.2 = pbody := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hb2
      refine ⟨n₂, d₂, b₂, m₂, rfl,
        hdoms 0 (n₁, d₁, m₁) (n₂, d₂, m₂) rfl rfl, ?_⟩
      exact ih hs1 hs2 (fun i c₁ c₂ hc₁ hc₂ =>
        hdoms (i + 1) c₁ c₂ (by simpa using hc₁) (by simpa using hc₂))

/-- The relation survives instantiating both sides with related
arguments. -/
theorem LamPiDomsRenEq.instantiate1 {f : Name → Name} {a₁ a₂ : Expr}
    (ha : RenEq f a₁ a₂) :
    ∀ (k : Nat) {e₁ e₂ : Expr} (j : Nat), LamPiDomsRenEq f k e₁ e₂ →
      LamPiDomsRenEq f k (e₁.instantiate1 a₁ j) (e₂.instantiate1 a₂ j) := by
  intro k
  induction k with
  | zero => intro e₁ e₂ j _; trivial
  | succ k ih =>
    intro e₁ e₂ j h
    match e₁, h with
    | .lam n₁ d₁ b₁ m₁, h =>
      obtain ⟨n₂, d₂, b₂, m₂, rfl, hd, hb⟩ := h
      exact ⟨n₂, d₂.instantiate1 a₂ j, b₂.instantiate1 a₂ (j + 1), m₂, rfl,
        RenEq.instantiate1 hd ha, ih (j + 1) hb⟩

/-- A type-telescope fit transfers to a λ-tower whose binder domains
are related through the renaming (the fit's domains rename to the
tower's own). -/
theorem TeleFitI.toLamRen {f : Name → Name} (hro : RenameOk cval env f) :
    ∀ {args : List Expr} {ty e : Expr} {vs : List V} {restT : Expr},
      TeleFitI V cval env φ d ρ ty args vs restT →
      LamPiDomsRenEq f args.length e ty →
      Expr.fvarsBelow d e →
      (∀ a ∈ args, RenEq f a a) →
      ∃ restE, TeleFitLam cval env φ d ρ e args vs restE
  | [], ty, e, vs, restT, hfit, hdoms, hfbe, hargs => by
    generalize ty = t at hfit
    cases hfit with
    | nil => exact ⟨e, TeleFitLam.nil⟩
  | arg :: args, ty, e, vs, restT, hfit, hdoms, hfbe, hargs => by
    obtain ⟨n₁, d₁, b₁, m₁, rfl⟩ :
        ∃ n₁ d₁ b₁ m₁, e = .lam n₁ d₁ b₁ m₁ := by
      match e, hdoms with
      | .lam n₁ d₁ b₁ m₁, _ => exact ⟨n₁, d₁, b₁, m₁, rfl⟩
    obtain ⟨n₂, d₂, b₂, m₂, rfl, hd, hb⟩ := hdoms
    have hfbe' : Expr.fvarsBelow d d₁ ∧ Expr.fvarsBelow d b₁ := by
      simpa [Expr.fvarsBelow] using hfbe
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨restE, hfitE⟩ := TeleFitI.toLamRen hro hsub
      (LamPiDomsRenEq.instantiate1 (hargs arg List.mem_cons_self)
        args.length 0 hb)
      (fvarsBelow_instantiate1_gen hwarg.fvarsBelow 0 hfbe'.2)
      (fun a ha => hargs a (List.mem_cons_of_mem _ ha))
    refine ⟨restE, TeleFitLam.cons ?_ hiarg hx hfbe'.2 hwarg hbarg hAarg
      hfitE⟩
    rw [← RenEq.interp hro hd d ρ]
    exact hity

/-- Build a pointwise argument relation from indexed facts. -/
theorem ArgsRel.of_pointwise {P : Expr → Expr → Prop} :
    ∀ {l₁ l₂ : List Expr}, l₁.length = l₂.length →
      (∀ (i : Nat) (a₁ a₂ : Expr), l₁[i]? = some a₁ → l₂[i]? = some a₂ →
        P a₁ a₂) →
      ArgsRel P l₁ l₂
  | [], [], _, _ => ArgsRel.nil
  | a₁ :: l₁, a₂ :: l₂, hlen, h =>
    ArgsRel.cons (h 0 a₁ a₂ rfl rfl)
      (ArgsRel.of_pointwise (by simpa using hlen)
        (fun i b₁ b₂ hb₁ hb₂ => h (i + 1) b₁ b₂ (by simpa using hb₁)
          (by simpa using hb₂)))

/-- Replace the leading arguments of a fit with pointwise interp-equal,
well-formed alternatives. -/
theorem TeleFitI.swap_prefix :
    ∀ {pre₁ pre₂ post : List Expr} {ty : Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty (pre₁ ++ post) vs rest →
      (ty.stripPis (pre₁ ++ post).length).isSome →
      ArgsRel (fun a₁ a₂ =>
        interpExpr V cval env φ d ρ a₂ =
          interpExpr V cval env φ d ρ a₁ ∧
        WScoped d a₂ ∧ a₂.looseBVarsBounded 0 = true ∧
        AnnotOk V cval env φ d ρ a₂) pre₁ pre₂ →
      ∃ rest₂, TeleFitI V cval env φ d ρ ty (pre₂ ++ post) vs rest₂ := by
  intro pre₁
  induction pre₁ with
  | nil =>
    intro pre₂ post ty vs rest hfit _ hrel
    cases hrel with
    | nil => exact ⟨rest, hfit⟩
  | cons a₁ pre₁ ih =>
    intro pre₂ post ty vs rest hfit harity hrel
    cases hrel with
    | @cons _ a₂ _ pre₂ hP hrel' =>
    obtain ⟨hia, hwa₂, hba₂, hAa₂⟩ := hP
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, ty = .forallE n dom body m := by
      cases hfit; exact ⟨_, _, _, _, rfl⟩
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have hia₂ : interpExpr V cval env φ d ρ a₂ = some x := by
      rw [hia]; exact hiarg
    have harity' : (body.stripPis (pre₁ ++ post).length).isSome := by
      simpa [Expr.stripPis, Option.isSome_map] using harity
    obtain ⟨restS, hsw⟩ := TeleFitI.arg_swap hwarg hbarg hwa₂ hba₂ hiarg
      hia₂ (k := 0) hsub hfbI harity'
    obtain ⟨rest₂, hfit₂⟩ := ih hsw
      (Expr.stripPis_instantiate1_isSome _ 0 harity') hrel'
    exact ⟨rest₂, TeleFitI.cons hity hia₂ hx hfbI hwa₂ hba₂ hAa₂ hfit₂⟩

/-- Peeling preserves the `fvar` bound. -/
theorem telescopeInst_fvarsBelow {D : Nat} :
    ∀ (args : List Expr) {ty mid : Expr},
      Expr.fvarsBelow D ty → (∀ a ∈ args, Expr.fvarsBelow D a) →
      telescopeInst ty args = some mid → Expr.fvarsBelow D mid
  | [], ty, mid, hty, _, h => by
    obtain rfl := Option.some.inj h
    exact hty
  | a :: as, ty, mid, hty, hargs, h => by
    match ty, h with
    | .forallE n dom body m, h =>
      have hty' : Expr.fvarsBelow D dom ∧ Expr.fvarsBelow D body := by
        simpa [Expr.fvarsBelow] using hty
      exact telescopeInst_fvarsBelow as
        (fvarsBelow_instantiate1_gen (hargs a List.mem_cons_self) 0 hty'.2)
        (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) h

/-- Normalize an `fvar`'s annotation away. -/
def sanitizeArg : Expr → Expr
  | .fvar i n _ => .fvar i n (.sort .zero)
  | e => e

/-- Normalize a fit's fvar arguments: the interpretation reads neither
their names nor their annotations. -/
theorem TeleFitI.sanitize :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      (ty.stripPis args.length).isSome →
      (∀ a ∈ args, ∃ i n t, a = .fvar i n t) →
      ∃ rest₂, TeleFitI V cval env φ d ρ ty (args.map sanitizeArg) vs
        rest₂ := by
  intro ty args vs rest hfit harity hshape
  have hfit' : TeleFitI V cval env φ d ρ ty (args ++ []) vs rest := by
    simpa using hfit
  obtain ⟨rest₂, h₂⟩ := TeleFitI.swap_prefix hfit'
    (by simpa using harity)
    (show ArgsRel _ args (args.map sanitizeArg) from by
      refine ArgsRel.of_pointwise (by simp) ?_
      intro i a₁ a₂ ha₁ ha₂
      have ha₂' : (args.map sanitizeArg)[i]? = some a₂ := ha₂
      rw [List.getElem?_map, ha₁] at ha₂'
      obtain rfl : sanitizeArg a₁ = a₂ := Option.some.inj ha₂'
      obtain ⟨j, n, t, rfl⟩ := hshape a₁ (List.mem_of_getElem? ha₁)
      obtain ⟨hw, -, -⟩ := TeleFitI.arg_wf hfit i _ ha₁
      have hw' : j < d ∧ WScoped j t := by simpa [WScoped] using hw
      refine ⟨by simp [sanitizeArg, interpExpr], ?_, rfl,
        by simp [AnnotOk, sanitizeArg]⟩
      show WScoped d (Expr.fvar j n (.sort .zero))
      simp only [WScoped]
      exact ⟨hw'.1, trivial⟩)
  exact ⟨rest₂, by simpa using h₂⟩

/-- Uninstantiate the levels of a fit's telescope: the fit transfers
to the raw telescope at the composed assignment. -/
theorem TeleFitI.instLev_down {ks : List Name} {lvs : List Level}
    (hcp : ConstValParams cval env) :
    ∀ {args : List Expr} {e : Expr} {vsl : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ (e.instantiateLevelParams ks lvs) args vsl
        rest →
      (∀ a ∈ args, ∃ i n, a = .fvar i n (.sort .zero)) →
      Expr.fvarsBelow d e →
      ∃ rest₂, TeleFitI V cval env (Level.substFn φ ks lvs) d ρ e args vsl
        rest₂
  | [], e, vsl, rest, hfit, _, _ => by
    generalize e.instantiateLevelParams ks lvs = E at hfit
    cases hfit with
    | nil => exact ⟨e, TeleFitI.nil⟩
  | arg :: args, e, vsl, rest, hfit, hshape, hfbe => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, e = .forallE n dom body m := by
      match e, hfit with
      | .forallE n dom body m, _ => exact ⟨n, dom, body, m, rfl⟩
      | .bvar _, hfit => exact nomatch hfit
      | .fvar _ _ _, hfit => exact nomatch hfit
      | .sort _, hfit => exact nomatch hfit
      | .const _ _, hfit => exact nomatch hfit
      | .app _ _, hfit => exact nomatch hfit
      | .lam _ _ _ _, hfit => exact nomatch hfit
      | .letE _ _ _ _, hfit => exact nomatch hfit
      | .lit _, hfit => exact nomatch hfit
      | .proj _ _ _, hfit => exact nomatch hfit
    have hfbe' : Expr.fvarsBelow d dom ∧ Expr.fvarsBelow d body := by
      simpa [Expr.fvarsBelow] using hfbe
    obtain ⟨i₀, n₀, rfl⟩ := hshape arg List.mem_cons_self
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    have hsub' : TeleFitI V cval env φ d ρ
        ((body.instantiate1 (.fvar i₀ n₀ (.sort .zero))).instantiateLevelParams
          ks lvs) args xs rest := by
      rw [instantiateLevelParams_instantiate1]
      exact hsub
    obtain ⟨rest₂, h₂⟩ := TeleFitI.instLev_down hcp hsub'
      (fun a ha => hshape a (List.mem_cons_of_mem _ ha))
      (fvarsBelow_instantiate1_gen (by
        simp only [Expr.fvarsBelow]
        have hw2 := hwarg
        simp only [WScoped] at hw2
        exact hw2.1) 0 hfbe'.2)
    refine ⟨rest₂, TeleFitI.cons ?_ ?_ hx hfbe'.2 ?_ rfl
      (by simp [AnnotOk]) h₂⟩
    · rw [← interp_instLevels hcp]
      exact hity
    · simpa [interpExpr] using hiarg
    · simp only [WScoped]
      have hi : i₀ < d := by
        have hw2 := hwarg
        simp only [WScoped] at hw2
        exact hw2.1
      exact ⟨hi, trivial⟩

/-- Change the level assignment of a fit off the telescope's defined
parameters. -/
theorem TeleFitI.params_ext {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) (hcp : ConstValParams cval env) :
    ∀ {args : List Expr} {e : Expr} {vsl : List V} {rest : Expr},
      TeleFitI V cval env φ₁ d ρ e args vsl rest →
      e.allLevelParamsDefined ps = true →
      (∀ a ∈ args, ∃ i n, a = .fvar i n (.sort .zero)) →
      ∃ rest₂, TeleFitI V cval env φ₂ d ρ e args vsl rest₂
  | [], e, vsl, rest, hfit, _, _ => by
    cases hfit with
    | nil => exact ⟨e, TeleFitI.nil⟩
  | arg :: args, e, vsl, rest, hfit, hps, hshape => by
    obtain ⟨n, dom, body, m, rfl⟩ :
        ∃ n dom body m, e = .forallE n dom body m := by
      cases hfit; exact ⟨_, _, _, _, rfl⟩
    have hps' : dom.allLevelParamsDefined ps = true ∧
        body.allLevelParamsDefined ps = true := by
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hps
      exact ⟨hps.1.1, hps.1.2⟩
    obtain ⟨i₀, n₀, rfl⟩ := hshape arg List.mem_cons_self
    cases hfit with
    | @cons _ _ _ _ _ _ x xs A rest hity hiarg hx hfbI hwarg hbarg hAarg
        hsub =>
    obtain ⟨rest₂, h₂⟩ := TeleFitI.params_ext hφ hcp hsub
      (allLevelParamsDefined_instantiate1 (by rfl) 0 hps'.2)
      (fun a ha => hshape a (List.mem_cons_of_mem _ ha))
    refine ⟨rest₂, TeleFitI.cons ?_ ?_ hx hfbI hwarg hbarg
      (by simp [AnnotOk]) h₂⟩
    · rw [← interp_params_ext hcp hφ dom d ρ hps'.1]
      exact hity
    · simpa [interpExpr] using hiarg

/-- A value-spine fit transfers between environments agreeing on the
level parameters of stored constants (e.g. differing only in a
recursor's rule list). -/
theorem TeleFit.env_levelext {env₁ env₂ : Env}
    (henv : ∀ n, (env₁.find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported env₁ = natLitSupported env₂)
    (hstr : strLitSupported env₁ = strLitSupported env₂) :
    ∀ {d : Nat} {ρ : Nat → V} {e : Expr} {vs : List V} {d' : Nat}
      {ρ' : Nat → V} {rest : Expr},
      TeleFit V cval env₁ φ d ρ e vs d' ρ' rest →
      TeleFit V cval env₂ φ d ρ e vs d' ρ' rest := by
  intro d ρ e vs d' ρ' rest ht
  induction ht with
  | nil => exact TeleFit.nil
  | cons hity hx ht ih =>
    refine TeleFit.cons ?_ hx ih
    rw [← interp_env_ext henv hnat hstr _ _ _]
    exact hity

end Setlec
