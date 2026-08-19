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

end Setlec
