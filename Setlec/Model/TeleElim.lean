import Setlec.Model.InterpLemmas
import Setlec.Model.AnnotOkLemmas

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

end Setlec
