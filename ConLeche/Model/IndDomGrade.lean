module

public import ConLeche.Model.Currency
import ConLeche.Model.Rules.RedSoundKit
public section

/-!
# Gradings read back out of `.pi` readings and application spines

`WellDenoted`/`AnnotValid` are conjunctive at `.pi` and `.app`, so a
graded reading's domain, body and arguments are graded — each one
projection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The `.pi` split, in the P currency -/

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem WellDenotedV_pi_dom {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) : WellDenotedV V ρ A :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).1,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).1⟩

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem WellDenotedV_pi_body {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) {x : V}
    (hx : x ∈ˢ interp V ρ A) : WellDenotedV V (cons x ρ) B :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).2 x hx,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).2.1 x hx⟩

/-! ## Application spines, graded backwards -/

/-- An application's argument is graded when the application is. -/
theorem WellDenotedV_app_arg {ρ : Nat → V} {g a : AnnotTerm}
    (h : WellDenotedV V ρ (.app g a)) : WellDenotedV V ρ a :=
  ⟨((WellDenoted_app V ρ g a) ▸ h.1).2.1,
    ((AnnotValid_app V ρ g a) ▸ h.2).2⟩

/-- **Every argument of a graded application spine is graded.** -/
theorem WellDenotedV_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {g : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN g as) → ∀ a ∈ as, WellDenotedV V ρ a := by
  intro as
  induction as with
  | nil => intro g _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro g h a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact WellDenotedV_app_arg (Rules.mkAppN_head xs h)
    · exact ih (g := .app g x) h a ha'

end ConLeche.Model
