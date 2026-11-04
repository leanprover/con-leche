module

public import ConLeche.Model.Currency
public import ConLeche.Model.OpenedCtx
import ConLeche.Model.Rules.RedSoundKit
public section

/-!
# Gradings read back out of `.pi` readings and application spines

`WellDenoted` is conjunctive at `.pi` and `.app`, so a
graded reading's domain, body and arguments are graded — each one
projection.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-! ## The `.pi` split, in the P currency -/

/-! ## Application spines, graded backwards -/

/-- An application's argument is graded when the application is. -/
theorem WellDenoted_app_arg {ρ : Nat → V} {g a : Term}
    (h : WellDenoted V ρ (.app g a)) : WellDenoted V ρ a :=
  (cast (WellDenoted_app V ρ g a) h).2.1

/-- **Every argument of a graded application spine is graded.** -/
theorem WellDenoted_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List Term) {g : Term},
      WellDenoted V ρ (Term.mkAppN g as) → ∀ a ∈ as, WellDenoted V ρ a := by
  intro as
  induction as with
  | nil => intro g _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro g h a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact WellDenoted_app_arg (Rules.mkAppN_head xs h)
    · exact ih (g := .app g x) h a ha'

end ConLeche.Model
