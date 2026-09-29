module

public import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge

public section

/-!
# The target rule's `ih` openers

The certificate bundle's third opening at the target data: the `ih`
variables are the openers of a generated Π-tower over their `ih` types
(`ihTeleOf`), which are bvar-closed, so opening it at the frame yields
exactly the variables `fvar (B + r) tyᵣ` (`ihFvarsAt`); and an `ih`
type, inferred at the frame (`TargetCallRun.hihTy`), reads there and is
graded under the frame's context.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo CheckMode FEnv BlockShape BlockParts
  TargetMajor RecShape)

universe w

/-! ## The `ih` openers' generated tower -/

section IhTele

/-- The `ih` variables' generated Π-tower: their types, then `Sort 0`. -/
@[expose] def ihTeleOf : List Expr → Expr
  | [] => .sort .zero
  | ty :: tys => .forallE ty (ihTeleOf tys) default

theorem ihTeleOf_bounded : ∀ {tys : List Expr},
    (∀ t ∈ tys, t.looseBVarsBounded 0 = true) → (ihTeleOf tys).looseBVarsBounded 0 = true
  | [], _ => rfl
  | ty :: tys, h => by
    simp only [ihTeleOf, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨h ty List.mem_cons_self, ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le _)
      (ihTeleOf_bounded fun t ht => h t (List.mem_cons_of_mem _ ht))⟩

theorem ihTeleOf_WScoped {B : Nat} : ∀ {tys : List Expr},
    (∀ t ∈ tys, Expr.WScoped B t) → Expr.WScoped B (ihTeleOf tys)
  | [], _ => by simp [ihTeleOf, Expr.WScoped]
  | ty :: tys, h => by
    rw [ihTeleOf, Expr.WScoped]
    exact ⟨h ty List.mem_cons_self, ihTeleOf_WScoped fun t ht => h t (List.mem_cons_of_mem _ ht)⟩

theorem ihFvarsAt_cons (B : Nat) (ty : Expr) (tys : List Expr) :
    ihFvarsAt B (ty :: tys) = Expr.fvar B ty :: ihFvarsAt (B + 1) tys := by
  simp only [ihFvarsAt, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- **Opening the generated tower** at the frame yields the `ih`
variables. -/
theorem openPisAtFvars_ihTeleOf : ∀ {tys : List Expr},
    (∀ t ∈ tys, t.looseBVarsBounded 0 = true) → ∀ B : Nat,
    ConLeche.openPisAtFvars tys.length (ihTeleOf tys) B = some (ihFvarsAt B tys, .sort .zero)
  | [], _, B => by simp [ConLeche.openPisAtFvars, ihTeleOf, ihFvarsAt]
  | ty :: tys, h, B => by
    have hb := ihTeleOf_bounded (tys := tys) fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ih := openPisAtFvars_ihTeleOf (tys := tys) (fun t ht => h t (List.mem_cons_of_mem _ ht))
      (B + 1)
    simp only [List.length_cons, ihTeleOf, ConLeche.openPisAtFvars,
      ConLeche.Expr.instantiate1_eq_self hb, ih, ihFvarsAt_cons]

end IhTele

/-! ## An `ih` type reads at the frame, graded -/

section IhTy

variable {V : Type w} [SetTheory V] {μ : CheckMode}

end IhTy

end ConLeche.Model
