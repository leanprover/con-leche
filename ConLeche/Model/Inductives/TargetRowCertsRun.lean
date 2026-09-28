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
  TargetMajor TargetIh RecShape)

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

set_option maxHeartbeats 1000000 in
/-- **An `ih` type is graded** under the frame's context: it was
inferred there (`TargetCallRun.hihTy`, `InferClaim`). -/
theorem targetCall_ihTy_graded (hμ : μ.verifiedChecks = true) {envT : Env}
    {mT : EnvModel V envT} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F B k dA : Nat} {fam : ConLeche.TargetFamily} {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {absM mvF : Expr → Expr}
    {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF teles absM mvF B k dA pw ih)
    {L : List Expr} (hL : FvarList B L) {ρ : Nat → V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ B ρ Δ L)
    (hlT : ∀ l ∈ ih.ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hbT : ih.ty.looseBVarsBounded 0 = true) :
    ∃ T : AnnotTerm, denoteMeta mT.acval envT φ B ih.ty = some T ∧
      (∀ σ : Nat → V, Sat V Δ σ → WellDenotedV V σ T) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  have hFrT : Rules.Frame B ih.ty :=
    ⟨wscoped_of_leaves_mem hL _ hlT, hbT, fun l hl => hW.2.2.2.2.1 _ (hlT l hl)⟩
  have hCT := hW.ctxOk hacl1 hL hlT
  obtain ⟨T, hT⟩ := acceptedReads_of mT φ C.hihTy hFrT.1 hFrT.2.1 hFrT.2.2
  obtain ⟨-, -, -, -, hGT, -, -⟩ :=
    Rules.infer_sound hin (Rules.inferTypeCore_bridge C.hihTy) hFrT hCT hT
  exact ⟨T, hT, hGT⟩

/-- **An `ih` type reads** at the frame (it was inferred there). -/
theorem targetCall_ihTy_reads {envT : Env} (mT : EnvModel V envT) (φ : Name → Nat)
    {F B k dA : Nat} {fam : ConLeche.TargetFamily} {fvsPref fvsF : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {absM mvF : Expr → Expr}
    {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF teles absM mvF B k dA pw ih)
    (hws : Expr.WScoped B ih.ty) (hbT : ih.ty.looseBVarsBounded 0 = true)
    (hLB : Expr.LeavesBounded ih.ty) :
    ∃ T : AnnotTerm, denoteMeta mT.acval envT φ B ih.ty = some T :=
  acceptedReads_of mT φ C.hihTy hws hbT hLB

end IhTy

end ConLeche.Model
