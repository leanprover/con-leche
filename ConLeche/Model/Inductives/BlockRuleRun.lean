module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Rules.Recompose
import ConLeche.Model.Tiers
import ConLeche.Model.Inductives.BlockRecIdxConv

public section

/-!
# Opener lists and constant scoping at the rule stage

Opener lists (`FvarList`) extended by an opening, and `ConstsBound`
through `Expr.instPisAt` and the recursors' bare environment.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Opener lists -/

section Openers

omit [SetTheory V] in
/-- The empty opening list. -/
theorem fvarList_nil : FvarList 0 [] :=
  ⟨rfl, fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ hx => nomatch hx⟩

omit [SetTheory V] in
/-- **An opening EXTENDS an opener list**: opening `n` binders of a
subject scoped at `E`, at depth `E`, prepends the new openers (reversed)
to an `E`-long list. -/
theorem fvarList_of_open {E n : Nat} {L : List Expr} {e : Expr} {fvs : List Expr} {o : Expr}
    (hL : FvarList E L) (hop : ConLeche.openPisAtFvars n e E = some (fvs, o))
    (hw : Expr.WScoped E e) :
    FvarList (E + n) (fvs.reverse ++ L) := by
  have hlen : fvs.length = n := openPisAtFvars_length n hop
  have h := FvarList.openerExtend (r := n) hL
    (fun j x hx => ConLeche.openPisAtFvars_index n e E hop j x hx)
    (fun j x hx => openPisAtFvars_typeWScoped n hop hw j x hx) (by omega)
  rwa [List.take_of_length_le (by omega)] at h

end Openers

/-! ## The constant-scoping kit -/

section ConstsKit

variable {env : Env}

omit [SetTheory V] in
theorem constsBound_instPisAt :
    ∀ (sp : List Expr) {e : Expr} {ds : List Expr} {r : Expr},
      Expr.instPisAt sp e = some (ds, r) →
      ConstsBound env e → (∀ a ∈ sp, ConstsBound env a) → ConstsBound env r
  | [], e, ds, r, h, he, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ he
  | a :: sp, e, ds, r, h, he, hsp => by
    match e, h with
    | .forallE _ body _, h =>
      simp only [Expr.instPisAt, Option.map_eq_some_iff] at h
      obtain ⟨⟨ds', r'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      rw [constsBound_forallE] at he
      exact constsBound_instPisAt sp h'
        (ConstsBound.instantiate1 (hsp a List.mem_cons_self) body 0 he.2)
        (fun x hx => hsp x (List.mem_cons_of_mem _ hx))

end ConstsKit

end ConLeche.Model
