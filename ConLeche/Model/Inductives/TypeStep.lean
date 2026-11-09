module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLemmas

public section

/-!
# Walking types: the whnf step and the sort test, at the conditional claims

The positivity readers (`PosDerivMono`, `PosDerivNodes`, `PosDerivAcc`,
`NestPosRed`) walk the TYPES of constructor fields.  Under the conditional
claims (task #342, L9) a whnf step equates a subject with its reduct only
where the subject is not the point; a type never is ("not pt" source (1)),
so the readers carry the walked types' `IsTy` (`GradedTy`) and read their
steps through `red_sound_ty` (task #342, L12).

* `gradedTy_of_sort` — a term whose inferred type whnf's to a sort (the
  checker's `ensureSort`) reads as a graded type: its type reads as a
  universe ("not pt" source (1) for the type's own step), whose members are
  types (`IsTy_of_mem_univ`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- **The `GradedTy` ∀-splitter**: both the domain and the body are graded
TYPES (`WellDenoted.hoist_piTy` already gives the domain; the body's
`IsTy` at `ρ ⊨ A :: Δa` is the fibre `IsTy` at `ρ 0 ∈ ⟦A⟧` of the tail
valuation, the same move `Semantics.WellDenoted.hoist_pi` makes for the body's
grading). -/
theorem _root_.ConLeche.Semantics.WellDenoted.hoist_piTy' {Δa : List Term} {A B : Term}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenotedTy V ρ B) := by
  obtain ⟨hgAT, hgB⟩ := WellDenoted.hoist_piTy (V := V) h
  refine ⟨hgAT, fun ρ hρ => ⟨hgB ρ hρ, ?_⟩⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := (cast (WellDenoted_pi V _ A B) (h _ (Sat_tail hρ))).2.2.2 (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

/-- A `GradedTy` Π-type from `Graded` parts and their `IsTy` facts, the way
`graded_pi_intro` (`NestPosRed.lean`) does for `Graded`: the Π's own
`IsTy` is free (`IsTy_piV`). -/
theorem gradedTy_pi_intro {Δ : List Term} {A B : Term}
    (hA : Graded V Δ A) (hB : Graded V (A :: Δ) B)
    (hAt : ∀ ρ : Nat → V, Sat V Δ ρ → IsTy (interp V ρ A))
    (hBt : ∀ ρ : Nat → V, Sat V (A :: Δ) ρ → IsTy (interp V ρ B)) :
    GradedTy V Δ (.pi A B) := fun ρ hρ => by
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_pi]
    exact ⟨hA ρ hρ, hAt ρ hρ, fun x hx => hB _ (Sat_cons V hρ hx),
      fun x hx => hBt _ (Sat_cons V hρ hx)⟩
  · rw [interp_pi]; exact IsTy_piV

/-- **A term whose type is a sort reads as a graded type**: the inference
claim puts its reading in its type's, the type is a type (so the sort
test's whnf step is an equation, "not pt" source (1)), and it reads as a
universe, whose members are types. -/
theorem gradedTy_of_sort (hin : RulesInputs V m φ) {F d : Nat} {e ty : Expr} {u : Level}
    (hty : ConLeche.inferTypeCore .verified false env F d e = .ok ty)
    (hsort : ConLeche.ensureSortCore .verified false env F d ty = .ok u) (hf : Frame d e)
    {Δa : List Term} {ea : Term} (hC : CtxOk m φ d Δa e)
    (hea : denote m.acval env φ d e = some ea) : GradedTy V Δa ea := by
  have hI : InferSemFull m φ d e ty := infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty)
  obtain ⟨hft, hsub, ta, hta, hs⟩ := hI hf hC.toS hea
  obtain ⟨-, -, sa, hsa, hrs⟩ := red_sound hin
    (ConLeche.Rules.whnf_bridge (ConLeche.ensureSortCore_inv hsort)) hft
    (hC.toS.of_subset hsub) hta
  rw [denote_sort] at hsa
  obtain rfl := Option.some.inj hsa
  intro ρ hρ
  obtain ⟨hgE, hgT, hmem⟩ := hs ρ hρ (hC.leavesGr hρ)
  obtain ⟨-, heq⟩ := hrs ρ hρ ((hC.leavesGr hρ).of_subset hsub) hgT.1 hgT.2.ne_pt
  rw [heq, interp_sort] at hmem
  exact ⟨hgE, IsTy_of_mem_univ hmem⟩

end ConLeche.Model
