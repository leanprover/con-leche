module

public import ConLeche.Model.Inductives.TargetNestOwn
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.SumKit

public section

/-!
# The class ↔ node reading tie (PRIMREC / NESTKN-NL, piece (i))

A pair `q` of the recursor route pairs a class with a node at an INSTANCE `I` (levels
`I.us`, parameters `I.ds` at the canonical parameter variables).  The node lemma reads
the node at the instance's FRAME — the instance's parameters read over the prefix's
parameter values (`instFr`, call-independent, `keyFrame_inst`).  This module ties the
class's own reading to it.

* `erasedEq_replaceFVars_vars` — a renaming of variables to variables of the same index
  (the route's `rn`) is invisible up to erasure;
* `seed_frame` — a SEED pair: the class's frame (`keyFrame` of its major's parameters at
  the rule prefix) IS the instance frame, the instance's parameters being the major's
  renamed (`SeedRK`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-- **Renaming variables to variables of the same index is invisible up to erasure.** -/
theorem erasedEq_replaceFVars_vars {f : Nat → Option Expr}
    (hf : ∀ i b, f i = some b → ∃ ty, b = .fvar i ty) :
    ∀ e : Expr, Expr.ErasedEq (e.replaceFVars f) e := by
  intro e
  induction e with
  | fvar i ty _ =>
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => exact Expr.ErasedEq.rfl _
    | some b =>
      obtain ⟨ty', rfl⟩ := hf i b hi
      simp [Expr.ErasedEq]
  | app a b iha ihb => exact ⟨iha, ihb⟩
  | lam ty b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | forallE ty b m iht ihb => exact ⟨rfl, iht, ihb⟩
  | letE ty v b iht ihv ihb => exact ⟨iht, ihv, ihb⟩
  | proj s i x ih => exact ⟨rfl, rfl, ih⟩
  | _ => exact Expr.ErasedEq.rfl _

section Frame

variable {env : Env} {mT : EnvModel V env} {φ : Name → Nat}

/-- **The instance frame**: the instance's parameters read at the prefix's parameter
count `nP`, over the prefix's parameter values `xs.take nP`. -/
@[expose] noncomputable def instFr (dsaI : List AnnotTerm) (nP : Nat) (xs : List V)
    (ρ : Nat → V) : Nat → V :=
  keyFrame dsaI nP (consList (xs.take nP) ρ)

/-- **A seed's frame is its instance's** (see the module docstring): the major's
parameters `ds` scoped at `nP` (variables below the block's parameters), the instance's
parameters erasure-equal to them renamed by `rn` (variables to variables of the same
index); then the class's frame at any prefix spine is the instance frame. -/
theorem seed_frame {nP rP : Nat} (hle : nP ≤ rP) {ds dsI : List Expr}
    {rn : Expr → Expr} (hrn : ∀ x, Expr.ErasedEq (rn x) x)
    (hdsE : dsI.map Expr.eraseFVarTys = (ds.map rn).map Expr.eraseFVarTys)
    (hws : ∀ x ∈ ds, Expr.WScoped nP x)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval env φ rP ds dsa)
    {dsaI : List AnnotTerm} (hdsaI : DenoteMetaSpine mT.acval env φ nP dsI dsaI)
    {xs : List V} (hxl : xs.length = rP) (ρ : Nat → V) :
    keyFrame dsa rP (consList xs ρ) = instFr dsaI nP xs ρ := by
  -- the instance's parameters read as the major's, at `nP`
  have hspine : DenoteMetaSpine mT.acval env φ nP ds dsaI := by
    have hl : dsI.length = ds.length := by
      have := congrArg List.length hdsE; simpa using this
    suffices ∀ (as bs : List Expr) (vs : List AnnotTerm), as.length = bs.length →
        (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.ErasedEq a b) →
        DenoteMetaSpine mT.acval env φ nP as vs → DenoteMetaSpine mT.acval env φ nP bs vs by
      refine this dsI ds dsaI hl (fun i a b ha hb => ?_) hdsaI
      have h1 : (dsI.map Expr.eraseFVarTys)[i]? = some a.eraseFVarTys := by simp [ha]
      rw [hdsE] at h1
      simp only [List.map_map, List.getElem?_map, hb, Option.map_some, Option.some.injEq,
        Function.comp] at h1
      exact Expr.ErasedEq.trans (Expr.eraseFVarTys_eq_iff.mp h1.symm) (hrn b)
    intro as
    induction as with
    | nil => intro bs vs hl _ h; cases bs <;> simp_all
    | cons a as ih =>
      intro bs vs hl he h
      cases bs with
      | nil => simp at hl
      | cons b bs =>
        cases h with
        | cons ha h' =>
          refine .cons ?_ (ih bs _ (by simpa using hl) (fun i a' b' h1 h2 =>
            he (i + 1) a' b' (by simpa using h1) (by simpa using h2)) h')
          rw [← denoteMeta_erasedEq (he 0 a b rfl rfl) nP]; exact ha
  -- the major's reading at the rule prefix is the lift
  have hl := DenoteMetaSpine.lift (m := mT) (φ := φ) hle hws hspine
  obtain rfl := DenoteMetaSpine.unique hdsa hl
  unfold instFr
  have hk := keyFrame_lift dsaI nP (xs.drop nP) (consList (xs.take nP) ρ)
  rw [show (xs.drop nP).length = rP - nP by simp [hxl]] at hk
  rw [← hk, ← consList_append, List.take_append_drop,
    show nP + (rP - nP) = rP by omega]

end Frame

end ConLeche.Model
