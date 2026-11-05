module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.PropWhen
import ConLeche.Model.OpenedCtx
import ConLeche.Semantics.Frame
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Rules.IotaSoundKit

/-!
# The walk to a family's sort, and the ι case split's verdict

Task #480.  A family's former is stored at its declared type; a use that needs its
sort walks the binders, reducing, down to a sort (`FormerSort`).  What the walk
establishes is a tower over that universe at every valuation, up to the point,
of which a reduction claims nothing (`FormerSortSem`).  That is what a family's
never being `Prop` at some levels means to the laws (`FamNZ`).
-/

@[expose] public section

namespace ConLeche.Model.Rules

open ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env} {φ : Name → Nat}

/-- The walk's end: a sort, by a reduction. -/
theorem FormerSort.sort_sound {d : Nat} {e : Expr} {s : Level}
    (hr : RedSem m φ d e (.sort s)) : FormerSortSem m φ d 0 e s := by
  intro hf Δa ea hC hea ρ hρ hL hw
  by_cases hpt : interp V ρ ea = pt
  · exact .inl hpt
  obtain ⟨-, -, ea', hea', hall⟩ := hr hf hC hea
  obtain ⟨-, heq⟩ := hall ρ hρ hL hw hpt
  rw [denote] at hea'
  cases hea'
  exact .inr heq

/-- The walk's step: a binder, by a reduction, and the walk at every value of it. -/
theorem FormerSort.pi_sound {d n : Nat} {e dom b : Expr} {s : Level}
    (hr : RedSem m φ d e (.forallE dom b))
    (hrec : FormerSortSem m φ (d + 1) n (b.instantiate1 (.fvar d dom)) s) :
    FormerSortSem m φ d (n + 1) e s := by
  intro hf Δa ea hC hea ρ hρ hL hw
  by_cases hpt : interp V ρ ea = pt
  · exact .inl hpt
  obtain ⟨hf', hsub, ea', hea', hall⟩ := hr hf hC hea
  obtain ⟨hw', heq⟩ := hall ρ hρ hL hw hpt
  obtain ⟨tyA, baA, htyA, hbaA, rfl⟩ := denote_forallE_inv hea'
  have hC' := hC.of_subset hsub
  have hL' := hL.of_subset hsub
  obtain ⟨hws, hbd, hLb⟩ := hf'
  simp only [Expr.WScoped] at hws
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbd
  have hLty : Expr.LeavesBounded dom := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  have hLbody : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
  obtain ⟨hwopen, hbopen, hLopen⟩ := frame_open2 hws.1 hbd.1 hws.2 hbd.2 hLty hLbody
  refine .inr ⟨_, _, heq.trans (interp_pi V ρ tyA baA), fun x hx => ?_⟩
  have hdomTy : WellDenotedTy V ρ tyA := ⟨hw'.1, hw'.2.1⟩
  exact hrec ⟨hwopen, hbopen, hLopen⟩ (CtxOkS.openS hC'.forallE_ty hC'.forallE_body htyA) hbaA
    (cons x ρ) (Sat_cons V hρ hx)
    (LeavesGr.open hC'.forallE_ty hC'.forallE_body hL'.forallE_ty hL'.forallE_body htyA hdomTy)
    (hw'.2.2.1 x hx)

/-- The ι case split's verdict, its K rule and its three reasons. -/
theorem IotaCase.three_sound {isK : Bool} {cvj : ConstantVal} {us : List Level} :
    IotaCaseSem m φ isK cvj us true := fun h => nomatch h

theorem IotaCase.k_sound {cvj : ConstantVal} {us : List Level} :
    IotaCaseSem m φ true cvj us false := fun _ h => nomatch h

theorem IotaCase.never_sound {cvj cvT : ConstantVal} {caps : ConLeche.IndCaps} {us : List Level}
    (hfam : ConLeche.ctorFamily env.find? cvj = some (cvT, caps))
    (hlen : cvT.levelParams.length = us.length)
    (hnz : ConLeche.formerNeverZero cvT us = true) :
    IotaCaseSem m φ false cvj us false :=
  fun _ _ => ⟨cvT, caps, hfam, hlen, .inl hnz⟩

/-- A level whose zero-ness datum is never is not zero. -/
theorem eval_ne_zero_of_isNever {s : Level} (hnv : (Level.zeronessOf s).isNever = true)
    (φ : Name → Nat) : s.eval φ ≠ 0 := by
  intro h0
  have hsnd := ConLeche.PropWhen.zeronessOf_sound φ s
  rw [h0] at hsnd
  cases hz : Level.zeronessOf s with
  | never => rw [hz] at hsnd; exact nomatch hsnd
  | ifAllZero ps => rw [hz] at hnv; exact nomatch hnv

/-- **The walk reaching a sort, at the use's levels**: its tower, closed. -/
theorem formerSort_tower (hin : RulesInputs V m φ) {T : Name} {cvT : ConstantVal}
    {caps : ConLeche.IndCaps} {us : List Level} {s : Level}
    (hT : env.find? T = some (.indInfo cvT caps)) (hlen : us.length = cvT.levelParams.length)
    (hsort : FormerSortSem m φ 0 (caps.nparams + caps.nIdx)
      (cvT.type.instantiateLevelParams cvT.levelParams us) s) :
    ∀ ta : Term, denote m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us) = some ta →
      ∀ ρ : Nat → V, TowerEndsPt (caps.nparams + caps.nIdx) (interp V ρ ta) (s.eval φ) := by
  intro ta hta ρ
  obtain ⟨ta', hta', hok, -, hnf, hbd⟩ := constTy_pkg hin.const_ty hT (show us.length = _ from hlen)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hta' hok hnf hbd
  obtain rfl : ta' = ta := Option.some.inj ((hta' 0).symm.trans hta)
  obtain ⟨hf, hC⟩ := frame_of_not_hasFvar (m := m) (Δa := []) (d := 0) hnf hbd rfl
  exact hsort hf hC hta ρ (Sat_nil V ρ)
    (LeavesGr.of_fvarLeaves_nil (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf)) (hok ρ)

theorem IotaCase.walk_sound (hin : RulesInputs V m φ) {cvj cvT : ConstantVal}
    {caps : ConLeche.IndCaps} {us : List Level} {s : Level}
    (hfam : ConLeche.ctorFamily env.find? cvj = some (cvT, caps))
    (hlen : cvT.levelParams.length = us.length)
    (hnone : ConLeche.formerResSort cvT.type = none)
    (hsort : FormerSortSem m φ 0 (caps.nparams + caps.nIdx)
      (cvT.type.instantiateLevelParams cvT.levelParams us) s)
    (hnv : (Level.zeronessOf s).isNever = true) :
    IotaCaseSem m φ false cvj us false := by
  intro _ _
  obtain ⟨T, _, -, hT⟩ := ctorFamily_find hfam
  refine ⟨cvT, caps, hfam, hlen, .inr ⟨hnone, s.eval φ, ?_, fun ta hta ρ => ?_⟩⟩
  · exact eval_ne_zero_of_isNever hnv φ
  · exact formerSort_tower hin hT hlen.symm hsort ta hta ρ

/-- A level that is zero everywhere evaluates to zero. -/
theorem eval_of_isAlwaysZero {s : Level} (h : s.isAlwaysZero = true) (φ : Name → Nat) :
    s.eval φ = 0 := by
  have hsnd := ConLeche.PropWhen.zeronessOf_sound φ s
  unfold Level.isAlwaysZero at h
  split at h
  · next hz =>
    rw [hz] at hsnd
    simpa using hsnd.symm
  · exact nomatch h

end ConLeche.Model.Rules
