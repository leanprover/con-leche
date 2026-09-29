module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.InstSpine
import ConLeche.Verify.AbstractRange
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InstLevels
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.NestedRecRest
public import ConLeche.Model.Inductives.BlockRecAssembly
public import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndOpenRev
import ConLeche.Model.RecRulesCons
import ConLeche.Model.Levels
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# The nested recursors' stage: the `.nested` pins' law

`tgtRecPinsOk`: `RecRulePinsOk` at every stored rule of the target
family.  A rule fires `.nested` only at an OUTSIDE major
(`tgtFireOf`); there its pins are the major's parameters closed over the
rule prefix (`nestedRuleSyn_open`), so instantiated back at the prefix
openers they ARE the parameters (`instSeq_abstractRange_open`), whose
readings are graded at every prefix spine (`tgtOutSatW`).
`nestedPinGrade` (cnF = 0) carries that grading to the conjunct's chain.
-/

namespace ConLeche

/-! ## The round trip, the other way: closing then opening -/

/-- **Closing a term over the opened variables, then opening it again,
is the identity**: a term whose fvar leaves are all among the openers
`0 … n-1` (in position), abstracted over that range at cursor `c` and
instantiated back at the openers, is itself. -/
theorem instSeq_abstractRange_open {pre : List Expr}
    (hpre : ∀ j (hj : j < pre.length), ∃ ty, pre[j] = .fvar j ty) :
    ∀ (x : Expr) (c : Nat), x.looseBVarsBounded c = true →
      (∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ pre) →
      Expr.instSeq pre (c + pre.length - 1) (x.abstractRange 0 pre.length c) = x := by
  have hcl : ∀ a ∈ pre, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hty⟩ := hpre j hj
    rw [hty]; rfl
  cases hn : pre.length with
  | zero =>
    have : pre = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    intro x c _ _
    rw [abstractRange_zero]; rfl
  | succ n =>
  intro x
  induction x with
  | bvar i =>
    intro c hb _
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstractRange]
    exact instSeq_bvar_below pre _ i (by omega)
  | fvar idx ty _ =>
    intro c _ hl
    have hmem : Expr.fvar idx ty ∈ pre := hl (idx, ty) (by simp [Expr.fvarLeaves])
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hmem
    obtain ⟨ty', hty'⟩ := hpre k hk
    rw [hkx] at hty'
    injection hty' with hik hty''
    subst hik
    simp only [Expr.abstractRange]
    rw [if_pos (by omega)]
    have hget := Expr.instSeq_bvar pre (c + (n + 1) - 1) (c + (0 + (n + 1) - 1 - idx)) hcl
      (by omega) (by omega)
    rw [show c + (n + 1) - 1 - (c + (0 + (n + 1) - 1 - idx)) = idx by omega,
      List.getElem?_eq_getElem hk, hkx] at hget
    exact (Option.some.inj hget).symm
  | sort u =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | const nm us =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | lit l =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | app f a ihf iha =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [Expr.instSeq_app, ihf c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      iha c hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | lam ty b m iht ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_lam pre _ _ _ _ (by omega),
      iht c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) (by rw [show c + 1 = c + 1 from rfl]; exact hb.2)
        (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | forallE ty b m iht ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [Expr.instSeq_forallE pre _ _ _ _ (by omega),
      iht c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | letE ty v b iht ihv ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_letE pre _ _ _ _ (by omega),
      iht c hb.1.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      ihv c hb.1.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | proj s i e ih =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_proj, ih c hb (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]

/-- Level instantiation commutes with the reverse opening. -/
theorem openRev_instantiateLevelParams (ks : List Name) (us : List Level) (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      Verify.openRev d n (e.instantiateLevelParams ks us)
        = (Verify.openRev d n e).instantiateLevelParams ks us
  | 0, _ => rfl
  | n + 1, e => by
    simp only [Verify.openRev]
    rw [openRev_instantiateLevelParams ks us d n e, Expr.instantiateLevelParams_instantiate1]
    congr 2

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Pins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

end Pins

end ConLeche.Model
