module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructFrameKit

public section

/-!
# The rule rows at an OUTSIDE class, at the CHAIN frame

The graph producer (`graphRecPre_core`) reads the rule rows `hrule` and
`hdec` at the chain frame `chainFrame K a ρ`, where the rule data are
the base-frame forms lifted past the `K` chain binders at their own
depths (`liftDomsK`, `liftN`; the member rows' `blockRecFdomsK` etc.).
At an outside class the base-frame forms are the target check's field
domains and fired spine (`tgtFdomsAV`, `tgtMkAV`) and the class's
index expressions (`tgtOutEs`, the substituted recorded result indices).

* `chainFit_base` — the chain move, once: a spine fitting the lifted
  prefix-and-field data at the chain frame fits the base data at the
  base frame (the prefix domains are closed, `blockRecPdomsK_run`);
* `tgtOutDecK` — `hdec` at an outside class;
* `tgtOutRuleK` — `hrule` at an outside class: the prefix, the class's
  index values (which fit the container's index telescope, so the
  recursor's index binders, `tgtOutIdxConv`) and the fired
  spine (the injection, in the carrier at that tuple, which is the
  major's domain there, `tgtOutMajor`) fit the recursor's binder data.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The target field domains, lifted past `K` chain binders. -/
@[expose] def tgtFdomsK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (c i : Nat) : List AnnotTerm :=
  liftDomsK K (blockRulePdomsAV acval envC p (tgtRs out) ψ c).length
    (tgtFdomsAV p out acval envC ψ c i)

/-- The target fired spine, lifted past `K` chain binders. -/
@[expose] def tgtMkK (K : Nat) (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (ψ : Name → Nat)
    (c i : Nat) : AnnotTerm :=
  (tgtMkAV p out acval envC ψ c i).liftN K
    ((blockRulePdomsAV acval envC p (tgtRs out) ψ c).length
      + (tgtFdomsAV p out acval envC ψ c i).length)

/-- An index-expression list, lifted past `K` chain binders at depth `n`. -/
@[expose] def liftEsK (K n : Nat) (es : List AnnotTerm) : List AnnotTerm :=
  es.map fun e => e.liftN K n

/-- **The chain move**: a spine fitting the lifted prefix-and-field data
at the chain frame fits the base data at the base frame, when the prefix
domains are unchanged by the lift. -/
theorem chainFit_base {K : Nat} {a ρ : Nat → V} {pd fd : List AnnotTerm}
    (hpK : liftDomsK K 0 pd = pd) {xs fs : List V} (hxl : xs.length = pd.length)
    (h : SpineFit (chainFrame K a ρ) (pd ++ liftDomsK K pd.length fd) (xs ++ fs)) :
    SpineFit ρ (pd ++ fd) (xs ++ fs) := by
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv h
  have hl₁ : as₁.length = xs.length := by rw [h1.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  rw [← hpK] at h1
  have h1' := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) pd [] as₁).mp h1
  rw [← hxl] at h2
  have h2' := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) fd as₁ as₂).mp h2
  exact SpineFit.append h1' h2'

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

end Rows

end ConLeche.Model
