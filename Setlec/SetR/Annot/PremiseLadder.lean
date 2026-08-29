import Setlec.SetR.Annot.SimSubst
import Setlec.SetR.Main

/-!
# The premise ladder's countermodel, mechanized (task #151 tier C)

`SortSubstStable`'s β premise went through two refuted semantic forms
before the v3 (run-shaped) currency — the DESIGN "REFUTATION" /
"SECOND REFUTATION" records.  This file banks the refutations
mechanically, so the two dead rungs stay dead: anyone later
"simplifying" the premise back to a membership or an interp-equality
re-opens a proof of `False`.

## The countermodel family: sort-blind carriers

One family kills both rungs.  The pinned basis' `PUnit` is
universe-polymorphic and its valuation is **level-uniform**:
`cval PUnit ψ = punitT (ψ u)` (`BasisPinnedTT` + `pinnedDirectT`) and
`interp (punitT u) = unitSet` *for every `u`* — the carrier does not
see the sort.  So with

* `ty := PUnit.{2}` (the λ's domain annotation, sort `2`),
* `a  := PUnit.unit.{0}` (the argument, inferring `PUnit.{0}`, sort `0`),
* `body := .bvar 0` (the base case: `lamSortE` is `sortOfE` of the
  leaf itself),

the checker computes `v = 2` on the opened side and `v' = 0` on the
substituted side — while `interp ⟦a⟧ = pt ∈ˢ unitSet = interp ⟦ty⟧`
(rung 1's premise holds) and `interp ⟦ta⟧ = unitSet = interp ⟦ty⟧`
(rung 2's premise holds).  The v3 premise correctly *fails* here: the
checker's `defeq(PUnit.{0}, PUnit.{2})` is `false` — equal shadows,
no certifying run.

## Mechanization notes

* Parametric in `V` — `∀ V [SetTheory V], ¬ rung`: the env is built by
  the *actual checker* (`checkDecls` on `[.basisDecl .punitK]`), its
  model by the *actual acceptance theorem* (`checkDecls_sound_R`), and
  the carrier facts by the basis-pinned valuation clause.  No custom
  model, no axioms beyond the standard three.
* Checker runs are evaluated by `decide +kernel`: the elaborator-side
  `decide` stalls on `@[irreducible] whnfLoopFuel`, the kernel does
  not respect reducibility and evaluates the whole install + runs in
  well under a second.
* The run fuel (`f0 := 10`) is deliberately independent of the
  install fuel (`F0 := 200`) — the statement quantifies its own fuel.
-/

namespace Setlec.SetR.Interp2.Ladder

open Setlec.TT Setlec.TTVerify
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level Declaration BasisKind
  inferTypeCore whnf checkDecls fueledOps punitName punitUnitName)
open SetTheory

/-! ## The countermodel's data -/

/-- The verified mode. -/
def μ0 : CheckMode := .setModel
/-- Install fuel (for `checkDecls`). -/
def F0 : Nat := 200
/-- Run fuel (for the `lamSortE` hypotheses) — independent of `F0`. -/
def f0 : Nat := 10
/-- The stream: exactly the pinned `PUnit` basis block. -/
def ds0 : List Declaration := [.basisDecl .punitK]
/-- The (irrelevant) level assignment. -/
def φ0 : Name → Nat := fun _ => 0
/-- The binder name. -/
def nX : Name := .str .anonymous "x"
/-- The λ's domain annotation: `PUnit.{2} : Sort 2`. -/
def tyE : Expr := .const punitName [.succ (.succ .zero)]
/-- The argument: `PUnit.unit.{0} : PUnit.{0}`. -/
def aE : Expr := .const punitUnitName [.zero]

/-- The one decided probe: the install accepts, both sort computations
succeed with the *diverging* numerals, and the two constants are
stored as their pins. -/
def probeB : Bool :=
  match checkDecls μ0 (fueledOps μ0 F0) ds0 with
  | .ok e =>
    (Setlec.SetR.Interp2.lamSortE μ0 e φ0 f0 1 (.fvar 0 nX tyE) == some 2) &&
    (Setlec.SetR.Interp2.lamSortE μ0 e φ0 f0 0 aE == some 0) &&
    (e.find? punitName == some Setlec.punitA) &&
    (e.find? punitUnitName == some Setlec.punitUnitA)
  | .error _ => false

theorem probeB_true : probeB = true := by decide +kernel

/-! ## Syntactic helpers -/

/-- Instantiating `.bvar 0` is the identity — the base-case shape. -/
theorem inst1_bvar0 (x : Expr) : (Expr.bvar 0).instantiate1 x = x := by
  simp [Expr.instantiate1]

/-! ## The dead rungs, stated

Mirrors of the sealed `SortSubstStable` with only the β premise
swapped for the refuted rung.  Keep these in sync with the statement
if it ever changes shape — the refutations below are only worth their
salt against the real quantifier pattern. -/

/-- **Rung 1 (refuted)**: the β premise as argument-membership. -/
def SortSubstStable_mem (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {env : Env} (mS : EnvS V env) (φ : Name → Nat)
    {fuel d : Nat} {n : Name} {ty body a : Expr} {Δv : List VExpr}
    {v v' : Nat},
    μ.verified = true →
    lamSortE μ env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some v →
    lamSortE μ env φ fuel d (body.instantiate1 a) = some v' →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) →
    (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) →
    CtxOkR μ mS.cval env φ d Δv a →
    CtxOkR μ mS.cval env φ d Δv ty →
    ∀ {tyv : VExpr}, denote mS.cval env φ d ty = some tyv →
    ∀ {av : VExpr}, denote mS.cval env φ d a = some av →
    (∀ ρ : Nat → V, Sat V Δv ρ → interp V ρ av ∈ˢ interp V ρ tyv) →
    ∀ ρ : Nat → V, Sat V Δv ρ → v = v'

/-- **Rung 2 (refuted)**: the β premise as type-level interp equality
of the argument's (any-fuel) inferred type with the domain. -/
def SortSubstStable_interpEq (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {env : Env} (mS : EnvS V env) (φ : Name → Nat)
    {fuel d : Nat} {n : Name} {ty body a : Expr} {Δv : List VExpr}
    {v v' : Nat},
    μ.verified = true →
    lamSortE μ env φ fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) = some v →
    lamSortE μ env φ fuel d (body.instantiate1 a) = some v' →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d ty → ty.looseBVarsBounded 0 = true →
    Expr.LeavesBounded ty →
    Expr.WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) →
    (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) →
    CtxOkR μ mS.cval env φ d Δv a →
    CtxOkR μ mS.cval env φ d Δv ty →
    ∀ {tyv : VExpr}, denote mS.cval env φ d ty = some tyv →
    ∀ {av : VExpr}, denote mS.cval env φ d a = some av →
    (∀ (fuel' : Nat) {ta : Expr},
      inferTypeCore μ env fuel' d a = .ok ta →
        ∀ {tav : VExpr}, denote mS.cval env φ d ta = some tav →
          ∀ ρ : Nat → V, Sat V Δv ρ → interp V ρ tav = interp V ρ tyv) →
    ∀ ρ : Nat → V, Sat V Δv ρ → v = v'

/-! ## The countermodel facts -/

/-- The probe, destructured once: the accepted env and the four
run/storage facts. -/
private theorem cm_facts :
    ∃ env : Env,
      checkDecls μ0 (fueledOps μ0 F0) ds0 = .ok env ∧
      lamSortE μ0 env φ0 f0 1 (.fvar 0 nX tyE) = some 2 ∧
      lamSortE μ0 env φ0 f0 0 aE = some 0 ∧
      env.find? punitName = some Setlec.punitA ∧
      env.find? punitUnitName = some Setlec.punitUnitA := by
  have hp := probeB_true
  unfold probeB at hp
  cases hrun : checkDecls μ0 (fueledOps μ0 F0) ds0 with
  | error err => rw [hrun] at hp; exact nomatch hp
  | ok env =>
    rw [hrun] at hp
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨env, rfl, hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-- The level assignment the domain's denotation carries (`PUnit.{2}`). -/
def ψ2v : Name → Nat :=
  Level.substFn φ0
    (Setlec.ConstantInfo.toConstantVal Setlec.punitA).levelParams
    [.succ (.succ .zero)]

/-- The level assignment the argument's denotation carries
(`PUnit.unit.{0}`). -/
def ψ0v : Name → Nat :=
  Level.substFn φ0
    (Setlec.ConstantInfo.toConstantVal Setlec.punitUnitA).levelParams
    [.zero]

/-- Ditto for the argument's *inferred type* (`PUnit.{0}`). -/
def ψ0v' : Name → Nat :=
  Level.substFn φ0
    (Setlec.ConstantInfo.toConstantVal Setlec.punitA).levelParams
    [.zero]

section WithModel

variable {V : Type w} [SetTheory V] {env : Env}

/-- The stored `PUnit` is valued by its level-uniform pin: the carrier
does not see the sort.  (`ψ` stays abstract — this is the sort-blind
fact itself.) -/
private theorem cval_punit (mS : EnvS V env)
    (hfT : env.find? punitName = some Setlec.punitA) (ψ : Name → Nat) :
    mS.cval punitName ψ = punitT (ψ Setlec.uN) :=
  (mS.basis_pinned punitName _ hfT (by decide)).2 _ ψ
    (by simp +decide [pinnedDirectT, punitT])

/-- Ditto for the constructor. -/
private theorem cval_punitUnit (mS : EnvS V env)
    (hfU : env.find? punitUnitName = some Setlec.punitUnitA)
    (ψ : Name → Nat) :
    mS.cval punitUnitName ψ = punitUnitT (ψ Setlec.uN) :=
  (mS.basis_pinned punitUnitName _ hfU (by decide)).2 _ ψ
    (by simp +decide [pinnedDirectT, punitUnitT])

private theorem denote_tyE (mS : EnvS V env)
    (hfT : env.find? punitName = some Setlec.punitA) :
    denote mS.cval env φ0 0 tyE = some (mS.cval punitName ψ2v) := by
  rw [tyE, denote_const, hfT]
  exact if_pos (by decide)

private theorem denote_aE (mS : EnvS V env)
    (hfU : env.find? punitUnitName = some Setlec.punitUnitA) :
    denote mS.cval env φ0 0 aE = some (mS.cval punitUnitName ψ0v) := by
  rw [aE, denote_const, hfU]
  exact if_pos (by decide)

private theorem denote_taE (mS : EnvS V env)
    (hfT : env.find? punitName = some Setlec.punitA) :
    denote mS.cval env φ0 0 (.const punitName [.zero]) =
      some (mS.cval punitName ψ0v') := by
  rw [denote_const, hfT]
  exact if_pos (by decide)

end WithModel

/-- **Every** inference of the argument — at any fuel — returns
`PUnit.{0}`: the `const` clause never consults the knot, so the
characterization is fuel-free once the storage fact is in hand. -/
private theorem infer_aE_char {env : Env}
    (hfU : env.find? punitUnitName = some Setlec.punitUnitA) :
    ∀ (fuel' : Nat) {ta : Expr},
      inferTypeCore μ0 env fuel' 0 aE = .ok ta →
        ta = .const punitName [.zero] := by
  intro fuel' ta hta
  cases fuel' with
  | zero => exact nomatch hta
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at hta
    simp only [aE, Setlec.inferBody, Setlec.viewM, Setlec.Expr.view,
      Bind.bind, Except.bind, pure, Except.pure] at hta
    rw [hfU] at hta
    simp +decide at hta
    exact hta.symm

/-! ## The refutations -/

/-- **Rung 1 is false**, at every `SetTheory` instance. -/
theorem SortSubstStable_mem_refuted (V : Type w) [SetTheory V] :
    ¬ SortSubstStable_mem V := by
  intro h
  obtain ⟨env, hrun, h1, h2, hfT, hfU⟩ := cm_facts
  obtain ⟨mS⟩ := checkDecls_sound_R (V := V) hrun
  have h1' : lamSortE μ0 env φ0 f0 (0 + 1)
      ((Expr.bvar 0).instantiate1 (.fvar 0 nX tyE)) = some 2 := by
    rw [inst1_bvar0]; exact h1
  have h2' : lamSortE μ0 env φ0 f0 0
      ((Expr.bvar 0).instantiate1 aE) = some 0 := by
    rw [inst1_bvar0]; exact h2
  have hcontra :=
    h (μ := μ0) (mS := mS) φ0 (fuel := f0) (d := 0) (n := nX)
      (body := .bvar 0) (Δv := [])
      rfl h1' h2'
      (Expr.WScoped.of_wscopedB (by simp [Setlec.Expr.wscopedB, aE]))
      (by decide)
      (Expr.LeavesBounded.of_not_hasFvar (by decide))
      (Expr.WScoped.of_wscopedB (by simp [Setlec.Expr.wscopedB, tyE]))
      (by decide)
      (Expr.LeavesBounded.of_not_hasFvar (by decide))
      (by rw [inst1_bvar0]
          exact Expr.WScoped.of_wscopedB
            (by simp [Setlec.Expr.wscopedB, tyE]))
      (by rw [inst1_bvar0]; decide)
      (by rw [inst1_bvar0]
          intro l hl
          simp [Setlec.Expr.fvarLeaves, tyE] at hl
          subst hl; decide)
      (CtxOkR.nil (by simp [Setlec.Expr.fvarLeaves, aE]))
      (CtxOkR.nil (by simp [Setlec.Expr.fvarLeaves, tyE]))
      (denote_tyE mS hfT) (denote_aE mS hfU)
      (by -- the membership premise HOLDS: sort-blind carriers
        intro ρ _
        rw [cval_punitUnit mS hfU, cval_punit mS hfT,
          interp_punitUnitT, interp_punitT]
        exact mem_unitSet_iff.mpr rfl)
      (fun _ => pt) (Sat_nil V _)
  exact absurd hcontra (by decide)

/-- **Rung 2 is false**, at every `SetTheory` instance — by the *same*
countermodel: type-level interp equality is sort-blind too. -/
theorem SortSubstStable_interpEq_refuted (V : Type w) [SetTheory V] :
    ¬ SortSubstStable_interpEq V := by
  intro h
  obtain ⟨env, hrun, h1, h2, hfT, hfU⟩ := cm_facts
  obtain ⟨mS⟩ := checkDecls_sound_R (V := V) hrun
  have h1' : lamSortE μ0 env φ0 f0 (0 + 1)
      ((Expr.bvar 0).instantiate1 (.fvar 0 nX tyE)) = some 2 := by
    rw [inst1_bvar0]; exact h1
  have h2' : lamSortE μ0 env φ0 f0 0
      ((Expr.bvar 0).instantiate1 aE) = some 0 := by
    rw [inst1_bvar0]; exact h2
  have hcontra :=
    h (μ := μ0) (mS := mS) φ0 (fuel := f0) (d := 0) (n := nX)
      (body := .bvar 0) (Δv := [])
      rfl h1' h2'
      (Expr.WScoped.of_wscopedB (by simp [Setlec.Expr.wscopedB, aE]))
      (by decide)
      (Expr.LeavesBounded.of_not_hasFvar (by decide))
      (Expr.WScoped.of_wscopedB (by simp [Setlec.Expr.wscopedB, tyE]))
      (by decide)
      (Expr.LeavesBounded.of_not_hasFvar (by decide))
      (by rw [inst1_bvar0]
          exact Expr.WScoped.of_wscopedB
            (by simp [Setlec.Expr.wscopedB, tyE]))
      (by rw [inst1_bvar0]; decide)
      (by rw [inst1_bvar0]
          intro l hl
          simp [Setlec.Expr.fvarLeaves, tyE] at hl
          subst hl; decide)
      (CtxOkR.nil (by simp [Setlec.Expr.fvarLeaves, aE]))
      (CtxOkR.nil (by simp [Setlec.Expr.fvarLeaves, tyE]))
      (denote_tyE mS hfT) (denote_aE mS hfU)
      (by -- the interp-equality premise HOLDS: sort-blind carriers
        intro fuel' ta hta tav hdenote ρ _
        obtain rfl := infer_aE_char hfU fuel' hta
        rw [denote_taE mS hfT] at hdenote
        obtain rfl := Option.some.inj hdenote
        rw [cval_punit mS hfT, cval_punit mS hfT,
          interp_punitT, interp_punitT])
      (fun _ => pt) (Sat_nil V _)
  exact absurd hcontra (by decide)

end Setlec.SetR.Interp2.Ladder
