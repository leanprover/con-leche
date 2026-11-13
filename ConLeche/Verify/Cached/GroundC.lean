module

public import ConLeche.Verify.Cached.Grind
public import ConLeche.Cached.CoreC
import ConLeche.Verify.Ground.SimSite
import ConLeche.Verify.Ground.Fuel
import ConLeche.Verify.EnvBound

public section

/-!
# The ground gate against the specification's engine call (task #423)

The cached core runs the ground engine on the declaration's kept program
(`CState.ground4`), at `groundFuel` and its maximum `Nat` size
(`groundGateM`); the specification runs it on a fresh program, at
`2 * groundFuel + 1` and with no size bound (`groundSite`).  Where the
cached run answers, the specification's answers the same: the kept
program against a fresh one (`ground4_fresh`), then the bound against no
bound (`ground4BoolCoreF_unbounded`).  A cached stop is raised, and the
simulation is one-directional, so it needs nothing there.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche ConLeche.Verify ConLeche.Verify.Ground Std.WP
open scoped Lean.Order

variable {env : Env}

/-- **The gate's answer against the specification's**: no answer where the
specification calls no engine, and the specification's `.ok v` where the
gate answers `v`. -/
@[expose] def GateRes (eager : Bool) (env : Env) (a b : Expr) : Option Bool → Prop
  | none => groundSite eager env a b = none
  | some v => groundSite eager env a b = some (.ok v)

@[conleche_grind =] theorem GateRes.none_eq (eager : Bool) (env : Env) (a b : Expr) :
    GateRes eager env a b none = (groundSite eager env a b = none) := rfl

@[conleche_grind =] theorem GateRes.some_eq (eager : Bool) (env : Env) (a b : Expr) (v : Bool) :
    GateRes eager env a b (some v) = (groundSite eager env a b = some (.ok v)) := rfl

/-- The engine on the index of `env` is the engine on `env`. -/
theorem ground4Bool_mkFEnv (M : Nat) (P : G4Prog) (t : Expr) :
    ground4Bool (mkFEnv env) M P t =
      ground4BoolCoreF env.find? env.findProj? (natLitStored env) (strLitStored env) (some M)
        groundFuel P t := by
  unfold ground4Bool ground4BoolCore
  rw [natLitStoredF_eq, strLitStoredF_eq, show (mkFEnv env).find? = env.find? from
    funext (mkFEnv_find? env), show (mkFEnv env).findProj? = env.findProj? from
    funext fun T => funext fun i => mkFEnv_findProj? env T i]

/-- **The kept program after the gate** is one the next run can start from. -/
theorem groundShortcut_kept (hwf : EnvWF env) (eager : Bool) (M : Nat) {P : G4Prog}
    (hP : P.kTag.size = 0 ∨ KeptOK env P) (a b : Expr) :
    (groundShortcut eager (mkFEnv env) M P a b).2.kTag.size = 0 ∨
      KeptOK env (groundShortcut eager (mkFEnv env) M P a b).2 := by
  unfold groundShortcut
  rcases ht : groundTarget eager a b with _ | t
  · exact hP
  · have hs := (ground4_site (mx := some M) (fuel := groundFuel) hwf rfl rfl hP
      (groundTarget_some ht).2).1
    dsimp only
    rw [ground4Bool_mkFEnv]
    rcases hq : ground4BoolCoreF env.find? env.findProj? (natLitStored env) (strLitStored env)
      (some M) groundFuel P t with ⟨⟨r, c⟩, P'⟩
    rw [hq] at hs
    exact hs

/-- **The gate's answer is the specification's**, where the gate answers. -/
theorem groundShortcut_res (hwf : EnvWF env) (eager : Bool) (M : Nat) {P : G4Prog}
    (hP : P.kTag.size = 0 ∨ KeptOK env P) (a b : Expr) :
    ((groundShortcut eager (mkFEnv env) M P a b).1 = none → groundSite eager env a b = none) ∧
      ∀ v, (groundShortcut eager (mkFEnv env) M P a b).1 = some (.ok v) →
        groundSite eager env a b = some (.ok v) := by
  unfold groundShortcut groundSite
  rcases ht : groundTarget eager a b with _ | t
  · exact ⟨fun _ => rfl, fun _ h => nomatch h⟩
  · simp only [ground4Bool_mkFEnv]
    rcases hq : ground4BoolCoreF env.find? env.findProj? (natLitStored env) (strLitStored env)
      (some M) groundFuel P t with ⟨⟨r, c⟩, P'⟩
    refine ⟨fun h => ?_, fun v h => ?_⟩
    · exact nomatch h
    have hk : (ground4BoolCoreF env.find? env.findProj? (natLitStored env) (strLitStored env)
        (some M) groundFuel P t).1.1 = .ok v := by
      rw [hq]
      exact Option.some.inj h
    have hcl := (groundTarget_some ht).2
    have hf := (ground4_fresh (mx := some M) (F := groundFuel) hwf rfl rfl hP hcl
      (by rw [hk]; exact fun h => nomatch h)).1
    rw [hk] at hf
    rw [ground4BoolCoreF_unbounded (by rw [hf]; exact fun _ _ _ _ h => nomatch h), hf]

/-- The invariant with another kept program. -/
theorem CSOK.withGround4 {mode : CheckMode} {eager : Bool} {s : CState}
    (hs : CSOK mode eager env s) {P : G4Prog} (hP : P.kTag.size = 0 ∨ KeptOK env P) :
    CSOK mode eager env { s with ground4 := P } :=
  { hs with ground4 := hP }

/-- **The ground gate simulates the specification's engine call.** -/
theorem groundGateC_spec {mode : CheckMode} (henv : EnvWF env) (eager : Bool) {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) :
    ⦃fun s => s = s₀⦄ groundGateM eager (mkFEnv env) a b
    ⦃fun v s' => CSOK mode eager env s' ∧ GateRes eager env a b v; ⊤⦄ := by
  have hk := groundShortcut_kept henv eager s₀.maxNatSize hs.ground4 a b
  have hr := groundShortcut_res henv eager s₀.maxNatSize hs.ground4 a b
  have hs' := hs.withGround4 hk
  sym only [conleche_grind] =>
    vcgen [groundGateM, maxNatSizeM] <;> finish

end ConLeche.Cached
