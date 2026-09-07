import ConLeche.Verify.Cached.GuardsC

/-!
# The cached driver's walkers are the plain ones (task #214)

`directWalkersC` — the memoised constant-resolution gate and the
memoised projection-body builder the cached driver hands the direct
installers (`DirectWalkers`, `ConLeche/Kernel/Direct/InstallF.lean`) —
is equal to the specification record `DirectWalkers.plain`: the gate by
`constsResolveFC_spec` (task #171), the builder by
`instantiate1Lift_spec` (`OpsC.lean`) through the two loops.  Every
bridge lemma about the driver rewrites by `directWalkersC_eq_plain`
once and then reads the plain installer.
-/

namespace ConLeche.Cached

open ConLeche

theorem instPisAtLiftC_eq : ∀ (as : List Expr) (e : Expr),
    instPisAtLiftC as e = Expr.instPisAtLift as e
  | [], _ => rfl
  | _ :: _, .bvar _ => rfl
  | _ :: _, .fvar .. => rfl
  | _ :: _, .sort _ => rfl
  | _ :: _, .const .. => rfl
  | _ :: _, .app .. => rfl
  | _ :: _, .lam .. => rfl
  | _ :: _, .letE .. => rfl
  | _ :: _, .lit _ => rfl
  | _ :: _, .proj .. => rfl
  | a :: as, .forallE _ body _ => by
    simp only [instPisAtLiftC, Expr.instPisAtLift, ExprC.instantiate1Lift_spec]
    exact instPisAtLiftC_eq as _

theorem directProjBodiesGoC_eq (T : Name) : ∀ (k i : Nat) (r : Expr),
    directProjBodiesGoC T k i r = directProjBodiesGo T k i r
  | 0, _, _ => rfl
  | _ + 1, _, .bvar _ => rfl
  | _ + 1, _, .fvar .. => rfl
  | _ + 1, _, .sort _ => rfl
  | _ + 1, _, .const .. => rfl
  | _ + 1, _, .app .. => rfl
  | _ + 1, _, .lam .. => rfl
  | _ + 1, _, .letE .. => rfl
  | _ + 1, _, .lit _ => rfl
  | _ + 1, _, .proj .. => rfl
  | k + 1, i, .forallE fdom body _ => by
    simp only [directProjBodiesGoC, directProjBodiesGo, ExprC.instantiate1Lift_spec]
    rw [directProjBodiesGoC_eq T k (i + 1)]

theorem directProjBodiesC_eq (T : Name) (nP nF : Nat) (cty : Expr) :
    directProjBodiesC T nP nF cty = directProjBodies T nP nF cty := by
  unfold directProjBodiesC directProjBodies
  rw [instPisAtLiftC_eq]
  cases Expr.instPisAtLift (directProjPs nP) cty with
  | none => rfl
  | some r => simp only [directProjBodiesGoC_eq]

/-- **The driver's walkers are the plain ones.** -/
theorem directWalkersC_eq_plain : directWalkersC = DirectWalkers.plain := by
  unfold directWalkersC DirectWalkers.plain
  congr 1
  · funext fe e; exact constsResolveFC_spec
  · funext T nP nF cty; exact directProjBodiesC_eq T nP nF cty

end ConLeche.Cached
