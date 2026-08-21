import Setlec.Model.Consistency
import Setlec.Verify.BridgeDecl

/-!
# Consistency of the executable checker

The refinement bridge (`checkDecls_bridge`) reproduces a successful
`checkDecls cachedOps` run — the memoized instantiation the binary
actually executes — by the pure fueled checker at some fuel, and the
consistency layer is fuel-generic, so every consistency statement
transfers to the executable.
-/

namespace Setlec

/-- Soundness of the **executable** checker: every environment it
accepts has a set-theoretic model. -/
theorem checkDeclsC_sound (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls cachedOps ds = .ok env') :
    Nonempty (EnvModel V env') := by
  obtain ⟨F, hF⟩ := checkDecls_bridge h
  exact checkDecls_sound hF

/-- The executable checker never accepts a declaration list containing
a `def` or `theorem` whose stated type is `Empty`. -/
theorem no_proof_of_Empty_input_C (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls cachedOps ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  obtain ⟨F, hF⟩ := checkDecls_bridge h
  exact no_proof_of_Empty_input V hF hd hty

/-- **No proof of `Empty` is ever accepted by the executable
checker**: if it accepts a declaration list, no constant in the
resulting environment has type `Empty`. -/
theorem no_proof_of_Empty_C (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls cachedOps ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨F, hF⟩ := checkDecls_bridge h
  exact no_proof_of_Empty V hF c hc hty

end Setlec
