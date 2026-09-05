import Setlec.Kernel.Direct
import Setlec.Verify.FastOps

/-!
# The incremental projection residual agrees with the generator (task #175 W4c)

The cached drivers thread `directProjResidP` — the constructor
telescope peeled one earlier-projection substitute at a time — and read
each slot's type off it (`directProjTyR`); the pure checker computes
`directProjTyP` from scratch.  The two agree: the incremental residual
is the whole-spine `instPisAtLift`.
-/

namespace Setlec

theorem directProjResidP_eq (T : Name) (nP : Nat) (cty : Expr) :
    ∀ i, directProjResidP T nP cty i
      = Expr.instPisAtLift
          (directProjPs nP ++ (List.range i).map (directProjArgP T)) cty
  | 0 => by simp [directProjResidP, List.range_zero, List.map_nil, List.append_nil]
  | i + 1 => by
    rw [directProjResidP, directProjResidP_eq T nP cty i, List.range_succ,
      List.map_append, List.map_singleton, ← List.append_assoc,
      instPisAtLift_append (directProjPs nP ++ (List.range i).map (directProjArgP T))
        [directProjArgP T i]]

/-- The slot type read off the incremental residual is the generator's. -/
theorem directProjTyR_residP (T : Name) (lps : List Name) (nP nF i : Nat)
    (tty cty : Expr) :
    directProjTyR T lps nP nF i tty (directProjResidP T nP cty i)
      = directProjTyP T lps nP nF i tty cty := by
  unfold directProjTyP
  rw [directProjResidP_eq]

end Setlec
