module

public import ConLeche.Cached.CoreC

@[expose] public section

/-!
# The cached twin of the inductive check: the formers' telescopes (task #498)

The production twins of `ConLeche/Kernel/Inductives/Positivity.lean`:
monomorphic `CheckCM` definitions at a mode and an environment index,
calling the cached core (`coreKnotI`) directly and the cached walks of
`ConLeche/Cached/ExprOpsC.lean` where the specification runs the plain
ones.  Each is the specification at the shared operations
(`whnfTelescopeC_eq`, `reducedFormerC_eq`,
`ConLeche/Verify/Cached/WalkersC.lean`).
-/

namespace ConLeche.Cached

open ConLeche

variable (mode : CheckMode)

/-- The cached `whnfTelescope`: official's telescope loop, the residual
reduced by the cached core and each binder opened by `instantiate1C`. -/
def whnfTelescopeC (fe : FEnv) : Nat → Nat → Expr → CheckCM (List Expr × Level)
  | i, 0, e => do
    let e' ← (coreKnotI mode false fe checkFuel).whnf i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← (coreKnotI mode false fe checkFuel).whnf i e
    match e' with
    | .forallE dom body =>
      let (bs, s) ← whnfTelescopeC fe (i + 1) n (Expr.instantiate1C body (.fvar i dom))
      pure (dom :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- The cached `reducedFormer`: the reduced telescope closed by
`closeTelescopeC` (each domain abstracted once). -/
def reducedFormerC (fe : FEnv) (cv : ConstantVal) (n : Nat) : CheckCM ConstantVal := do
  let (bs, s) ← whnfTelescopeC mode fe 0 n cv.type
  pure { cv with type := Expr.closeTelescopeC bs 0 (.sort s) }

end ConLeche.Cached
