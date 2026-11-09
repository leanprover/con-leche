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
`ConLeche/Verify/Cached/WalkersC.lean`; the family readers
`familyTelescopeC`, `checkSpineAtC`, `familyKeyCheckC`:
`ConLeche/Verify/Cached/IndPassC.lean`).
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

/-- The cached `familyTelescope`: a definition-headed family at its
reduct by `reducedFormerC`, any other at its stored type. -/
def familyTelescopeC (fe : FEnv) (cv : ConstantVal) (caps : IndCaps) : CheckCM Expr :=
  if formerDefHeaded cv then do
    let cvR ← reducedFormerC mode fe cv (caps.nparams + caps.nIdx)
    pure cvR.type
  else pure cv.type

/-- The cached `checkSpineAt`: each argument inferred and compared by
the cached core, the telescope instantiated by `instantiate1C`. -/
def checkSpineAtC (fe : FEnv) (d : Nat) : Expr → List Expr → CheckCM Unit
  | _, [] => pure ()
  | t, a :: as =>
    match t with
    | .forallE ty body => do
      let ta ← (coreKnotI mode false fe checkFuel).infer d a
      unless ← (coreKnotI mode false fe checkFuel).defeq d ta ty do
        throw (.invalid "application type mismatch at a family's parameters")
      checkSpineAtC fe d (Expr.instantiate1C body a) as
    | _ => throw (.invalid "function expected at a family's parameters")

/-- The cached `familyKeyCheck`: the family's telescope at the key's
levels by the cached `instLevelParams`. -/
def familyKeyCheckC (fe : FEnv) (find? : Name → Option ConstantInfo) (d : Nat)
    (c : Name) (us : List Level) (ds : List Expr) : CheckCM Unit :=
  match find? c with
  | some (.indInfo cv caps) => do
    unless us.length = cv.levelParams.length do
      throw (.invalid "incorrect number of universe levels at a family's key")
    let ty ← familyTelescopeC mode fe cv caps
    checkSpineAtC mode fe d (Expr.instLevelParams cv.levelParams us ty) ds
  | _ => throw (.invalid "a family's key is no stored family")

end ConLeche.Cached
