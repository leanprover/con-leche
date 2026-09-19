module

public import ConLeche.Verify.Rules.Defs

public section

/-!
# The inference bridges (task #305, lane B4)

`inferTypeCore` (full grade) and `inferTypeCoreIO` (io grade) at
`fuel + 1` from the five bridges at `fuel`.  Eleven shapes each:

| clause | full inversion | io inversion | rule |
|---|---|---|---|
| `.sort` | inline | `inferTypeCoreIO_sort_eq` | `Infer.sort` |
| `.bvar` | throws | throws | — |
| `.fvar` | inline | `inferTypeCoreIO_fvar_eq` | `Infer.fvar` |
| `.const` | `inferTypeCore_const_inv` (+ the arity guard, `Accepted.lean:70`) | `inferTypeCoreIO_const_eq` | `Infer.const` |
| `.lit` | `inferTypeCore_natLit_inv` / `_strLit_inv` (`Accepted.lean`) | `inferTypeCoreIO_lit_eq` | `Infer.natLit` / `strLit` |
| `.forallE` | `inferTypeCore_forall_inv` | `inferTypeCoreIO_forall_inv` | `Infer.forallE` (+ `ensureSort_bridge`) |
| `.lam` | `inferTypeCore_lam_inv` | `inferTypeCoreIO_lam_inv` | `Infer.lam` |
| `.app` | `inferTypeCore_app_inv` | `inferTypeCoreIO_app_inv` | `Infer.app` / `Infer.appSkip` |
| `.proj` | `inferTypeCore_proj_inv` | `inferTypeCoreIO_proj_inv` | `Infer.proj` |
| `.letE` | `inferTypeCore_letE_inv` | `inferTypeCoreIO_letE_inv` | — |

The io body recurses through `pureFnsIO`, whose `whnf`/`defeq` are the
full knot's at the same fuel (`pureFnsIO_whnf`, `pureFnsIO_defeq`) and
whose `infer` is the lane at `fuel` (`inferIO_def`).
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- **`inferTypeCore` at `fuel + 1`**, full grade. -/
theorem infer_bridge_succ (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hi : InferBridge env fuel) (hio : InferIOBridge env fuel) :
    InferBridge env (fuel + 1) := by
  sorry

/-- **`inferTypeCoreIO` at `fuel + 1`**, io grade. -/
theorem inferIO_bridge_succ (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) :
    InferIOBridge env (fuel + 1) := by
  sorry

end ConLeche.Rules
