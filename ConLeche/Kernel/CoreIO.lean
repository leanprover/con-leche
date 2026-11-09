module

public import ConLeche.Kernel.TypeChecker

@[expose] public section

/-!
# The io lane: infer at official's infer-only grade

`inferBodyIO` lives in `ConLeche/Kernel/Core.lean` (so the knot can tie
it); the executable knot's `inferIO` slot runs it at every mode.  The
leaf lane below (`coreKnotIO` / `inferTypeCoreIO`) is the *statement
subject* the io claims are phrased at; `Verify/Knot.lean`'s
`inferTypeIO_on` identifies the executable slot with it.

## What the lane is

The reference kernels type-check a declaration *once*, at the front
door, and let the inferences that reduction and definitional equality
perform on their own intermediate terms re-derive types **without
re-checking** (`infer_type_core(e, infer_only)`, lean4lean's
`inferType (inferOnly := true)`).  Since task #342 the io body is that
grade (the rules tier's `InferIO`, `ConLeche/Rules/Rel.lean`): an
application infers the function's type and instantiates its codomain
at the argument, with no argument check; a λ infers its body opened at
its domain, with no domain check; a `let` infers its body at the
value, with no value check.  The ∀ domain and codomain sorts and the
projection typing stay, as in official's infer-only.

## The knot boundary

`coreKnotIO` is a **leaf** lane: its `whnfCore`/`whnf`/`defeq` are the
*full* knot's, unchanged, so every relation that models those bodies
(`Red`/`Infer`/`DefEq`) keeps its subject.  Only `infer` is the io
body, and only the io body calls it; nothing in the full lane reaches
an io conclusion except through the knot's `inferIO` slot.
-/

namespace ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- **The io knot** (the leaf lane).  `whnfCore`/`whnf`/`defeq`/`defeqE`
are the *full* knot's at the same fuel — the io lane consumes reduction
and definitional equality and never supplies them — and `infer` is
`inferBodyIO` tied to the io knot one level down.  This leaf lane is
the *statement subject* the io claims are phrased at, and the knot
equations (`Verify/Knot.lean`) identify the executable slot with it.
Its own `inferIO` slot is the io body again — the io grade is
idempotent (there is nothing below io to select). -/
def coreKnotIO (eager : Bool) (env : Env) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      defeqE := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    { whnfCore := (coreKnot mode eager env id (fuel + 1)).whnfCore
      whnf := (coreKnot mode eager env id (fuel + 1)).whnf
      defeq := (coreKnot mode eager env id (fuel + 1)).defeq
      defeqE := (coreKnot mode eager env id (fuel + 1)).defeqE
      infer := fun d e => inferBodyIO (coreKnotIO eager env fuel) env d e
      inferIO := fun d e => inferBodyIO (coreKnotIO eager env fuel) env d e }

/-- The io core, tied at `CheckM`: the specification the
`InferClaimIO` family is stated at. -/
def pureFnsIO (eager : Bool) (env : Env) : Nat → CoreFns CheckM :=
  coreKnotIO mode eager env

/-- Infer-only (io-grade) type inference, fueled — the io lane's single
entry point. -/
def inferTypeCoreIO (eager : Bool) (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Expr :=
  (pureFnsIO mode eager env fuel).infer depth e

end ConLeche
