import Setlec.Kernel.TypeChecker

/-!
# The P lane: head normalization with the β-certificate gate
(task #161, S9 — THE PAYOFF CHECK)

**Status: the statement subject, not an executable lane.**  This is the
parked stage-1 β-cert gate (`agent/bucket2-s1` @ `139b68db`) **rebased
onto the ruled mode shape (ii)** — duplicate knots, driver-selected.
Stage 1 took shape (i): it edited `Kernel/Core.lean`, `CoreI.lean` and
`Cached/CoreC.lean` *in place*, which changes the function every landed
R capstone is stated about.  Shape (ii) instead adds a second
`whnfCore` body and a second knot; `Kernel/Core.lean` is byte-
untouched, so **every R capstone stays verbatim and mode-generic**, and
the executable is byte-identical to master by construction — nothing
here is reachable from `Main.lean`'s import closure.

The wiring (`--set-model=p`, the interned and cached twins, the memo
discipline) is **HELD** at the stop recorded in `DESIGN.md`, "Task #161
SEPARATION — S9 SEALED": the P capstone's proof path still reaches
`Red.beta` through one constant, `checkDeclR_ofEnvRE`, and until the
ind tier's record split lands there is no soundness theorem for a
driver that runs this knot.

## The gate

At a λ-binder whose **validated** annotation is `.never` ("the codomain
sort is nonzero at *every* valuation") the per-redex argument
certificate is dead weight: the sealed P claim's positive branch
(`whnfCore_app_claimP`, `AnnotOkP_beta_pos` + `annotOk2_beta_dom_pos`,
side-condition free via `piR_dom_unique`) derives the domain membership
from the redex's own `AnnotOk2` slot and consumes no certificate at
all.  `PropWhen.isNever` is exactly the ∀-`φ` uniform form of that
branch's split (`isNever_iff_forall_pwBit_ne_zero`,
`SetP/Annot/Bit.lean`).

At a possibly-zero datum the certificate runs **unconditionally** — the
establishment/consumption asymmetry (the squash regime's membership is
model-class-wide unrecoverable, `io_membership_fails_at_squash`), and
that fence is absolute.  Task #100's de-gating ruling is untouched:
*that* gate skipped the certificate at a **computed** nonzero sort,
which is unsound-to-model under the domain-relative collapse; this one
reads a **validated annotation** and is licensed by a P-tier theorem.

`mode.verified` is law 1's mode gate (clause (i)): the annotation is
only validated in the verified modes, so at `.noModel` the datum means
nothing and the certificate runs.  The gate wraps the **test** only —
both arms are `whnfCoreBody`'s verbatim, so reducts stay
annotation-blind (clause (iii)).
-/

namespace Setlec

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- **The gated head-normalization body**: `whnfCoreBody` with one
clause changed — the `.app` clause's β certificate is skipped when the
λ-binder's validated annotation licenses it (see the module
docstring).  Every other clause (iota, the native pair projection,
zeta, the value clauses) is `whnfCoreBody`'s, verbatim. -/
def whnfCoreBodyP (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app f a => do
      match ← r.whnfCore depth f with
      | .lam n ty body mb => do
        -- **THE β SITE.**  The gate wraps the test only; both arms are
        -- `whnfCoreBody`'s verbatim.
        if ← (if mode.verified && mb.pw.isNever then pure true else do
                let ta ← r.infer depth a
                r.defeq depth ta ty) then
          r.whnfCore depth (body.instantiate1 a)
        else pure (.app (.lam n ty body mb) a)
      | f' => do
        match ← iotaRec mode r env depth (.app f' a) with
        | some e'' => r.whnfCore depth e''
        | none => pure (.app f' a)
    | .proj sn i pe => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtor r env depth e'
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          let args := e'.getAppArgs
          if entry.tower ∧ c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length ∧
              entry.fireOk us = true then
            let arg := args.getD (entry.numParams + i) (.bvar 0)
            -- the projection certificate is NOT gated: the asymmetry
            -- fence keeps every zero-kind certificate, and the
            -- projection slot has no `pw` datum of its own
            if ← projCert r env depth mode.betaGate c us args then
              r.whnfCore depth arg
            else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .letE _ _ v b =>
      r.whnfCore depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- **The P knot.**  `coreKnot`'s tie with `whnfCoreBodyP` in the
`whnfCore` slot; `whnf`, `infer`, `defeq` and `annotate` are the *same
bodies* (`whnfBody`, `inferBody`, `defeqBody`, `annotateBody`), tied to
this knot one fuel level down.

Unlike `coreKnotIO`'s leaf lane this knot is **not** a leaf: reduction
sits under definitional equality and inference, so a gated `whnfCore`
propagates through the whole knot.  That is why shape (ii)'s cost here
is a duplicated *knot* rather than a duplicated *clause*, and why the
verification side owes a transposed claims tower rather than one extra
family. -/
def coreKnotP (env : Env) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    { whnfCore := fun d e =>
        whnfCoreBodyP mode (coreKnotP env fuel) env d e
      whnf := fun d e => whnfBody (coreKnotP env fuel) env d e
      infer := fun d e =>
        inferBody mode (coreKnotP env fuel) env d e
      defeq := fun d a b =>
        defeqBody mode (coreKnotP env fuel) env d a b
      annotate := fun d e =>
        annotateBody mode (coreKnotP env fuel) env d e
      -- parked stage-1 artifact: the io grade postdates this knot, and
      -- nothing states claims at its io slot — the full body keeps the
      -- record well-formed
      inferIO := fun d e =>
        inferBody mode (coreKnotP env fuel) env d e }

/-- The P core, tied at `CheckM`: the specification a gated-lane claims
tower would be stated at. -/
def pureFnsP (env : Env) : Nat → CoreFns CheckM :=
  coreKnotP mode env

/-- Head normalization with the β-cert gate (fueled). -/
def whnfCoreP (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFnsP mode env fuel).whnfCore depth e

/-- The full reduction loop over the gated knot (fueled). -/
def whnfP (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFnsP mode env fuel).whnf depth e

/-- Type inference over the gated knot (fueled). -/
def inferTypeCoreP (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Expr :=
  (pureFnsP mode env fuel).infer depth e

/-- Definitional equality over the gated knot (fueled). -/
def isDefEqCoreP (env : Env) (fuel depth : Nat) (a b : Expr) :
    CheckM Bool :=
  (pureFnsP mode env fuel).defeq depth a b

/-- The annotation pass over the gated knot (fueled). -/
def annotateCoreP (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Expr :=
  (pureFnsP mode env fuel).annotate depth e

/-- `ensureSort` over the gated knot (fueled). -/
def ensureSortCoreP (env : Env) (fuel depth : Nat) (e : Expr) :
    CheckM Level :=
  ensureSort (pureFnsP mode env fuel) env depth e

end Setlec
