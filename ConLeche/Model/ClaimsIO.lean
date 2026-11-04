module

public import ConLeche.Model.Claims
public import ConLeche.Model.Rules.IORel
import ConLeche.Kernel.CoreIO
public section

/-!
# The io claims family, PREMISE FORM (task #161)

The fifth family of the P ladder: the same soundness statement as
`InferClaim`, about the **io lane** (`inferTypeCoreIO`,
`Kernel/CoreIO.lean`), with one deliberate change of species.

## The species: premise form, and why it must be

`InferClaim` is an **establishment** statement — the subject's
truthfulness `WellDenoted ea` is a *conclusion*, derived from the run.
The io lane cannot establish it at the application clause: with the
argument's certificate skipped there is nothing connecting `⟦tya⟧` to
`⟦Aa⟧`, which is exactly the proof-theoretic receipt for keeping the
front door ungated (the round-D study's refutation item 4).  What the
io lane *can* do is **consume**: given the subject's truthfulness, it
returns the hereditary claim at the inferred type.  So

* `WellDenoted ea` moves from the conclusion to the **premises**;
* the conclusion is the hereditary `IORel` at the **io-computed**
  type (`Model/Rules/IORel.lean`): the value is the point, a member of
  the type, or, at a ∀, hereditarily a graph over its domain — never
  identity with "the" type (which is why the old unique-typing and
  Π-domain-injectivity refutations do not bite: they refute an
  identity the statement never asserts), and not plain membership
  either, which fails at an abstraction over an empty domain.

This is the establishment/consumption asymmetry, in one statement.
Every consumer of the io lane already holds the premise
(`DefEq.proofIrrel_sound` is the canonical one).

## The five-way step

The io lane is a *leaf* lane (`Kernel/CoreIO.lean`): its reduction and
definitional equality are the full lane's, so the assembly grows by
one slot and nothing else moves —

    {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel
      ⟹ {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel + 1

with the io slot at `fuel + 1` consuming `Whnf`, `DefEq` and `InferIO`
at `fuel`.  The five claims are recomposed at every fuel by
`checkSoundAtP5` (`Model/Rules/Recompose.lean`).

**Mode provenance (binding).**  An io conclusion must never feed a
site that needs establishment form.  The knot boundary is the
enforcement: the full lane's bodies never mention `coreKnotIO`, so no
full-lane claim can be discharged from an io claim by construction.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name inferTypeCoreIO)

universe w

variable {V : Type w} [SetTheory V]

/-- **The io inference family, premise form.**  Compare `InferClaim`:
the subject's `WellDenoted` is a *premise* here, the run is the io
lane's (Lean's `infer_only`), and the claim is the hereditary `IORel`
(task #346; task #342 L18): an io-inferred type need not hold its
term. -/
@[expose] def InferClaimIO (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List Term},
    inferTypeCoreIO μ false env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : Term},
      CtxOk m φ d Δa e →
      denote m.acval env φ d e = some ea →
      denote m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ ea) →
        ∀ ρ : Nat → V, Sat V Δa ρ →
          Rules.IORel m φ d t ρ (interp V ρ ea)

end ConLeche.Model
