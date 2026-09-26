module

public import ConLeche.Model.Claims
import ConLeche.Kernel.CoreIO
public section

/-!
# The io claims family, PREMISE FORM (task #161)

The fifth family of the P ladder: the same soundness statement as
`InferClaim`, about the **io lane** (`inferTypeCoreIO`,
`Kernel/CoreIO.lean`), with one deliberate change of species.

## The species: premise form, and why it must be

`InferClaim` is an **establishment** statement — the subject's
truthfulness `WellDenotedV ea` is a *conclusion*, derived from the run.
The io lane cannot establish it at the application clause: with the
argument's certificate skipped there is nothing connecting `⟦tya⟧` to
`⟦Aa⟧`, which is exactly the proof-theoretic receipt for keeping the
front door ungated (the round-D study's refutation item 4).  What the
io lane *can* do is **consume**: given the subject's truthfulness, it
returns the type's truthfulness and the membership.  So

* `WellDenotedV ea` moves from the conclusion to the **premises**;
* the conclusions are `WellDenotedV ta` and `⟦ea⟧ ∈ ⟦ta⟧` — membership in
  the **io-computed** type, never identity with "the" type (which is
  why the old unique-typing and Π-domain-injectivity refutations do
  not bite: they refute an identity the statement never asserts).

This is the establishment/consumption asymmetry, in one statement.
Every consumer of the io lane already holds the premise
(`DefEq.proofIrrel_sound` is the canonical one).

## The licensed fragment, and the wall

The only new mathematics is the application clause, and it splits:

* **graph regime** (`pw = .never`, where the gate fires): the skipped
  membership is recovered from the subject's own hereditary app slot
  by `io_domain_transfer` + `piR_dom_unique`, with **no** nonemptiness
  and **no** freshness side condition;
* **squash regime**: the certificate runs, and the clause reuses
  today's `ihd` route verbatim.

The split is not an engineering convenience.  `io_membership_fails_at_
squash` exhibits closed `V`-values satisfying every premise of the
premise-form claim at a squash binder with `app ⟦f⟧ ⟦a⟧ ∉ ⟦B'⟧⟦a⟧`:
truth values do not remember domains, so **no** proof-irrelevant set
model can license official's full inferOnly.  `pw = .never` is the
whole licensed fragment, forever.

## The five-way step

The io lane is a *leaf* lane (`Kernel/CoreIO.lean`): its reduction and
definitional equality are the full lane's, so the assembly grows by
one slot and nothing else moves —

    {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel
      ⟹ {WhnfCore, Whnf, DefEq, Infer, InferIO} at fuel + 1

with the io slot at `fuel + 1` consuming `Whnf`, `DefEq` and `InferIO`
at `fuel` (and, at the kept-check branch of the app clause, nothing
else).  The five claims are recomposed at every fuel by
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
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name inferTypeCoreIO)

universe w

variable {V : Type w} [SetTheory V]

/-- **The io inference family, premise form** (the frozen shape).
Compare `InferClaim`: the subject's `WellDenotedV` is a *premise* here,
and the run is the io lane's. -/
@[expose] def InferClaimIO (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr} {Δa : List AnnotTerm},
    inferTypeCoreIO μ env fuel d e = .ok t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

end ConLeche.Model
