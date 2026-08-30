import Setlec.SetR.Interp2.Step2.InferQ

/-!
# `CtxOk2Open` discharged — the trap-check's verdict

`Step2/InferQ.lean` routes `CtxOk2Open` (opening a binder extends the
annotated context by the domain's annotation) and seal 11 flags it as
**not yet trap-checked**: its conclusion asserts `denote2 … F (d+1) …`
for annotations only hypothesised at `denote2 … F d …`, and
`denote2`'s binder clauses run `sortOfE … F d` — the checker — *at
that depth*.

**Verdict: satisfiable, and in fact a theorem, premise-free.**  Both
dimensions come back clean, for different reasons:

* **Fuel.**  The residue never asserts a `denote2` *success* the
  consumer does not already hand it: the depth-shift law
  (`denote2_weaken_top`, `Step2/Dispatch.lean`) is an *equation*
  between `denote2 … (d+1)` and `denote2 … d`, uniform in `F`, whose
  two `sortOfE` obligations are discharged by `sortOfE_shiftFrom` —
  also an equation, also uniform in `F`.  So the smallest-fuel test
  has nothing to bite on: at any `F` where the hypotheses' runs fail,
  the conclusion's fail identically.
* **Depth.**  This is the part seal 11 named as untested, and the side
  conditions `denote2_shiftFrom` carries are `Setlec.EnvWF env` and
  the leaf-closedness `hacl`, plus `Expr.WScoped` of the shifted term.
  All three are **already available**: `EnvWF` is `m.base.wf`, `hacl`
  is `EnvS2.acval_closed` (landed at seal 8), and the two `WScoped`
  hypotheses are `CtxOk2.wScoped` of the two contexts the residue is
  handed — `CtxOk2`'s leaf package already *contains* its scoping
  (`l.1 < d` and `Expr.fvarsBelow l.1 l.2.2` at every leaf,
  hereditarily, because `Expr.fvarLeaves` descends into annotations).

So the residue is not a carried obligation at all.  The one-liner is
below; `CtxOk2.openS` (`Step2/Dispatch.lean`) is the kit lemma with
`CtxOk2Open`'s signature.

The file is separate only to keep out of `InferQ.lean` while it has
another owner; the theorem is one line and belongs beside the residue
whenever that file is next touched.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-- **`CtxOk2Open` is discharged.**  No environment shape, no fuel
condition, no mode, no level assignment, and no extra premise. -/
theorem ctxOk2Open_of {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : CtxOk2Open m μ φ :=
  fun ht hb hty hfb => CtxOk2.openS ht hb hty hfb

/-! ## Generation four leaves this residue alone — and names its twin

`CtxOk2Open` mentions no `AnnotOk2` at all: it is a statement about
`denote2` and the leaf package's three conjuncts, so the hoist above
`ρ` passes straight through it and the theorem above still stands
verbatim.

What generation four *does* add is a **second** obligation at the same
site, and it is recorded here because this file is the residue's
ledger.  `InferClaims2C` now delivers the returned type's `AnnotOk2`,
and at the `.fvar` clause the returned type is the leaf's own
annotation — a fact `CtxOk2`'s package does not carry
(`Step2/Dispatch.lean`, the STOP before `infer_fvar_claim2C`).  The
proposed fourth conjunct is `CtxOk2Ann`, and its opening lemma is
`CtxOk2Ann.openS`, whose signature mirrors `CtxOk2.openS` with one
extra premise: the domain's own hoisted grading, which every
congruence site already holds.

So *if* the junction adopts the strengthening, this residue's
discharge becomes the pair `⟨CtxOk2.openS, CtxOk2Ann.openS⟩` and
nothing above changes. -/

/-! ## Generation five: the prediction, closed

The junction did adopt the strengthening (`CtxOk2D`), and the
discharge below is the pair the note above named, in that order and
with nothing else.  The **one** thing the note did not predict is the
extra premise: `CtxOk2Ann.openS` reads the domain's hoisted grading,
because the opened variable's annotation *is* the domain and the
fourth conjunct has to say something about it.  So `CtxOk2OpenD`
carries a hypothesis `CtxOk2Open` does not.

That is not a weakening of the residue past its consumers.  The three
sites that open a binder in the inference quarter — `.forallE`,
`.lam`, `.app` — each already compute it: the first two from
`SortSem2`'s own conclusion, the third from `AnnotOk2.hoist_pi` of the
reduct.  All three are wired in `Step2/InferQ.lean`'s generation-five
lane, which takes **no** `ctx_open` field at all. -/

/-- `CtxOk2Open` in the new currency, with the premise the fourth
conjunct adds. -/
def CtxOk2OpenD {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : Prop :=
  ∀ {F d : Nat} {Δa : List AVExpr} {n : Name} {ty body : Expr}
    {ta : AVExpr},
    CtxOk2D m μ φ F d Δa ty → CtxOk2D m μ φ F d Δa body →
    denote2 μ m.acval env φ F d ty = some ta →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOk2 V ρ ta) →
    CtxOk2D m μ φ F (d + 1) (ta :: Δa)
      (body.instantiate1 (.fvar d n ty))

/-- **`CtxOk2OpenD` is discharged**, and the `Expr.fvarsBelow`
argument `CtxOk2Open` carried is gone too: `CtxOk2D` contains its own
scoping. -/
theorem ctxOk2OpenD_of {env : Env} (m : EnvS2 V env) (μ : CheckMode)
    (φ : Name → Nat) : CtxOk2OpenD m μ φ :=
  fun ht hb hty hok => CtxOk2D.openS ht hb hty hok

end Setlec.SetR.Interp2
