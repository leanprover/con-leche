import Setlec.SetR.Interp2.Step2.WhnfCore

/-!
# `CheckStep2`, the reduction loop — Tier A

`whnf` is `whnfCore` under a loop on a **separate private budget**
(`whnfLoopFuel`, `@[irreducible]`), and by the campaign map's discipline
the loop is discharged by `induction budget` with the continuation's
contract named — never by the knot's `fuel`, which the loop does not
decrement.

The loop takes three exits: literal acceleration, delta, and the
fixpoint.  **Two of the three are free in the annotated currency**, and
that is this file's content:

* the **fixpoint** exit returns the subject, so the claim is
  `whnfStep2_id`;
* the **delta** exit moves neither the interpretation nor the
  invariant, because the unfolded body's canonical annotation *is* the
  constant's own leaf — `EnvS2.acval_defn`, added for exactly this.
  The v1 lane records the same fact as "the reduct denotes
  *identically*"; here it is an environment field rather than a lemma,
  because `denote2` reads `acval` where `denote` read `cval`.

The literal exit is Tier B.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The delta exit is free.**  A definition's body carries the
constant's own canonical annotation, so unfolding it changes no
`interp2` value and no `AnnotOk2`. -/
theorem whnfStep2_delta (m : EnvS2 V env) {fuel : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hc : ConstantInfo.defnInfo cv value hint ∈ env.consts) :
    denote2 μ m.acval env φ fuel 0 value = some (m.acval cv.name φ) :=
  m.acval_defn μ φ fuel cv value hint hc

/-- Ditto for a theorem's proof value. -/
theorem whnfStep2_delta_thm (m : EnvS2 V env) {fuel : Nat}
    {cv : ConstantVal} {value : Expr}
    (hc : ConstantInfo.thmInfo cv value ∈ env.consts) :
    denote2 μ m.acval env φ fuel 0 value = some (m.acval cv.name φ) :=
  m.acval_thm μ φ fuel cv value hc

/-! ## On the loop's "contract"

A first draft named a `WhnfLoopCont2` here, on the map's instruction to
name the continuation's contract at the function boundary.  It was
**deleted before landing**: written out, it said
`interp2 ρ ea = interp2 ρ ea ∧ (AnnotOk2 ρ ea → AnnotOk2 ρ ea)` — true
by `⟨rfl, id⟩`, i.e. nothing.

The reason is worth keeping, because the map's instruction was right
for v1 and wrong here.  v1's loop must *construct a `Red` derivation*,
so its continuation genuinely owes something at each budget step and
the contract carries it.  `WhnfClaims2` concludes an **equality and a
transport**, and the loop moves the subject without moving either — so
every budget step is the identity on the claim, and the only content is
the three exits' step facts (`whnfStep2_id`, `whnfStep2_delta`, and
Tier B's literal exit).  The budget recursion is bookkeeping and
belongs inside the dispatch lemma, not in a standalone `Prop`.

*Rule: a named contract that proves by `rfl` is not a contract.  When
transposing a proof architecture, check whether the thing the original
carried still has content in the new currency before giving it a
name.*
-/

end Setlec.SetR.Interp2
