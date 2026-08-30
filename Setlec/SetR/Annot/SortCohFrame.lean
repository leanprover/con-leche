import Setlec.SetR.Annot.SortCoh
import Setlec.SetR.Bridge.Claims

/-!
# The semantic trio's frame (`Q`-slot instantiation) — statements

The sort-coherence branch stays `V`-free (`SortCoh.lean`'s
centerpiece); this module is where the `Q`-slot meets the model.
Per the currency ruling, the trio (probe/rescue/eta vacuities) is
discharged SEMANTICALLY: their content — a proposition cannot be a
universe — is `mem_univ_zero` + `univ_ne_pt`
(`SetTheory/Derive/PtFresh.lean:116` — the "one-lemma gap" was
already in the tree).

`FrameQ` is the consumer's instantiation of the abstract pair slot:
per side, the bridge-standard guards (self-carried — the
`QPreserve*F` species pass no `SubjInv`, so the frame must travel
with its own guards), the context correspondence at the consumer's
`Δv`, and denotability.  It is symmetric by construction
(`frameQ_symm`), as the slot requires.

## The discharge route (named suppliers; proofs at their own seals)

1. The trio's premises are checker runs; `checkBridge (m) (φ)`
   (unconditional given `EnvR env`) turns them into relation
   derivations (`WhnfClaimsR` on the subject's sort convergence —
   loop runs lift to whole-`whnf` via `whnfLoop_budget_mono` +
   `whnf_of_loop`; `InferClaimsR` on the cert's own infer runs,
   which also ESTABLISHES the denotability the reduct-side facts
   need).
2. The `Sound` tier (`EnvSHyp`) reads them into the model:
   `DefEq.sound`/`Infer.sound` give `interp` facts at any
   `ρ` with `Sat V Δv ρ` (the discharge theorems take `(ρ, hSat)`
   as parameters — the consumer holds them at its application
   site; at `d = 0`, `Sat_nil`).
3. The collision: the subject interprets as `univ (eval ℓ)` (its
   run reaches `.sort ℓ`, reduction preserves interpretation) AND
   as a member of a `univ 0` fibre (the cert says its type is a
   proposition) — `mem_univ_zero` forces it to be `pt`, and
   `univ_ne_pt` refutes.
4. The `FrameQ` preservers (`QPreserve*F` at this instantiation)
   ride `WhnfCoreClaimsR` (core steps: reduct denotes; leaf sets
   shrink, so `CtxOkR` restricts), `denote_delta_step` (δ: the
   reduct denotes identically), and the literal/`Bool` denotes
   (nat) — plus the same guard-preservation the `InvPreserve*F`
   suppliers prove.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.TTVerify (denote TConstVal)
open Setlec.SetR (CtxOkR)
open Setlec (CheckMode Env Expr Name)

/-- One side's frame: guards, context correspondence, denotability. -/
def FrameSide (μ : CheckMode) (cval : TConstVal) (env : Env)
    (φ : Name → Nat) (Δv : List VExpr) (d : Nat) (e : Expr) : Prop :=
  Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded e ∧
    CtxOkR μ cval env φ d Δv e ∧
    (denote cval env φ d e).isSome = true

/-- The semantic trio's `Q`-slot instantiation: both sides framed. -/
def FrameQ (μ : CheckMode) (cval : TConstVal) (env : Env)
    (φ : Name → Nat) (Δv : List VExpr) :
    Nat → Expr → Expr → Prop :=
  fun d a b =>
    FrameSide μ cval env φ Δv d a ∧ FrameSide μ cval env φ Δv d b

/-- The slot's symmetry requirement, by construction. -/
theorem frameQ_symm {μ : CheckMode} {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {Δv : List VExpr} {d : Nat} {a b : Expr}
    (h : FrameQ μ cval env φ Δv d a b) :
    FrameQ μ cval env φ Δv d b a :=
  ⟨h.2, h.1⟩

end Setlec.SetR.Interp2
