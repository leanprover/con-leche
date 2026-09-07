import Lech.SetP.Annot.BitShift
import Lech.Semantics.Denote2Closed

/-!
# `denoteP`, closed and depth-independent (task #161, P3.2)

The mirrors of `denote2_closed` (`Interp2/Denote2Closed.lean`) and
`denote2_depth_of_closed` (`Interp2/Step2/Levels.lean`).

**Closedness transposes for free, again.**  `denote2_closed` is not an
induction: it is `denote2_erase` composed with v1's `denote_closed`
and `AVExpr.liftN_eq_self` (a lift cannot be moved by a numeral slot).
`denoteP` has the *same* erasure law (`denoteP_erase`, `Annot/Bit.lean`)
onto the *same* `denote`, so the composition transports verbatim.  No
premise of the original fed a sort run — `hlink`/`hcl` are the leaf
valuation's, `hnf`/`hb` are the subject's scoping — so the only
deltas are the deleted `fuel` and `mode` indices.

**The depth statement drops `EnvWF`**, following the shift it is built
on (see `BitShift.lean`): its sole use in the original is inside
`denote2_shiftFrom`, whose mirror does not take it.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level PropWhen)

/-- **`denoteP`'s closedness law.**  A closed subject's validated
annotation is closed, in the lifting form `EnvS2U.acval_closed` and
`ValueResidues2.closed` state it.  Mirror of `denote2_closed`, with
`denoteP_erase` in place of `denote2_erase`. -/
theorem denoteP_closed {acval : Name → (Name → Nat) → AVExpr}
    {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ)
    (hcl : ∀ n ψ, VExpr.Closed (cval n ψ))
    {e : Expr} {ea : AVExpr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denoteP acval env φ 0 e = some ea) (n k : Nat) :
    ea.liftN n k = ea :=
  AVExpr.liftN_eq_self ea
    (VExpr.bvarsBelow.mono (Nat.zero_le k)
      (denote_closed hcl hnf hb (denoteP_erase hlink 0 e h))) n

/-- **A closed term's validated annotation does not depend on the
depth**, provided the annotation itself is lift-invariant.  Mirror of
`denote2_depth_of_closed`; `EnvWF` goes with `denoteP_shiftFrom`. -/
theorem denoteP_depth_of_closed {env : Env} {φ : Name → Nat}
    {acval : Name → (Name → Nat) → AVExpr}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {e : Expr} {ea : AVExpr} (hfv : e.hasFvar = false)
    (hcl : ∀ k : Nat, ea.liftN 1 k = ea)
    (h : denoteP acval env φ 0 e = some ea) :
    ∀ d : Nat, denoteP acval env φ d e = some ea := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih =>
    have hs := denoteP_shiftFrom (env := env) (acval := acval) (φ := φ)
      (p := 0) hacl e d (Nat.zero_le d)
      (Expr.WScoped.of_not_hasFvar hfv)
    rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv, ih] at hs
    rw [hs]
    simp [hcl]

end Lech.SetP
