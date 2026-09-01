import Setlec.SetR.Annot.Bit

/-!
# The `denoteP` lemma battery (task #161, P3.2)

The Step2 ladder consumes `denote2` through a fixed lemma surface —
clause equations, inversions, the depth shift, the environment
crossing — stated and proved at `DefEqRun.lean`'s prelude,
`Dispatch.lean`, and `Denote2Extend.lean`.  This file is that surface
for `denoteP`, mirror by mirror, with the systematic deltas of the
validated-annotation reading:

* **no fuel parameter** — the fuel-monotonicity/cross-fuel/`fuelDown`
  family has no mirror because there is nothing to be monotone in;
* **no sort-run conjuncts** — the binder inversions conclude
  `ea = .pi 0 (pwBit φ mb.pw) ta ba` (resp. `.lam (pwBit φ mb.pw)`)
  *definitionally*, where `denote2`'s conclude `sortOfE`/`lamSortE`
  successes;
* **premises that existed only to move a sort run are dropped** —
  `EnvWF` in the depth shift, `SortAgree` in the environment crossing.
  A premise kept by a mirror is one the *reading itself* needs
  (`hacl`: leaf lift-invariance; `FindPreserved`/`LitGuardsAgree`:
  the constant and literal clauses read the environment).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## Clause equations -/

theorem denoteP_forallE (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (n : Name) (ty body : Expr) (mb : Setlec.BinderMeta) :
    denoteP acval env φ d (.forallE n ty body mb)
      = (do
        let ta ← denoteP acval env φ d ty
        let ba ← denoteP acval env φ (d + 1)
          (body.instantiate1 (.fvar d n ty))
        some (.pi 0 (pwBit φ mb.pw) ta ba)) := by
  rw [denoteP]

/-! ## Inversions -/

theorem denoteP_forallE_inv {d : Nat} {n : Name} {ty bd : Expr}
    {mb : Setlec.BinderMeta} {ea : AVExpr}
    (h : denoteP acval env φ d (.forallE n ty bd mb) = some ea) :
    ∃ ta ba, denoteP acval env φ d ty = some ta ∧
      denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d n ty)) = some ba ∧
      ea = .pi 0 (pwBit φ mb.pw) ta ba := by
  rw [denoteP] at h
  cases ht : denoteP acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d n ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

end Setlec.SetR.Interp2
