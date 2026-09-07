import ConLeche.SetP.Direct.DirectDataP
import ConLeche.Verify.Direct.DirectInv

/-!
# The former's cons (task #175 W4c, P3 module 6, part 2)

`stageFormer`: the P step at the type former's cons, for a given
field chain `Fs`.  The leaf is `directTyAV (resSort.eval ψ) (pps ψ)
(Fs ψ)`; the chain's hereditary grading at the former's parameter
frame is the one premise the two installs of the former differ in —
the *dummy* install (`Fs = []`, whose premise is trivial) serves the
constructor-stage claims that grade the real chain, and the *real*
install builds the model the rest of the block extends.
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AVExpr)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

theorem stripPisAV_mkPisAV :
    ∀ (pps : List (Nat × Nat × AVExpr)) (b : AVExpr),
      stripPisAV pps.length (mkPisAV pps b) = some (pps, b)
  | [], _ => rfl
  | d :: pps, b => by
    simp only [List.length_cons, mkPisAV, stripPisAV, stripPisAV_mkPisAV pps b,
      Option.map_some]

/-! ## The former's hereditary premises -/

/-! ## The cons -/

end ConLeche.SetP
