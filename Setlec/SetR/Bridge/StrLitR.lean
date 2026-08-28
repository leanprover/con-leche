import Setlec.SetR.Bridge.Eta
import Setlec.Verify.Denote.StrLit

/-!
# The string-literal expansion, bridged (task #148, T3)

R7/R16 `Red.strLitCtor` carries `denoteClosed cval env φ
(strLitToConstructor s) = some SC` and `VExpr.Closed SC` as side
conditions — deviation D5/D1's honest transpose, since `denote`'s
`strVal` clause and the constructor form are only *near*-`rfl`.  This
module supplies both, at any depth, from the relocated
`denote_strLitToConstructorV` (`Setlec/Verify/Denote/StrLit.lean`).

Consumed by `defeqStep`'s two string-expansion cases (the stuck block),
by `projLitToCtor` (the `.proj` clause, batch e) and by
`litMajorToCtor` (the iota major, batch g) — three sites, one fact.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- **A string literal's constructor form denotes to the literal's
term, closedly, at every depth** — R7's two side conditions and the
premise's subject, in one package. -/
theorem denote_strLitCtorR {env : Env} (m : EnvR env) (φ : Name → Nat)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hg : strLitSupported env = true) (d : Nat) (s : String) :
    denoteClosed m.cval env φ (strLitToConstructor s)
        = some (strLitT m.cval env φ s) ∧
      VExpr.Closed (strLitT m.cval env φ s) ∧
      denote m.cval env φ d (strLitToConstructor s)
        = some (strLitT m.cval env φ s) := by
  have hd : ∀ k, denote m.cval env φ k (strLitToConstructor s)
      = some (strLitT m.cval env φ s) := by
    intro k
    rw [denote_strLitToConstructorV φ hg k, denote_strLit, if_pos hg]
  exact ⟨hd 0,
    denote_closed hcl (strLitToConstructor_hasFvar s)
      (strLitToConstructor_looseBVars s 0) (hd 0),
    hd d⟩

/-- The frame conditions of a string literal's constructor form: it is
closed, so all four are free. -/
theorem frame_strLitCtorR {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {Δ : List VExpr} (s : String) (hlen : Δ.length = d) :
    Expr.WScoped d (strLitToConstructor s) ∧
      (strLitToConstructor s).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (strLitToConstructor s) ∧
      CtxOkR mode cval env φ d Δ (strLitToConstructor s) := by
  refine ⟨strLitToConstructor_WScoped s d, strLitToConstructor_looseBVars s 0,
    fun l hl => ?_, ⟨hlen, fun l hl => ?_⟩⟩ <;>
    · rw [strLitToConstructor_fvarLeaves] at hl
      exact nomatch hl

end Setlec.SetR
