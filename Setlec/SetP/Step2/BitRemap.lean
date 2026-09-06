import Setlec.SetP.Step2.BitLevels

/-!
# The context remap, read (the packed `pw` datum, 2026-09-06)

`Expr.remapPW from to e` is the identity level substitution with a
context change: the levels are unchanged, the positional masks are
re-indexed from `from` to `to`.  Its reading at context `to` is the
reading of `e` at context `from` — the crossing (`denotePInstLevels`) at
the identity substitution, whose valuation is the ambient one
(`substFn_self`).  Needed where the checker reuses a stored term by
parameter-*name* identity: the iota theorems' constructor telescopes and
the direct install's constructor type in the recursor's context.
-/

namespace Setlec.Level

/-- The identity level substitution is the identity valuation. -/
theorem substFn_self (φ : Name → Nat) : ∀ (ks : List Name),
    substFn φ ks (ks.map .param) = φ := by
  intro ks
  funext n
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.map_cons, substFn]
    split
    · next h => subst h; rfl
    · exact ih

end Setlec.Level

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level PropWhen)

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- **The remap, read.**  At a valuation nonzero outside the target
context, a term whose parameters are all in `from` reads at context `to`
through `remapPW from to` exactly as it reads at context `from`. -/
theorem denoteP_remapPW (m : EnvS2Core V env) (φ : Name → Nat)
    {«from» to : List Name}
    (hnd : «from».Nodup) (hfrom : «from».length ≤ PropWhen.maxParams)
    (hto : to.length ≤ PropWhen.maxParams)
    (hφ : Level.NonzeroOutside to φ) (d : Nat) (e : Expr)
    (hdef : e.allLevelParamsDefined «from» = true) :
    denoteP m.acval (env.withLpsL to) φ d (e.remapPW «from» to)
      = denoteP m.acval (env.withLpsL «from») φ d e := by
  have h := denotePInstLevels (env := env.withLpsL to) (m.withLps (UnivCtx.ofList to)) φ
    «from» («from».map .param) hnd hfrom (by simp)
    (by rw [Env.lpsL_withLpsL env hto]; exact hφ) d e hdef
  rw [EnvS2Core.withLps_acval, Env.lpsL_withLpsL env hto, Level.substFn_self] at h
  exact h

end Setlec.SetP
