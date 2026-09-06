import Setlec.SetP.Step2.BitLevels

/-!
# The representative valuation (the packed `pw` datum, 2026-09-06)

The crossing (`denotePInstLevels`) and the tier's claims are available
at valuations **nonzero outside the universe context**
(`Level.NonzeroOutside env.lpsL φ`).  A harvest that must speak at
*every* valuation ψ routes through the representative `repr env.lpsL ψ`
— ψ on the context, `1` elsewhere — and transports its readings back
with `denoteP_params_ext`: a subject whose level parameters are all in
the context reads identically at ψ and at its representative.
-/

namespace Setlec.Level

/-- The representative of `φ` at `ps`: `φ` on `ps`, `1` outside. -/
def repr (ps : List Name) (φ : Name → Nat) : Name → Nat :=
  fun n => if n ∈ ps then φ n else 1

theorem repr_nonzero (ps : List Name) (φ : Name → Nat) :
    NonzeroOutside ps (repr ps φ) := by
  intro n hn
  simp [repr, hn]

theorem repr_agree (ps : List Name) (φ : Name → Nat) :
    ∀ p ∈ ps, repr ps φ p = φ p := by
  intro p hp
  simp [repr, hp]

end Setlec.Level

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level)

universe w
variable {V : Type w} [SetTheory V] {env : Env}

/-- A context-covered subject reads the same at a valuation and at its
representative. -/
theorem denoteP_repr (m : EnvS2Core V env) (ψ : Name → Nat)
    {d : Nat} {e : Expr} (hdef : e.allLevelParamsDefined env.lpsL = true) :
    denoteP m.acval env (Level.repr env.lpsL ψ) d e = denoteP m.acval env ψ d e :=
  denoteP_params_ext m (Level.repr_agree env.lpsL ψ) d e hdef

end Setlec.SetP
