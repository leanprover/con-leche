import Setlec.SetR.Interp2.AxiomBitsP

/-!
# The pinned axioms' `interp2` memberships (task #161, ENDGAME C, task 1a)

`StdAxiomKey.lean`'s two forcing arguments, re-derived at the graded
currency.  The ENDGAME B seal wrote the route; this file executes it,
and one step of it needed content the seal did not predict.

## The unpredicted step, and the lemma that supplies it

The seal's route says: *instantiate `Iff.rec` at `ψ uN ≠ 0`, where
every bit is `1`, so the motive space is the graph regime and
`app_lamR_pos` computes*.  **The bits it names are the pin's, not the
stored constant's** — `matchesPin` compares through `erasePw`, so the
stored companions' binder data are exactly what the comparison
forgives, and `AxiomBitsP`'s bit lemmas are unavailable here: they read
`ConstantValR`'s recorded run, and the recorded run in scope belongs to
the *axiom being installed*, never to `Iff.rec`, which was stored many
declarations ago.

So the route as written does not close, and the missing step is not a
bit lemma (there is no run to read).  It is this:

> **`pi_sort_bit_ne_zero`** — a graded `∀`-node whose codomain is a
> *sort* and whose domain is *inhabited* has a nonzero bit.

`AnnotValidV`'s `pi` third component is one-directional — `v = 0 → ∀ x
∈ A, B x ∈ˢ univZero` — which the ENDGAME A seal recorded as the reason
it cannot *pin* a bit.  It can still *refute* one: at a sort codomain
the consequent is `univ n ∈ˢ univZero`, and no universe is a truth
value (`univ_not_mem_univZero`, one line from `mem_univZero` +
`pt_not_mem_univZero`).  The domain's inhabitant is free at both
recursors — it is the very witness being eliminated.

That is the whole of the difference, and it makes the memberships
**bit-agnostic in the companions**: every elimination of a stored
family goes through `app_mem_piR` with its side condition read off
`type_okP` (the seal's dissolved case-split, confirmed), and the one
place a *computation* is needed — the motive's β — is licensed by
`pi_sort_bit_ne_zero` rather than by a known bit.  `Iff.rec` is still
instantiated at `ψ uN ≠ 0`, but now only because `eqv A B` must inhabit
`univ (ψ uN)`; the graph regime comes from the sort codomain, at every
assignment.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The lever

Two lemmas.  The first is pure set theory and belongs to no tier; the
second is the graded model's reading of `AnnotValidV`'s one-directional
`pi` obligation. -/

/-- **No universe is a truth value.**  `univZero`'s members are subsets
of `{pt}`, and `empty` is in every universe, so a universe inside
`univZero` would make `empty = pt` — and `empty` *is* a truth value,
while `pt` is not (`pt_not_mem_univZero`). -/
theorem univ_not_mem_univZero (n : Nat) : ¬ (univ n : V) ∈ˢ univZero := by
  intro h
  have hemp : (empty : V) ∈ˢ unitSet := mem_univZero.mp h _ (empty_mem_univ n)
  have he : (empty : V) = pt := mem_unitSet hemp
  refine pt_not_mem_univZero (V := V) ?_
  rw [← he]
  exact univ_zero (V := V) ▸ empty_mem_univ 0

/-- **A graded `∀` over an inhabited domain, with a sort codomain, is
in the graph regime.**  The lever of this file (see the module
docstring): `AnnotValidV`'s `pi` clause cannot *establish* a bit, but
at a sort codomain it *refutes* zero, and the refutation needs only an
inhabitant of the domain — which every elimination has in hand. -/
theorem pi_sort_bit_ne_zero {ρ : Nat → V} {u v n : Nat} {Aa : AVExpr}
    (hv : AnnotValidV V ρ (.pi u v Aa (.sort n)))
    {x : V} (hx : x ∈ˢ interp2 V ρ Aa) : v ≠ 0 := by
  intro h0
  rw [AnnotValidV_pi] at hv
  exact univ_not_mem_univZero (V := V) n (hv.2.2 h0 x hx)

/-- Elimination at a `pi` reading, with the side condition read off the
node's own validity — the ENDGAME B seal's dissolved case-split, as a
lemma.  **No knowledge of `v` is needed**: this is why the stored
companions' unpinned bits never have to be established. -/
theorem app_mem_pi_validV {ρ : Nat → V} {u v : Nat} {Aa Ba : AVExpr}
    {f a : V} (hf : f ∈ˢ interp2 V ρ (.pi u v Aa Ba))
    (ha : a ∈ˢ interp2 V ρ Aa)
    (hv : AnnotValidV V ρ (.pi u v Aa Ba)) :
    SetTheory.app f a ∈ˢ interp2 V (cons a ρ) Ba := by
  rw [interp2_pi] at hf
  rw [AnnotValidV_pi] at hv
  exact app_mem_piR hf ha hv.2.2

end Setlec.SetR.Interp2
