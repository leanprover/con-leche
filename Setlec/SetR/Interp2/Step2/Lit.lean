import Setlec.SetR.Interp2.Step2.Infer
import Setlec.SetR.Interp2.BasisType

/-!
# `CheckStep2`, the literal clauses — Tier B (the transposition batch)

`Sound/Lit.lean`'s numeral facts onto `piR`/`AnnotOk2`/`interp2` and
`denote2`'s own numeral spine (`natLitT2`, from `Interp2/BasisType.lean`
— the same former `denote2`'s `.lit natVal` clause emits).

**This is transposition, not new argument**, which is what
`interp2_closed` (seal 2 of step 3) bought: the block touches the
interpretation through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed`, and all five now have `interp2`
analogues.

The numeral induction is stated over the two head facts as **explicit
arguments** rather than re-deriving them from the environment.  That is
deliberate: the head facts are a `mem_type2` chain over the stored
`Nat`/`Nat.zero`/`Nat.succ` shapes — the *same* chain for every numeral
— and factoring them out keeps the induction free of the literal
guards' inversion plumbing, exactly as v1 factors `natHeads_facts` out
of `natLit_facts`.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- **The numeral facts.**  Every `denote2` numeral is truthful and
inhabits the stored `Nat`'s interpretation — by induction on the
numeral, from the zero's membership and the successor's `piR`
membership.

`Nat → Nat` sits at result sort `1`, so the successor's product is in
the **graph regime** and `app_mem_piR_pos` applies with no fibre
premise; the app slot's kind-`0` component is vacuous for the same
reason.  v1 needed `app_mem_piC` plus the collapse's side conditions
here. -/
theorem natLit_facts2 {ρ : Nat → V} {za sa natA : AVExpr}
    (hokz : AnnotOk2 V ρ za) (hoks : AnnotOk2 V ρ sa)
    (hz : interp2 V ρ za ∈ˢ interp2 V ρ natA)
    (hsucc : interp2 V ρ sa
      ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA) :
    ∀ n : Nat,
      AnnotOk2 V ρ (natLitT2 za sa n) ∧
        interp2 V ρ (natLitT2 za sa n) ∈ˢ interp2 V ρ natA := by
  intro n
  induction n with
  | zero => exact ⟨hokz, hz⟩
  | succ n ih =>
    obtain ⟨ihA, ihm⟩ := ih
    refine ⟨?_, ?_⟩
    · show AnnotOk2 V ρ (.app sa (natLitT2 za sa n))
      rw [AnnotOk2_app]
      exact ⟨hoks, ihA, 1, _, _, hsucc, ihm,
        fun h => absurd h Nat.one_ne_zero⟩
    · show interp2 V ρ (.app sa (natLitT2 za sa n)) ∈ˢ _
      rw [interp2_app]
      exact app_mem_piR_pos Nat.one_ne_zero hsucc ihm

/-! ## Re-pointed to `Claims2A` (seal 6)

**`natLit_facts2` needed no repair, and that is a fact about the
amendment rather than about this file.**  All four repairs are about
*fuel*: R1 and R3 move the annotation's fuel, R2 grades a reduction, R4
restricts the modes.  `natLit_facts2` mentions no fuel, no `denote2`
and no mode — it is a pure `interp2`/`AnnotOk2` statement about a
`natLitT2` spine — so it is amendment-neutral by construction.

*Rule: a lemma stated in the interpretation alone survives every
repair to the claim family, because every defect this campaign found
lives in the indexing between the run and the annotation.  The literal
blocks were transposed to `interp2` early, and that is why they cost
nothing here.*

What did have to be re-pointed is the **clause** built on top, below.
-/

open Setlec (CheckMode Env Expr Name inferTypeCore inferBody viewM
  natLitSupported)

variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-- **I10A (`.lit natVal`), amended.**  The checker returns
`.const Nat []`, whose `denote2` is a **fuel-free** leaf read out of
`acval`; so, exactly like `.sort` and `.fvar`, this clause takes
`F' = F` and spends none of R3's slack.

The two membership facts stay explicit arguments for the reason the
module docstring gives — they are one `mem_type2` chain over the
stored `Nat` shapes, the same for every numeral — and the two
truthfulness facts do *not*, because `EnvS2.acval_ok2` supplies them.
The returned type's annotation is likewise a hypothesis rather than a
computation: `.const`'s `denote2` needs the stored `Nat` to be found
with the right level arity, which `natLitSupported` guarantees for the
*checker* but which no lemma yet transports to `denote2`. -/
theorem infer_natLit_claim2A (m : EnvS2 V env) {d k F : Nat}
    {t : Expr} {Δa : List AVExpr} {ea natA : AVExpr}
    (h : inferTypeCore μ env (fuel + 1) d (.lit (.natVal k)) = .ok t)
    (hea : denote2 μ m.acval env φ F d (.lit (.natVal k)) = some ea)
    (hty : denote2 μ m.acval env φ F d (.const Setlec.natName [])
      = some natA)
    (hz : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ (m.acval Setlec.natZeroName (Level.substFn φ [] []))
        ∈ˢ interp2 V ρ natA)
    (hsucc : ∀ ρ : Nat → V, Sat2 V Δa ρ →
      interp2 V ρ (m.acval Setlec.natSuccName (Level.substFn φ [] []))
        ∈ˢ piR 1 (interp2 V ρ natA) fun _ => interp2 V ρ natA) :
    ∃ F' ta, F ≤ F' ∧
      denote2 μ m.acval env φ F' d t = some ta ∧
      ∀ ρ : Nat → V, Sat2 V Δa ρ →
        AnnotOk2 V ρ ea ∧ interp2 V ρ ea ∈ˢ interp2 V ρ ta := by
  rw [Setlec.inferTypeCore_succ] at h
  simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  split at h
  · next hsup =>
    simp only [Except.ok.injEq] at h
    subst h
    rw [denote2] at hea
    simp only [hsup, if_true] at hea
    obtain rfl : ea = natLitT2
        (m.acval Setlec.natZeroName (Level.substFn φ [] []))
        (m.acval Setlec.natSuccName (Level.substFn φ [] [])) k :=
      (Option.some.inj hea).symm
    refine ⟨F, natA, Nat.le_refl F, hty, fun ρ hρ => ?_⟩
    exact natLit_facts2 (m.acval_ok2 _ _ ρ) (m.acval_ok2 _ _ ρ)
      (hz ρ hρ) (hsucc ρ hρ) k
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end Setlec.SetR.Interp2
