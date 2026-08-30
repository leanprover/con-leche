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

end Setlec.SetR.Interp2
