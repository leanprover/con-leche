import Setlec.TTVerify.DefEqStep
import Setlec.Verify.PinnedShapes

/-!
# The proof-irrelevance obligation

`ProofIrrelStepTT`: a positive `proofIrrel` verdict yields a derivable
equation.  `proofIrrel` has exactly two branches and the layer has
exactly two rules for them:

| checker branch | rule |
| --- | --- |
| both sides' types whnf to a unit-like inductive | `HasType.punitEta` |
| both sides' types' types whnf to `Prop` | `HasType.proofIrrel` |

The `Prop` branch is `proof_irrel_step`, proved with the K rescue that
motivated the per-side generalization of both rules
(`Setlec/TTVerify/DESIGN.md` §10.2).  The unit-like branch is the work
here, and its content is one identification: **the checker's unit-like
test can only accept `PUnit`**, which is the family `punitEta` is
stated at.

Read that identification as §8.4 again — *the pins exist so the checker
can compare against known shapes, and the same pins are why the bridge
can compute against them*.  `isUnitLikeTy` does not name `PUnit`; it
asks for a stored inductive whose recursor is **reserved**, index-free
(`mI = rP`), and has a single zero-field rule.  Five reserved names end
in `rec`, and reading their pinned declarations settles it:

| recursor | pinned shape | why it fails |
| --- | --- | --- |
| `Eq.rec` | `mI = 5`, `rP = 4` | has an index |
| `Nat.rec` | two rules | not single-rule |
| `PSigma'.rec` | `nfields = 2` | has fields |
| `Empty.rec` | no rules | not single-rule |
| `PUnit.rec` | `mI = rP = 2`, one rule, `nfields = 0` | — |

So the test is a four-way refutation with one survivor, and it is a
`decide` once the declarations are in hand.  Getting them in hand is
what `BasisPinnedTT`'s declaration clause is for; it was dropped on the
first transposition and came back here (`Setlec/TTVerify/DESIGN.md`
§12.10).
-/

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode; the seven gated checks
reduce definitionally at `.ttModel`. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/- The identification (`unitLike_eq_punit`) lives in
`Setlec/Verify/PinnedShapes.lean` since task #148 T4 (lane-shared). -/

/-! ## The branch

With the identification in hand the unit-like branch is the same shape
as `proof_irrel_step`'s `side`: infer, whnf, read the result off the
pin.  The one difference is where the level comes from — `punitEta`
takes each side's level separately, and here each side's level is
whatever the *stored* `PUnit`'s instantiation says, which is why the
two sides never have to be compared.  That is the same per-side reading
the layer change bought (`Setlec/TTVerify/DESIGN.md` §10.2), used a
second time. -/

/-- One side of the unit-like branch: a term whose inferred type whnfs
to a unit-like family is derivably of `PUnit` at some level. -/
theorem punit_side {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel d : Nat} {Δ : List VExpr}
    (ihw : WhnfClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel)
    {e t wt : Expr}
    (het : inferTypeCore mode env fuel d e = .ok t)
    (hwt : whnf mode env fuel d t = .ok wt)
    (hu : isUnitLikeTy env wt = true)
    (hC : CtxOk m.cval env φ d Δ e) (hws : Expr.WScoped d e)
    (hb : e.looseBVarsBounded 0 = true) (hL : Expr.LeavesBounded e) :
    ∃ E u, denote m.cval env φ d e = some E ∧ HasType Δ E (punitT u) := by
  obtain ⟨E, T, hE, hT, hEt⟩ := ihi het hws hb hL hC
  have hCt : CtxOk m.cval env φ d Δ t :=
    CtxOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel het hws) hC
  have hwst : Expr.WScoped d t := inferTypeCore_WScoped m.wf fuel het hws
  have hbt : t.looseBVarsBounded 0 = true :=
    inferTypeCore_looseBVars m.wf fuel het hws hb hL
  have hLt : Expr.LeavesBounded t := fun l hl =>
    hL l (inferTypeCore_fvarLeaves m.wf fuel het hws l hl)
  obtain ⟨W, hW, hDeq⟩ := ihw hwt hwst hbt hLt hCt hT
  obtain ⟨us, rfl, hfind⟩ := unitLike_eq_punit m.basis_pinned hu
  -- the pin computes the whnf'd type: it is `PUnit` at the level the
  -- stored declaration's parameter is instantiated to
  rw [denote_const, hfind] at hW
  dsimp only at hW
  by_cases hlen : us.length = punitA.toConstantVal.levelParams.length
  · rw [if_pos hlen] at hW
    obtain rfl : m.cval punitName
        (Level.substFn φ punitA.toConstantVal.levelParams us) = W :=
      Option.some.inj hW
    have hpv : m.cval punitName
        (Level.substFn φ punitA.toConstantVal.levelParams us)
        = punitT
            ((Level.substFn φ punitA.toConstantVal.levelParams us) uN) :=
      cval_pinned m (n := punitName) (by decide) (by rw [hfind]; rfl) _ rfl
    exact ⟨E, (Level.substFn φ punitA.toConstantVal.levelParams us) uN,
      hE, hpv ▸ Deq.conv hEt hDeq⟩
  · rw [if_neg hlen] at hW
    exact nomatch hW

/-- **`ProofIrrelStepTT`, discharged.** -/
theorem proofIrrel_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsTT mode m φ fuel)
    (ihi : InferClaimsTT mode m φ fuel) : ProofIrrelStepTT m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨ta, wta, hta, hwta, hcase⟩ := proofIrrel_inv h
  rcases hcase with ⟨hua, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwsta, huT, htb, hstb, hwstb, hvT⟩
  · -- both sides inhabit a unit-like family: only `PUnit` is one
    obtain ⟨A, u, hA, hAt⟩ :=
      punit_side m φ ihw ihi hta hwta hua hCa hwa hba hLa
    obtain ⟨B, v, hB, hBt⟩ :=
      punit_side m φ ihw ihi htb hwtb hub hCb hwb hbb hLb
    obtain rfl : A = va := by rw [hA] at hva; exact Option.some.inj hva
    obtain rfl : B = vb := by rw [hB] at hvb; exact Option.some.inj hvb
    exact ⟨punitT u, HasType.punitEta hAt hBt⟩
  · -- both sides' types are `Prop`s
    obtain ⟨A, B, hA, hB, hDeq⟩ :=
      proof_irrel_step m φ ihw ihi hta hsta hwsta
        (Level.isEquiv_sound huT φ) htb hstb hwstb
        (Level.isEquiv_sound hvT φ) hCa hCb hwa hwb hba hbb hLa hLb
    obtain rfl : A = va := by rw [hA] at hva; exact Option.some.inj hva
    obtain rfl : B = vb := by rw [hB] at hvb; exact Option.some.inj hvb
    exact hDeq

end Setlec.TTVerify
