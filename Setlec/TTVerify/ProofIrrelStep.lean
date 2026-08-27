import Setlec.TTVerify.DefEqStep

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

/-! ## The identification

Two steps: the reserved name ending in `rec` is one of five, and four
of the five have pinned shapes the unit-like test rejects. -/

/-- Which reserved names carry recursor-shaped pinned declarations.
The transpose of `Setlec/Model/BasisVal.lean`'s
`pinnedInfo_ctorInfo_cases`, and proved the same way. -/
theorem pinnedInfoT_recInfo_cases {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfoT n = .recInfo cv mI rP rules) :
    n = eqName.str "rec" ∨ n = natName.str "rec" ∨
    n = psigmaName.str "rec" ∨ n = punitName.str "rec" ∨
    n = emptyName.str "rec" ∨ n = quotLiftName ∨ n = quotIndName := by
  unfold pinnedInfoT at h
  by_cases h1 : n = eqName
  · rw [if_pos h1] at h; exact nomatch h
  rw [if_neg h1] at h
  by_cases h2 : n = eqReflName
  · rw [if_pos h2] at h; exact nomatch h
  rw [if_neg h2] at h
  by_cases h3 : n = eqName.str "rec"
  · exact Or.inl h3
  rw [if_neg h3] at h
  by_cases h4 : n = natName
  · rw [if_pos h4] at h; exact nomatch h
  rw [if_neg h4] at h
  by_cases h5 : n = natZeroName
  · rw [if_pos h5] at h; exact nomatch h
  rw [if_neg h5] at h
  by_cases h6 : n = natSuccName
  · rw [if_pos h6] at h; exact nomatch h
  rw [if_neg h6] at h
  by_cases h7 : n = natName.str "rec"
  · exact Or.inr (Or.inl h7)
  rw [if_neg h7] at h
  by_cases h8 : n = psigmaName
  · rw [if_pos h8] at h; exact nomatch h
  rw [if_neg h8] at h
  by_cases h9 : n = psigmaMkName
  · rw [if_pos h9] at h; exact nomatch h
  rw [if_neg h9] at h
  by_cases h10 : n = psigmaName.str "rec"
  · exact Or.inr (Or.inr (Or.inl h10))
  rw [if_neg h10] at h
  by_cases h11 : n = punitName
  · rw [if_pos h11] at h; exact nomatch h
  rw [if_neg h11] at h
  by_cases h12 : n = punitUnitName
  · rw [if_pos h12] at h; exact nomatch h
  rw [if_neg h12] at h
  by_cases h13 : n = punitName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
  rw [if_neg h13] at h
  by_cases h14 : n = emptyName
  · rw [if_pos h14] at h; exact nomatch h
  rw [if_neg h14] at h
  by_cases h15 : n = emptyName.str "rec"
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h15))))
  rw [if_neg h15] at h
  by_cases h16 : n = quotName
  · rw [if_pos h16] at h; exact nomatch h
  rw [if_neg h16] at h
  by_cases h17 : n = quotMkName
  · rw [if_pos h17] at h; exact nomatch h
  rw [if_neg h17] at h
  by_cases h18 : n = quotLiftName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h18)))))
  rw [if_neg h18] at h
  by_cases h19 : n = quotIndName
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h19))))))
  rw [if_neg h19] at h
  by_cases h20 : n = quotSoundName
  · rw [if_pos h20] at h; exact nomatch h
  rw [if_neg h20] at h
  exact nomatch h

/-- **Only `PUnit` passes the unit-like test.**  Every other reserved
recursor's pinned shape fails one of its three conditions. -/
theorem unitLike_eq_punit {env : Env} (m : EnvTT env) {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ us, e = .const punitName us ∧
      env.find? punitName = some punitA := by
  obtain ⟨c, us, cvi, capsi, cvr, mI, rP, r, rfl, hfc, hfr, hmI, hnf,
    hres⟩ := isUnitLikeTy_inv h
  -- the recursor's stored declaration is the pinned one
  have hpin : pinnedInfoT (c.str "rec") = .recInfo cvr mI rP [r] :=
    ((m.basis_pinned _ _ hfr hres).1 rfl).symm
  -- and every pin but `PUnit.rec`'s is refuted by the test's own
  -- three conditions, or by its name
  have hc : c = punitName := by
    rcases pinnedInfoT_recInfo_cases hpin with
      he | he | he | he | he | he | he
    · -- `Eq.rec` has an index: `mI = 5`, `rP = 4`
      rw [he] at hpin
      rw [show pinnedInfoT (eqName.str "rec") = eqRecA from rfl] at hpin
      simp only [eqRecA, ConstantInfo.recInfo.injEq] at hpin
      omega
    · -- `Nat.rec` has two rules
      rw [he] at hpin
      rw [show pinnedInfoT (natName.str "rec") = natRecA from rfl] at hpin
      simp [natRecA] at hpin
    · -- `PSigma'.rec`'s single rule has two fields
      rw [he] at hpin
      rw [show pinnedInfoT (psigmaName.str "rec") = psigmaRecA from rfl]
        at hpin
      simp only [psigmaRecA, ConstantInfo.recInfo.injEq,
        List.cons.injEq] at hpin
      have h2 : r.nfields = 2 := by rw [← hpin.2.2.2.1]
      omega
    · exact (Name.str.injEq .. ▸ he).1
    · -- `Empty.rec` has no rules
      rw [he] at hpin
      rw [show pinnedInfoT (emptyName.str "rec") = emptyRecA from rfl]
        at hpin
      simp [emptyRecA] at hpin
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
  subst hc
  have hp : ConstantInfo.indInfo cvi capsi = pinnedInfoT punitName :=
    (m.basis_pinned _ _ hfc (by decide)).1 rfl
  rw [show pinnedInfoT punitName = punitA from rfl] at hp
  exact ⟨us, rfl, hp ▸ hfc⟩

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
  obtain ⟨us, rfl, hfind⟩ := unitLike_eq_punit m hu
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
            ((Level.substFn φ punitA.toConstantVal.levelParams us) uNT) :=
      cval_pinned m (n := punitName) (by decide) (by rw [hfind]; rfl) _ rfl
    exact ⟨E, (Level.substFn φ punitA.toConstantVal.levelParams us) uNT,
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
