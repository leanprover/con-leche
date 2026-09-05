import Setlec.SetBase.Bridge.Spine

/-!
# `ProofIrrelStepR`, discharged (task #148, T3, batch c)

`proofIrrel` (`Core.lean:775-792`) has two branches and the family has
one rule for each: D9 `irrelUnit` (each side's type whnfs to a pinned
unit-like family head) and D8 `irrelProp` (each side's type's type
whnfs to `Prop`).  `proofIrrel_inv` hands back exactly the two
branches' certificate lists, in the checker's order.

Both branches are now straight compositions of `inferShapeR` /
`inferSortR` — D9 was always one, and D8 became one with the Finding 3
amendment's linking `DefEq` (`Infer a ta → DefEq ta ta' → Infer ta' sta
→ DefEq sta (.sort 0)`): the bridge's `Infer` at `T₁` and its `Infer` at
`⟦ta⟧` are joined by the slack itself, which is what the extra premise
names.  Reading D8's application below is the cleanest statement of what
that amendment bought — `hI1 hD1 hI2 hD2` in the rule's own order,
twice.

The level guards are absorbed at the denotation: `Level.isEquiv uT
.zero = some true` gives `uT.eval φ = 0`, and D8's premise is stated at
the ground `.sort 0`.  D9 needs no common-type check — exactly as the
checker, which compares neither side's unit family with the other's.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

variable {mode : CheckMode} {env : Env}

/-- A unit-like type's whnf denotes to a bare valuation leaf, and the
level-length side condition D9 asks for comes from that denotation's
own guard. -/
theorem unitLike_denote {cval : TConstVal} {φ : Name → Nat} {d : Nat}
    {wta : Expr} {W : VExpr} (hu : isUnitLikeTy env wta = true)
    (hW : denote cval env φ d wta = some W) :
    ∃ c us, isUnitLikeTy env (.const c us) = true ∧
      us.length = (levelParamsAt env c).length ∧
      W = cval c (Level.substFn φ (levelParamsAt env c) us) := by
  obtain ⟨c, us, cvi, capsi, cvr, mI, rP, r, rfl, hfind, -, -, -, -⟩ :=
    isUnitLikeTy_inv hu
  rw [denote_const] at hW
  cases hf : env.find? c with
  | none => rw [hf] at hW; exact nomatch hW
  | some ci =>
    rw [hf] at hW
    dsimp only at hW
    split at hW
    · next hlen =>
      have hlp : levelParamsAt env c = ci.toConstantVal.levelParams := by
        simp [levelParamsAt, hf]
      exact ⟨c, us, hu, by rw [hlp]; exact hlen,
        by rw [hlp]; exact (Option.some.inj hW).symm⟩
    · exact nomatch hW

/-- **`ProofIrrelStepR`, proved.** -/
theorem proofIrrel_stepR {env : Env} (hg : mode.betaGate = false)
    (m : EnvR env) (φ : Name → Nat)
    {fuel : Nat} (ihw : WhnfClaimsR mode m φ fuel)
    (ihi : InferClaimsR mode m φ fuel) :
    ProofIrrelStepR (mode := mode) m φ fuel := by
  intro d Δ a b h hwa hba hLa hwb hbb hLb hCa hCb va vb hva hvb
  obtain ⟨ta, wta, hta, hwta, hcase⟩ := proofIrrel_inv h
  rw [Setlec.inferTypeIO_off hg] at hta
  rcases hcase with ⟨hu, tb, wtb, htb, hwtb, hub⟩ |
    ⟨sta, uT, tb, stb, vT, hsta, hwsta, hequ, htb, hstb, hwstb, heqv⟩
  · -- D9: the unit branch
    rw [Setlec.inferTypeIO_off hg] at htb
    obtain ⟨va', WA, hva', hWA, TA, hAI, hAD⟩ :=
      inferShapeR m φ ihw ihi hta hwta hwa hba hLa hCa
    obtain rfl : va' = va := by rw [hva'] at hva; exact Option.some.inj hva
    obtain ⟨vb', WB, hvb', hWB, TB, hBI, hBD⟩ :=
      inferShapeR m φ ihw ihi htb hwtb hwb hbb hLb hCb
    obtain rfl : vb' = vb := by rw [hvb'] at hvb; exact Option.some.inj hvb
    obtain ⟨c₁, us₁, hu₁, hlen₁, rfl⟩ := unitLike_denote hu hWA
    obtain ⟨c₂, us₂, hu₂, hlen₂, rfl⟩ := unitLike_denote hub hWB
    exact DefEq.irrelUnit hu₁ hlen₁ hu₂ hlen₂ hAI hAD hBI hBD
  · -- D8: the `Prop` branch
    rw [Setlec.inferTypeIO_off hg] at hsta htb hstb
    have hu0 : Level.eval φ uT = 0 := by
      have := Level.isEquiv_sound hequ φ
      simpa [Level.eval] using this
    have hv0 : Level.eval φ vT = 0 := by
      have := Level.isEquiv_sound heqv φ
      simpa [Level.eval] using this
    -- side a: the type, then the type's type
    obtain ⟨va', vta, hva', hvta, T₁, hI1, hD1⟩ := ihi hta hwa hba hLa hCa
    obtain rfl : va' = va := by rw [hva'] at hva; exact Option.some.inj hva
    obtain ⟨htaw, htab, htaL, htaC⟩ := frame_inferR m.wf hta hwa hba hLa hCa
    obtain ⟨T₂, hI2, hD2⟩ :=
      inferSortR m φ ihw ihi hsta hwsta htaw htab htaL htaC hvta
    rw [hu0] at hD2
    -- side b, the same three moves
    obtain ⟨vb', vtb, hvb', hvtb, S₁, hJ1, hE1⟩ := ihi htb hwb hbb hLb hCb
    obtain rfl : vb' = vb := by rw [hvb'] at hvb; exact Option.some.inj hvb
    obtain ⟨htbw, htbb, htbL, htbC⟩ := frame_inferR m.wf htb hwb hbb hLb hCb
    obtain ⟨S₂, hJ2, hE2⟩ :=
      inferSortR m φ ihw ihi hstb hwstb htbw htbb htbL htbC hvtb
    rw [hv0] at hE2
    exact DefEq.irrelProp hI1 hD1 hI2 hD2 hJ1 hE1 hJ2 hE2

end Setlec.SetR
