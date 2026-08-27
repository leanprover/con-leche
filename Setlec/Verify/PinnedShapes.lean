import Setlec.Verify.InferLemmas
import Setlec.Verify.Denote.Pinned

/-!
# The pinned-shape identifications (lane-shared)

The reserved-recursor refutations both verified lanes use to identify
the checker's shape tests with the pinned basis families: only `PUnit`
passes `isUnitLikeTy`, and only `PSigma'` passes the pair-eta test.
Relocated from `Setlec/TTVerify/{ProofIrrelStep,PairEtaStep}.lean`
(task #148 T4, the T1-style move), generalized from `EnvTT` to the one
field they consume (`BasisPinnedTT` — itself relocated here-adjacent,
`Setlec/Verify/Denote/Pinned.lean`), so `Setlec/SetR/*` can consume
them without importing the TT lane.
-/

namespace Setlec.TTVerify

open Setlec.TT

/-- Which reserved names carry recursor-shaped pinned declarations.
The transpose of `Setlec/Model/BasisVal.lean`'s
`pinnedInfo_ctorInfo_cases`, and proved the same way. -/
theorem pinnedInfoT_recInfo_cases {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rules : List RecRule}
    (h : pinnedInfo n = .recInfo cv mI rP rules) :
    n = eqName.str "rec" ∨ n = natName.str "rec" ∨
    n = psigmaName.str "rec" ∨ n = punitName.str "rec" ∨
    n = emptyName.str "rec" ∨ n = quotLiftName ∨ n = quotIndName := by
  unfold pinnedInfo at h
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
theorem unitLike_eq_punit {env : Env} {cval : TConstVal}
    (hbp : BasisPinnedTT env cval) {e : Expr}
    (h : isUnitLikeTy env e = true) :
    ∃ us, e = .const punitName us ∧
      env.find? punitName = some punitA := by
  obtain ⟨c, us, cvi, capsi, cvr, mI, rP, r, rfl, hfc, hfr, hmI, hnf,
    hres⟩ := isUnitLikeTy_inv h
  -- the recursor's stored declaration is the pinned one
  have hpin : pinnedInfo (c.str "rec") = .recInfo cvr mI rP [r] :=
    ((hbp _ _ hfr hres).1 rfl).symm
  -- and every pin but `PUnit.rec`'s is refuted by the test's own
  -- three conditions, or by its name
  have hc : c = punitName := by
    rcases pinnedInfoT_recInfo_cases hpin with
      he | he | he | he | he | he | he
    · -- `Eq.rec` has an index: `mI = 5`, `rP = 4`
      rw [he] at hpin
      rw [show pinnedInfo (eqName.str "rec") = eqRecA from rfl] at hpin
      simp only [eqRecA, ConstantInfo.recInfo.injEq] at hpin
      omega
    · -- `Nat.rec` has two rules
      rw [he] at hpin
      rw [show pinnedInfo (natName.str "rec") = natRecA from rfl] at hpin
      simp [natRecA] at hpin
    · -- `PSigma'.rec`'s single rule has two fields
      rw [he] at hpin
      rw [show pinnedInfo (psigmaName.str "rec") = psigmaRecA from rfl]
        at hpin
      simp only [psigmaRecA, ConstantInfo.recInfo.injEq,
        List.cons.injEq] at hpin
      have h2 : r.nfields = 2 := by rw [← hpin.2.2.2.1]
      omega
    · exact (Name.str.injEq .. ▸ he).1
    · -- `Empty.rec` has no rules
      rw [he] at hpin
      rw [show pinnedInfo (emptyName.str "rec") = emptyRecA from rfl]
        at hpin
      simp [emptyRecA] at hpin
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
  subst hc
  have hp : ConstantInfo.indInfo cvi capsi = pinnedInfo punitName :=
    (hbp _ _ hfc (by decide)).1 rfl
  rw [show pinnedInfo punitName = punitA from rfl] at hp
  exact ⟨us, rfl, hp ▸ hfc⟩

/-- **Only `PSigma'` passes the pair-eta test**: a reserved recursor
with one two-field rule and no indices.  The same refutation as
`unitLike_eq_punit`, at a different rule shape. -/
theorem pairLike_eq_psigma {env : Env} {cval : TConstVal}
    (hbp : BasisPinnedTT env cval) {c' : Name}
    {cvr : ConstantVal} {mI rP : Nat} {rr : RecRule}
    (hfr : env.find? (c'.str "rec") = some (.recInfo cvr mI rP [rr]))
    (hnf : rr.nfields = 2) (hmi : mI = rP)
    (hres : reservedBasisNames.contains (c'.str "rec") = true) :
    c' = psigmaName ∧ rr.ctor = psigmaMkName := by
  have hpin : pinnedInfo (c'.str "rec") = .recInfo cvr mI rP [rr] :=
    ((hbp _ _ hfr hres).1 rfl).symm
  have hc : c' = psigmaName := by
    rcases pinnedInfoT_recInfo_cases hpin with
      he | he | he | he | he | he | he
    · rw [he] at hpin
      rw [show pinnedInfo (eqName.str "rec") = eqRecA from rfl] at hpin
      simp only [eqRecA, ConstantInfo.recInfo.injEq] at hpin
      omega
    · rw [he] at hpin
      rw [show pinnedInfo (natName.str "rec") = natRecA from rfl] at hpin
      simp [natRecA] at hpin
    · exact (Name.str.injEq ..  ▸ he).1
    · rw [he] at hpin
      rw [show pinnedInfo (punitName.str "rec") = punitRecA from rfl]
        at hpin
      simp only [punitRecA, ConstantInfo.recInfo.injEq,
        List.cons.injEq] at hpin
      have h2 : rr.nfields = 0 := by rw [← hpin.2.2.2.1]
      omega
    · rw [he] at hpin
      rw [show pinnedInfo (emptyName.str "rec") = emptyRecA from rfl]
        at hpin
      simp [emptyRecA] at hpin
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
    · exact absurd (Name.str.injEq .. ▸ he).2 (by decide)
  refine ⟨hc, ?_⟩
  rw [hc] at hpin
  rw [show pinnedInfo (psigmaName.str "rec") = psigmaRecA from rfl] at hpin
  simp only [psigmaRecA, ConstantInfo.recInfo.injEq, List.cons.injEq] at hpin
  rw [← hpin.2.2.2.1]
  rfl

end Setlec.TTVerify
