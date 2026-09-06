import Lech.SetP.DivModP
import Lech.PinGen.Certs

/-!
# The WF-recursive `Nat` operations' literal values at `interp2`
(task #161, literal tier — the divmod leg, part 2)

`Sound/NatOpsWf.lean`'s meta-level strong inductions, re-proved at the
validated-annotation currency: the `ble`-guarded value clauses of
`DivModP` drive the recursion, the guards are computed by
`natOpV2_ble`, the steps by the structural operations' closed forms
(`NatSemP.lean`), and the metatheory-side bit-operation recurrences
are the pin generator's own certificate theorems (`PinGen.*Cert`) —
pure `Nat` facts, reused verbatim.

The one presentational improvement over v1: each operation's clause
dispatch is unpacked by a named lemma stated at the interpretation
valuation (`divModClausesP_gcd` …), instead of a page-wide type
ascription inline in the induction.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint natOpGuard natLitSupported)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}

/-! ## The small numerals, unfolded -/

/-- The literal `1` (definitional, packaged for rewriting). -/
theorem natLitP_one (m : EnvS2Core V env) (ρ : Nat → V) :
    interp2 V ρ (natLitP m φ 1)
      = SetTheory.app (interp2 V ρ (m.acval Lech.natSuccName φ))
          (interp2 V ρ (m.acval Lech.natZeroName φ)) := rfl

/-- The literal `2` (definitional). -/
theorem natLitP_two (m : EnvS2Core V env) (ρ : Nat → V) :
    interp2 V ρ (natLitP m φ 2)
      = SetTheory.app (interp2 V ρ (m.acval Lech.natSuccName φ))
          (SetTheory.app (interp2 V ρ (m.acval Lech.natSuccName φ))
            (interp2 V ρ (m.acval Lech.natZeroName φ))) := rfl

/-! ## The clause dispatch, unpacked per operation

Each lemma below is `DivModClausesV`'s branch for one operation, read
at the interpretation valuation.  `divModClausesV_divmod`
(`Sound/NatOpsWf.lean`) is already valuation-generic and is reused for
`Nat.div`/`Nat.mod`. -/

section Unpack

variable (m : EnvS2Core V env) (ρ : Nat → V)

/-- `Nat.gcd`'s two clauses. -/
theorem divModClausesP_gcd {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natGcdName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natGcdName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natGcdName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natModName φ)) y) x)) x) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natGcdName φ)) x) y = y) := by
  rw [natLitP_one]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.shiftLeft`'s two clauses. -/
theorem divModClausesP_shiftLeft {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natShiftLeftName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) y
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natShiftLeftName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natShiftLeftName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natMulName φ))
              (interp2 V ρ (natLitP m φ 2))) x))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natSubName φ)) y)
              (interp2 V ρ (natLitP m φ 1)))) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) y
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natShiftLeftName φ)) x) y = x) := by
  rw [natLitP_one, natLitP_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.shiftRight`'s two clauses. -/
theorem divModClausesP_shiftRight {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natShiftRightName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) y
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natShiftRightName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natDivName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natShiftRightName φ)) x)
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natSubName φ)) y)
                (interp2 V ρ (natLitP m φ 1)))))
            (interp2 V ρ (natLitP m φ 2))) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) y
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natShiftRightName φ)) x) y
        = x) := by
  rw [natLitP_one, natLitP_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.land`'s two clauses. -/
theorem divModClausesP_land {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natLandName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natLandName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natMulName φ))
              (interp2 V ρ (natLitP m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natLandName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) y)
                  (interp2 V ρ (natLitP m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natMulName φ))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natModName φ)) x)
                (interp2 V ρ (natLitP m φ 2))))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natModName φ)) y)
                (interp2 V ρ (natLitP m φ 2))))) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natLandName φ)) x) y
        = interp2 V ρ (m.acval Lech.natZeroName φ)) := by
  rw [natLitP_one, natLitP_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.lor`'s two clauses. -/
theorem divModClausesP_lor {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natLorName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natLorName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natMulName φ))
              (interp2 V ρ (natLitP m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natLorName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) y)
                  (interp2 V ρ (natLitP m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natSubName φ))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natAddName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) y)
                  (interp2 V ρ (natLitP m φ 2)))))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natMulName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) y)
                  (interp2 V ρ (natLitP m φ 2)))))) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natLorName φ)) x) y = y) := by
  rw [natLitP_one, natLitP_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

/-- `Nat.xor`'s two clauses. -/
theorem divModClausesP_xor {x y : V}
    (h : DivModClausesV V (fun n => interp2 V ρ (m.acval n φ))
      Lech.natXorName x y) :
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolTrueName φ) →
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natXorName φ)) x) y
        = SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natAddName φ))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natMulName φ))
              (interp2 V ρ (natLitP m φ 2)))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natXorName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natDivName φ)) y)
                  (interp2 V ρ (natLitP m φ 2))))))
            (SetTheory.app (SetTheory.app
              (interp2 V ρ (m.acval Lech.natModName φ))
              (SetTheory.app (SetTheory.app
                (interp2 V ρ (m.acval Lech.natAddName φ))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) x)
                  (interp2 V ρ (natLitP m φ 2))))
                (SetTheory.app (SetTheory.app
                  (interp2 V ρ (m.acval Lech.natModName φ)) y)
                  (interp2 V ρ (natLitP m φ 2)))))
              (interp2 V ρ (natLitP m φ 2)))) ∧
    (SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natBleName φ))
        (interp2 V ρ (natLitP m φ 1))) x
      = interp2 V ρ (m.acval Lech.boolFalseName φ) →
      SetTheory.app (SetTheory.app
        (interp2 V ρ (m.acval Lech.natXorName φ)) x) y = y) := by
  rw [natLitP_one, natLitP_two]
  simpa +decide only [DivModClausesV, if_false, if_true] using h

end Unpack

/-! ## The per-operation strong inductions -/

variable {m : EnvS2Core V env}

/-- The common induction for `Nat.div` and `Nat.mod` (they share their
guards and their step argument) — `natOpV_divmod`'s mirror. -/
theorem natOpV2_divmod (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ) {c : Name}
    (hc : c = Lech.natDivName ∨ c = Lech.natModName)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app (interp2 V ρ (m.acval c φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ
          (if c = Lech.natDivName then a / b else a % b)) := by
  have hcmem : c ∈ Lech.natDivModNames := by
    rcases hc with rfl | rfl <;> decide
  obtain ⟨hg, hclauses⟩ := hdm c hcmem cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  have hdepmem : Lech.natSubName ∈ Lech.natOpDeps c ∧
      Lech.natBleName ∈ Lech.natOpDeps c := by
    rcases hc with rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨cvsu, vsu, hsu, hfsu, -⟩ := hdeps Lech.natSubName hdepmem.1
  obtain ⟨cvbl, vbl, hbl, hfbl, -⟩ := hdeps Lech.natBleName hdepmem.2
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have hamem := natLitP_mem m hnh hval hs ρ a
    have hbmem := natLitP_mem m hnh hval hs ρ b
    obtain ⟨hrec, hgt, hzero⟩ :=
      divModClausesV_divmod hc (hclauses ρ _ _ hamem hbmem)
    by_cases hb0 : b = 0
    · subst hb0
      -- `ble 1 0` is `false`: the second base clause fires
      have h1 : SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natBleName φ))
          (SetTheory.app (interp2 V ρ (m.acval Lech.natSuccName φ))
            (interp2 V ρ (m.acval Lech.natZeroName φ))))
          (interp2 V ρ (natLitP m φ 0))
          = interp2 V ρ (m.acval Lech.boolFalseName φ) := by
        have h := natOpV2_ble m hops hnh hval hfbl ρ 1 0
        rw [natLitP_one] at h
        rw [h, if_neg (by omega)]
      rw [hzero h1]
      rcases hc with rfl | rfl
      · rw [if_pos rfl, if_pos rfl, Nat.div_zero]
        rfl
      · rw [if_neg (by decide), if_neg (by decide), Nat.mod_zero]
    · by_cases hba : b ≤ a
      · have h1 : SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natBleName φ))
            (interp2 V ρ (natLitP m φ b)))
            (interp2 V ρ (natLitP m φ a))
            = interp2 V ρ (m.acval Lech.boolTrueName φ) := by
          rw [natOpV2_ble m hops hnh hval hfbl ρ b a, if_pos hba]
        have h2 : SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natBleName φ))
            (SetTheory.app (interp2 V ρ (m.acval Lech.natSuccName φ))
              (interp2 V ρ (m.acval Lech.natZeroName φ))))
            (interp2 V ρ (natLitP m φ b))
            = interp2 V ρ (m.acval Lech.boolTrueName φ) := by
          have h := natOpV2_ble m hops hnh hval hfbl ρ 1 b
          rw [natLitP_one] at h
          rw [h, if_pos (by omega)]
        have hsub : SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natSubName φ))
            (interp2 V ρ (natLitP m φ a)))
            (interp2 V ρ (natLitP m φ b))
            = interp2 V ρ (natLitP m φ (a - b)) :=
          natOpV2_sub m hops hnh hval hfsu ρ a b
        have hlt : a - b < a := Nat.sub_lt (by omega) (by omega)
        have hih := ih (a - b) hlt
        rw [hrec h1 h2, hsub, hih]
        by_cases hcd : c = Lech.natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          have hd : a / b = (a - b) / b + 1 := by
            rw [Nat.div_eq a b, if_pos ⟨by omega, hba⟩]
          rw [hd]
          rfl
        · rw [if_neg hcd, if_neg hcd, if_neg hcd]
          have hmo : a % b = (a - b) % b := Nat.mod_eq_sub_mod hba
          rw [hmo]
      · have h1 : SetTheory.app (SetTheory.app
            (interp2 V ρ (m.acval Lech.natBleName φ))
            (interp2 V ρ (natLitP m φ b)))
            (interp2 V ρ (natLitP m φ a))
            = interp2 V ρ (m.acval Lech.boolFalseName φ) := by
          rw [natOpV2_ble m hops hnh hval hfbl ρ b a, if_neg hba]
        rw [hgt h1]
        have hab : a < b := by omega
        by_cases hcd : c = Lech.natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, Nat.div_eq_of_lt hab]
          rfl
        · rw [if_neg hcd, if_neg hcd, Nat.mod_eq_of_lt hab]

/-- `Nat.div` on literal values. -/
theorem natOpV2_div (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natDivName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natDivName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a / b)) := by
  intro a b
  have h := natOpV2_divmod hops hnh hval hdm (Or.inl rfl) hf ρ a b
  rwa [if_pos rfl] at h

/-- `Nat.mod` on literal values. -/
theorem natOpV2_mod (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natModName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natModName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (a % b)) := by
  intro a b
  have h := natOpV2_divmod hops hnh hval hdm (Or.inr rfl) hf ρ a b
  rwa [if_neg (by decide)] at h

/-- `Nat.gcd` on literal values. -/
theorem natOpV2_gcd (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natGcdName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natGcdName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.gcd a b)) := by
  obtain ⟨hg, hclauses⟩ := hdm Lech.natGcdName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Lech.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_gcd m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, Nat.gcd_zero_left]
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 a
      rw [hrec (by rw [h1, if_pos (by omega)]),
        natOpV2_mod hops hnh hval hdm hfmo ρ b a,
        ih (b % a) (Nat.mod_lt _ (by omega)) a, Nat.gcd_rec a b]

/-- `Nat.shiftLeft` on literal values. -/
theorem natOpV2_shiftLeft (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natShiftLeftName
      = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natShiftLeftName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.shiftLeft a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Lech.natShiftLeftName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Lech.natSubName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Lech.natMulName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_shiftLeft m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 b
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV2_mul m hops hnh hval hfmu ρ 2 a,
        natOpV2_sub m hops hnh hval hfsu ρ b 1,
        ih (b - 1) (by omega) (2 * a)]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

/-- `Nat.shiftRight` on literal values. -/
theorem natOpV2_shiftRight (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natShiftRightName
      = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natShiftRightName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.shiftRight a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Lech.natShiftRightName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Lech.natSubName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Lech.natDivName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_shiftRight m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 b
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV2_sub m hops hnh hval hfsu ρ b 1,
        ih (b - 1) (by omega) a,
        natOpV2_div hops hnh hval hdm hfdi ρ (Nat.shiftRight a (b - 1)) 2]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

/-- `Nat.land` on literal values. -/
theorem natOpV2_land (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natLandName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natLandName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.land a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Lech.natLandName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Lech.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Lech.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Lech.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Lech.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_land m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.land 0 b = 0 from PinGen.landBaseCert 0 b rfl]
      exact rfl
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV2_div hops hnh hval hdm hfdi ρ a 2,
        natOpV2_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV2_mul m hops hnh hval hfmu ρ 2 (Nat.land (a / 2) (b / 2)),
        natOpV2_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV2_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV2_mul m hops hnh hval hfmu ρ (a % 2) (b % 2),
        natOpV2_add m hops hnh hval hfad ρ
          (2 * Nat.land (a / 2) (b / 2)) _,
        show Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + _ from
          PinGen.landRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

/-- `Nat.lor` on literal values. -/
theorem natOpV2_lor (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natLorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natLorName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.lor a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Lech.natLorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Lech.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Lech.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Lech.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Lech.natModName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps Lech.natSubName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_lor m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.lor 0 b = b from PinGen.lorBaseCert 0 b rfl]
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV2_div hops hnh hval hdm hfdi ρ a 2,
        natOpV2_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV2_mul m hops hnh hval hfmu ρ 2 (Nat.lor (a / 2) (b / 2)),
        natOpV2_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV2_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV2_add m hops hnh hval hfad ρ (a % 2) (b % 2),
        natOpV2_mul m hops hnh hval hfmu ρ (a % 2) (b % 2),
        natOpV2_sub m hops hnh hval hfsu ρ (a % 2 + b % 2)
          (a % 2 * (b % 2)),
        natOpV2_add m hops hnh hval hfad ρ
          (2 * Nat.lor (a / 2) (b / 2)) _,
        show Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + _ from
          PinGen.lorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

/-- `Nat.xor` on literal values. -/
theorem natOpV2_xor (hops : NatOpsP m φ) (hnh : NatHeadsP m φ)
    (hval : AcvalValidP m) (hdm : DivModP m φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? Lech.natXorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat,
      SetTheory.app (SetTheory.app
          (interp2 V ρ (m.acval Lech.natXorName φ))
          (interp2 V ρ (natLitP m φ a)))
        (interp2 V ρ (natLitP m φ b))
      = interp2 V ρ (natLitP m φ (Nat.xor a b)) := by
  obtain ⟨hg, hclauses⟩ :=
    hdm Lech.natXorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := Lech.natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps Lech.natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps Lech.natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps Lech.natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps Lech.natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps Lech.natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ := divModClausesP_xor m ρ
      (hclauses ρ _ _ (natLitP_mem m hnh hval hs ρ a)
        (natLitP_mem m hnh hval hs ρ b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 0
      rw [if_neg (by omega)] at h1
      rw [hbase h1, show Nat.xor 0 b = b from PinGen.xorBaseCert 0 b rfl]
    · have h1 := natOpV2_ble m hops hnh hval hfbl ρ 1 a
      rw [if_pos (by omega)] at h1
      rw [hrec h1, natOpV2_div hops hnh hval hdm hfdi ρ a 2,
        natOpV2_div hops hnh hval hdm hfdi ρ b 2,
        ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2),
        natOpV2_mul m hops hnh hval hfmu ρ 2 (Nat.xor (a / 2) (b / 2)),
        natOpV2_mod hops hnh hval hdm hfmo ρ a 2,
        natOpV2_mod hops hnh hval hdm hfmo ρ b 2,
        natOpV2_add m hops hnh hval hfad ρ (a % 2) (b % 2),
        natOpV2_mod hops hnh hval hdm hfmo ρ (a % 2 + b % 2) 2,
        natOpV2_add m hops hnh hval hfad ρ
          (2 * Nat.xor (a / 2) (b / 2)) _,
        show Nat.xor a b = 2 * Nat.xor (a / 2) (b / 2) + _ from
          PinGen.xorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

end Lech.SetP
