import Setlec.SetR.Sound.NatOps
import Setlec.PinGen.Certs

/-!
# Soundness — the WF-recursive `Nat` operations' literal values
(task #148, T4, batch f2, part 2)

The `Model/NatOps.lean` WF-op section, transposed onto the
`interp`-values (`natOpV_div` … `natOpV_xor`): meta-level strong
inductions over the `ble`-guarded value clauses of `EnvSHyp.div_mod`,
with the guards computed by `natOpV_ble` and the steps by the
structural operations' facts; the bit-operation closed forms are the
pin generator's certificate theorems (`PinGen.*Cert`), exactly as in
the model.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

section Cases

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-- The literal `1`, unfolded (packaged for rewriting). -/
theorem natLitV_one (ρ : Nat → V) :
    interp V ρ (natLitV cval φ 1)
      = SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
          (interp V ρ (cval natZeroName (Level.substFn φ [] []))) := rfl

/-- The literal `2`, unfolded (packaged for rewriting). -/
theorem natLitV_two (ρ : Nat → V) :
    interp V ρ (natLitV cval φ 2)
      = SetTheory.app
          (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
          (SetTheory.app
            (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))) :=
  rfl


/-- The common induction: `natOpVal_div` and `natOpVal_mod` at once
(the two operations share their guards and their step argument). -/
theorem natOpV_divmod (henv : EnvSHyp V env cval φ) {c : Name}
    (hc : c = natDivName ∨ c = natModName)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval c (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (if c = natDivName then a / b else a % b)) := by
  have hcmem : c ∈ natDivModNames := by
    rcases hc with rfl | rfl <;> decide
  obtain ⟨hg, hclauses⟩ := henv.div_mod c hcmem cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  have hdepmem : natSubName ∈ natOpDeps c ∧ natBleName ∈ natOpDeps c := by
    rcases hc with rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨cvsu, vsu, hsu, hfsu, -⟩ := hdeps natSubName hdepmem.1
  obtain ⟨cvbl, vbl, hbl, hfbl, -⟩ := hdeps natBleName hdepmem.2
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have hamem := (natLit_facts henv hs ρ a).2
    have hbmem := (natLit_facts henv hs ρ b).2
    obtain ⟨hrec, hgt, hzero⟩ :=
      divModClausesV_divmod hc (hclauses ρ _ _ hamem hbmem)
    by_cases hb0 : b = 0
    · subst hb0
      -- `ble 1 0` is `false`: the second base clause fires
      have h1 : app (app (interp V ρ (cval natBleName (Level.substFn φ [] [])))
          (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
          (interp V ρ (natLitV cval φ 0)) =
          interp V ρ (cval boolFalseName (Level.substFn φ [] [])) := by
        have h := natOpV_ble henv hfbl ρ 1 0
        rw [natLitV_one] at h
        rw [h, if_neg (by omega)]
      rw [hzero h1]
      rcases hc with rfl | rfl
      · rw [if_pos rfl, if_pos rfl, Nat.div_zero]
        rfl
      · rw [if_neg (by decide), if_neg (by decide), Nat.mod_zero]
    · by_cases hba : b ≤ a
      · -- both guards true: the recurrence clause fires, then induct
        have h1 : app (app (interp V ρ (cval natBleName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ b)))
            (interp V ρ (natLitV cval φ a)) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) := by
          rw [natOpV_ble henv hfbl ρ b a, if_pos hba]
        have h2 : app (app (interp V ρ (cval natBleName (Level.substFn φ [] [])))
            (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) := by
          have h := natOpV_ble henv hfbl ρ 1 b
          rw [natLitV_one] at h
          rw [h, if_pos (by omega)]
        have hsub : app (app (interp V ρ (cval natSubName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (natLitV cval φ (a - b)) :=
          natOpV_sub henv hfsu ρ a b
        have hlt : a - b < a := Nat.sub_lt (by omega) (by omega)
        have hih := ih (a - b) hlt
        rw [hrec h1 h2, hsub, hih]
        by_cases hcd : c = natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, if_pos rfl]
          have : a / b = (a - b) / b + 1 := by
            rw [Nat.div_eq a b, if_pos ⟨by omega, hba⟩]
          rw [this]
          rfl
        · rw [if_neg hcd, if_neg hcd, if_neg hcd]
          have : a % b = (a - b) % b :=
            Nat.mod_eq_sub_mod hba
          rw [this]
      · -- `ble b a` is `false`: the first base clause fires
        have h1 : app (app (interp V ρ (cval natBleName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ b)))
            (interp V ρ (natLitV cval φ a)) =
            interp V ρ (cval boolFalseName (Level.substFn φ [] [])) := by
          rw [natOpV_ble henv hfbl ρ b a, if_neg hba]
        rw [hgt h1]
        have hab : a < b := by omega
        by_cases hcd : c = natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, Nat.div_eq_of_lt hab]
          rfl
        · rw [if_neg hcd, if_neg hcd, Nat.mod_eq_of_lt hab]

/-- `Nat.div` on literal values. -/
theorem natOpV_div (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natDivName = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natDivName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (a / b)) := by
  intro a b
  have h := natOpV_divmod henv (Or.inl rfl) hf ρ a b
  rwa [if_pos rfl] at h

/-- `Nat.mod` on literal values. -/
theorem natOpV_mod (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natModName = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natModName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (a % b)) := by
  intro a b
  have h := natOpV_divmod henv (Or.inr rfl) hf ρ a b
  rwa [if_neg (by decide)] at h


/-! ## The remaining pin-certified operations on literal values

Per operation, the clause dispatch is collapsed to its two `ble`-guarded
clauses and a meta-level strong induction computes the stored operation
on literals; the metatheory-side recurrences for the bit operations are
the pin generator's own certificate theorems
(`Setlec.PinGen.landRecCert` …), reused at the meta level. -/

theorem natOpV_gcd (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natGcdName = some (.defnInfo cv v hint)) (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natGcdName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.gcd a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natGcdName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ a)) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natGcdName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          app (app (interp V ρ (cval natGcdName (Level.substFn φ [] [])))
            (app (app (interp V ρ (cval natModName (Level.substFn φ [] [])))
              (interp V ρ (natLitV cval φ b)))
              (interp V ρ (natLitV cval φ a))))
            (interp V ρ (natLitV cval φ a))) ∧
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ a)) =
            interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natGcdName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          interp V ρ (natLitV cval φ b)))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1, Nat.gcd_zero_left]
    · have h1 := natOpV_ble henv hfbl ρ 1 a
      rw [natLitV_one] at h1
      rw [hrec (by rw [h1, if_pos (by omega)]),
        natOpV_mod henv hfmo ρ b a,
        ih (b % a) (Nat.mod_lt _ (by omega)) a, Nat.gcd_rec a b]


theorem natOpV_shiftLeft (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natShiftLeftName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natShiftLeftName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.shiftLeft a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natShiftLeftName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps natSubName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps natMulName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natShiftLeftName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          app (app (interp V ρ (cval natShiftLeftName (Level.substFn φ [] [])))
            (app (app (interp V ρ (cval natMulName (Level.substFn φ [] [])))
              (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
                (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))
              (interp V ρ (natLitV cval φ a))))
            (app (app (interp V ρ (cval natSubName (Level.substFn φ [] [])))
              (interp V ρ (natLitV cval φ b)))
              (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) ∧
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natShiftLeftName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          interp V ρ (natLitV cval φ a)))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV_ble henv hfbl ρ 1 b
      rw [natLitV_one, if_pos (by omega)] at h1
      have hmu := natOpV_mul henv hfmu ρ 2 a
      rw [natLitV_two] at hmu
      have hsu := natOpV_sub henv hfsu ρ b 1
      rw [natLitV_one] at hsu
      rw [hrec h1, hmu, hsu, ih (b - 1) (by omega) (2 * a)]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

theorem natOpV_shiftRight (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natShiftRightName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natShiftRightName (Level.substFn φ [] [])))
        (interp V ρ (natLitV cval φ a)))
        (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.shiftRight a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natShiftRightName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps natSubName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natShiftRightName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          app (app (interp V ρ (cval natDivName (Level.substFn φ [] [])))
            (app (app (interp V ρ (cval natShiftRightName (Level.substFn φ [] [])))
              (interp V ρ (natLitV cval φ a)))
              (app (app (interp V ρ (cval natSubName (Level.substFn φ [] [])))
                (interp V ρ (natLitV cval φ b)))
                (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))))
            (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
              (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) ∧
        (app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] [])))
            (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))
            (interp V ρ (natLitV cval φ b)) =
            interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          app (app (interp V ρ (cval natShiftRightName (Level.substFn φ [] [])))
            (interp V ρ (natLitV cval φ a)))
            (interp V ρ (natLitV cval φ b)) =
          interp V ρ (natLitV cval φ a)))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpV_ble henv hfbl ρ 1 b
      rw [natLitV_one, if_pos (by omega)] at h1
      have hsu := natOpV_sub henv hfsu ρ b 1
      rw [natLitV_one] at hsu
      have hdi := natOpV_div henv hfdi ρ (Nat.shiftRight a (b - 1)) 2
      rw [natLitV_two] at hdi
      rw [hrec h1, hsu, ih (b - 1) (by omega) a, hdi]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl


theorem natOpV_log2 (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLog2Name = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a : Nat, app (interp V ρ (cval natLog2Name (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a)) =
      interp V ρ (natLitV cval φ (Nat.log2 a)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natLog2Name (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ a).2) :
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) (interp V ρ (natLitV cval φ a))) =
            interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          (app (interp V ρ (cval natLog2Name (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) = (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natLog2Name (Level.substFn φ [] []))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))))) ∧
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) (interp V ρ (natLitV cval φ a))) =
            interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          (app (interp V ρ (cval natLog2Name (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval natZeroName (Level.substFn φ [] []))))
    by_cases ha2 : 2 ≤ a
    · have h1 := natOpV_ble henv hfbl ρ 2 a
      rw [natLitV_two, if_pos ha2] at h1
      have hdi := natOpV_div henv hfdi ρ a 2
      rw [natLitV_two] at hdi
      rw [hrec h1, hdi, ih (a / 2) (Nat.div_lt_self (by omega) (by omega)),
        show Nat.log2 a = Nat.log2 (a / 2) + 1 from by
          rw [Nat.log2_def]; exact if_pos ha2]
      exact rfl
    · have h1 := natOpV_ble henv hfbl ρ 2 a
      rw [natLitV_two, if_neg ha2] at h1
      rw [hbase h1, Nat.log2_def, if_neg ha2]
      exact rfl


theorem natOpV_land (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLandName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natLandName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.land a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natLandName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natLandName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = (app (app (interp V ρ (cval natAddName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natMulName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) (app (app (interp V ρ (cval natLandName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))))) (app (app (interp V ρ (cval natMulName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))))) ∧
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natLandName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = interp V ρ (cval natZeroName (Level.substFn φ [] []))))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.land 0 b = 0 from PinGen.landBaseCert 0 b rfl]
      exact rfl
    · have h1 := natOpV_ble henv hfbl ρ 1 a
      rw [natLitV_one, if_pos (by omega)] at h1
      have hdia := natOpV_div henv hfdi ρ a 2
      have hdib := natOpV_div henv hfdi ρ b 2
      rw [natLitV_two] at hdia hdib
      have hmoa := natOpV_mod henv hfmo ρ a 2
      have hmob := natOpV_mod henv hfmo ρ b 2
      rw [natLitV_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpV_mul henv hfmu ρ 2 (Nat.land (a / 2) (b / 2))
      rw [natLitV_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      rw [natOpV_mul henv hfmu ρ (a % 2) (b % 2)]
      rw [natOpV_add henv hfad ρ (2 * Nat.land (a / 2) (b / 2)) _,
        show Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + _ from
          PinGen.landRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

theorem natOpV_lor (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natLorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.lor a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natLorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps natModName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps natSubName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natLorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = (app (app (interp V ρ (cval natAddName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natMulName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) (app (app (interp V ρ (cval natLorName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))))) (app (app (interp V ρ (cval natSubName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natAddName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))))) (app (app (interp V ρ (cval natMulName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))))))) ∧
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natLorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = (interp V ρ (natLitV cval φ b))))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.lor 0 b = b from PinGen.lorBaseCert 0 b rfl]
    · have h1 := natOpV_ble henv hfbl ρ 1 a
      rw [natLitV_one, if_pos (by omega)] at h1
      have hdia := natOpV_div henv hfdi ρ a 2
      have hdib := natOpV_div henv hfdi ρ b 2
      rw [natLitV_two] at hdia hdib
      have hmoa := natOpV_mod henv hfmo ρ a 2
      have hmob := natOpV_mod henv hfmo ρ b 2
      rw [natLitV_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpV_mul henv hfmu ρ 2 (Nat.lor (a / 2) (b / 2))
      rw [natLitV_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      rw [natOpV_add henv hfad ρ (a % 2) (b % 2),
        natOpV_mul henv hfmu ρ (a % 2) (b % 2),
        natOpV_sub henv hfsu ρ (a % 2 + b % 2) (a % 2 * (b % 2))]
      rw [natOpV_add henv hfad ρ (2 * Nat.lor (a / 2) (b / 2)) _,
        show Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + _ from
          PinGen.lorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

theorem natOpV_xor (henv : EnvSHyp V env cval φ)
    {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natXorName = some (.defnInfo cv v hint))
    (ρ : Nat → V) :
    ∀ a b : Nat, app (app (interp V ρ (cval natXorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b)) =
      interp V ρ (natLitV cval φ (Nat.xor a b)) := by
  obtain ⟨hg, hclauses⟩ := henv.div_mod natXorName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvad, vad, hiad, hfad, -⟩ := hdeps natAddName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps natMulName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClausesV, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        hclauses ρ _ _ ((natLit_facts henv hs ρ a).2) ((natLit_facts henv hs ρ b).2) :
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolTrueName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natXorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = (app (app (interp V ρ (cval natAddName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natMulName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))) (app (app (interp V ρ (cval natXorName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natDivName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natAddName (Level.substFn φ [] []))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))))) (app (app (interp V ρ (cval natModName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ b))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] [])))))))) ∧
        ((app (app (interp V ρ (cval natBleName (Level.substFn φ [] []))) (app (interp V ρ (cval natSuccName (Level.substFn φ [] []))) (interp V ρ (cval natZeroName (Level.substFn φ [] []))))) (interp V ρ (natLitV cval φ a))) = interp V ρ (cval boolFalseName (Level.substFn φ [] [])) →
          (app (app (interp V ρ (cval natXorName (Level.substFn φ [] []))) (interp V ρ (natLitV cval φ a))) (interp V ρ (natLitV cval φ b))) = (interp V ρ (natLitV cval φ b))))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpV_ble henv hfbl ρ 1 0
      rw [natLitV_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.xor 0 b = b from PinGen.xorBaseCert 0 b rfl]
    · have h1 := natOpV_ble henv hfbl ρ 1 a
      rw [natLitV_one, if_pos (by omega)] at h1
      have hdia := natOpV_div henv hfdi ρ a 2
      have hdib := natOpV_div henv hfdi ρ b 2
      rw [natLitV_two] at hdia hdib
      have hmoa := natOpV_mod henv hfmo ρ a 2
      have hmob := natOpV_mod henv hfmo ρ b 2
      rw [natLitV_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpV_mul henv hfmu ρ 2 (Nat.xor (a / 2) (b / 2))
      rw [natLitV_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      have hbm := natOpV_mod henv hfmo ρ (a % 2 + b % 2) 2
      rw [natLitV_two] at hbm
      rw [natOpV_add henv hfad ρ (a % 2) (b % 2), hbm]
      rw [natOpV_add henv hfad ρ (2 * Nat.xor (a / 2) (b / 2)) _,
        show Nat.xor a b = 2 * Nat.xor (a / 2) (b / 2) + _ from
          PinGen.xorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl


/-! ### R9/R10: the certified `Nat`-operation reductions -/

/-- R9: unary certified ops (`pred`/`log2`). -/
theorem sndRedNatOp1 (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {va Vr : VExpr} {c : Name} {n : Nat} {r : Expr}
    (h1 : c = natPredName ∨ c = natLog2Name)
    (h2 : natOpGuard env c = true)
    (h3 : natOpResult c n 0 = some r)
    (h4 : denoteClosed cval env φ r = some Vr)
    (_ : VExpr.Closed Vr)
    (_ : Red μ env cval φ Δ va (natLitV cval φ n))
    (ih : RedS V Δ va (natLitV cval φ n)) :
    RedS V Δ (.app (cval c (Level.substFn φ [] [])) va) Vr := by
  intro ρ hΔ
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv h2
  rcases h1 with rfl | rfl
  · -- `Nat.pred`
    obtain rfl : r = .lit (.natVal (n - 1)) := by
      simpa +decide [natOpResult] using h3.symm
    rw [show denoteClosed cval env φ (.lit (.natVal (n - 1)))
        = denote cval env φ 0 (.lit (.natVal (n - 1))) from rfl,
      denote_natLit, if_pos hs] at h4
    obtain rfl : Vr = natLitV cval φ (n - 1) := (Option.some.inj h4).symm
    obtain ⟨cvp, vp, hpnt, hfp, -⟩ := hdeps natPredName (by decide)
    refine ⟨?_, fun _ => (natLit_facts henv hs ρ (n - 1)).1⟩
    rw [interp_app, (ih ρ hΔ).1]
    exact natOpV_pred henv hfp ρ n
  · -- `Nat.log2`
    obtain rfl : r = .lit (.natVal (Nat.log2 n)) := by
      simpa +decide [natOpResult] using h3.symm
    rw [show denoteClosed cval env φ (.lit (.natVal (Nat.log2 n)))
        = denote cval env φ 0 (.lit (.natVal (Nat.log2 n))) from rfl,
      denote_natLit, if_pos hs] at h4
    obtain rfl : Vr = natLitV cval φ (Nat.log2 n) :=
      (Option.some.inj h4).symm
    obtain ⟨cvp, vp, hpnt, hfp, -⟩ := hdeps natLog2Name (by decide)
    refine ⟨?_, fun _ => (natLit_facts henv hs ρ (Nat.log2 n)).1⟩
    rw [interp_app, (ih ρ hΔ).1]
    exact natOpV_log2 henv hfp ρ n

/-- R10: binary certified ops (the 14-name list). -/
theorem sndRedNatOp2 (henv : EnvSHyp V env cval φ)
    {Δ : List VExpr} {va vb Vr : VExpr} {c : Name} {n₁ n₂ : Nat}
    {r : Expr}
    (h1 : c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
      c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
      c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
      c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
      c = natShiftLeftName ∨ c = natShiftRightName)
    (h2 : natOpGuard env c = true)
    (h3 : natOpResult c n₁ n₂ = some r)
    (h4 : denoteClosed cval env φ r = some Vr)
    (_ : VExpr.Closed Vr)
    (_ : Red μ env cval φ Δ va (natLitV cval φ n₁))
    (_ : Red μ env cval φ Δ vb (natLitV cval φ n₂))
    (ih1 : RedS V Δ va (natLitV cval φ n₁))
    (ih2 : RedS V Δ vb (natLitV cval φ n₂)) :
    RedS V Δ
      (.app (.app (cval c (Level.substFn φ [] [])) va) vb) Vr := by
  intro ρ hΔ
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv h2
  -- the arithmetic cases share their closing move
  have close : ∀ k : Nat,
      r = .lit (.natVal k) →
      (SetTheory.app (SetTheory.app
          (interp V ρ (cval c (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ n₁)))
        (interp V ρ (natLitV cval φ n₂))
        = interp V ρ (natLitV cval φ k)) →
      interp V ρ (.app (.app (cval c (Level.substFn φ [] [])) va) vb)
          = interp V ρ Vr ∧
      (AnnotOkV V ρ (.app (.app (cval c (Level.substFn φ [] [])) va) vb)
        → AnnotOkV V ρ Vr) := by
    intro k hr hop
    subst hr
    rw [show denoteClosed cval env φ (.lit (.natVal k))
        = denote cval env φ 0 (.lit (.natVal k)) from rfl,
      denote_natLit, if_pos hs] at h4
    obtain rfl : Vr = natLitV cval φ k := (Option.some.inj h4).symm
    refine ⟨?_, fun _ => (natLit_facts henv hs ρ k).1⟩
    rw [interp_app, interp_app, (ih1 ρ hΔ).1, (ih2 ρ hΔ).1]
    exact hop
  -- the boolean cases share theirs
  have closeB : ∀ bn : Name,
      (c = natBeqName ∨ c = natBleName) →
      r = .const bn [] →
      (bn = boolTrueName ∨ bn = boolFalseName) →
      (SetTheory.app (SetTheory.app
          (interp V ρ (cval c (Level.substFn φ [] [])))
          (interp V ρ (natLitV cval φ n₁)))
        (interp V ρ (natLitV cval φ n₂))
        = interp V ρ (cval bn (Level.substFn φ [] []))) →
      interp V ρ (.app (.app (cval c (Level.substFn φ [] [])) va) vb)
          = interp V ρ Vr ∧
      (AnnotOkV V ρ (.app (.app (cval c (Level.substFn φ [] [])) va) vb)
        → AnnotOkV V ρ Vr) := by
    intro bn hcb hr hbn hop
    subst hr
    obtain ⟨⟨ciT, hfT, hlpT⟩, ⟨ciF, hfF, hlpF⟩⟩ := hbool
      (by rcases hcb with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl))
    have h4' : denote cval env φ 0 (.const bn [])
        = some (cval bn (Level.substFn φ [] [])) := by
      rcases hbn with rfl | rfl
      · exact denote_const_mono hfT hlpT 0
      · exact denote_const_mono hfF hlpF 0
    rw [show denoteClosed cval env φ (.const bn [])
        = denote cval env φ 0 (.const bn []) from rfl, h4'] at h4
    obtain rfl : Vr = cval bn (Level.substFn φ [] []) :=
      (Option.some.inj h4).symm
    refine ⟨?_, fun _ => henv.annot_okV _ _ ρ⟩
    rw [interp_app, interp_app, (ih1 ρ hΔ).1, (ih2 ρ hΔ).1]
    exact hop
  rcases h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natAddName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_add henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natSubName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_sub henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natMulName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_mul henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natPowName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_pow henv hfo ρ n₁ n₂)
  · -- `Nat.beq`
    obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natBeqName (by decide)
    refine closeB _ (Or.inl rfl)
      (by simpa +decide [natOpResult] using h3.symm)
      (by by_cases h : n₁ = n₂ <;> simp [h]) ?_
    exact natOpV_beq henv hfo ρ n₁ n₂
  · -- `Nat.ble`
    obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natBleName (by decide)
    refine closeB _ (Or.inr rfl)
      (by simpa +decide [natOpResult] using h3.symm)
      (by by_cases h : n₁ ≤ n₂ <;> simp [h]) ?_
    exact natOpV_ble henv hfo ρ n₁ n₂
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natDivName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_div henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natModName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_mod henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natGcdName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_gcd henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natLandName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_land henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natLorName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_lor henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natXorName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_xor henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natShiftLeftName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_shiftLeft henv hfo ρ n₁ n₂)
  · obtain ⟨cvo, vo, ho, hfo, -⟩ := hdeps natShiftRightName (by decide)
    exact close _ (by simpa +decide [natOpResult] using h3.symm)
      (natOpV_shiftRight henv hfo ρ n₁ n₂)

end Cases

end Setlec.SetR
