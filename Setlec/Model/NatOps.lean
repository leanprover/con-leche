import Setlec.Model.NatLit
import Setlec.Verify.InferLeaves
import Setlec.PinGen.Certs

/-!
# The structural-Nat operations in the model

The kernel's literal fast path (`reduceNat`) computes the seven
structural-Nat operations on literals; `NatOpsOk` (a field of
`EnvModel`) records that every stored operation satisfies its
recurrence equations semantically.  This module provides

* inversions of the fast-path guard (`natOpGuard_inv`) and its
  transport along fresh extension (`natOpGuard_cons`),
* the interpretation computations turning the interp-level recurrence
  equations into value-level ones (`natOpRec_*`),
* the meta-level inductions computing each operation on `natLitVal`
  values (`natLit_add`, …), assembled per operation (`natOpVal_*`) —
  `reduceNat`'s soundness consumes these,
* the head-substitution transport (`interp_substConst0`) and the
  `NatOpsOk` extension step (`NatOpsOk.cons`) the model-extension
  lemmas consume.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-! ## Small interpretation computations -/

/-- The interpretation of a stored level-monomorphic constant. -/
theorem interp_const_mono {cval : ConstVal V} {c : Name}
    {ci : ConstantInfo} (hf : env.find? c = some ci)
    (hlp : ci.toConstantVal.levelParams = []) {d : Nat} {ρ : Nat → V} :
    interpExpr V cval env φ d ρ (.const c []) = some (cval c φ) := by
  simp [interpExpr, hf, hlp, Level.substFn_nil]

/-- The interpretation of a one-argument application spine. -/
theorem interp_app1 {cval : ConstVal V} {d : Nat} {ρ : Nat → V}
    {f a : Expr} {vf va : V}
    (hif : interpExpr V cval env φ d ρ f = some vf)
    (hia : interpExpr V cval env φ d ρ a = some va) :
    interpExpr V cval env φ d ρ (.app f a) = some (app vf va) := by
  rw [interpExpr, hif, hia]

/-- The interpretation of an `fvar` leaf. -/
theorem interp_fvar {cval : ConstVal V} {d idx : Nat} {ρ : Nat → V}
    {n : Name} {ty : Expr} :
    interpExpr V cval env φ d ρ (.fvar idx n ty) = some (ρ idx) := by
  simp [interpExpr]

/-- The equations' canonical valuation, read at its two slots. -/
theorem updV01_0 {x y : V} : updV V (updV V (rho0 V) 0 x) 1 y 0 = x := by
  simp [updV]

theorem updV01_1 {x y : V} : updV V (updV V (rho0 V) 0 x) 1 y 1 = y := by
  simp [updV]

/-! ## Meta-level literal inductions

Pure value-level: given the recurrences of an operation value over an
abstract "`Nat` set" `N` with zero/successor values, compute the
operation on iterated-successor values. -/

section LitInduction

variable {N zv sv : V}

/-- Iterated-successor values inhabit `N`. -/
theorem natLitVal_mem_gen (hz : zv ∈ˢ N) (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N) :
    ∀ n, natLitVal V zv sv n ∈ˢ N
  | 0 => hz
  | n + 1 => hs _ (natLitVal_mem_gen hz hs n)

theorem natLit_pred {fv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (h0 : app fv zv = zv)
    (hS : ∀ x, x ∈ˢ N → app fv (app sv x) = x) :
    ∀ a, app fv (natLitVal V zv sv a) = natLitVal V zv sv (a - 1)
  | 0 => h0
  | a + 1 => by
    have h := hS _ (natLitVal_mem_gen hz hs a)
    simpa [natLitVal] using h

theorem natLit_add {fv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (h0 : ∀ x, x ∈ˢ N → app (app fv x) zv = x)
    (hS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv x) (app sv y) = app sv (app (app fv x) y)) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a + b)
  | a, 0 => h0 _ (natLitVal_mem_gen hz hs a)
  | a, b + 1 => by
    show app (app fv (natLitVal V zv sv a)) (app sv (natLitVal V zv sv b)) =
      app sv (natLitVal V zv sv (a + b))
    rw [hS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_add hz hs h0 hS a b]

theorem natLit_sub {fv pv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (hpred : ∀ a, app pv (natLitVal V zv sv a) = natLitVal V zv sv (a - 1))
    (h0 : ∀ x, x ∈ˢ N → app (app fv x) zv = x)
    (hS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv x) (app sv y) = app pv (app (app fv x) y)) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a - b)
  | a, 0 => h0 _ (natLitVal_mem_gen hz hs a)
  | a, b + 1 => by
    show app (app fv (natLitVal V zv sv a)) (app sv (natLitVal V zv sv b)) =
      natLitVal V zv sv (a - (b + 1))
    rw [hS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_sub hz hs hpred h0 hS a b, hpred]
    congr 1 <;> omega

theorem natLit_mul {fv av : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (hadd : ∀ a b, app (app av (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a + b))
    (h0 : ∀ x, x ∈ˢ N → app (app fv x) zv = zv)
    (hS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv x) (app sv y) = app (app av (app (app fv x) y)) x) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a * b)
  | a, 0 => h0 _ (natLitVal_mem_gen hz hs a)
  | a, b + 1 => by
    show app (app fv (natLitVal V zv sv a)) (app sv (natLitVal V zv sv b)) =
      natLitVal V zv sv (a * (b + 1))
    rw [hS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_mul hz hs hadd h0 hS a b, hadd]
    congr 1 <;> omega

theorem natLit_pow {fv mv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (hmul : ∀ a b, app (app mv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a * b))
    (h0 : ∀ x, x ∈ˢ N → app (app fv x) zv = app sv zv)
    (hS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv x) (app sv y) = app (app mv (app (app fv x) y)) x) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      natLitVal V zv sv (a ^ b)
  | a, 0 => h0 _ (natLitVal_mem_gen hz hs a)
  | a, b + 1 => by
    show app (app fv (natLitVal V zv sv a)) (app sv (natLitVal V zv sv b)) =
      natLitVal V zv sv (a ^ (b + 1))
    rw [hS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_pow hz hs hmul h0 hS a b, hmul]
    congr 1 <;> simp [Nat.pow_succ]

theorem natLit_beq {fv tv flv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (h00 : app (app fv zv) zv = tv)
    (h0S : ∀ y, y ∈ˢ N → app (app fv zv) (app sv y) = flv)
    (hS0 : ∀ x, x ∈ˢ N → app (app fv (app sv x)) zv = flv)
    (hSS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv (app sv x)) (app sv y) = app (app fv x) y) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      if a = b then tv else flv
  | 0, 0 => by rw [if_pos rfl]; exact h00
  | 0, b + 1 => by
    show app (app fv zv) (app sv (natLitVal V zv sv b)) = _
    rw [h0S _ (natLitVal_mem_gen hz hs b), if_neg (by omega)]
  | a + 1, 0 => by
    show app (app fv (app sv (natLitVal V zv sv a))) zv = _
    rw [hS0 _ (natLitVal_mem_gen hz hs a), if_neg (by omega)]
  | a + 1, b + 1 => by
    show app (app fv (app sv (natLitVal V zv sv a)))
      (app sv (natLitVal V zv sv b)) = _
    rw [hSS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_beq hz hs h00 h0S hS0 hSS a b]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (by omega)]
    · rw [if_neg hab, if_neg (by omega)]

theorem natLit_ble {fv tv flv : V} (hz : zv ∈ˢ N)
    (hs : ∀ x, x ∈ˢ N → app sv x ∈ˢ N)
    (h0 : ∀ y, y ∈ˢ N → app (app fv zv) y = tv)
    (hS0 : ∀ x, x ∈ˢ N → app (app fv (app sv x)) zv = flv)
    (hSS : ∀ x y, x ∈ˢ N → y ∈ˢ N →
      app (app fv (app sv x)) (app sv y) = app (app fv x) y) :
    ∀ a b, app (app fv (natLitVal V zv sv a)) (natLitVal V zv sv b) =
      if a ≤ b then tv else flv
  | 0, b => by
    show app (app fv zv) (natLitVal V zv sv b) = _
    rw [h0 _ (natLitVal_mem_gen hz hs b), if_pos (by omega)]
  | a + 1, 0 => by
    show app (app fv (app sv (natLitVal V zv sv a))) zv = _
    rw [hS0 _ (natLitVal_mem_gen hz hs a), if_neg (by omega)]
  | a + 1, b + 1 => by
    show app (app fv (app sv (natLitVal V zv sv a)))
      (app sv (natLitVal V zv sv b)) = _
    rw [hSS _ _ (natLitVal_mem_gen hz hs a) (natLitVal_mem_gen hz hs b),
      natLit_ble hz hs h0 hS0 hSS a b]
    by_cases hab : a ≤ b
    · rw [if_pos hab, if_pos (by omega)]
    · rw [if_neg hab, if_neg (by omega)]

end LitInduction

/-! ## The stored operations on literal values

Extraction of the value-level recurrences from `EnvModel.nat_ops`
(computing the equations' interpretations) plus the meta-level
inductions, per operation.  The zero/successor membership facts come
from the `Nat` pins alone (`Setlec/Model/NatLit.lean`). -/

section OpValues

variable (m : EnvModel V env)

/-- The membership premise of the recurrence equations, discharged. -/
private theorem memPrem (hs : natLitSupported env = true)
    {ψ : Name → Nat} {x y : V}
    (hx : x ∈ˢ m.val natName ψ) (hy : y ∈ˢ m.val natName ψ) :
    ∀ T, interpExpr V m.val env ψ 2 (rho0 V) (.const natName []) = some T →
      x ∈ˢ T ∧ y ∈ˢ T := by
  intro T hT
  rw [interpExpr_const_nat hs] at hT
  injection hT with hT
  subst hT
  exact ⟨hx, hy⟩

private theorem succ_closed (hs : natLitSupported env = true) (ψ : Name → Nat) :
    ∀ x, x ∈ˢ m.val natName ψ →
      app (m.val natSuccName ψ) x ∈ˢ m.val natName ψ := fun _ hx =>
  app_mem (natSuccVal_mem_pi m hs ψ) hx (fun _ _ => natVal_mem_univ m hs ψ)

/-- `Nat.pred` on literal values. -/
theorem natOpVal_pred {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natPredName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a : Nat, app (m.val natPredName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a - 1) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natPredName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natPredName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : app (m.val natPredName ψ) (m.val natZeroName ψ) =
      m.val natZeroName ψ := by
    have h := heqs (.app (.const natPredName []) (.const natZeroName []),
        .const natZeroName []) (by decide) ψ
      (m.val natZeroName ψ) (m.val natZeroName ψ)
      (memPrem m hs (natZeroVal_mem m hs ψ) (natZeroVal_mem m hs ψ))
    rw [interp_app1 (interp_const_mono hf hlp) (interpExpr_const_natZero hs),
      interpExpr_const_natZero hs] at h
    exact Option.some.inj h
  have hS : ∀ x, x ∈ˢ m.val natName ψ →
      app (m.val natPredName ψ) (app (m.val natSuccName ψ) x) = x := by
    intro x hx
    have h := heqs (.app (.const natPredName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))),
        .fvar 0 (.str .anonymous "x") (.const natName [])) (by decide) ψ x x
      (memPrem m hs hx hx)
    rw [interp_app1 (interp_const_mono hf hlp)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_fvar] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  exact natLit_pred (natZeroVal_mem m hs ψ) (succ_closed m hs ψ) h0 hS

/-- `Nat.add` on literal values. -/
theorem natOpVal_add {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natAddName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natAddName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a + b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natAddName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natAddName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natAddName ψ) x) (m.val natZeroName ψ) = x := by
    intro x hx
    have h := heqs (.app (.app (.const natAddName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.const natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const natName [])) (by decide) ψ x x
      (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interpExpr_const_natZero hs),
      interp_fvar] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natAddName ψ) x) (app (m.val natSuccName ψ) y) =
        app (m.val natSuccName ψ) (app (app (m.val natAddName ψ) x) y) := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natAddName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.const natSuccName [])
          (.app (.app (.const natAddName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interpExpr_const_natSucc hs)
        (interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
          interp_fvar)] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_add (natZeroVal_mem m hs ψ) (succ_closed m hs ψ) h0 hS

/-- `Nat.sub` on literal values. -/
theorem natOpVal_sub {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natSubName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natSubName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a - b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natSubName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvp, vp, hnt1, hfp, hlpp⟩ := hdeps natPredName (by decide)
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natSubName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natSubName ψ) x) (m.val natZeroName ψ) = x := by
    intro x hx
    have h := heqs (.app (.app (.const natSubName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.const natZeroName []),
        .fvar 0 (.str .anonymous "x") (.const natName [])) (by decide) ψ x x
      (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interpExpr_const_natZero hs),
      interp_fvar] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natSubName ψ) x) (app (m.val natSuccName ψ) y) =
        app (m.val natPredName ψ) (app (app (m.val natSubName ψ) x) y) := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natSubName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.const natPredName [])
          (.app (.app (.const natSubName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interp_const_mono hfp hlpp)
        (interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
          interp_fvar)] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_sub (natZeroVal_mem m hs ψ) (succ_closed m hs ψ)
    (natOpVal_pred m hfp ψ) h0 hS

/-- `Nat.mul` on literal values. -/
theorem natOpVal_mul {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natMulName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natMulName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a * b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natMulName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cva, va, hnt2, hfa, hlpa⟩ := hdeps natAddName (by decide)
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natMulName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natMulName ψ) x) (m.val natZeroName ψ) =
        m.val natZeroName ψ := by
    intro x hx
    have h := heqs (.app (.app (.const natMulName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.const natZeroName []),
        .const natZeroName []) (by decide) ψ x x (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interpExpr_const_natZero hs),
      interpExpr_const_natZero hs] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natMulName ψ) x) (app (m.val natSuccName ψ) y) =
        app (app (m.val natAddName ψ)
          (app (app (m.val natMulName ψ) x) y)) x := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natMulName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natAddName [])
          (.app (.app (.const natMulName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interp_app1 (interp_const_mono hfa hlpa)
        (interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
          interp_fvar)) interp_fvar] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_mul (natZeroVal_mem m hs ψ) (succ_closed m hs ψ)
    (natOpVal_add m hfa ψ) h0 hS

/-- `Nat.pow` on literal values. -/
theorem natOpVal_pow {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natPowName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natPowName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a ^ b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natPowName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvm, vm, hnt3, hfm, hlpm⟩ := hdeps natMulName (by decide)
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natPowName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natPowName ψ) x) (m.val natZeroName ψ) =
        app (m.val natSuccName ψ) (m.val natZeroName ψ) := by
    intro x hx
    have h := heqs (.app (.app (.const natPowName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.const natZeroName []),
        .app (.const natSuccName []) (.const natZeroName []))
      (by decide) ψ x x (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interpExpr_const_natZero hs),
      interp_app1 (interpExpr_const_natSucc hs)
        (interpExpr_const_natZero hs)] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natPowName ψ) x) (app (m.val natSuccName ψ) y) =
        app (app (m.val natMulName ψ)
          (app (app (m.val natPowName ψ) x) y)) x := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natPowName [])
        (.fvar 0 (.str .anonymous "x") (.const natName [])))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natMulName [])
          (.app (.app (.const natPowName [])
            (.fvar 0 (.str .anonymous "x") (.const natName [])))
            (.fvar 1 (.str .anonymous "y") (.const natName []))))
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interp_app1 (interp_const_mono hfm hlpm)
        (interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
          interp_fvar)) interp_fvar] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_pow (natZeroVal_mem m hs ψ) (succ_closed m hs ψ)
    (natOpVal_mul m hfm ψ) h0 hS

/-- `Nat.beq` on literal values. -/
theorem natOpVal_beq {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBeqName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natBeqName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      if a = b then m.val boolTrueName ψ else m.val boolFalseName ψ := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natBeqName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool (Or.inl rfl)
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natBeqName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h00 : app (app (m.val natBeqName ψ) (m.val natZeroName ψ))
      (m.val natZeroName ψ) = m.val boolTrueName ψ := by
    have h := heqs (.app (.app (.const natBeqName []) (.const natZeroName []))
        (.const natZeroName []), .const boolTrueName []) (by decide) ψ
      (m.val natZeroName ψ) (m.val natZeroName ψ)
      (memPrem m hs (natZeroVal_mem m hs ψ) (natZeroVal_mem m hs ψ))
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interpExpr_const_natZero hs)) (interpExpr_const_natZero hs),
      interp_const_mono hT hlpT] at h
    exact Option.some.inj h
  have h0S : ∀ y, y ∈ˢ m.val natName ψ →
      app (app (m.val natBeqName ψ) (m.val natZeroName ψ))
        (app (m.val natSuccName ψ) y) = m.val boolFalseName ψ := by
    intro y hy
    have h := heqs (.app (.app (.const natBeqName []) (.const natZeroName []))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .const boolFalseName []) (by decide) ψ y y (memPrem m hs hy hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interpExpr_const_natZero hs))
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_const_mono hF hlpF] at h
    simp only [updV01_1] at h
    exact Option.some.inj h
  have hS0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natBeqName ψ) (app (m.val natSuccName ψ) x))
        (m.val natZeroName ψ) = m.val boolFalseName ψ := by
    intro x hx
    have h := heqs (.app (.app (.const natBeqName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.const natZeroName []), .const boolFalseName [])
      (by decide) ψ x x (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar))
        (interpExpr_const_natZero hs),
      interp_const_mono hF hlpF] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hSS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natBeqName ψ) (app (m.val natSuccName ψ) x))
        (app (m.val natSuccName ψ) y) =
        app (app (m.val natBeqName ψ) x) y := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natBeqName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natBeqName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName [])))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar))
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        interp_fvar] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_beq (natZeroVal_mem m hs ψ) (succ_closed m hs ψ)
    h00 h0S hS0 hSS

/-- `Nat.ble` on literal values. -/
theorem natOpVal_ble {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natBleName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natBleName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      if a ≤ b then m.val boolTrueName ψ else m.val boolFalseName ψ := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natBleName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool (Or.inr (Or.inl rfl))
  obtain ⟨cv', v', hnt', hf', hlp⟩ := hdeps natBleName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := hf'
  have h0 : ∀ y, y ∈ˢ m.val natName ψ →
      app (app (m.val natBleName ψ) (m.val natZeroName ψ)) y =
        m.val boolTrueName ψ := by
    intro y hy
    have h := heqs (.app (.app (.const natBleName []) (.const natZeroName []))
        (.fvar 1 (.str .anonymous "y") (.const natName [])),
        .const boolTrueName []) (by decide) ψ y y (memPrem m hs hy hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interpExpr_const_natZero hs)) interp_fvar,
      interp_const_mono hT hlpT] at h
    simp only [updV01_1] at h
    exact Option.some.inj h
  have hS0 : ∀ x, x ∈ˢ m.val natName ψ →
      app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) x))
        (m.val natZeroName ψ) = m.val boolFalseName ψ := by
    intro x hx
    have h := heqs (.app (.app (.const natBleName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.const natZeroName []), .const boolFalseName [])
      (by decide) ψ x x (memPrem m hs hx hx)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar))
        (interpExpr_const_natZero hs),
      interp_const_mono hF hlpF] at h
    simp only [updV01_0] at h
    exact Option.some.inj h
  have hSS : ∀ x y, x ∈ˢ m.val natName ψ → y ∈ˢ m.val natName ψ →
      app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) x))
        (app (m.val natSuccName ψ) y) =
        app (app (m.val natBleName ψ) x) y := by
    intro x y hx hy
    have h := heqs (.app (.app (.const natBleName [])
        (.app (.const natSuccName [])
          (.fvar 0 (.str .anonymous "x") (.const natName []))))
        (.app (.const natSuccName [])
          (.fvar 1 (.str .anonymous "y") (.const natName []))),
        .app (.app (.const natBleName [])
          (.fvar 0 (.str .anonymous "x") (.const natName [])))
          (.fvar 1 (.str .anonymous "y") (.const natName [])))
      (by decide) ψ x y (memPrem m hs hx hy)
    rw [interp_app1 (interp_app1 (interp_const_mono hf hlp)
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar))
        (interp_app1 (interpExpr_const_natSucc hs) interp_fvar),
      interp_app1 (interp_app1 (interp_const_mono hf hlp) interp_fvar)
        interp_fvar] at h
    simp only [updV01_0, updV01_1] at h
    exact Option.some.inj h
  exact natLit_ble (natZeroVal_mem m hs ψ) (succ_closed m hs ψ) h0 hS0 hSS

end OpValues

/-! ## Transport of the invariant along environment extension -/

/-- Each operation is among its own dependencies. -/
theorem natOpDeps_self {c : Name} (hc : c ∈ natOpNames) : c ∈ natOpDeps c := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The guard stores the operation itself as a level-monomorphic
definition. -/
theorem natOpGuard_self_defn {c : Name} (hc : c ∈ natOpNames)
    (hg : natOpGuard env c = true) :
    ∃ cv v h, env.find? c = some (.defnInfo cv v h) ∧ cv.levelParams = [] :=
  (natOpGuard_inv hg).2.1 c (natOpDeps_self hc)

/-- Same for the pin-certified WF-recursive operations. -/
theorem natDivModGuard_self_defn {c : Name} (hc : c ∈ natDivModNames)
    (hg : natOpGuard env c = true) :
    ∃ cv v h, env.find? c = some (.defnInfo cv v h) ∧ cv.levelParams = [] := by
  refine (natOpGuard_inv hg).2.1 c ?_
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The equation sides are application spines over constants and free
variables. -/
def Expr.natEqShape : Expr → Bool
  | .const _ _ => true
  | .fvar _ _ _ => true
  | .app f a => f.natEqShape && a.natEqShape
  | _ => false

theorem natOpEquations_shape {c : Name} (hc : c ∈ natOpNames) :
    ∀ eq ∈ natOpEquations 0 c,
      Expr.natEqShape eq.1 = true ∧ Expr.natEqShape eq.2 = true := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every constant of an equation side resolves in an environment
satisfying the guard (with the operation stored). -/
theorem natOpEquations_constsResolve {c : Name} (hc : c ∈ natOpNames)
    (hg : natOpGuard env c = true) :
    ∀ eq ∈ natOpEquations 0 c,
      eq.1.constsResolve env = true ∧ eq.2.constsResolve env = true := by
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, -⟩ :=
    natLitSupported_inv hs
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨cvc, vc, hnt4, hfc, -⟩ := hdeps natPredName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc]
  · obtain ⟨cvc, vc, hnt5, hfc, -⟩ := hdeps natAddName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc]
  · obtain ⟨cvp, vp, hnt6, hfp, -⟩ := hdeps natPredName (by decide)
    obtain ⟨cvc, vc, hnt7, hfc, -⟩ := hdeps natSubName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfp]
  · obtain ⟨cva, va, hnt8, hfa, -⟩ := hdeps natAddName (by decide)
    obtain ⟨cvc, vc, hnt9, hfc, -⟩ := hdeps natMulName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfa]
  · obtain ⟨cvm, vm, hnt10, hfm, -⟩ := hdeps natMulName (by decide)
    obtain ⟨cvc, vc, hnt11, hfc, -⟩ := hdeps natPowName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfm]
  · obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hbool (Or.inl rfl)
    obtain ⟨cvc, vc, hnt12, hfc, -⟩ := hdeps natBeqName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hT, hF]
  · obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hbool (Or.inr (Or.inl rfl))
    obtain ⟨cvc, vc, hnt13, hfc, -⟩ := hdeps natBleName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hT, hF]

/-! ## Install-side derivation helpers

The `defnDecl` install case turns the kernel's certification run into
the semantic equations.  These lemmas read the pinned type shapes off
`natOpTyPinned`/`natOpStoredOk` and provide the side conditions
(`EqSideOk`) that feed definitional-equality soundness. -/

section Install

private theorem find?_ciname {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- The interpretation of a `∀`-type with a known domain
interpretation. -/
theorem interp_forallE {cval : ConstVal V} {d : Nat} {ρ : Nat → V}
    {nm : Name} {ty body : Expr} {mb : BinderMeta} {A : V}
    (hty : interpExpr V cval env φ d ρ ty = some A) :
    interpExpr V cval env φ d ρ (.forallE nm ty body mb) =
      some (piC A fun x =>
        (interpExpr V cval env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d nm ty))).getD SetTheory.empty) := by
  simp only [interpExpr, hty]

/-- The pinned codomain's interpretation: a set in `univ 1`, the `Nat`
value for the arithmetic operations. -/
theorem natOpCod_interp (m : EnvModel V env) {c : Name} {e : Expr}
    (h : natOpCod env c e = true) (hs : natLitSupported env = true)
    (ψ : Name → Nat) :
    ∃ bn C, e = .const bn [] ∧
      (∀ (d : Nat) (ρ : Nat → V),
        interpExpr V m.val env ψ d ρ e = some C) ∧ C ∈ˢ univ 1 ∧
      (c ≠ natBeqName → c ≠ natBleName → C = m.val natName ψ) ∧
      ((c = natBeqName ∨ c = natBleName) → C = m.val boolName ψ) := by
  unfold natOpCod at h
  split at h
  · next hcb =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hbool⟩ := h
    revert hbool
    split
    · next ci heq =>
      intro hbool
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hbool
      obtain ⟨hlp, hbty⟩ := hbool
      refine ⟨boolName, m.val boolName ψ, rfl,
        fun d ρ => interp_const_mono heq hlp, ?_, ?_, fun _ => rfl⟩
      · obtain ⟨T, hT, hmem⟩ := m.mem_type _ (find?_mem heq) ψ
        rw [find?_ciname heq] at hmem
        rw [hbty] at hT
        simp only [interpClosed, interpExpr, Option.some.injEq] at hT
        subst hT
        simpa [Level.eval] using hmem
      · intro h1 h2
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hcb
        rcases hcb with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h2
    · intro hbool; exact nomatch hbool
  · next hncb =>
    simp only [beq_iff_eq] at h
    subst h
    refine ⟨natName, m.val natName ψ, rfl,
      fun d ρ => interpExpr_const_nat hs, natVal_mem_univ m hs ψ,
      fun _ _ => rfl, fun hcb => ?_⟩
    exfalso
    apply hncb
    rcases hcb with rfl | rfl <;> simp

/-- The pinned type's interpretation: the function space over the
`Nat` value with the pinned codomain. -/
theorem natOpTyPinned_interp (m : EnvModel V env) {c : Name} {ty : Expr}
    (hty : natOpTyPinned env c ty = true) (hs : natLitSupported env = true)
    (ψ : Name → Nat) :
    (c = natPredName ∨ c = natLog2Name →
      interpClosed V m.val env ψ ty =
        some (pi 1 (m.val natName ψ) (fun _ => m.val natName ψ))) ∧
    (¬(c = natPredName ∨ c = natLog2Name) → ∃ C,
      interpClosed V m.val env ψ ty =
        some (pi 1 (m.val natName ψ)
          (fun _ => pi 1 (m.val natName ψ) (fun _ => C))) ∧
      C ∈ˢ univ 1 ∧
      (c ≠ natBeqName → c ≠ natBleName → C = m.val natName ψ) ∧
      ((c = natBeqName ∨ c = natBleName) → C = m.val boolName ψ)) := by
  unfold natOpTyPinned at hty
  by_cases hcp : c = natPredName ∨ c = natLog2Name
  · rw [if_pos (by rcases hcp with rfl | rfl <;> simp)] at hty
    refine ⟨fun _ => ?_, fun hne => absurd hcp hne⟩
    revert hty
    match ty with
    | .forallE nm dom body mb => ?_
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
      intro hty; exact nomatch hty
    intro hty
    simp only [Bool.and_eq_true, beq_iff_eq] at hty
    obtain ⟨rfl, hcod⟩ := hty
    have hbody : body = .const natName [] := by
      unfold natOpCod at hcod
      rw [if_neg (by rcases hcp with rfl | rfl <;> decide)] at hcod
      simpa using hcod
    subst hbody
    unfold interpClosed
    rw [interp_forallE (interpExpr_const_nat hs)]
    congr 2
    funext x
    simp [Expr.instantiate1, interpExpr_const_nat hs]
  · rw [if_neg (by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact fun h => hcp (h.imp id id))] at hty
    refine ⟨fun heq => absurd heq hcp, fun _ => ?_⟩
    revert hty
    match ty with
    | .forallE nm dom (.forallE nm2 dom2 body mb2) mb => ?_
    | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
    | .lam _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _
    | .forallE _ _ (.bvar _) _ | .forallE _ _ (.fvar _ _ _) _
    | .forallE _ _ (.sort _) _ | .forallE _ _ (.const _ _) _
    | .forallE _ _ (.app _ _) _ | .forallE _ _ (.lam _ _ _ _) _
    | .forallE _ _ (.letE _ _ _ _) _ | .forallE _ _ (.lit _) _
    | .forallE _ _ (.proj _ _ _) _ =>
      intro hty; exact nomatch hty
    intro hty
    simp only [Bool.and_eq_true, beq_iff_eq] at hty
    obtain ⟨⟨rfl, rfl⟩, hcod⟩ := hty
    obtain ⟨bn, C, rfl, hCi, hCu, hCid, hCbool⟩ := natOpCod_interp m hcod hs ψ
    refine ⟨C, ?_, hCu, hCid, hCbool⟩
    unfold interpClosed
    rw [interp_forallE (interpExpr_const_nat hs)]
    congr 2
    funext x
    simp only [Expr.instantiate1]
    rw [interp_forallE (interpExpr_const_nat hs)]
    simp only [Option.getD_some]
    congr 1
    funext x2
    simp [Expr.instantiate1, hCi]

/-- The pinned-type check only reads the `Bool` slot. -/
theorem natOpTyPinned_congr {env₁ env₂ : Env} {c : Name} {ty : Expr}
    (h : env₁.find? boolName = env₂.find? boolName) :
    natOpTyPinned env₁ c ty = natOpTyPinned env₂ c ty := by
  have hcod : ∀ e, natOpCod env₁ c e = natOpCod env₂ c e := by
    intro e
    unfold natOpCod
    rw [h]
  unfold natOpTyPinned
  split
  · split <;> simp [hcod]
  · split <;> simp [hcod]

/-- A stored-pinned fact transported below a fresh extension. -/
theorem natOpStoredOk_cons_down {c₀ : ConstantInfo} {n : Name}
    (hne : n ≠ c₀.name) (hneb : c₀.name ≠ boolName)
    (h : natOpStoredOk (⟨c₀ :: env.consts⟩ : Env) n = true) :
    natOpStoredOk env n = true := by
  have hb : (⟨c₀ :: env.consts⟩ : Env).find? boolName =
      env.find? boolName := by
    rw [Env.find?_cons, if_neg hneb]
  unfold natOpStoredOk at h ⊢
  rw [Env.find?_cons, if_neg (fun hh => hne hh.symm)] at h
  revert h
  split
  · next cvn vn heq =>
    intro h
    rw [natOpTyPinned_congr hb] at h
    exact h
  · intro h; exact nomatch h

/-- Everything a stored-pinned operation contributes: the definition
slot, level monomorphy, and the value's function-space membership. -/
theorem natOpStored_facts (m : EnvModel V env) {n : Name}
    (hst : natOpStoredOk env n = true) (hs : natLitSupported env = true)
    (ψ : Name → Nat) :
    ∃ cvn vn hn, env.find? n = some (.defnInfo cvn vn hn) ∧
      cvn.levelParams = [] ∧
      (n = natPredName ∨ n = natLog2Name →
        m.val n ψ ∈ˢ pi 1 (m.val natName ψ)
        (fun _ => m.val natName ψ)) ∧
      (¬(n = natPredName ∨ n = natLog2Name) →
        ∃ C, m.val n ψ ∈ˢ pi 1 (m.val natName ψ)
        (fun _ => pi 1 (m.val natName ψ) (fun _ => C)) ∧ C ∈ˢ univ 1 ∧
        (n ≠ natBeqName → n ≠ natBleName → C = m.val natName ψ) ∧
        ((n = natBeqName ∨ n = natBleName) → C = m.val boolName ψ)) := by
  unfold natOpStoredOk at hst
  revert hst
  split
  · next cvn vn hn heq =>
    intro hst
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hst
    obtain ⟨hlp, hty⟩ := hst
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ (find?_mem heq) ψ
    rw [find?_ciname heq] at hmem
    obtain ⟨h1, h2⟩ := natOpTyPinned_interp m hty hs ψ
    refine ⟨cvn, vn, hn, heq, hlp, ?_, ?_⟩
    · intro hp
      rw [show (ConstantInfo.defnInfo cvn vn hn).toConstantVal.type = cvn.type
        from rfl, h1 hp] at hT
      obtain rfl := Option.some.inj hT
      exact hmem
    · intro hp
      obtain ⟨C, hCi, hCu, hCid, hCb⟩ := h2 hp
      rw [show (ConstantInfo.defnInfo cvn vn hn).toConstantVal.type = cvn.type
        from rfl, hCi] at hT
      obtain rfl := Option.some.inj hT
      exact ⟨C, hmem, hCu, hCid, hCb⟩
  · intro hst; exact nomatch hst

/-- Everything a certification-equation side must satisfy to feed
definitional-equality soundness, bundled: interpretation, membership,
truthful annotations, and the syntactic invariants — at binder depth
`dd` (the structural-Nat equations use `2`, the div/mod certificate
frame `4`). -/
def EqSideOk (env : Env) (cval : ConstVal V) (ψ : Name → Nat) (dd : Nat)
    (ρ : Nat → V) (e : Expr) (v T : V) : Prop :=
  interpExpr V cval env ψ dd ρ e = some v ∧ v ∈ˢ T ∧
  AnnotOk V cval env ψ dd ρ e ∧ FvarsOk V cval env ψ dd ρ e ∧
  WScoped dd e ∧ e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e

section EqSides

variable (m : EnvModel V env) (hs : natLitSupported env = true)
  {ψ : Name → Nat} {dd : Nat} {ρ : Nat → V}

include hs

/-- `Nat.zero` as an equation side. -/
theorem eqSide_zero : EqSideOk env m.val ψ dd ρ (.const natZeroName [])
    (m.val natZeroName ψ) (m.val natName ψ) :=
  ⟨interpExpr_const_natZero hs, natZeroVal_mem m hs ψ, by simp [AnnotOk],
    fun l hl => by simp [Expr.fvarLeaves] at hl, by simp [WScoped], rfl,
    fun l hl => by simp [Expr.fvarLeaves] at hl⟩

/-- An `fvar` slot valued in the `Nat` value. -/
theorem eqSide_fvar {idx : Nat} {nm : Name} (hidx : idx < dd)
    (hval : ρ idx ∈ˢ m.val natName ψ) :
    EqSideOk env m.val ψ dd ρ (.fvar idx nm (.const natName []))
      (ρ idx) (m.val natName ψ) := by
  refine ⟨interp_fvar, hval, by simp [AnnotOk], ?_, ?_, rfl, ?_⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact ⟨hidx, by simp [AnnotOk],
        m.val natName ψ, interpExpr_const_nat hs, hval⟩
    · simp [Expr.fvarLeaves] at hl
  · simp only [WScoped]
    exact ⟨hidx, by simp [WScoped]⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl
    · rfl
    · simp [Expr.fvarLeaves] at hl

/-- `Nat.succ` applied to a `Nat`-valued side. -/
theorem eqSide_succ {a : Expr} {va : V}
    (ha : EqSideOk env m.val ψ dd ρ a va (m.val natName ψ)) :
    EqSideOk env m.val ψ dd ρ (.app (.const natSuccName []) a)
      (app (m.val natSuccName ψ) va) (m.val natName ψ) := by
  obtain ⟨hai, ham, haA, haF, haW, haB, haL⟩ := ha
  refine ⟨interp_app1 (interpExpr_const_natSucc hs) hai,
    succ_closed m hs ψ va ham, ?_, ?_, ?_,
    by simp [Expr.looseBVarsBounded, haB], ?_⟩
  · simp only [AnnotOk]
    exact ⟨by simp [AnnotOk], haA, m.val natSuccName ψ, va,
      m.val natName ψ, fun _ => m.val natName ψ,
      interpExpr_const_natSucc hs, hai, natSuccVal_mem_pi m hs ψ, ham⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.nil_append] at hl
    exact haF l hl
  · simp only [WScoped]
    exact ⟨by simp [WScoped], haW⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.nil_append] at hl
    exact haL l hl

/-- A binary head (the head's own facts supplied) applied to two
`Nat`-valued sides; the result lands in the head's codomain. -/
theorem eqSide_app2 {H a b : Expr} {hv va vb C : V}
    (hHi : interpExpr V m.val env ψ dd ρ H = some hv)
    (hHA : AnnotOk V m.val env ψ dd ρ H)
    (hHF : FvarsOk V m.val env ψ dd ρ H)
    (hHW : WScoped dd H) (hHB : H.looseBVarsBounded 0 = true)
    (hHL : Expr.LeavesBounded H)
    (hHm : hv ∈ˢ pi 1 (m.val natName ψ)
      (fun _ => pi 1 (m.val natName ψ) (fun _ => C)))
    (hCu : C ∈ˢ univ 1)
    (ha : EqSideOk env m.val ψ dd ρ a va (m.val natName ψ))
    (hb : EqSideOk env m.val ψ dd ρ b vb (m.val natName ψ)) :
    EqSideOk env m.val ψ dd ρ (.app (.app H a) b) (app (app hv va) vb) C := by
  obtain ⟨hai, ham, haA, haF, haW, haB, haL⟩ := ha
  obtain ⟨hbi, hbm, hbA, hbF, hbW, hbB, hbL⟩ := hb
  have hfib1 : ∀ x, x ∈ˢ m.val natName ψ →
      pi 1 (m.val natName ψ) (fun _ => C) ∈ˢ univ 1 := by
    intro x hx
    have := pi_mem_univ (natVal_mem_univ m hs ψ) (fun _ _ => hCu)
    simpa using this
  have h1m : app hv va ∈ˢ pi 1 (m.val natName ψ) (fun _ => C) :=
    app_mem hHm ham hfib1
  refine ⟨interp_app1 (interp_app1 hHi hai) hbi,
    app_mem h1m hbm (fun _ _ => hCu), ?_, ?_, ?_,
    by simp [Expr.looseBVarsBounded, hHB, haB, hbB], ?_⟩
  · simp only [AnnotOk]
    refine ⟨?_, hbA, app hv va, vb, m.val natName ψ, fun _ => C,
      interp_app1 hHi hai, hbi, h1m, hbm⟩
    exact ⟨hHA, haA, hv, va, m.val natName ψ,
      fun _ => pi 1 (m.val natName ψ) (fun _ => C), hHi, hai, hHm, ham⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hHF l hl
    · exact haF l hl
    · exact hbF l hl
  · simp only [WScoped]
    exact ⟨⟨hHW, haW⟩, hbW⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hHL l hl
    · exact haL l hl
    · exact hbL l hl

/-- A stored level-monomorphic constant as a binary head. -/
theorem eqSide_app2c {n : Name} {ci : ConstantInfo} {a b : Expr}
    {va vb C : V}
    (hf : env.find? n = some ci) (hlp : ci.toConstantVal.levelParams = [])
    (hm : m.val n ψ ∈ˢ pi 1 (m.val natName ψ)
      (fun _ => pi 1 (m.val natName ψ) (fun _ => C)))
    (hCu : C ∈ˢ univ 1)
    (ha : EqSideOk env m.val ψ dd ρ a va (m.val natName ψ))
    (hb : EqSideOk env m.val ψ dd ρ b vb (m.val natName ψ)) :
    EqSideOk env m.val ψ dd ρ (.app (.app (.const n []) a) b)
      (app (app (m.val n ψ) va) vb) C :=
  eqSide_app2 m hs (interp_const_mono hf hlp) (by simp [AnnotOk])
    (fun l hl => by simp [Expr.fvarLeaves] at hl) (by simp [WScoped]) rfl
    (fun l hl => by simp [Expr.fvarLeaves] at hl) hm hCu ha hb

omit hs

/-- A unary head applied to one `Nat`-valued side. -/
theorem eqSide_app1 {H a : Expr} {hv va C : V}
    (hHi : interpExpr V m.val env ψ dd ρ H = some hv)
    (hHA : AnnotOk V m.val env ψ dd ρ H)
    (hHF : FvarsOk V m.val env ψ dd ρ H)
    (hHW : WScoped dd H) (hHB : H.looseBVarsBounded 0 = true)
    (hHL : Expr.LeavesBounded H)
    (hHm : hv ∈ˢ pi 1 (m.val natName ψ) (fun _ => C))
    (hCu : C ∈ˢ univ 1)
    (ha : EqSideOk env m.val ψ dd ρ a va (m.val natName ψ)) :
    EqSideOk env m.val ψ dd ρ (.app H a) (app hv va) C := by
  obtain ⟨hai, ham, haA, haF, haW, haB, haL⟩ := ha
  refine ⟨interp_app1 hHi hai,
    app_mem hHm ham (fun _ _ => hCu), ?_, ?_, ?_,
    by simp [Expr.looseBVarsBounded, hHB, haB], ?_⟩
  · simp only [AnnotOk]
    exact ⟨hHA, haA, hv, va, m.val natName ψ, fun _ => C, hHi, hai,
      hHm, ham⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hHF l hl
    · exact haF l hl
  · simp only [WScoped]
    exact ⟨hHW, haW⟩
  · intro l hl
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hHL l hl
    · exact haL l hl

/-- A stored level-monomorphic constant as a unary head. -/
theorem eqSide_app1c {n : Name} {ci : ConstantInfo} {a : Expr} {va C : V}
    (hf : env.find? n = some ci) (hlp : ci.toConstantVal.levelParams = [])
    (hm : m.val n ψ ∈ˢ pi 1 (m.val natName ψ) (fun _ => C))
    (hCu : C ∈ˢ univ 1)
    (ha : EqSideOk env m.val ψ dd ρ a va (m.val natName ψ)) :
    EqSideOk env m.val ψ dd ρ (.app (.const n []) a)
      (app (m.val n ψ) va) C :=
  eqSide_app1 m (interp_const_mono hf hlp) (by simp [AnnotOk])
    (fun l hl => by simp [Expr.fvarLeaves] at hl) (by simp [WScoped]) rfl
    (fun l hl => by simp [Expr.fvarLeaves] at hl) hm hCu ha

end EqSides

end Install

/-- Operation names are distinct from the `Nat`/`Bool` pins. -/
theorem natOpNames_ne_pins {c : Name} (hc : c ∈ natOpNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧
    c ≠ boolName ∧ c ≠ boolTrueName ∧ c ≠ boolFalseName := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The invariant ignores a stored recursor's rule list (the operations
are stored definitions, and neither the guard nor the interpretation
reads a recursor's rules). -/
theorem NatOpsOk.cons_recRules {cvA : ConstantVal} {mI rP : Nat}
    {rules₁ rules₂ : List RecRule} {val : ConstVal V}
    (h : NatOpsOk V ⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ val) :
    NatOpsOk V ⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ val := by
  have henv : ∀ n,
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₂).name = n
    · rw [if_pos hn,
        if_pos (show (ConstantInfo.recInfo cvA mI rP rules₁).name = n
          from hn)]
      rfl
    · rw [if_neg hn,
        if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₁).name = n
          from hn)]
  have hfind : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2 h2, ci ≠ .defnInfo cv2 v2 h2) ∨
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₂).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₁).name = n
        from hn)]
      exact Or.inr hf
  have hfind' : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2 h2, ci ≠ .defnInfo cv2 v2 h2) ∨
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₁).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₂).name = n
        from hn)]
      exact Or.inr hf
  have hnat : natLitSupported
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) =
      natLitSupported (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) :=
    natLitSupported_cons_recRules
  have hstr : strLitSupported
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) =
      strLitSupported (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) :=
    strLitSupported_cons_recRules
  intro c hc cv v hv hf
  rcases hfind c _ hf with hnd | hf₁
  · exact absurd rfl (hnd cv v hv)
  obtain ⟨hg, heqs⟩ := h c hc cv v hv hf₁
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  refine ⟨natOpGuard_intro (by rw [hnat]; exact hs) ?_ ?_, ?_⟩
  · intro n hn
    obtain ⟨cvn, vn, hnt14, hfn, hlpn⟩ := hdeps n hn
    rcases hfind' n _ hfn with hnd | hfn₂
    · exact absurd rfl (hnd cvn vn hnt14)
    · exact ⟨cvn, vn, hnt14, hfn₂, hlpn⟩
  · intro hcb
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb
    have conv : ∀ (nb : Name) (ci : ConstantInfo),
        (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? nb =
          some ci → ci.toConstantVal.levelParams = [] →
        ∃ ci₂, (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find?
          nb = some ci₂ ∧ ci₂.toConstantVal.levelParams = [] := by
      intro nb ci hfb hlpb
      have h2 := henv nb
      rw [hfb] at h2
      cases hf2 : (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ :
          Env).find? nb with
      | none => rw [hf2] at h2; exact nomatch h2
      | some ci₂ =>
        rw [hf2] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        exact ⟨ci₂, rfl, by rw [h2, hlpb]⟩
    exact ⟨conv _ _ hT hlpT, conv _ _ hF hlpF⟩
  · intro eq heq ψ x y hxy
    have hie : ∀ (e : Expr) (dd : Nat) (ρ : Nat → V),
        interpExpr V val
          (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) ψ dd ρ e =
        interpExpr V val
          (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) ψ dd ρ e :=
      fun e dd ρ => interp_env_ext henv hnat hstr e dd ρ
    rw [hie eq.1 2 _, hie eq.2 2 _]
    refine heqs eq heq ψ x y ?_
    intro T hT
    refine hxy T ?_
    rw [hie]
    exact hT

/-- Interpreting an equation side over the extended environment equals
interpreting its self-substituted form over the base environment: the
new constant's value is the substituted expression's, all other
constants agree, and non-`app` structure is untouched. -/
theorem interp_substConst0 {c₀ : ConstantInfo} {val val' : ConstVal V}
    {value : Expr} {ψ : Name → Nat} {d : Nat} {ρ : Nat → V}
    (hfresh : env.find? c₀.name = none)
    (hlp : c₀.toConstantVal.levelParams = [])
    (hagree : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = val n ψ')
    (hhead : interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ d ρ
        (.const c₀.name []) = interpExpr V val env ψ d ρ value) :
    ∀ e : Expr, Expr.natEqShape e = true →
      interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ d ρ e =
        interpExpr V val env ψ d ρ (Expr.substConst0 c₀.name value e)
  | .const n us, _ => by
    by_cases hn : n = c₀.name ∧ us = []
    · obtain ⟨rfl, rfl⟩ := hn
      rw [Expr.substConst0, if_pos ⟨rfl, rfl⟩]
      exact hhead
    · rw [Expr.substConst0, if_neg hn]
      by_cases hne : n = c₀.name
      · subst hne
        have hus : us ≠ [] := fun h => hn ⟨rfl, h⟩
        have hlen : ¬ us.length = c₀.toConstantVal.levelParams.length := by
          rw [hlp]
          intro h
          exact hus (List.eq_nil_of_length_eq_zero h)
        have hf2 : (⟨c₀ :: env.consts⟩ : Env).find? c₀.name = some c₀ := by
          rw [Env.find?_cons, if_pos rfl]
        simp only [interpExpr, hf2, hfresh, if_neg hlen]
      · have hf2 : (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
          rw [Env.find?_cons, if_neg (fun h => hne (Eq.symm h))]
        simp only [interpExpr, hf2]
        cases hfn : env.find? n with
        | none => rfl
        | some ci =>
          dsimp only
          split
          · rw [hagree n hne]
          · rfl
  | .fvar idx n ty, _ => by
    show _ = interpExpr V val env ψ d ρ (.fvar idx n ty)
    simp [interpExpr]
  | .app f a, hshape => by
    simp only [Expr.natEqShape, Bool.and_eq_true] at hshape
    rw [Expr.substConst0]
    simp only [interpExpr]
    rw [interp_substConst0 hfresh hlp hagree hhead f hshape.1,
      interp_substConst0 hfresh hlp hagree hhead a hshape.2]

/-! ## The pin-certified WF-recursive operations (`Nat.div`/`Nat.mod`)

Value-level transports for `DivModOk` (the equations mention no
expressions, so only the guard and the lookup side move), plus the
meta-level strong inductions computing the stored operations on
literal values from the `ble`-guarded recurrences. -/

/-- The pin names are distinct from the `Nat`/`Bool` pins. -/
theorem natDivModNames_ne_pins {c : Name} (hc : c ∈ natDivModNames) :
    c ≠ natName ∧ c ≠ natZeroName ∧ c ≠ natSuccName ∧
    c ≠ boolName ∧ c ≠ boolTrueName ∧ c ≠ boolFalseName := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `DivModClauses` only reads the valuation at the `Nat`/`Bool` pins,
the operation's dependencies, and the operation itself (which is among
its own dependencies). -/
theorem DivModEqs.val_congr {val val' : ConstVal V} {c : Name}
    (hc : c ∈ natDivModNames)
    (h : DivModEqs V val c)
    (hN : ∀ ψ : Name → Nat, val' natName ψ = val natName ψ)
    (hS : ∀ ψ : Name → Nat, val' natSuccName ψ = val natSuccName ψ)
    (hZ : ∀ ψ : Name → Nat, val' natZeroName ψ = val natZeroName ψ)
    (hT : ∀ ψ : Name → Nat, val' boolTrueName ψ = val boolTrueName ψ)
    (hF : ∀ ψ : Name → Nat, val' boolFalseName ψ = val boolFalseName ψ)
    (hdep : ∀ n, n ∈ natOpDeps c → ∀ ψ' : Name → Nat,
      val' n ψ' = val n ψ') :
    DivModEqs V val' c := by
  intro ψ x y hx hy
  rw [hN] at hx hy
  have hcl := h ψ x y hx hy
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp +decide only [DivModClauses, hN, hS, hZ, hT, hF, hdep]
       at hcl ⊢
     exact hcl)

/-- Extend `ReduceOpsOk` by one fresh constant: the head's own
obligation is forwarded (nontrivial only for an `axiomInfo` under a
reduce-op name — the compiler-trust opaque install), and the stored
facts survive because a stored constant (and its stored element
inductive) is never the fresh head. -/
theorem ReduceOpsOk.cons {env : Env} {val val' : ConstVal V}
    {c₀ : ConstantInfo}
    (h : ReduceOpsOk V env val)
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = val n ψ')
    (hhead : ∀ cv₀, c₀ = .axiomInfo cv₀ → c₀.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv₀ (reduceOpCvA c₀.name) = true →
      ((⟨c₀ :: env.consts⟩ : Env).find? (reduceElemName c₀.name)).isSome
        = true ∧
      ∀ (ψ : Name → Nat) (x : V),
        x ∈ˢ val' (reduceElemName c₀.name) ψ →
        SetTheory.app (val' c₀.name ψ) x = x) :
    ReduceOpsOk V (⟨c₀ :: env.consts⟩ : Env) val' := by
  intro c hc cv hf hpin
  rw [Env.find?_cons] at hf
  by_cases hn : c₀.name = c
  · rw [if_pos hn] at hf
    subst hn
    exact hhead cv (Option.some.inj hf) hc hpin
  · rw [if_neg hn] at hf
    obtain ⟨hsome, hid⟩ := h c hc cv hf hpin
    have helemne : reduceElemName c ≠ c₀.name := by
      intro he
      rw [he, hfresh] at hsome
      exact nomatch hsome
    refine ⟨?_, ?_⟩
    · rw [Env.find?_cons]
      split
      · rfl
      · exact hsome
    · intro ψ x hx
      rw [hagree c (fun hcc => hn hcc.symm) ψ]
      exact hid ψ x (by rw [← hagree _ helemne ψ]; exact hx)

/-- `DivModOk` extension step: preservation for the stored operations
(every name the equations mention is stored, hence distinct from the
fresh head), plus a handler for the case that the new constant is
itself `Nat.div`/`Nat.mod`. -/
theorem DivModOk.cons {val val' : ConstVal V} {c₀ : ConstantInfo}
    (h : DivModOk V env val)
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = val n ψ')
    (hhead : ∀ cv₀ v₀ h₀, c₀ = .defnInfo cv₀ v₀ h₀ →
      c₀.name ∈ natDivModNames →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) c₀.name = true ∧
      DivModEqs V val' c₀.name) :
    DivModOk V (⟨c₀ :: env.consts⟩ : Env) val' := by
  intro c hc cv v hv hf
  rw [Env.find?_cons] at hf
  by_cases hn : c₀.name = c
  · rw [if_pos hn] at hf
    subst hn
    exact hhead cv v hv (Option.some.inj hf) hc
  · rw [if_neg hn] at hf
    obtain ⟨hg, heqs⟩ := h c hc cv v hv hf
    have hstoredne : ∀ n, (env.find? n).isSome = true → n ≠ c₀.name := by
      intro n hnf he
      rw [he, hfresh] at hnf
      exact nomatch hnf
    obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, -⟩ :=
      natLitSupported_inv hs
    obtain ⟨⟨ciT, hTf, -⟩, ⟨ciF, hFf, -⟩⟩ :=
      hbool (Or.inr (Or.inr hc))
    refine ⟨natOpGuard_cons hfresh hg, ?_⟩
    refine DivModEqs.val_congr hc heqs ?_ ?_ ?_ ?_ ?_ ?_
    · intro ψ'
      exact hagree _ (hstoredne _ (by simp [hnn])) ψ'
    · intro ψ'
      exact hagree _ (hstoredne _ (by simp [hss])) ψ'
    · intro ψ'
      exact hagree _ (hstoredne _ (by simp [hzz])) ψ'
    · intro ψ'
      exact hagree _ (hstoredne _ (by simp [hTf])) ψ'
    · intro ψ'
      exact hagree _ (hstoredne _ (by simp [hFf])) ψ'
    · intro n hmem ψ'
      obtain ⟨cvn, vn, hn2, hfn, -⟩ := hdeps n hmem
      exact hagree _ (hstoredne _ (by simp [hfn])) ψ'

/-- The `DivModOk` invariant ignores a stored recursor's rule list
(mirror of `NatOpsOk.cons_recRules`; the equations are value-level, so
only the guard and the lookup move). -/
theorem DivModOk.cons_recRules {cvA : ConstantVal} {mI rP : Nat}
    {rules₁ rules₂ : List RecRule} {val : ConstVal V}
    (h : DivModOk V ⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ val) :
    DivModOk V ⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ val := by
  have henv : ∀ n,
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₂).name = n
    · rw [if_pos hn,
        if_pos (show (ConstantInfo.recInfo cvA mI rP rules₁).name = n
          from hn)]
      rfl
    · rw [if_neg hn,
        if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₁).name = n
          from hn)]
  have hfind : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2 h2, ci ≠ .defnInfo cv2 v2 h2) ∨
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₂).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₁).name = n
        from hn)]
      exact Or.inr hf
  have hfind' : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2 h2, ci ≠ .defnInfo cv2 v2 h2) ∨
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA mI rP rules₁).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA mI rP rules₂).name = n
        from hn)]
      exact Or.inr hf
  have hnat : natLitSupported
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) =
      natLitSupported (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) :=
    natLitSupported_cons_recRules
  have hstr : strLitSupported
      (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) =
      strLitSupported (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) :=
    strLitSupported_cons_recRules
  intro c hc cv v hv hf
  rcases hfind c _ hf with hnd | hf₁
  · exact absurd rfl (hnd cv v hv)
  obtain ⟨hg, heqs⟩ := h c hc cv v hv hf₁
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  refine ⟨natOpGuard_intro (by rw [hnat]; exact hs) ?_ ?_, heqs⟩
  · intro n hn
    obtain ⟨cvn, vn, hnt15, hfn, hlpn⟩ := hdeps n hn
    rcases hfind' n _ hfn with hnd | hfn₂
    · exact absurd rfl (hnd cvn vn hnt15)
    · exact ⟨cvn, vn, hnt15, hfn₂, hlpn⟩
  · intro hcb
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb
    have conv : ∀ (nb : Name) (ci : ConstantInfo),
        (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? nb =
          some ci → ci.toConstantVal.levelParams = [] →
        ∃ ci₂, (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find?
          nb = some ci₂ ∧ ci₂.toConstantVal.levelParams = [] := by
      intro nb ci hfb hlpb
      have h2 := henv nb
      rw [hfb] at h2
      cases hf2 : (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ :
          Env).find? nb with
      | none => rw [hf2] at h2; exact nomatch h2
      | some ci₂ =>
        rw [hf2] at h2
        simp only [Option.map_some, Option.some.injEq] at h2
        exact ⟨ci₂, rfl, by rw [h2, hlpb]⟩
    exact ⟨conv _ _ hT hlpT, conv _ _ hF hlpF⟩

/-- `NatOpsOk` extension step: preservation for the stored operations
(the guard keeps every referenced constant away from the fresh name),
plus a handler for the case that the new constant is itself an
operation. -/
theorem NatOpsOk.cons {val val' : ConstVal V} {c₀ : ConstantInfo}
    (h : NatOpsOk V env val)
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = val n ψ')
    (hhead : ∀ cv₀ v₀ h₀, c₀ = .defnInfo cv₀ v₀ h₀ → c₀.name ∈ natOpNames →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2 (rho0 V)
          (.const natName []) = some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.1 =
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.2) :
    NatOpsOk V (⟨c₀ :: env.consts⟩ : Env) val' := by
  intro c hc cv v hv hf
  rw [Env.find?_cons] at hf
  by_cases hn : c₀.name = c
  · rw [if_pos hn] at hf
    subst hn
    exact hhead cv v hv (Option.some.inj hf) hc
  · rw [if_neg hn] at hf
    obtain ⟨hg, heqs⟩ := h c hc cv v hv hf
    have hagree' : ∀ n, (env.find? n).isSome = true →
        ∀ ψ' : Name → Nat, val' n ψ' = val n ψ' := by
      intro n hnf ψ'
      refine hagree n (fun he => ?_) ψ'
      rw [he, hfresh] at hnf
      exact nomatch hnf
    have hs := (natOpGuard_inv hg).1
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hnn, -⟩ :=
      natLitSupported_inv hs
    refine ⟨natOpGuard_cons hfresh hg, ?_⟩
    intro eq heq ψ x y hxy
    have htrans : ∀ (e : Expr), e.constsResolve env = true →
        ∀ (d : Nat) (ρ : Nat → V),
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ d ρ e =
          interpExpr V val env ψ d ρ e := by
      intro e hres d ρ
      rw [interp_mono hfresh e d ρ hres]
      exact interp_cval_ext hagree' e d ρ
    obtain ⟨hres1, hres2⟩ := natOpEquations_constsResolve hc hg eq heq
    have hprem : ∀ T, interpExpr V val env ψ 2 (rho0 V)
        (.const natName []) = some T → x ∈ˢ T ∧ y ∈ˢ T := by
      intro T hT
      refine hxy T ?_
      rw [htrans _ (by simp [Expr.constsResolve, hnn]) 2 (rho0 V)]
      exact hT
    rw [htrans _ hres1 2 _, htrans _ hres2 2 _]
    exact heqs eq heq ψ x y hprem

/-! ## `Nat.div`/`Nat.mod` on literal values

Meta-level strong induction: the `ble`-guarded value-level recurrences
(`EnvModel.div_mod`) at literal values, with the guards computed by
`natOpVal_ble` and the argument step by `natOpVal_sub`, determine the
stored operations to be the metatheory's own `Nat.div`/`Nat.mod`.
This is the uniqueness argument justifying the literal fast path. -/

section DivModValues

variable (m : EnvModel V env)

/-- The value of the literal `1` is the `succ` value on the `zero`
value (definitional unfold of `natLitVal`, packaged for rewriting). -/
private theorem natLitVal_one :
    natLitVal V (m.val natZeroName ψ₀) (m.val natSuccName ψ₀) 1 =
      SetTheory.app (m.val natSuccName ψ₀) (m.val natZeroName ψ₀) := rfl

/-- For `c` one of `Nat.div`/`Nat.mod`, the clause dispatch collapses
to the original three `ble`-guarded clauses. -/
private theorem DivModClauses.divmod {val : ConstVal V} {c : Name}
    {ψ : Name → Nat} {x y : V}
    (hc : c = natDivName ∨ c = natModName)
    (h : DivModClauses V val c ψ x y) :
    (app (app (val natBleName ψ) y) x = val boolTrueName ψ →
     app (app (val natBleName ψ)
       (app (val natSuccName ψ) (val natZeroName ψ))) y =
       val boolTrueName ψ →
     app (app (val c ψ) x) y =
       (if c = natDivName then
         app (val natSuccName ψ)
           (app (app (val c ψ) (app (app (val natSubName ψ) x) y)) y)
        else app (app (val c ψ) (app (app (val natSubName ψ) x) y)) y)) ∧
    (app (app (val natBleName ψ) y) x = val boolFalseName ψ →
     app (app (val c ψ) x) y =
       (if c = natDivName then val natZeroName ψ else x)) ∧
    (app (app (val natBleName ψ)
       (app (val natSuccName ψ) (val natZeroName ψ))) y =
       val boolFalseName ψ →
     app (app (val c ψ) x) y =
       (if c = natDivName then val natZeroName ψ else x)) := by
  rcases hc with rfl | rfl <;>
    simpa +decide only [DivModClauses, if_false, if_true,
      reduceCtorEq, decide_true, decide_false] using h

/-- The common induction: `natOpVal_div` and `natOpVal_mod` at once
(the two operations share their guards and their step argument). -/
private theorem natOpVal_divmod {c : Name}
    (hc : c = natDivName ∨ c = natModName)
    {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? c = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val c ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ)
        (if c = natDivName then a / b else a % b) := by
  have hcmem : c ∈ natDivModNames := by
    rcases hc with rfl | rfl <;> decide
  obtain ⟨hg, heqs⟩ := m.div_mod c hcmem cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  have hdepmem : natSubName ∈ natOpDeps c ∧ natBleName ∈ natOpDeps c := by
    rcases hc with rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨cvsu, vsu, hsu, hfsu, -⟩ := hdeps natSubName hdepmem.1
  obtain ⟨cvbl, vbl, hbl, hfbl, -⟩ := hdeps natBleName hdepmem.2
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    have hamem := natLitVal_mem_nat m hs ψ a
    have hbmem := natLitVal_mem_nat m hs ψ b
    obtain ⟨hrec, hgt, hzero⟩ :=
      DivModClauses.divmod hc (heqs ψ _ _ hamem hbmem)
    by_cases hb0 : b = 0
    · subst hb0
      -- `ble 1 0` is `false`: the second base clause fires
      have h1 : app (app (m.val natBleName ψ)
          (app (m.val natSuccName ψ) (m.val natZeroName ψ)))
          (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) 0) =
          m.val boolFalseName ψ := by
        have h := natOpVal_ble m hfbl ψ 1 0
        rw [natLitVal_one] at h
        rw [h, if_neg (by omega)]
      rw [hzero h1]
      rcases hc with rfl | rfl
      · rw [if_pos rfl, if_pos rfl, Nat.div_zero]
        rfl
      · rw [if_neg (by decide), if_neg (by decide), Nat.mod_zero]
    · by_cases hba : b ≤ a
      · -- both guards true: the recurrence clause fires, then induct
        have h1 : app (app (m.val natBleName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
            m.val boolTrueName ψ := by
          rw [natOpVal_ble m hfbl ψ b a, if_pos hba]
        have h2 : app (app (m.val natBleName ψ)
            (app (m.val natSuccName ψ) (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            m.val boolTrueName ψ := by
          have h := natOpVal_ble m hfbl ψ 1 b
          rw [natLitVal_one] at h
          rw [h, if_pos (by omega)]
        have hsub : app (app (m.val natSubName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a - b) :=
          natOpVal_sub m hfsu ψ a b
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
        have h1 : app (app (m.val natBleName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
            m.val boolFalseName ψ := by
          rw [natOpVal_ble m hfbl ψ b a, if_neg hba]
        rw [hgt h1]
        have hab : a < b := by omega
        by_cases hcd : c = natDivName
        · subst hcd
          rw [if_pos rfl, if_pos rfl, Nat.div_eq_of_lt hab]
          rfl
        · rw [if_neg hcd, if_neg hcd, Nat.mod_eq_of_lt hab]

/-- `Nat.div` on literal values. -/
theorem natOpVal_div {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natDivName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natDivName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a / b) := by
  intro a b
  have h := natOpVal_divmod m (by decide) hf ψ a b
  rwa [if_pos rfl] at h

/-- `Nat.mod` on literal values. -/
theorem natOpVal_mod {cv : ConstantVal} {v : Expr} {hint : ReducibilityHint}
    (hf : env.find? natModName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natModName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a % b) := by
  intro a b
  have h := natOpVal_divmod m (by decide) hf ψ a b
  rwa [if_neg (by decide)] at h


/-! ## The remaining pin-certified operations on literal values

Per operation, the clause dispatch is collapsed to its two `ble`-guarded
clauses and a meta-level strong induction computes the stored operation
on literals; the metatheory-side recurrences for the bit operations are
the pin generator's own certificate theorems
(`Setlec.PinGen.landRecCert` …), reused at the meta level. -/

private theorem natLitVal_two :
    natLitVal V (m.val natZeroName ψ₀) (m.val natSuccName ψ₀) 2 =
      SetTheory.app (m.val natSuccName ψ₀)
        (SetTheory.app (m.val natSuccName ψ₀) (m.val natZeroName ψ₀)) := rfl

private theorem clauses_collapse {val : ConstVal V} {c : Name}
    {ψ : Name → Nat} {x y : V} {P : Prop}
    (h : DivModClauses V val c ψ x y)
    (hP : DivModClauses V val c ψ x y = P) : P := hP ▸ h

end DivModValues

section WfOpValues

variable (m : EnvModel V env)

theorem natOpVal_gcd {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natGcdName = some (.defnInfo cv v hint)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natGcdName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ)
        (Nat.gcd a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natGcdName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvmo, vmo, himo, hfmo, -⟩ := hdeps natModName (by decide)
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
            m.val boolTrueName ψ →
          app (app (m.val natGcdName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          app (app (m.val natGcdName ψ)
            (app (app (m.val natModName ψ)
              (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
              (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) ∧
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
            m.val boolFalseName ψ →
          app (app (m.val natGcdName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1, Nat.gcd_zero_left]
    · have h1 := natOpVal_ble m hfbl ψ 1 a
      rw [natLitVal_one] at h1
      rw [hrec (by rw [h1, if_pos (by omega)]),
        natOpVal_mod m hfmo ψ b a,
        ih (b % a) (Nat.mod_lt _ (by omega)) a, Nat.gcd_rec a b]


theorem natOpVal_shiftLeft {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natShiftLeftName = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natShiftLeftName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ)
        (Nat.shiftLeft a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natShiftLeftName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps natSubName (by decide)
  obtain ⟨cvmu, vmu, himu, hfmu, -⟩ := hdeps natMulName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            m.val boolTrueName ψ →
          app (app (m.val natShiftLeftName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          app (app (m.val natShiftLeftName ψ)
            (app (app (m.val natMulName ψ)
              (app (m.val natSuccName ψ) (app (m.val natSuccName ψ)
                (m.val natZeroName ψ))))
              (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)))
            (app (app (m.val natSubName ψ)
              (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
              (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) ∧
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            m.val boolFalseName ψ →
          app (app (m.val natShiftLeftName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpVal_ble m hfbl ψ 1 b
      rw [natLitVal_one, if_pos (by omega)] at h1
      have hmu := natOpVal_mul m hfmu ψ 2 a
      rw [natLitVal_two] at hmu
      have hsu := natOpVal_sub m hfsu ψ b 1
      rw [natLitVal_one] at hsu
      rw [hrec h1, hmu, hsu, ih (b - 1) (by omega) (2 * a)]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl

theorem natOpVal_shiftRight {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natShiftRightName = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natShiftRightName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ)
        (Nat.shiftRight a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natShiftRightName (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvsu, vsu, hisu, hfsu, -⟩ := hdeps natSubName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            m.val boolTrueName ψ →
          app (app (m.val natShiftRightName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          app (app (m.val natDivName ψ)
            (app (app (m.val natShiftRightName ψ)
              (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
              (app (app (m.val natSubName ψ)
                (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b))
                (app (m.val natSuccName ψ) (m.val natZeroName ψ)))))
            (app (m.val natSuccName ψ) (app (m.val natSuccName ψ)
              (m.val natZeroName ψ)))) ∧
        (app (app (m.val natBleName ψ) (app (m.val natSuccName ψ)
            (m.val natZeroName ψ)))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
            m.val boolFalseName ψ →
          app (app (m.val natShiftRightName ψ)
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
            (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
          natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
    by_cases hb0 : b = 0
    · subst hb0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1]
      exact rfl
    · have h1 := natOpVal_ble m hfbl ψ 1 b
      rw [natLitVal_one, if_pos (by omega)] at h1
      have hsu := natOpVal_sub m hfsu ψ b 1
      rw [natLitVal_one] at hsu
      have hdi := natOpVal_div m hfdi ψ (Nat.shiftRight a (b - 1)) 2
      rw [natLitVal_two] at hdi
      rw [hrec h1, hsu, ih (b - 1) (by omega) a, hdi]
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rfl


theorem natOpVal_log2 {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLog2Name = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a : Nat, app (m.val natLog2Name ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (Nat.log2 a) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natLog2Name (by decide) cv v hint hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvbl, vbl, hibl, hfbl, -⟩ := hdeps natBleName (by decide)
  obtain ⟨cvdi, vdi, hidi, hfdi, -⟩ := hdeps natDivName (by decide)
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    obtain ⟨hrec, hbase⟩ :=
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ a) :
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) =
            m.val boolTrueName ψ →
          (app (m.val natLog2Name ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = (app (m.val natSuccName ψ) (app (m.val natLog2Name ψ) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))))) ∧
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) =
            m.val boolFalseName ψ →
          (app (m.val natLog2Name ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val natZeroName ψ))
    by_cases ha2 : 2 ≤ a
    · have h1 := natOpVal_ble m hfbl ψ 2 a
      rw [natLitVal_two, if_pos ha2] at h1
      have hdi := natOpVal_div m hfdi ψ a 2
      rw [natLitVal_two] at hdi
      rw [hrec h1, hdi, ih (a / 2) (Nat.div_lt_self (by omega) (by omega)),
        show Nat.log2 a = Nat.log2 (a / 2) + 1 from by
          rw [Nat.log2_def]; exact if_pos ha2]
      exact rfl
    · have h1 := natOpVal_ble m hfbl ψ 2 a
      rw [natLitVal_two, if_neg ha2] at h1
      rw [hbase h1, Nat.log2_def, if_neg ha2]
      exact rfl


theorem natOpVal_land {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLandName = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natLandName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (Nat.land a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natLandName (by decide) cv v hint hf
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
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolTrueName ψ →
          (app (app (m.val natLandName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = (app (app (m.val natAddName ψ) (app (app (m.val natMulName ψ) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) (app (app (m.val natLandName ψ) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))))) (app (app (m.val natMulName ψ) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))))) ∧
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolFalseName ψ →
          (app (app (m.val natLandName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = m.val natZeroName ψ))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.land 0 b = 0 from PinGen.landBaseCert 0 b rfl]
      exact rfl
    · have h1 := natOpVal_ble m hfbl ψ 1 a
      rw [natLitVal_one, if_pos (by omega)] at h1
      have hdia := natOpVal_div m hfdi ψ a 2
      have hdib := natOpVal_div m hfdi ψ b 2
      rw [natLitVal_two] at hdia hdib
      have hmoa := natOpVal_mod m hfmo ψ a 2
      have hmob := natOpVal_mod m hfmo ψ b 2
      rw [natLitVal_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpVal_mul m hfmu ψ 2 (Nat.land (a / 2) (b / 2))
      rw [natLitVal_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      rw [natOpVal_mul m hfmu ψ (a % 2) (b % 2)]
      rw [natOpVal_add m hfad ψ (2 * Nat.land (a / 2) (b / 2)) _,
        show Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + _ from
          PinGen.landRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

theorem natOpVal_lor {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natLorName = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natLorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (Nat.lor a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natLorName (by decide) cv v hint hf
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
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolTrueName ψ →
          (app (app (m.val natLorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = (app (app (m.val natAddName ψ) (app (app (m.val natMulName ψ) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) (app (app (m.val natLorName ψ) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))))) (app (app (m.val natSubName ψ) (app (app (m.val natAddName ψ) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))))) (app (app (m.val natMulName ψ) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))))))) ∧
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolFalseName ψ →
          (app (app (m.val natLorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.lor 0 b = b from PinGen.lorBaseCert 0 b rfl]
    · have h1 := natOpVal_ble m hfbl ψ 1 a
      rw [natLitVal_one, if_pos (by omega)] at h1
      have hdia := natOpVal_div m hfdi ψ a 2
      have hdib := natOpVal_div m hfdi ψ b 2
      rw [natLitVal_two] at hdia hdib
      have hmoa := natOpVal_mod m hfmo ψ a 2
      have hmob := natOpVal_mod m hfmo ψ b 2
      rw [natLitVal_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpVal_mul m hfmu ψ 2 (Nat.lor (a / 2) (b / 2))
      rw [natLitVal_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      rw [natOpVal_add m hfad ψ (a % 2) (b % 2),
        natOpVal_mul m hfmu ψ (a % 2) (b % 2),
        natOpVal_sub m hfsu ψ (a % 2 + b % 2) (a % 2 * (b % 2))]
      rw [natOpVal_add m hfad ψ (2 * Nat.lor (a / 2) (b / 2)) _,
        show Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + _ from
          PinGen.lorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

theorem natOpVal_xor {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint}
    (hf : env.find? natXorName = some (.defnInfo cv v hint))
    (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natXorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (Nat.xor a b) := by
  obtain ⟨hg, heqs⟩ := m.div_mod natXorName (by decide) cv v hint hf
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
      (by simpa +decide only [DivModClauses, if_false, if_true,
          reduceCtorEq, decide_true, decide_false] using
        heqs ψ _ _ (natLitVal_mem_nat m hs ψ a) (natLitVal_mem_nat m hs ψ b) :
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolTrueName ψ →
          (app (app (m.val natXorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = (app (app (m.val natAddName ψ) (app (app (m.val natMulName ψ) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))) (app (app (m.val natXorName ψ) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natDivName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))))) (app (app (m.val natModName ψ) (app (app (m.val natAddName ψ) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))))) (app (app (m.val natModName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))))) (app (m.val natSuccName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ)))))) ∧
        ((app (app (m.val natBleName ψ) (app (m.val natSuccName ψ) (m.val natZeroName ψ))) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) = m.val boolFalseName ψ →
          (app (app (m.val natXorName ψ) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a)) (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)) = (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b)))
    by_cases ha0 : a = 0
    · subst ha0
      have h1 := natOpVal_ble m hfbl ψ 1 0
      rw [natLitVal_one, if_neg (by omega)] at h1
      rw [hbase h1, show Nat.xor 0 b = b from PinGen.xorBaseCert 0 b rfl]
    · have h1 := natOpVal_ble m hfbl ψ 1 a
      rw [natLitVal_one, if_pos (by omega)] at h1
      have hdia := natOpVal_div m hfdi ψ a 2
      have hdib := natOpVal_div m hfdi ψ b 2
      rw [natLitVal_two] at hdia hdib
      have hmoa := natOpVal_mod m hfmo ψ a 2
      have hmob := natOpVal_mod m hfmo ψ b 2
      rw [natLitVal_two] at hmoa hmob
      have hih := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2)
      have hmu2 := natOpVal_mul m hfmu ψ 2 (Nat.xor (a / 2) (b / 2))
      rw [natLitVal_two] at hmu2
      rw [hrec h1, hdia, hdib, hih, hmu2, hmoa, hmob]
      have hbm := natOpVal_mod m hfmo ψ (a % 2 + b % 2) 2
      rw [natLitVal_two] at hbm
      rw [natOpVal_add m hfad ψ (a % 2) (b % 2), hbm]
      rw [natOpVal_add m hfad ψ (2 * Nat.xor (a / 2) (b / 2)) _,
        show Nat.xor a b = 2 * Nat.xor (a / 2) (b / 2) + _ from
          PinGen.xorRecCert a b
            (Nat.ble_eq_true_of_le (by omega : 1 ≤ a))]
      exact rfl

end WfOpValues


end Setlec
