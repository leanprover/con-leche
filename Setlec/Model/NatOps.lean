import Setlec.Model.NatLit

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

/-! ## The guard, inverted -/

/-- Everything `natOpGuard` checked, as separate facts. -/
theorem natOpGuard_inv {c : Name} (h : natOpGuard env c = true) :
    natLitSupported env = true ∧
    (∀ n ∈ natOpDeps c, ∃ cvn vn,
      env.find? n = some (.defnInfo cvn vn) ∧ cvn.levelParams = []) ∧
    ((c = natBeqName ∨ c = natBleName) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = [])) := by
  unfold natOpGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hdeps⟩, hbool⟩ := h
  refine ⟨hs, ?_, ?_⟩
  · intro n hn
    have := List.all_eq_true.mp hdeps n hn
    revert this
    split
    · next cvn vn heq =>
      intro hlp
      exact ⟨cvn, vn, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
    · intro hh; exact nomatch hh
  · intro hc
    have hcb : (c = natBeqName || c = natBleName) = true := by
      rcases hc with rfl | rfl <;> simp
    rw [if_pos hcb] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    constructor
    · revert hT
      split
      · next ciT heq =>
        intro hlp
        exact ⟨ciT, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
      · intro hh; exact nomatch hh
    · revert hF
      split
      · next ciF heq =>
        intro hlp
        exact ⟨ciF, heq, List.isEmpty_iff.mp (by simpa using hlp)⟩
      · intro hh; exact nomatch hh

/-- Rebuild the guard from the separate facts. -/
theorem natOpGuard_intro {c : Name}
    (hs : natLitSupported env = true)
    (hdeps : ∀ n ∈ natOpDeps c, ∃ cvn vn,
      env.find? n = some (.defnInfo cvn vn) ∧ cvn.levelParams = [])
    (hbool : (c = natBeqName ∨ c = natBleName) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = [])) :
    natOpGuard env c = true := by
  unfold natOpGuard
  simp only [Bool.and_eq_true]
  refine ⟨⟨hs, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr ?_
    intro n hn
    obtain ⟨cvn, vn, heq, hlp⟩ := hdeps n hn
    rw [heq]
    simp [hlp]
  · split
    · next hcb =>
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hcb
      have hcb' : c = natBeqName ∨ c = natBleName := by
        rcases hcb with h | h
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb'
      rw [hT, hF]
      simp [hlpT, hlpF]
    · rfl

/-- The guard survives extension by a fresh constant. -/
theorem natOpGuard_cons {c : Name} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (h : natOpGuard env c = true) :
    natOpGuard (⟨c₀ :: env.consts⟩ : Env) c = true := by
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv h
  obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, -⟩ :=
    natLitSupported_inv hs
  refine natOpGuard_intro ?_ ?_ ?_
  · rw [natLitSupported_congr
      (Env.find?_cons_of_isSome hfresh (by simp [hnn]))
      (Env.find?_cons_of_isSome hfresh (by simp [hzz]))
      (Env.find?_cons_of_isSome hfresh (by simp [hss]))]
    exact hs
  · intro n hn
    obtain ⟨cvn, vn, heq, hlp⟩ := hdeps n hn
    exact ⟨cvn, vn,
      (Env.find?_cons_of_isSome hfresh (by simp [heq])).trans heq, hlp⟩
  · intro hc
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hc
    exact ⟨⟨ciT, (Env.find?_cons_of_isSome hfresh (by simp [hT])).trans hT,
        hlpT⟩,
      ⟨ciF, (Env.find?_cons_of_isSome hfresh (by simp [hF])).trans hF,
        hlpF⟩⟩

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
theorem natOpVal_pred {cv : ConstantVal} {v : Expr}
    (hf : env.find? natPredName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a : Nat, app (m.val natPredName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a - 1) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natPredName (by decide) cv v hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natPredName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_add {cv : ConstantVal} {v : Expr}
    (hf : env.find? natAddName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natAddName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a + b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natAddName (by decide) cv v hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natAddName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_sub {cv : ConstantVal} {v : Expr}
    (hf : env.find? natSubName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natSubName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a - b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natSubName (by decide) cv v hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvp, vp, hfp, hlpp⟩ := hdeps natPredName (by decide)
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natSubName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_mul {cv : ConstantVal} {v : Expr}
    (hf : env.find? natMulName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natMulName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a * b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natMulName (by decide) cv v hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cva, va, hfa, hlpa⟩ := hdeps natAddName (by decide)
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natMulName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_pow {cv : ConstantVal} {v : Expr}
    (hf : env.find? natPowName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natPowName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) (a ^ b) := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natPowName (by decide) cv v hf
  obtain ⟨hs, hdeps, -⟩ := natOpGuard_inv hg
  obtain ⟨cvm, vm, hfm, hlpm⟩ := hdeps natMulName (by decide)
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natPowName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_beq {cv : ConstantVal} {v : Expr}
    (hf : env.find? natBeqName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natBeqName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      if a = b then m.val boolTrueName ψ else m.val boolFalseName ψ := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natBeqName (by decide) cv v hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool (Or.inl rfl)
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natBeqName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
theorem natOpVal_ble {cv : ConstantVal} {v : Expr}
    (hf : env.find? natBleName = some (.defnInfo cv v)) (ψ : Name → Nat) :
    ∀ a b : Nat, app (app (m.val natBleName ψ)
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) a))
        (natLitVal V (m.val natZeroName ψ) (m.val natSuccName ψ) b) =
      if a ≤ b then m.val boolTrueName ψ else m.val boolFalseName ψ := by
  obtain ⟨hg, heqs⟩ := m.nat_ops natBleName (by decide) cv v hf
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool (Or.inr rfl)
  obtain ⟨cv', v', hf', hlp⟩ := hdeps natBleName (by decide)
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf'
  obtain ⟨rfl, rfl⟩ := hf'
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
    ∃ cv v, env.find? c = some (.defnInfo cv v) ∧ cv.levelParams = [] :=
  (natOpGuard_inv hg).2.1 c (natOpDeps_self hc)

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
  · obtain ⟨cvc, vc, hfc, -⟩ := hdeps natPredName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc]
  · obtain ⟨cvc, vc, hfc, -⟩ := hdeps natAddName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc]
  · obtain ⟨cvp, vp, hfp, -⟩ := hdeps natPredName (by decide)
    obtain ⟨cvc, vc, hfc, -⟩ := hdeps natSubName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfp]
  · obtain ⟨cva, va, hfa, -⟩ := hdeps natAddName (by decide)
    obtain ⟨cvc, vc, hfc, -⟩ := hdeps natMulName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfa]
  · obtain ⟨cvm, vm, hfm, -⟩ := hdeps natMulName (by decide)
    obtain ⟨cvc, vc, hfc, -⟩ := hdeps natPowName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hfm]
  · obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hbool (Or.inl rfl)
    obtain ⟨cvc, vc, hfc, -⟩ := hdeps natBeqName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hT, hF]
  · obtain ⟨⟨ciT, hT, -⟩, ⟨ciF, hF, -⟩⟩ := hbool (Or.inr rfl)
    obtain ⟨cvc, vc, hfc, -⟩ := hdeps natBleName (by decide)
    simp +decide [natOpEquations, Expr.constsResolve, hnn, hzz, hss, hfc, hT, hF]

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
theorem NatOpsOk.cons_recRules {cvA : ConstantVal} {nP nM nm ni : Nat}
    {rules₁ rules₂ : List RecRule} {val : ConstVal V}
    (h : NatOpsOk V ⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ val) :
    NatOpsOk V ⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ val := by
  have henv : ∀ n,
      ((⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
    intro n
    rw [Env.find?_cons, Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA nP nM nm ni rules₂).name = n
    · rw [if_pos hn,
        if_pos (show (ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
          from hn)]
      rfl
    · rw [if_neg hn,
        if_neg (show ¬ (ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
          from hn)]
  have hfind : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2, ci ≠ .defnInfo cv2 v2) ∨
      (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA nP nM nm ni rules₂).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
        from hn)]
      exact Or.inr hf
  have hfind' : ∀ n (ci : ConstantInfo),
      (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? n =
        some ci → (∀ cv2 v2, ci ≠ .defnInfo cv2 v2) ∨
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find? n =
        some ci := by
    intro n ci hf
    rw [Env.find?_cons] at hf
    rw [Env.find?_cons]
    by_cases hn : (ConstantInfo.recInfo cvA nP nM nm ni rules₁).name = n
    · rw [if_pos hn] at hf
      obtain rfl := Option.some.inj hf
      exact Or.inl (fun cv2 v2 h => nomatch h)
    · rw [if_neg hn] at hf
      rw [if_neg (show ¬ (ConstantInfo.recInfo cvA nP nM nm ni rules₂).name = n
        from hn)]
      exact Or.inr hf
  have hnat : natLitSupported
      (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) =
      natLitSupported (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env) :=
    natLitSupported_cons_recRules
  intro c hc cv v hf
  rcases hfind c _ hf with hnd | hf₁
  · exact absurd rfl (hnd cv v)
  obtain ⟨hg, heqs⟩ := h c hc cv v hf₁
  obtain ⟨hs, hdeps, hbool⟩ := natOpGuard_inv hg
  refine ⟨natOpGuard_intro (by rw [hnat]; exact hs) ?_ ?_, ?_⟩
  · intro n hn
    obtain ⟨cvn, vn, hfn, hlpn⟩ := hdeps n hn
    rcases hfind' n _ hfn with hnd | hfn₂
    · exact absurd rfl (hnd cvn vn)
    · exact ⟨cvn, vn, hfn₂, hlpn⟩
  · intro hcb
    obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ := hbool hcb
    have conv : ∀ (nb : Name) (ci : ConstantInfo),
        (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env).find? nb =
          some ci → ci.toConstantVal.levelParams = [] →
        ∃ ci₂, (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env).find?
          nb = some ci₂ ∧ ci₂.toConstantVal.levelParams = [] := by
      intro nb ci hfb hlpb
      have h2 := henv nb
      rw [hfb] at h2
      cases hf2 : (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ :
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
          (⟨.recInfo cvA nP nM nm ni rules₂ :: env.consts⟩ : Env) ψ dd ρ e =
        interpExpr V val
          (⟨.recInfo cvA nP nM nm ni rules₁ :: env.consts⟩ : Env) ψ dd ρ e :=
      fun e dd ρ => interp_env_ext henv hnat e dd ρ
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

/-- `NatOpsOk` extension step: preservation for the stored operations
(the guard keeps every referenced constant away from the fresh name),
plus a handler for the case that the new constant is itself an
operation. -/
theorem NatOpsOk.cons {val val' : ConstVal V} {c₀ : ConstantInfo}
    (h : NatOpsOk V env val)
    (hfresh : env.find? c₀.name = none)
    (hagree : ∀ n, n ≠ c₀.name → ∀ ψ' : Name → Nat, val' n ψ' = val n ψ')
    (hhead : ∀ cv₀ v₀, c₀ = .defnInfo cv₀ v₀ → c₀.name ∈ natOpNames →
      natOpGuard (⟨c₀ :: env.consts⟩ : Env) c₀.name = true ∧
      ∀ eq ∈ natOpEquations 0 c₀.name, ∀ (ψ : Name → Nat) (x y : V),
        (∀ T, interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2 (rho0 V)
          (.const natName []) = some T → x ∈ˢ T ∧ y ∈ˢ T) →
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.1 =
        interpExpr V val' (⟨c₀ :: env.consts⟩ : Env) ψ 2
          (updV V (updV V (rho0 V) 0 x) 1 y) eq.2) :
    NatOpsOk V (⟨c₀ :: env.consts⟩ : Env) val' := by
  intro c hc cv v hf
  rw [Env.find?_cons] at hf
  by_cases hn : c₀.name = c
  · rw [if_pos hn] at hf
    subst hn
    exact hhead cv v (Option.some.inj hf) hc
  · rw [if_neg hn] at hf
    obtain ⟨hg, heqs⟩ := h c hc cv v hf
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

end Setlec
