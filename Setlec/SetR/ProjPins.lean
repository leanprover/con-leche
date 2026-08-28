import Setlec.SetR.Rel
import Setlec.Verify.Denote.SubstAlgebra
import Setlec.Verify.Denote.Levels
import Setlec.Verify.EnvPreds

/-!
# The pinned projection entries, denoted (task #148)

The projection table's `native` entries are pinned to the basis pair
(`ProjOkT`), so the entry types, the constructor's type and the
`piResidualV` walks along them are **concrete computations** — no
environment beyond the pin, no valuation beyond `cval`, and no `V`.

Relocated out of `Setlec/SetR/Sound/Proj.lean` (task #148, T3): the
soundness tier built them first, and the bridge's I9/R6 clauses need
exactly the same four facts (the entry identification, the two entry
types' denotations, the constructor type's denotation, and the two
residual walks).  They sit below both tiers so there is one proof.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify

section Pins

variable {env : Env} {cval : TConstVal} {φ : Name → Nat}

/-! ### Entry identification -/

/-- A native table entry is one of the two pinned pair entries, its
stored name pins the struct name and index, and the pair block is
stored.  (`Model/Core/Whnf.lean:317-326`'s moves, packaged.) -/
theorem projEntry_pins (hpo : ProjOkT env) {sn : Name} {i : Nat}
    {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    sn = psigmaName ∧ entry.idx = i ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA := by
  obtain ⟨hpin, hpsig, hpsigMk⟩ :=
    hpo.1 _ _ (Env.findProj?_some hf) hnat
  have h1 := List.find?_some (Env.findProj?_some hf)
  have h2 : (ConstantInfo.projInfo entry).name = projFnName sn i :=
    eq_of_beq (by simpa using h1)
  simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
  refine ⟨hpin, ?_, (projFnName_inj h2).2, hpsig, hpsigMk⟩
  have hsn : entry.structName = sn := (projFnName_inj h2).1
  rw [← hsn]
  rcases hpin with rfl | rfl <;> rfl

/-! ### The pinned types' denotations (concrete computations) -/

/-- The instantiated first-projection entry type denotes to its
concrete `VExpr`. -/
theorem denote_pairFstTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (pairFstEntry.ty.instantiateLevelParams pairFstEntry.levelParams
        [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.app (.app (cval psigmaName
                  (Level.substFn φ psigmaA.toConstantVal.levelParams
                    [l0, l1]))
                (.bvar 1)) (.bvar 0))
              (.bvar 2)))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, pairFstEntry, pairFstTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-- The instantiated second-projection entry type denotes to its
concrete `VExpr`. -/
theorem denote_pairSndTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (pairSndEntry.ty.instantiateLevelParams pairSndEntry.levelParams
        [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.app (.app (cval psigmaName
                  (Level.substFn φ psigmaA.toConstantVal.levelParams
                    [l0, l1]))
                (.bvar 1)) (.bvar 0))
              (.app (.bvar 1) (.proj 0 (.bvar 0)))))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, pairSndEntry, pairSndTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app, denote_proj,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-- The instantiated pinned constructor type denotes to its concrete
`VExpr`. -/
theorem denote_psigmaMkTy_eq
    (hpsig : env.find? psigmaName = some psigmaA) (l0 l1 : Level) :
    denoteClosed cval env φ
      (psigmaMkA.toConstantVal.type.instantiateLevelParams
        psigmaMkA.toConstantVal.levelParams [l0, l1])
      = some (.pi (.sort (Level.eval φ l0))
          (.pi (.pi (.bvar 0) (.sort (Level.eval φ l1)))
            (.pi (.bvar 1)
              (.pi (.app (.bvar 1) (.bvar 0))
                (.app (.app (cval psigmaName
                    (Level.substFn φ psigmaA.toConstantVal.levelParams
                      [l0, l1]))
                  (.bvar 3)) (.bvar 2)))))) := by
  have hpsigC : ∀ D : Nat, denote cval env φ D
      (.const psigmaName [l0, l1]) =
      some (cval psigmaName
        (Level.substFn φ psigmaA.toConstantVal.levelParams [l0, l1])) := by
    intro D
    rw [denote_const, hpsig]
    simp only [psigmaA, ConstantInfo.toConstantVal, List.length_cons,
      List.length_nil, if_true]
  simp only [psigmaName] at hpsigC
  simp +decide only [denoteClosed, psigmaMkA,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app,
    hpsigC, Expr.instantiate1, Nat.reduceSub, reduceIte,
    List.map_cons, List.map_nil]

/-! ### The concrete residual walks -/

/-- The first entry's residual at a full spine is the type argument. -/
theorem piResidualV_pairFst {K : VExpr} (hK : VExpr.Closed K)
    (u₀ v₀ : Nat) (X Y p : VExpr) :
    piResidualV
      (.pi (.sort u₀) (.pi (.pi (.bvar 0) (.sort v₀))
        (.pi (.app (.app K (.bvar 1)) (.bvar 0)) (.bvar 2))))
      [X, Y, p] = some X := by
  have e1 : ((VExpr.liftN 2 X).inst Y 1) = VExpr.liftN 1 X := by
    simpa using VExpr.inst_liftN_absorb X (j := 0) (k := 1) (m := 1)
      (by omega) (by omega) Y
  have e2 : ((VExpr.liftN 1 X).inst p) = X := by
    simpa [VExpr.liftN_zero] using
      VExpr.inst_liftN_absorb X (j := 0) (k := 0) (m := 0)
        (by omega) (by omega) p
  simp +decide only [piResidualV, VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_sort, VExpr.inst_bvar,
    VExpr.inst_eq_self_of_closed hK, if_true, if_false,
    Nat.reduceAdd, Nat.reduceSub, e1, e2]

/-- The second entry's residual at a full spine is the fibre at the
first projection. -/
theorem piResidualV_pairSnd {K : VExpr} (hK : VExpr.Closed K)
    (u₀ v₀ : Nat) (X Y p : VExpr) :
    piResidualV
      (.pi (.sort u₀) (.pi (.pi (.bvar 0) (.sort v₀))
        (.pi (.app (.app K (.bvar 1)) (.bvar 0))
          (.app (.bvar 1) (.proj 0 (.bvar 0))))))
      [X, Y, p] = some (.app Y (.proj 0 p)) := by
  have e3 : ((VExpr.liftN 1 Y).inst p) = Y := by
    simpa [VExpr.liftN_zero] using
      VExpr.inst_liftN_absorb Y (j := 0) (k := 0) (m := 0)
        (by omega) (by omega) p
  simp +decide only [piResidualV, VExpr.inst_pi, VExpr.inst_app,
    VExpr.inst_sort, VExpr.inst_bvar, VExpr.inst_proj,
    VExpr.inst_eq_self_of_closed hK, if_true, if_false,
    Nat.reduceAdd, Nat.reduceSub, e3, VExpr.liftN_zero]

end Pins

end Setlec.SetR
