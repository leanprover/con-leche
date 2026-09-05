import Setlec.SetBase.Rel
import Setlec.Verify.Denote.SubstAlgebra
import Setlec.Verify.Denote.Levels
import Setlec.Verify.EnvPreds
import Setlec.Verify.ProjPinInv

/-!
# The pinned projection entries, denoted (task #148)

*(Re-based to `Setlec/SetBase/*` at THE SEPARATION's S2, task #161, with
`SetBase/Rel` which it stands on: the graded lane's
`Step2/ProjPinsP` consumes `projEntry_pins` and was reaching it
through the 2U `Step2/DefEqRun`.  Path and module name changed;
namespaces, statements and proofs verbatim.)*


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

/-- A `ProjOkT`-pinned entry is not tower-backed (task #175 wiring):
the fact the P rows use to kill the inversion's tower side. -/
theorem projEntry_not_tower (hpo : ProjOkT env) {sn : Name} {i : Nat}
    {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    entry.tower = false := by
  obtain ⟨hpin, -, -⟩ := hpo.1 _ _ (Env.findProj?_some hf) hnat
  rcases hpin with rfl | rfl <;> rfl

/-- A native table entry is one of the two pinned pair entries, its
stored name pins the struct name and index, and the pair block is
stored.  (`Model/Core/Whnf.lean:317-326`'s moves, packaged.)

**Re-pointed (2026-09-04, the E2 gate).**  Statement unchanged; the
proof is now three parts with three different premises, which is the
finding:

* the **entry identity** comes from `ProjOkT` here, but it does not
  have to — `NativeProjPinned.pinned` (`Verify/ProjPinInv.lean`)
  derives it with **no environment predicate at all**, as an
  install-time invariant of the checker's own code.  That is what makes
  the `.proj` clause's pinned residual unconditional rather than a
  tier licence;
* the **name and index** never needed a predicate: `projEntry_names`
  reads them off the lookup, since a table entry is stored under
  `projFnName entry.structName entry.idx`;
* only the two **stored-block** conjuncts genuinely use `ProjOkT`, and
  they are read only by the denotation lemmas below.  They stay here. -/
theorem projEntry_pins (hpo : ProjOkT env) {sn : Name} {i : Nat}
    {entry : ProjEntry}
    (hf : env.findProj? sn i = some entry) (hnat : entry.native = true) :
    (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
    sn = psigmaName ∧ entry.idx = i ∧
    env.find? psigmaName = some psigmaA ∧
    env.find? psigmaMkName = some psigmaMkA := by
  obtain ⟨hpin, hpsig, hpsigMk⟩ :=
    hpo.1 _ _ (Env.findProj?_some hf) hnat
  obtain ⟨hsn, hidx⟩ := Setlec.projEntry_names hf hpin
  exact ⟨hpin, hsn, hidx, hpsig, hpsigMk⟩

/-! ### The residual, from the computed two-way branch (task #161 B2)

The `.proj` inference clause no longer *walks* the entry type: at a
pinned entry the parameter spine has exactly two members and the
residual is `A` or `B (pe.1)`, so the clause returns that outright
(harvest site 21 / list entry P10).  Both verification tiers state
their `.proj` conclusion with the walk (`piResidualV`/`denoteP` of
`piResidual`), so this is where the computed value is turned back into
the walk's — by `projEntry_pins`, and by the frame fact that the two
parameters carry no loose `bvar`s, which the clause's callers already
have. -/

/-- The first pinned entry's residual at a full spine is the type
argument. -/
theorem piResidual_pairFstS (l0 l1 : Level) {A B pe : Expr}
    (hA : ∀ k, Expr.looseBVarsBounded k A = true) :
    Setlec.piResidual
      (pairFstEntry.ty.instantiateLevelParams pairFstEntry.levelParams
        [l0, l1]) [A, B, pe] = some A := by
  simp +decide [Setlec.piResidual, pairFstEntry, pairFstTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go,
    Expr.instantiate1]
  rw [Setlec.Expr.instantiate1_eq_self (hA 1),
    Setlec.Expr.instantiate1_eq_self (hA 0)]

/-- The second pinned entry's residual at a full spine is the fibre at
the first projection. -/
theorem piResidual_pairSndS (l0 l1 : Level) {A B pe : Expr}
    (hB : ∀ k, Expr.looseBVarsBounded k B = true) :
    Setlec.piResidual
      (pairSndEntry.ty.instantiateLevelParams pairSndEntry.levelParams
        [l0, l1]) [A, B, pe]
      = some (.app B (.proj psigmaName 0 pe)) := by
  simp +decide [Setlec.piResidual, pairSndEntry, pairSndTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go,
    Expr.instantiate1]
  rw [Setlec.Expr.instantiate1_eq_self (hB 0)]

/-- **The walk, from the computed residual — from the entry alone.**

Re-pointed (2026-09-04, the E2 gate): this carries no environment
predicate.  Everything it needs is the pinned entry's *identity*, which
`ProjOkT` supplies in the tower and `NativeProjPinned.pinned`
(`Verify/ProjPinInv.lean`) supplies from the install path with no
premise at all.  `piResidual_of_computed` below is the `ProjOkT`
instance, statement byte-unchanged. -/
theorem piResidual_of_pinned {sn : Name} {i : Nat}
    {entry : ProjEntry} {us : List Level} {A B pe t : Expr}
    (hpin : entry = pairFstEntry ∨ entry = pairSndEntry)
    (hsn : sn = psigmaName) (hidx : entry.idx = i)
    (hlenUs : us.length = entry.levelParams.length)
    (hA : Expr.looseBVarsBounded 0 A = true)
    (hB : Expr.looseBVarsBounded 0 B = true)
    (hcomp : (i = 0 ∧ t = A) ∨
      (i = 1 ∧ t = .app B (.proj sn 0 pe))) :
    Setlec.piResidual
      (entry.ty.instantiateLevelParams entry.levelParams us)
      ([A, B] ++ [pe]) = some t := by
  subst hsn
  have hAk : ∀ k, Expr.looseBVarsBounded k A = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k) hA
  have hBk : ∀ k, Expr.looseBVarsBounded k B = true := fun k =>
    Setlec.Expr.looseBVarsBounded_mono (Nat.zero_le k) hB
  obtain ⟨l0, l1, rfl⟩ : ∃ l0 l1, us = [l0, l1] := by
    rcases hpin with rfl | rfl <;>
      (simp only [pairFstEntry, pairSndEntry, List.length_cons,
        List.length_nil] at hlenUs
       match us, hlenUs with
       | [l0, l1], _ => exact ⟨l0, l1, rfl⟩)
  rw [show ([A, B] ++ [pe] : List Expr) = [A, B, pe] from rfl]
  rcases hpin with rfl | rfl
  · have hi : i = 0 := by rw [← hidx]; rfl
    rcases hcomp with ⟨-, rfl⟩ | ⟨hi1, -⟩
    · exact piResidual_pairFstS l0 l1 hAk
    · exact absurd (hi.symm.trans hi1) (by decide)
  · have hi : i = 1 := by rw [← hidx]; rfl
    rcases hcomp with ⟨hi0, -⟩ | ⟨-, rfl⟩
    · exact absurd (hi.symm.trans hi0) (by decide)
    · exact piResidual_pairSndS l0 l1 hBk

/-- **The walk, from the computed residual.**  What the `.proj`
inference clause returns is what `piResidual` would have walked to —
under the pin, the two-element spine and the parameters' closedness.

The `ProjOkT` instance of `piResidual_of_pinned`; statement unchanged
across the E2-gate re-point, so its callers are untouched. -/
theorem piResidual_of_computed (hpo : ProjOkT env) {sn : Name} {i : Nat}
    {entry : ProjEntry} {us : List Level} {A B pe t : Expr}
    (hfe : env.findProj? sn i = some entry) (hnat : entry.native = true)
    (hlenUs : us.length = entry.levelParams.length)
    (hA : Expr.looseBVarsBounded 0 A = true)
    (hB : Expr.looseBVarsBounded 0 B = true)
    (hcomp : (i = 0 ∧ t = A) ∨
      (i = 1 ∧ t = .app B (.proj sn 0 pe))) :
    Setlec.piResidual
      (entry.ty.instantiateLevelParams entry.levelParams us)
      ([A, B] ++ [pe]) = some t :=
  let p := projEntry_pins hpo hfe hnat
  piResidual_of_pinned p.1 p.2.1 p.2.2.1 hlenUs hA hB hcomp

/-- **The walk, from the install-time invariant** — the same conclusion
with no environment record anywhere in the premises.  This is the form
the parity-alignment batch consumes when the five `.proj` inference
clauses unify onto the pinned residual. -/
theorem piResidual_of_invariant {sn : Name} {i : Nat}
    {entry : ProjEntry} {us : List Level} {A B pe t : Expr}
    (hI : Setlec.NativeProjPinned env)
    (hfe : env.findProj? sn i = some entry) (hnat : entry.native = true)
    (hlenUs : us.length = entry.levelParams.length)
    (hA : Expr.looseBVarsBounded 0 A = true)
    (hB : Expr.looseBVarsBounded 0 B = true)
    (hcomp : (i = 0 ∧ t = A) ∨
      (i = 1 ∧ t = .app B (.proj sn 0 pe))) :
    Setlec.piResidual
      (entry.ty.instantiateLevelParams entry.levelParams us)
      ([A, B] ++ [pe]) = some t :=
  let p := hI.pinned hfe hnat
  piResidual_of_pinned p.1 p.2.1 p.2.2 hlenUs hA hB hcomp

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
    (hpsig : env.find? psigmaName = some psigmaA)
    (hnt : ∀ e, env.findProj? psigmaName 0 = some e →
      e.tower = false) (l0 l1 : Level) :
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
  have hpp : ∀ (D : Nat) (e0 : Expr),
      denote cval env φ D (.proj psigmaName 0 e0)
        = match denote cval env φ D e0 with
          | none => none
          | some ve => some (.proj 0 ve) := by
    intro D e0
    rw [denote_proj_pair cval env φ D psigmaName 0 e0 hnt]
    cases denote cval env φ D e0 with
    | none => rfl
    | some ve => simp
  simp only [psigmaName] at hpp
  simp +decide only [denoteClosed, pairSndEntry, pairSndTyA,
    Expr.instantiateLevelParams, Level.subst, Level.subst.go, psigmaName,
    denote_forallE, denote_sort, denote_fvar, denote_app, hpp,
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
