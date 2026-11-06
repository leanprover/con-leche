module

public import InLeanProof.MkDataAxioms
/- The computed fields' equations are not exposed by `Lean.Expr`/`Lean.Level`. -/
import all Lean.Expr
import all Lean.Level

/-!
# Lean's cached fields, on terms in range (task #451, lane G)

`Expr.RangeOk e`: every `bvar` index and level depth in `e` is below C's bound.
It is a per-node property, and on such a term the cached fields are what the
structural walks compute (`Expr.fieldsOk`).  Nothing is said of a term out of
range: `Expr.bvar (2^20)` exists in the logic, and C aborts on building it.
-/

public section

namespace InLeanProof

open Lean

/-! ## Levels -/

@[expose] def depthS : Level → Nat
  | .zero | .param _ | .mvar _ => 0
  | .succ u => depthS u + 1
  | .max u v | .imax u v => max (depthS u) (depthS v) + 1

@[expose] def lparamS : Level → Bool
  | .zero | .mvar _ => false
  | .param _ => true
  | .succ u => lparamS u
  | .max u v | .imax u v => lparamS u || lparamS v

@[expose] def lmvarS : Level → Bool
  | .zero | .param _ => false
  | .mvar _ => true
  | .succ u => lmvarS u
  | .max u v | .imax u v => lmvarS u || lmvarS v

theorem Level.fields (l : Level) (h : depthS l ≤ maxLevelDepth) :
    l.data.depth.toNat = depthS l ∧ l.data.hasParam = lparamS l ∧ l.data.hasMVar = lmvarS l := by
  induction l with
  | zero =>
    exact ⟨levelMkData_depth _ _ _ _ (by decide), levelMkData_hasParam _ _ _ _ (by decide),
      levelMkData_hasMVar _ _ _ _ (by decide)⟩
  | param n =>
    exact ⟨levelMkData_depth _ _ _ _ (by decide), levelMkData_hasParam _ _ _ _ (by decide),
      levelMkData_hasMVar _ _ _ _ (by decide)⟩
  | mvar m =>
    exact ⟨levelMkData_depth _ _ _ _ (by decide), levelMkData_hasParam _ _ _ _ (by decide),
      levelMkData_hasMVar _ _ _ _ (by decide)⟩
  | succ u ih =>
    have hu : depthS u ≤ maxLevelDepth := by simp only [depthS] at h; omega
    obtain ⟨h1, h2, h3⟩ := ih hu
    have hb : u.data.depth.toNat + 1 ≤ maxLevelDepth := by rw [h1]; simpa only [depthS] using h
    refine ⟨?_, ?_, ?_⟩
    · exact (levelMkData_depth _ _ _ _ hb).trans (by simp only [depthS, h1])
    · exact (levelMkData_hasParam _ _ _ _ hb).trans (by simp only [lparamS, h2])
    · exact (levelMkData_hasMVar _ _ _ _ hb).trans (by simp only [lmvarS, h3])
  | max u v ihu ihv =>
    have hs : max (depthS u) (depthS v) + 1 ≤ maxLevelDepth := by simpa only [depthS] using h
    have hu : depthS u ≤ maxLevelDepth := by omega
    have hv : depthS v ≤ maxLevelDepth := by omega
    obtain ⟨h1, h2, h3⟩ := ihu hu
    obtain ⟨h4, h5, h6⟩ := ihv hv
    have hb : Nat.max u.data.depth.toNat v.data.depth.toNat + 1 ≤ maxLevelDepth := by
      rw [h1, h4]; exact hs
    refine ⟨?_, ?_, ?_⟩
    · exact (levelMkData_depth _ _ _ _ hb).trans (by simp only [depthS, h1, h4])
    · exact (levelMkData_hasParam _ _ _ _ hb).trans (by simp only [lparamS, h2, h5])
    · exact (levelMkData_hasMVar _ _ _ _ hb).trans (by simp only [lmvarS, h3, h6])
  | imax u v ihu ihv =>
    have hs : max (depthS u) (depthS v) + 1 ≤ maxLevelDepth := by simpa only [depthS] using h
    have hu : depthS u ≤ maxLevelDepth := by omega
    have hv : depthS v ≤ maxLevelDepth := by omega
    obtain ⟨h1, h2, h3⟩ := ihu hu
    obtain ⟨h4, h5, h6⟩ := ihv hv
    have hb : Nat.max u.data.depth.toNat v.data.depth.toNat + 1 ≤ maxLevelDepth := by
      rw [h1, h4]; exact hs
    refine ⟨?_, ?_, ?_⟩
    · exact (levelMkData_depth _ _ _ _ hb).trans (by simp only [depthS, h1, h4])
    · exact (levelMkData_hasParam _ _ _ _ hb).trans (by simp only [lparamS, h2, h5])
    · exact (levelMkData_hasMVar _ _ _ _ hb).trans (by simp only [lmvarS, h3, h6])

/-! ## Expressions -/

/-- **In range**: every `bvar` index below C's bound, every level depth too. -/
@[expose] def Expr.RangeOk : Expr → Prop
  | .bvar i => i + 1 ≤ maxRange
  | .fvar _ | .mvar _ | .lit _ => True
  | .sort u => depthS u ≤ maxLevelDepth
  | .const _ us => ∀ u ∈ us, depthS u ≤ maxLevelDepth
  | .app f a => Expr.RangeOk f ∧ Expr.RangeOk a
  | .lam _ t b _ | .forallE _ t b _ => Expr.RangeOk t ∧ Expr.RangeOk b
  | .letE _ t v b _ => Expr.RangeOk t ∧ Expr.RangeOk v ∧ Expr.RangeOk b
  | .mdata _ x | .proj _ _ x => Expr.RangeOk x

/-- The loose-variable range, structurally. -/
@[expose] def rangeS : Expr → Nat
  | .bvar i => i + 1
  | .fvar _ | .mvar _ | .lit _ | .sort _ | .const .. => 0
  | .app f a => max (rangeS f) (rangeS a)
  | .lam _ t b _ | .forallE _ t b _ => max (rangeS t) (rangeS b - 1)
  | .letE _ t v b _ => max (max (rangeS t) (rangeS v)) (rangeS b - 1)
  | .mdata _ x | .proj _ _ x => rangeS x

/-- Some free variable, structurally. -/
@[expose] def fvarS : Expr → Bool
  | .fvar _ => true
  | .bvar _ | .mvar _ | .lit _ | .sort _ | .const .. => false
  | .app f a | .lam _ f a _ | .forallE _ f a _ => fvarS f || fvarS a
  | .letE _ t v b _ => fvarS t || fvarS v || fvarS b
  | .mdata _ x | .proj _ _ x => fvarS x

/-- Some expression metavariable, structurally. -/
@[expose] def emvarS : Expr → Bool
  | .mvar _ => true
  | .bvar _ | .fvar _ | .lit _ | .sort _ | .const .. => false
  | .app f a | .lam _ f a _ | .forallE _ f a _ => emvarS f || emvarS a
  | .letE _ t v b _ => emvarS t || emvarS v || emvarS b
  | .mdata _ x | .proj _ _ x => emvarS x

/-- Some level metavariable, structurally. -/
@[expose] def elmvarS : Expr → Bool
  | .sort u => lmvarS u
  | .const _ us => us.any lmvarS
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => false
  | .app f a | .lam _ f a _ | .forallE _ f a _ => elmvarS f || elmvarS a
  | .letE _ t v b _ => elmvarS t || elmvarS v || elmvarS b
  | .mdata _ x | .proj _ _ x => elmvarS x

/-- Some level parameter, structurally. -/
@[expose] def elparamS : Expr → Bool
  | .sort u => lparamS u
  | .const _ us => us.any lparamS
  | .bvar _ | .fvar _ | .mvar _ | .lit _ => false
  | .app f a | .lam _ f a _ | .forallE _ f a _ => elparamS f || elparamS a
  | .letE _ t v b _ => elparamS t || elparamS v || elparamS b
  | .mdata _ x | .proj _ _ x => elparamS x

/-- A node's cached fields are the walks' values. -/
structure FieldsOk (e : Expr) : Prop where
  range : e.data.looseBVarRange.toNat = rangeS e
  bound : rangeS e ≤ maxRange
  fvar : e.data.hasFVar = fvarS e
  emvar : e.data.hasExprMVar = emvarS e
  lmvar : e.data.hasLevelMVar = elmvarS e
  lparam : e.data.hasLevelParam = elparamS e

theorem mkData_fieldsOk {e : Expr} {h : UInt64} {r : Nat} {d : UInt32} {a b c x : Bool}
    (hd : e.data = Expr.mkData h r d a b c x) (hr : r ≤ maxRange)
    (h1 : r = rangeS e) (h2 : a = fvarS e) (h3 : b = emvarS e) (h4 : c = elmvarS e)
    (h5 : x = elparamS e) : FieldsOk e :=
  ⟨by rw [hd, mkData_looseBVarRange _ _ _ _ _ _ _ hr, h1], h1 ▸ hr,
   by rw [hd, mkData_hasFVar _ _ _ _ _ _ _ hr, h2],
   by rw [hd, mkData_hasExprMVar _ _ _ _ _ _ _ hr, h3],
   by rw [hd, mkData_hasLevelMVar _ _ _ _ _ _ _ hr, h4],
   by rw [hd, mkData_hasLevelParam _ _ _ _ _ _ _ hr, h5]⟩

theorem levels_any_hasMVar : ∀ (us : List Level), (∀ u ∈ us, depthS u ≤ maxLevelDepth) →
    us.any Level.hasMVar = us.any lmvarS
  | [], _ => rfl
  | u :: us, h => by
    have h1 := (Level.fields u (h u List.mem_cons_self)).2.2
    have h2 := levels_any_hasMVar us (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.any_cons, h2]
    show (u.data.hasMVar || _) = _
    rw [h1]

theorem levels_any_hasParam : ∀ (us : List Level), (∀ u ∈ us, depthS u ≤ maxLevelDepth) →
    us.any Level.hasParam = us.any lparamS
  | [], _ => rfl
  | u :: us, h => by
    have h1 := (Level.fields u (h u List.mem_cons_self)).2.1
    have h2 := levels_any_hasParam us (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [List.any_cons, h2]
    show (u.data.hasParam || _) = _
    rw [h1]

/-- **On a term in range the cached fields are the walks' values.** -/
theorem Expr.fieldsOk (e : Expr) (h : Expr.RangeOk e) : FieldsOk e := by
  induction e with
  | bvar i =>
    exact mkData_fieldsOk rfl h rfl rfl rfl rfl rfl
  | fvar id => exact mkData_fieldsOk rfl (by decide) rfl rfl rfl rfl rfl
  | mvar id => exact mkData_fieldsOk rfl (by decide) rfl rfl rfl rfl rfl
  | lit l => exact mkData_fieldsOk rfl (by decide) rfl rfl rfl rfl rfl
  | sort u =>
    have := Level.fields u h
    exact mkData_fieldsOk rfl (by decide) rfl rfl rfl this.2.2 this.2.1
  | const n us =>
    exact mkData_fieldsOk rfl (by decide) rfl rfl rfl
      (levels_any_hasMVar us h) (levels_any_hasParam us h)
  | app f a ihf iha =>
    obtain ⟨hf, ha⟩ := h
    have F := ihf hf
    have A := iha ha
    obtain ⟨h1, h2, h3, h4, h5⟩ := Expr.mkAppData_fields f.data a.data
    have hb : rangeS (.app f a) ≤ maxRange := by
      have := F.bound; have := A.bound; simp only [rangeS]; omega
    exact ⟨by show (Expr.mkAppData f.data a.data).looseBVarRange.toNat = _
              rw [h1, F.range, A.range]; rfl,
      hb,
      by show (Expr.mkAppData f.data a.data).hasFVar = _
         rw [h2, F.fvar, A.fvar]; rfl,
      by show (Expr.mkAppData f.data a.data).hasExprMVar = _
         rw [h3, F.emvar, A.emvar]; rfl,
      by show (Expr.mkAppData f.data a.data).hasLevelMVar = _
         rw [h4, F.lmvar, A.lmvar]; rfl,
      by show (Expr.mkAppData f.data a.data).hasLevelParam = _
         rw [h5, F.lparam, A.lparam]; rfl⟩
  | lam n t b bi iht ihb =>
    obtain ⟨ht, hb⟩ := h
    have T := iht ht
    have B := ihb hb
    have hr : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ maxRange := by
      rw [T.range, B.range]; have := T.bound; have := B.bound; omega
    exact mkData_fieldsOk rfl hr (by rw [T.range, B.range]; rfl)
      (by rw [T.fvar, B.fvar]; rfl) (by rw [T.emvar, B.emvar]; rfl)
      (by rw [T.lmvar, B.lmvar]; rfl) (by rw [T.lparam, B.lparam]; rfl)
  | forallE n t b bi iht ihb =>
    obtain ⟨ht, hb⟩ := h
    have T := iht ht
    have B := ihb hb
    have hr : max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1) ≤ maxRange := by
      rw [T.range, B.range]; have := T.bound; have := B.bound; omega
    exact mkData_fieldsOk rfl hr (by rw [T.range, B.range]; rfl)
      (by rw [T.fvar, B.fvar]; rfl) (by rw [T.emvar, B.emvar]; rfl)
      (by rw [T.lmvar, B.lmvar]; rfl) (by rw [T.lparam, B.lparam]; rfl)
  | letE n t v b nd iht ihv ihb =>
    obtain ⟨ht, hv, hb⟩ := h
    have T := iht ht
    have V := ihv hv
    have B := ihb hb
    have hr : max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat)
        (b.data.looseBVarRange.toNat - 1) ≤ maxRange := by
      rw [T.range, V.range, B.range]
      have := T.bound; have := V.bound; have := B.bound; omega
    exact mkData_fieldsOk rfl hr (by rw [T.range, V.range, B.range]; rfl)
      (by rw [T.fvar, V.fvar, B.fvar]; rfl) (by rw [T.emvar, V.emvar, B.emvar]; rfl)
      (by rw [T.lmvar, V.lmvar, B.lmvar]; rfl) (by rw [T.lparam, V.lparam, B.lparam]; rfl)
  | mdata m x ih =>
    have X := ih h
    have hr : x.data.looseBVarRange.toNat ≤ maxRange := by rw [X.range]; exact X.bound
    exact mkData_fieldsOk rfl hr X.range X.fvar X.emvar X.lmvar X.lparam
  | proj s i x ih =>
    have X := ih h
    have hr : x.data.looseBVarRange.toNat ≤ maxRange := by rw [X.range]; exact X.bound
    exact mkData_fieldsOk rfl hr X.range X.fvar X.emvar X.lmvar X.lparam

theorem Expr.looseBVarRange_eq {e : Expr} (h : Expr.RangeOk e) : e.looseBVarRange = rangeS e :=
  (Expr.fieldsOk e h).range

theorem Expr.hasFVar_eq {e : Expr} (h : Expr.RangeOk e) : e.hasFVar = fvarS e :=
  (Expr.fieldsOk e h).fvar

theorem Expr.hasExprMVar_eq {e : Expr} (h : Expr.RangeOk e) : e.hasExprMVar = emvarS e :=
  (Expr.fieldsOk e h).emvar

theorem Expr.hasLevelParam_eq {e : Expr} (h : Expr.RangeOk e) : e.hasLevelParam = elparamS e :=
  (Expr.fieldsOk e h).lparam

end InLeanProof
