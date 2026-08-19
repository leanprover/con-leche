import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps
import Setlec.Verify.Level

/-!
# Syntactic lemmas about level-parameter instantiation

* substitution composition (`Level.subst_subst`, `Expr.instLevels_instLevels`),
* commutation with binder opening (`Expr.instLevels_instantiate1`),
* preservation of closedness and of level-parameter bounds.

Composition and bound-preservation need the original term to mention only
parameters from the substituted list *and* the lists to be aligned
(`us.length = ks.length`) — both checked by the checker before any
instantiation happens.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Setlec

namespace Level

private theorem subst_go_subst {ks : List Name} {us : List Level} :
    ∀ {ps : List Name} {vs : List Level} {n : Name},
      n ∈ ps → vs.length = ps.length →
      subst ks us (subst.go ps vs n) = subst.go ps (vs.map (subst ks us)) n := by
  intro ps
  induction ps with
  | nil => intro vs n hn _; simp at hn
  | cons p ps ih =>
    intro vs n hn hl
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.map, subst.go]
      split
      · rfl
      · next hne =>
        refine ih ?_ (by simpa using hl)
        rcases List.mem_cons.mp hn with rfl | h
        · exact absurd rfl hne
        · exact h

/-- Substituting into an already-substituted level composes, provided the
original level only mentions parameters from `ps` and the lists align. -/
theorem subst_subst {ks : List Name} {us : List Level} {ps : List Name} {vs : List Level}
    (hl : vs.length = ps.length) :
    ∀ {u : Level}, u.allParamsDefined ps = true →
      subst ks us (subst ps vs u) = subst ps (vs.map (subst ks us)) u := by
  intro u
  induction u <;> intro h <;> simp_all [subst, allParamsDefined]
  case param n => exact subst_go_subst (by simpa using h) hl

private theorem allParamsDefined_subst_go {ps' : List Name} :
    ∀ {ks : List Name} {us : List Level} {n : Name},
      n ∈ ks → us.length = ks.length → (∀ u ∈ us, u.allParamsDefined ps' = true) →
      (subst.go ks us n).allParamsDefined ps' = true := by
  intro ks
  induction ks with
  | nil => intro us n hn _ _; simp at hn
  | cons k ks ih =>
    intro us n hn hl hus
    cases us with
    | nil => simp at hl
    | cons u us =>
      simp only [subst.go]
      split
      · exact hus u (by simp)
      · next hne =>
        refine ih ?_ (by simpa using hl) (fun v hv => hus v (by simp [hv]))
        rcases List.mem_cons.mp hn with rfl | h
        · exact absurd rfl hne
        · exact h

/-- Substitution keeps parameters within the bound of the substituted
levels. -/
theorem allParamsDefined_subst {ks : List Name} {us : List Level} {ps' : List Name}
    (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {u : Level}, u.allParamsDefined ks = true →
      (subst ks us u).allParamsDefined ps' = true := by
  intro u
  induction u <;> intro h <;> simp_all [subst, allParamsDefined]
  case param n => exact allParamsDefined_subst_go (by simpa using h) hl hus

end Level

namespace Expr

/-- Level instantiation does not change the free-variable structure. -/
theorem hasFvar_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, (e.instantiateLevelParams ks us).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [instantiateLevelParams, hasFvar]

/-- Level instantiation does not change loose-bvar bounds. -/
theorem looseBVarsBounded_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiateLevelParams ks us).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiateLevelParams, looseBVarsBounded]

/-- Level instantiation preserves a `∀`-telescope's arity. -/
theorem stripPis_instantiateLevelParams_isSome (ks : List Name)
    (us : List Level) :
    ∀ (k : Nat) {e : Expr}, (e.stripPis k).isSome →
      ((e.instantiateLevelParams ks us).stripPis k).isSome := by
  intro k
  induction k with
  | zero => intro e _; simp [Expr.stripPis]
  | succ k ih =>
    intro e h
    match e, h with
    | .forallE n ty body m, h =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis,
        Option.isSome_map] at h ⊢
      exact ih h

/-- Renaming constants commutes with level instantiation. -/
theorem renameConsts_instantiateLevelParams (f : Name → Name)
    (ks : List Name) (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).renameConsts f =
      (e.renameConsts f).instantiateLevelParams ks us := by
  intro e
  induction e <;>
    simp_all [Expr.instantiateLevelParams, Expr.renameConsts]

/-- Renaming constants commutes with bvar lifting. -/
theorem renameConsts_liftLooseBVars (f : Name → Name) :
    ∀ (e : Expr) (k c : Nat),
      (e.liftLooseBVars k c).renameConsts f =
        (e.renameConsts f).liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c
    simp only [Expr.liftLooseBVars, Expr.renameConsts]
    split <;> simp [Expr.renameConsts]
  | _ =>
    intro k c
    simp_all [Expr.liftLooseBVars, Expr.renameConsts]

/-- Level instantiation commutes with binder opening. -/
theorem instantiateLevelParams_instantiate1 (ks : List Name) (us : List Level)
    {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d n ty) k).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).instantiate1
          (.fvar d n (ty.instantiateLevelParams ks us)) k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiate1, instantiateLevelParams]
  case bvar i =>
    split
    · rfl
    · split <;> simp [instantiateLevelParams]

theorem renameConsts_instantiate1 (f : Name → Name)
    {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d n ty) k).renameConsts f =
        (e.renameConsts f).instantiate1
          (.fvar d n (ty.renameConsts f)) k := by
  intro e
  induction e <;> intro k <;> simp_all [Expr.instantiate1, Expr.renameConsts]
  case bvar i =>
    split
    · rfl
    · split <;> simp [Expr.renameConsts]

/-- Level instantiation composes, provided the expression only mentions
parameters from `ps` and the lists align. -/
theorem instantiateLevelParams_instantiateLevelParams
    {ks : List Name} {us : List Level} {ps : List Name} {vs : List Level}
    (hl : vs.length = ps.length) :
    ∀ {e : Expr}, e.allLevelParamsDefined ps = true →
      (e.instantiateLevelParams ps vs).instantiateLevelParams ks us =
        e.instantiateLevelParams ps (vs.map (Level.subst ks us)) := by
  intro e
  induction e with
  | sort u =>
    intro h
    simp only [instantiateLevelParams]
    rw [Level.subst_subst hl (by simpa [Expr.allLevelParamsDefined] using h)]
  | const n ls =>
    intro h
    simp only [instantiateLevelParams, List.map_map]
    refine congrArg _ (List.map_congr_left fun l hml => ?_)
    have hb : l.allParamsDefined ps = true := by
      simp only [Expr.allLevelParamsDefined, List.all_eq_true] at h
      exact h l hml
    simpa [Function.comp] using Level.subst_subst (u := l) hl hb
  | lam n ty body m ihty ihbody =>
    intro h
    simp only [allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [instantiateLevelParams, ihty h.1.1, ihbody h.1.2]
    cases hc : m.cod with
    | none => simp
    | some v =>
      simp only [hc, Option.map_some]
      rw [Level.subst_subst hl (by simpa [hc] using h.2)]
  | forallE n ty body m ihty ihbody =>
    intro h
    simp only [allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [instantiateLevelParams, ihty h.1.1, ihbody h.1.2]
    cases hc : m.cod with
    | none => simp
    | some v =>
      simp only [hc, Option.map_some]
      rw [Level.subst_subst hl (by simpa [hc] using h.2)]
  | _ =>
    intro h
    simp_all [instantiateLevelParams, allLevelParamsDefined]

/-- Level instantiation keeps level parameters within the bound of the
substituted levels. -/
theorem allLevelParamsDefined_instantiateLevelParams
    {ks : List Name} {us : List Level} {ps' : List Name}
    (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {e : Expr}, e.allLevelParamsDefined ks = true →
      (e.instantiateLevelParams ks us).allLevelParamsDefined ps' = true := by
  intro e
  induction e with
  | lam n ty body m ihty ihbody =>
    intro h
    simp only [allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [instantiateLevelParams, allLevelParamsDefined, ihty h.1.1, ihbody h.1.2,
      Bool.and_eq_true, Bool.true_and]
    cases hc : m.cod with
    | none => simp
    | some v =>
      simp only [Option.map_some]
      exact Level.allParamsDefined_subst hl hus (by simpa [hc] using h.2)
  | forallE n ty body m ihty ihbody =>
    intro h
    simp only [allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [instantiateLevelParams, allLevelParamsDefined, ihty h.1.1, ihbody h.1.2,
      Bool.and_eq_true, Bool.true_and]
    cases hc : m.cod with
    | none => simp
    | some v =>
      simp only [Option.map_some]
      exact Level.allParamsDefined_subst hl hus (by simpa [hc] using h.2)
  | sort u =>
    intro h
    simp only [instantiateLevelParams, allLevelParamsDefined] at h ⊢
    exact Level.allParamsDefined_subst hl hus h
  | const n ls =>
    intro h
    simp only [instantiateLevelParams, allLevelParamsDefined, List.all_eq_true] at h ⊢
    intro l hl'
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl'
    exact Level.allParamsDefined_subst hl hus (h l0 hl0)
  | _ =>
    intro h
    simp_all [instantiateLevelParams, allLevelParamsDefined]

/-- Binder opening keeps level parameters bounded. -/
theorem allLevelParamsDefined_instantiate1 {ps : List Name} {d : Nat} {n : Name} {ty : Expr}
    (hty : ty.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 (.fvar d n ty) k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro k h <;> simp_all [instantiate1, allLevelParamsDefined]
  case bvar i =>
    split
    · simpa [allLevelParamsDefined] using hty
    · split <;> simp [allLevelParamsDefined]

end Expr

end Setlec
