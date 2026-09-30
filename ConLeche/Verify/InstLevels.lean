module

import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
import ConLeche.Verify.Level
public import ConLeche.Verify.PropWhen
public import ConLeche.Verify.Subst

public section

/-!
# Syntactic lemmas about level-parameter instantiation

* commutation with binder opening (`instantiateLevelParams_instantiate1`),
* preservation of closedness and of level-parameter bounds.

Bound-preservation needs the original term to mention only
parameters from the substituted list *and* the lists to be aligned
(`us.length = ks.length`) — both checked by the checker before any
instantiation happens.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ConLeche

namespace Level

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
    | .forallE ty body m, h =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis,
        Option.isSome_map] at h ⊢
      exact ih h

/-- Level instantiation distributes over an application spine's
arguments. -/
theorem getAppArgs_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).getAppArgs =
      e.getAppArgs.map (·.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | app f a ihf iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs, ihf,
      List.map_append, List.map_cons, List.map_nil]
  | _ => simp [Expr.instantiateLevelParams, Expr.getAppArgs]

/-- Level instantiation preserves the head shape. -/
theorem getAppFn_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).getAppFn =
      e.getAppFn.instantiateLevelParams ks us := by
  intro e
  induction e with
  | app f a ihf iha => simpa [Expr.instantiateLevelParams, Expr.getAppFn]
      using ihf
  | _ => simp [Expr.instantiateLevelParams, Expr.getAppFn]

/-- A stripped telescope's body keeps its level parameters defined. -/
theorem allLevelParamsDefined_stripPis_body {ps : List Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) →
      e.allLevelParamsDefined ps = true →
      body.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h hp
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hp
  | succ k ih =>
    intro e bs body h hp
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hb, heq⟩ := h
      obtain ⟨-, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hp
      exact ih hb hp.1.2

/-- Level instantiation commutes with binder opening. -/
theorem instantiateLevelParams_instantiate1 (ks : List Name) (us : List Level)
    {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).instantiate1
          (.fvar d (ty.instantiateLevelParams ks us)) k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiate1, instantiateLevelParams]
  case bvar i =>
    split
    · rfl
    · split <;> simp [instantiateLevelParams]

/-- Binder opening keeps level parameters bounded. -/
theorem allLevelParamsDefined_instantiate1 {ps : List Name} {d : Nat} {ty : Expr}
    (hty : ty.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 (.fvar d ty) k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro k h <;> simp_all [instantiate1, allLevelParamsDefined]
  case bvar i =>
    split
    · simpa [allLevelParamsDefined] using hty
    · split <;> simp [allLevelParamsDefined]


end Expr


/-- Level instantiation distributes over an application spine. -/
theorem instantiateLevelParams_mkAppN (ks : List Name) (us : List Level) :
    ∀ (xs : List Expr) (h : Expr),
      (Expr.mkAppN h xs).instantiateLevelParams ks us =
        Expr.mkAppN (h.instantiateLevelParams ks us)
          (xs.map (fun x => x.instantiateLevelParams ks us))
  | [], _ => rfl
  | x :: xs, h => by
    show (Expr.mkAppN (.app h x) xs).instantiateLevelParams ks us = _
    rw [instantiateLevelParams_mkAppN ks us xs]
    rfl

/-- Substituting each level parameter by itself is the identity. -/
theorem Level.subst_param_self (ks : List Name) :
    ∀ l : Level, Level.subst ks (ks.map Level.param) l = l := by
  have hgo : ∀ (ks : List Name) (n : Name),
      Level.subst.go ks (ks.map Level.param) n = .param n := by
    intro ks
    induction ks with
    | nil => intro n; rfl
    | cons k ks ih =>
      intro n
      by_cases h : k = n
      · subst h; simp [Level.subst.go]
      · simp only [List.map_cons, Level.subst.go, if_neg h]
        exact ih n
  intro l
  induction l with
  | zero => rfl
  | succ l ih => simp [Level.subst, ih]
  | max l r ihl ihr => simp [Level.subst, ihl, ihr]
  | imax l r ihl ihr => simp [Level.subst, ihl, ihr]
  | param n => exact hgo ks n

/-- …and so is instantiating a declaration at its own parameters. -/
theorem Expr.instantiateLevelParams_self (ks : List Name) :
    ∀ e : Expr, e.instantiateLevelParams ks (ks.map Level.param) = e := by
  intro e
  have hmap : ∀ us : List Level,
      us.map (Level.subst ks (ks.map Level.param)) = us := by
    intro us
    induction us with
    | nil => rfl
    | cons x xs ih => simp [Level.subst_param_self, ih]
  induction e <;>
    simp_all [Expr.instantiateLevelParams, Level.subst_param_self, hmap,
      Level.substPW_self]

end ConLeche
