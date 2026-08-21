import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps
import Setlec.Verify.Level
import Setlec.Verify.Subst

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

/-- Level instantiation distributes over a `∀`-telescope's
decomposition. -/
theorem stripPis_instantiateLevelParams_eq (ks : List Name)
    (us : List Level) :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr},
      e.stripPis k = some (bs, body) →
      (e.instantiateLevelParams ks us).stripPis k = some (bs', body') →
      body' = body.instantiateLevelParams ks us ∧
      ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.2.1 = b.2.1.instantiateLevelParams ks us := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' h1 h2
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' h1 h2
    match e, h1 with
    | .forallE n d b m, h1 =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis] at h1 h2
      cases hs1 : b.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiateLevelParams ks us).stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (n, d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (n, d.instantiateLevelParams ks us,
            ⟨m.bi, m.cod.map (Level.subst ks us)⟩) :: p2.1 = bs' ∧
            p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih hs1 hs2
      refine ⟨hbody, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        exact hdoms i bb bb' hbb hbb'

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

/-- Renaming along the identity is the identity. -/
theorem renameConsts_id :
    ∀ (e : Expr), e.renameConsts (fun n => n) = e := by
  intro e
  induction e <;> simp_all [Expr.renameConsts]

/-- Lambda-telescope decomposition distributes over level
instantiation. -/
theorem stripLams_instantiateLevelParams_eq (ks : List Name)
    (us : List Level) :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Name × Expr × BinderMeta)}
      {body body' : Expr},
      e.stripLams k = some (bs, body) →
      (e.instantiateLevelParams ks us).stripLams k = some (bs', body') →
      body' = body.instantiateLevelParams ks us ∧
      ∀ (i : Nat) (b b' : Name × Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.2.1 = b.2.1.instantiateLevelParams ks us := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' h1 h2
    simp only [Expr.stripLams, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' h1 h2
    match e, h1 with
    | .lam n d b m, h1 =>
      simp only [Expr.instantiateLevelParams, Expr.stripLams] at h1 h2
      cases hs1 : b.stripLams k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiateLevelParams ks us).stripLams k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (n, d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (n, d.instantiateLevelParams ks us,
            ⟨m.bi, m.cod.map (Level.subst ks us)⟩) :: p2.1 = bs' ∧
            p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih hs1 hs2
      refine ⟨hbody, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        exact hdoms i bb bb' hbb hbb'

/-- Level instantiation commutes with bvar lifting. -/
theorem instantiateLevelParams_liftLooseBVars (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr) (k c : Nat),
      (e.liftLooseBVars k c).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).liftLooseBVars k c := by
  intro e
  induction e with
  | bvar i =>
    intro k c
    simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams]
    split <;> simp [Expr.instantiateLevelParams]
  | _ =>
    intro k c
    simp_all [Expr.liftLooseBVars, Expr.instantiateLevelParams]

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
    ∀ (k : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
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
    | .forallE n ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hb, heq⟩ := h
      obtain ⟨-, rfl⟩ : (n, ty, m) :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hp
      exact ih hb hp.1.2

/-- Application-spine members keep their level parameters defined. -/
theorem allLevelParamsDefined_getAppArgs {ps : List Name} :
    ∀ {e : Expr}, e.allLevelParamsDefined ps = true →
      ∀ x ∈ e.getAppArgs, x.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hb x hx
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    rcases hx with hx | rfl
    · exact ihf hb.1 x hx
    · exact hb.2
  | _ => intro hb x hx; simp [Expr.getAppArgs] at hx

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

/-- Renaming constants commutes with instantiation (general argument). -/
theorem renameConsts_instantiate1_gen (f : Name → Name) {v : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 v k).renameConsts f =
        (e.renameConsts f).instantiate1 (v.renameConsts f) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1, Expr.renameConsts]
    split
    · rfl
    · split <;> simp [Expr.renameConsts]
  | _ =>
    intro k
    simp_all [Expr.instantiate1, Expr.renameConsts]

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

/-- Renaming an instantiation sequence: pushing the renaming inside is
exact on the telescope and erased on the (fvar) arguments. -/
theorem instSeq_renameConsts {f : Name → Name} :
    ∀ (args : List Expr) (t : Nat) {X : Expr},
      (∀ a ∈ args, ErasedEq (a.renameConsts f) a) →
      ErasedEq ((instSeq args t X).renameConsts f)
        (instSeq args t (X.renameConsts f)) := by
  intro args
  induction args with
  | nil => intro t X _; exact ErasedEq.rfl _
  | cons a as ih =>
    intro t X ha
    show ErasedEq
      ((instSeq as (t - 1) (X.instantiate1 a t)).renameConsts f) _
    refine ErasedEq.trans
      (ih (t - 1) (fun x hx => ha x (List.mem_cons_of_mem _ hx))) ?_
    rw [renameConsts_instantiate1_gen]
    exact instSeq_erasedEq as (t - 1)
      (ErasedEq.instantiate1 (ErasedEq.rfl _)
        (ha a List.mem_cons_self))

/-- Level instantiation distributes over an opening-variable
instantiation sequence. -/
theorem instSeq_instantiateLevelParams_fvars (ks : List Name)
    (us : List Level) :
    ∀ (args : List Expr) (t : Nat) (e : Expr),
      (∀ a ∈ args, ∃ i n ty, a = .fvar i n ty) →
      (instSeq args t e).instantiateLevelParams ks us =
      instSeq (args.map (·.instantiateLevelParams ks us)) t
        (e.instantiateLevelParams ks us) := by
  intro args
  induction args with
  | nil => intro t e _; rfl
  | cons x xs ih =>
    intro t e hfv
    obtain ⟨i, n, ty, rfl⟩ := hfv x List.mem_cons_self
    show (instSeq xs (t - 1)
        (e.instantiate1 (.fvar i n ty) t)).instantiateLevelParams ks us = _
    rw [ih (t - 1) _ (fun y hy => hfv y (List.mem_cons_of_mem _ hy))]
    rw [instantiateLevelParams_instantiate1]
    rfl


/-- Defined level parameters survive an opening-variable instantiation
sequence whose variables carry parameter-defined types. -/
theorem allLevelParamsDefined_instSeq_fvars {ps : List Name} :
    ∀ (args : List Expr) (t : Nat) {e : Expr},
      (∀ a ∈ args, a.allLevelParamsDefined ps = true ∧
        ∃ i n ty, a = .fvar i n ty) →
      e.allLevelParamsDefined ps = true →
      (instSeq args t e).allLevelParamsDefined ps = true := by
  intro args
  induction args with
  | nil => intro t e _ he; exact he
  | cons a as ih =>
    intro t e hargs he
    obtain ⟨hlpd, i, n, ty, rfl⟩ := hargs a List.mem_cons_self
    exact ih (t - 1)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
      (allLevelParamsDefined_instantiate1
        (by simpa [Expr.allLevelParamsDefined] using hlpd) t he)

end Expr

end Setlec
