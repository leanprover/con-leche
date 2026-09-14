module

public import ConLeche.Verify.ProjSlots

public section

/-!
# The literal clauses of `constsResolve`, and what preserves them

`denoteMeta`'s literal arms are guarded (`natLitSupported` /
`strLitSupported`): a `.lit` node denotes only where the environment
stores the constants the encoding names.  The DOWNWARD transfer
(`denoteMeta_envExtend_down`, task #310) therefore asks a condition on
its SUBJECT — `litsResolve env e`, `constsResolve` minus its `.const`
and `.proj` clauses and blind to `fvar` annotations exactly as
`Expr.blank` is.

This module is that condition's home: the guard itself, the bridge
from resolution (`litsResolve_of_constsResolve`), and the closure kit
the syntactic walks need (`Expr.LitsOk`, the `Prop` form, with the
clause equations and the substitution, abstraction, telescope and
spine lemmas).  Every fact here is about `Env.find?` alone, so it sits
below both the annotation tier that states the condition and the
inductive-elimination walks that establish it (task #311).
-/

namespace ConLeche

open ConLeche.Expr

/-- **The literal guard as a condition on the subject**:
`Expr.constsResolve` restricted to its `.lit` clauses.  A `.const`
node passes unconditionally (the blind mentions are the other
currency), a `.fvar` node's annotation is not read (the blank is
blind to it), and a `.proj` node's own structure name is not read
(the slot is the third condition's business). -/
@[expose] def litsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ | .fvar _ _ | .const _ _ => true
  | .lit (.natVal _) =>
    (env.find? ConLeche.natName).isSome && (env.find? ConLeche.natZeroName).isSome &&
      (env.find? ConLeche.natSuccName).isSome
  | .lit (.strVal _) =>
    (env.find? ConLeche.natName).isSome && (env.find? ConLeche.natZeroName).isSome &&
      (env.find? ConLeche.natSuccName).isSome && (env.find? ConLeche.stringName).isSome &&
      (env.find? ConLeche.stringOfListName).isSome && (env.find? ConLeche.listName).isSome &&
      (env.find? ConLeche.listNilName).isSome && (env.find? ConLeche.listConsName).isSome &&
      (env.find? ConLeche.charName).isSome && (env.find? ConLeche.charOfNatName).isSome
  | .app f a => litsResolve env f && litsResolve env a
  | .lam ty body _ | .forallE ty body _ => litsResolve env ty && litsResolve env body
  | .letE ty val body =>
    litsResolve env ty && litsResolve env val && litsResolve env body
  | .proj _ _ e => litsResolve env e

/-- A resolving term resolves its literals (`constsResolve`'s literal
clauses ARE these, and its other clauses only add). -/
theorem litsResolve_of_constsResolve {env : Env} :
    ∀ e : Expr, e.constsResolve env = true → litsResolve env e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ => rfl
  | .fvar _ _, _ => rfl
  | .lit (.natVal _), h => by simpa [litsResolve, Expr.constsResolve] using h
  | .lit (.strVal _), h => by simpa [litsResolve, Expr.constsResolve] using h
  | .app f a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve f h.1, litsResolve_of_constsResolve a h.2⟩
  | .lam ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve ty h.1, litsResolve_of_constsResolve b h.2⟩
  | .forallE ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_of_constsResolve ty h.1, litsResolve_of_constsResolve b h.2⟩
  | .letE ty v b, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve, Bool.and_eq_true]
    exact ⟨⟨litsResolve_of_constsResolve ty h.1.1, litsResolve_of_constsResolve v h.1.2⟩,
      litsResolve_of_constsResolve b h.2⟩
  | .proj _ _ e, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp only [litsResolve]
    exact litsResolve_of_constsResolve e h.2

/-- The literal clauses survive an instantiation whose value carries
them (the sequenced subjects of the nested route are built this
way). -/
theorem litsResolve_instantiate1 {env : Env} {v : Expr}
    (hv : litsResolve env v = true) :
    ∀ (e : Expr) (k : Nat), litsResolve env e = true →
      litsResolve env (e.instantiate1 v k) = true
  | .bvar i, k, _ => by
    simp only [ConLeche.Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ => rfl
  | .lit _, _, h => h
  | .app f a, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv f k h.1, litsResolve_instantiate1 hv a k h.2⟩
  | .lam ty b _, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv ty k h.1, litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .forallE ty b _, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨litsResolve_instantiate1 hv ty k h.1, litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .letE ty v' b, k, h => by
    simp only [litsResolve, Bool.and_eq_true] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve, Bool.and_eq_true]
    exact ⟨⟨litsResolve_instantiate1 hv ty k h.1.1, litsResolve_instantiate1 hv v' k h.1.2⟩,
      litsResolve_instantiate1 hv b (k + 1) h.2⟩
  | .proj _ _ e, k, h => by
    simp only [litsResolve] at h
    simp only [ConLeche.Expr.instantiate1, litsResolve]
    exact litsResolve_instantiate1 hv e k h

/-! ## `LitsOk`, the `Prop` form the walks carry -/

/-- The literal guard as a proposition — what a syntactic walk's
invariant carries. -/
@[expose] def Expr.LitsOk (env : Env) (e : Expr) : Prop := litsResolve env e = true

namespace Expr

variable {env : Env}

@[simp] theorem litsOk_bvar {j : Nat} : LitsOk env (.bvar j) := rfl

@[simp] theorem litsOk_sort {u : Level} : LitsOk env (.sort u) := rfl

@[simp] theorem litsOk_const {n : Name} {us : List Level} : LitsOk env (.const n us) := rfl

@[simp] theorem litsOk_fvar {idx : Nat} {ty : Expr} : LitsOk env (.fvar idx ty) := rfl

@[simp] theorem litsOk_app {f a : Expr} :
    LitsOk env (.app f a) ↔ LitsOk env f ∧ LitsOk env a := by
  simp [LitsOk, litsResolve]

@[simp] theorem litsOk_lam {ty b : Expr} {m : BinderMeta} :
    LitsOk env (.lam ty b m) ↔ LitsOk env ty ∧ LitsOk env b := by
  simp [LitsOk, litsResolve]

@[simp] theorem litsOk_forallE {ty b : Expr} {m : BinderMeta} :
    LitsOk env (.forallE ty b m) ↔ LitsOk env ty ∧ LitsOk env b := by
  simp [LitsOk, litsResolve]

@[simp] theorem litsOk_letE {t v b : Expr} :
    LitsOk env (.letE t v b) ↔ LitsOk env t ∧ LitsOk env v ∧ LitsOk env b := by
  simp [LitsOk, litsResolve, and_assoc]

@[simp] theorem litsOk_proj {s : Name} {j : Nat} {e : Expr} :
    LitsOk env (.proj s j e) ↔ LitsOk env e := by
  simp [LitsOk, litsResolve]

/-- A resolving term's literals are guarded. -/
theorem LitsOk.of_constsResolve {e : Expr} (h : e.constsResolve env = true) : LitsOk env e :=
  litsResolve_of_constsResolve e h

/-- The guard travels UP an extension: the support names it reads stay
stored. -/
theorem LitsOk.mono {env' : Env}
    (hm : ∀ n : Name, (env.find? n).isSome = true → (env'.find? n).isSome = true) :
    ∀ {e : Expr}, LitsOk env e → LitsOk env' e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .fvar _ _, _ => rfl
  | .lit (.natVal _), h => by
    simp only [LitsOk, litsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hm _ h.1.1, hm _ h.1.2⟩, hm _ h.2⟩
  | .lit (.strVal _), h => by
    simp only [LitsOk, litsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hm _ h.1.1.1.1.1.1.1.1.1, hm _ h.1.1.1.1.1.1.1.1.2⟩,
      hm _ h.1.1.1.1.1.1.1.2⟩, hm _ h.1.1.1.1.1.1.2⟩, hm _ h.1.1.1.1.1.2⟩,
      hm _ h.1.1.1.1.2⟩, hm _ h.1.1.1.2⟩, hm _ h.1.1.2⟩, hm _ h.1.2⟩, hm _ h.2⟩
  | .app f a, h => by
    rw [litsOk_app] at h
    exact litsOk_app.mpr ⟨LitsOk.mono hm h.1, LitsOk.mono hm h.2⟩
  | .lam ty b _, h => by
    rw [litsOk_lam] at h
    exact litsOk_lam.mpr ⟨LitsOk.mono hm h.1, LitsOk.mono hm h.2⟩
  | .forallE ty b _, h => by
    rw [litsOk_forallE] at h
    exact litsOk_forallE.mpr ⟨LitsOk.mono hm h.1, LitsOk.mono hm h.2⟩
  | .letE t v b, h => by
    rw [litsOk_letE] at h
    exact litsOk_letE.mpr ⟨LitsOk.mono hm h.1, LitsOk.mono hm h.2.1, LitsOk.mono hm h.2.2⟩
  | .proj _ _ e, h => by
    rw [litsOk_proj] at h
    exact litsOk_proj.mpr (LitsOk.mono hm h)

/-- Instantiation preserves the guard. -/
theorem LitsOk.instantiate1 {v : Expr} (hv : LitsOk env v) (e : Expr) (d : Nat)
    (he : LitsOk env e) : LitsOk env (e.instantiate1 v d) :=
  litsResolve_instantiate1 hv e d he

/-- An application spine's head and arguments carry the guard to the
spine. -/
theorem LitsOk.mkAppN :
    ∀ {as : List Expr} {f : Expr}, LitsOk env f → (∀ a ∈ as, LitsOk env a) →
      LitsOk env (Expr.mkAppN f as)
  | [], _, hf, _ => hf
  | a :: as, f, hf, has => by
    simp only [Expr.mkAppN]
    exact LitsOk.mkAppN (litsOk_app.mpr ⟨hf, has a List.mem_cons_self⟩)
      (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))

/-- … and back. -/
theorem LitsOk.getAppArgs : ∀ {e : Expr}, LitsOk env e → ∀ a ∈ e.getAppArgs, LitsOk env a
  | .app f a, h, b, hb => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hb
    rw [litsOk_app] at h
    rcases hb with hb | rfl
    · exact LitsOk.getAppArgs h.1 b hb
    · exact h.2
  | .bvar _, _, _, hb | .fvar _ _, _, _, hb | .sort _, _, _, hb | .const _ _, _, _, hb
  | .lam _ _ _, _, _, hb | .forallE _ _ _, _, _, hb | .letE _ _ _, _, _, hb | .lit _, _, _, hb
  | .proj _ _ _, _, _, hb => by simp [Expr.getAppArgs] at hb

/-- Instantiating a telescope preserves the guard. -/
theorem LitsOk.instPis :
    ∀ {e : Expr} {args : List Expr} {r : Expr}, Expr.instPis e args = some r →
      LitsOk env e → (∀ a ∈ args, LitsOk env a) → LitsOk env r
  | e, [], r, h, he, _ => by
    simp only [Expr.instPis, Option.some.injEq] at h
    subst h
    exact he
  | .forallE dom body m, a :: as, r, h, he, hargs => by
    simp only [Expr.instPis] at h
    rw [litsOk_forallE] at he
    exact LitsOk.instPis h
      (LitsOk.instantiate1 (hargs a List.mem_cons_self) body 0 he.2)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
  | .bvar _, _ :: _, _, h, _, _ | .fvar _ _, _ :: _, _, h, _, _ | .sort _, _ :: _, _, h, _, _
  | .const _ _, _ :: _, _, h, _, _ | .app _ _, _ :: _, _, h, _, _
  | .lam _ _ _, _ :: _, _, h, _, _ | .letE _ _ _, _ :: _, _, h, _, _
  | .lit _, _ :: _, _, h, _, _ | .proj _ _ _, _ :: _, _, h, _, _ => by
    simp [Expr.instPis] at h

/-- Abstraction moves no literal. -/
theorem LitsOk.abstract1 : ∀ (e : Expr) (d k : Nat), LitsOk env e → LitsOk env (e.abstract1 d k) := by
  intro e
  induction e with
  | bvar j => intro d k _; simp [Expr.abstract1]
  | sort u => intro d k _; simp [Expr.abstract1]
  | const n vs => intro d k _; simp [Expr.abstract1]
  | lit l => intro d k h; rw [Expr.abstract1]; exact h
  | fvar idx ty _ih =>
    intro d k _
    rw [Expr.abstract1]
    split <;> simp
  | app f a ihf iha =>
    intro d k h
    rw [litsOk_app] at h
    rw [Expr.abstract1, litsOk_app]
    exact ⟨ihf d k h.1, iha d k h.2⟩
  | lam ty b m ihty ihb =>
    intro d k h
    rw [litsOk_lam] at h
    rw [Expr.abstract1, litsOk_lam]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d k h
    rw [litsOk_forallE] at h
    rw [Expr.abstract1, litsOk_forallE]
    exact ⟨ihty d k h.1, ihb d (k + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d k h
    rw [litsOk_letE] at h
    rw [Expr.abstract1, litsOk_letE]
    exact ⟨iht d k h.1, ihval d k h.2.1, ihb d (k + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d k h
    rw [litsOk_proj] at h
    rw [Expr.abstract1, litsOk_proj]
    exact ihe d k h

/-- Level instantiation moves no literal. -/
theorem LitsOk.instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, LitsOk env e → LitsOk env (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | bvar j => intro _; simp [Expr.instantiateLevelParams]
  | sort u => intro _; simp [Expr.instantiateLevelParams]
  | const n vs => intro _; simp [Expr.instantiateLevelParams]
  | lit l => intro h; rw [Expr.instantiateLevelParams]; exact h
  | fvar idx ty _ih => intro _; simp [Expr.instantiateLevelParams]
  | app f a ihf iha =>
    intro h
    rw [litsOk_app] at h
    rw [Expr.instantiateLevelParams, litsOk_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    rw [litsOk_lam] at h
    rw [Expr.instantiateLevelParams, litsOk_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    rw [litsOk_forallE] at h
    rw [Expr.instantiateLevelParams, litsOk_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE t val b iht ihval ihb =>
    intro h
    rw [litsOk_letE] at h
    rw [Expr.instantiateLevelParams, litsOk_letE]
    exact ⟨iht h.1, ihval h.2.1, ihb h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [litsOk_proj] at h
    rw [Expr.instantiateLevelParams, litsOk_proj]
    exact ihe h

/-- The binder domains of a stripped telescope carry the guard. -/
theorem LitsOk.stripPis_doms :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis k = some (bs, body) → LitsOk env e → ∀ d ∈ bs, LitsOk env d.1
  | 0, e, bs, body, h, _ => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; intro d hd; exact absurd hd List.not_mem_nil
  | k + 1, e, bs, body, h, he => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [Expr.stripPis] at h
      cases hs : rest.stripPis k with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [litsOk_forallE] at he
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact he.1
        · exact LitsOk.stripPis_doms k hs he.2 d hd

end Expr

end ConLeche
