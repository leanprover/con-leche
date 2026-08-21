import Setlec.Verify.InferLemmas
import Setlec.Verify.Leaves
import Setlec.Verify.Subst
import Setlec.Verify.Abstract

/-!
# Leaf-closure and loose-bvar preservation for `whnf` and `inferTypeCore`

Reduction and inference only ever *copy* material from the input (delta
unfoldings are closed), so their outputs' free-variable leaves are a
subset of the input's — which transports every leaf-closure condition
(`FvarsOk`, `LeavesBounded`, `LeafCond`) for free.  Loose-bvar bounds
are threaded via `LeavesBounded` (the `fvar` rule jumps into the
annotation).
-/

namespace Setlec

open Expr

/-- Every leaf annotation is bvar-closed. -/
def Expr.LeavesBounded (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, Expr.looseBVarsBounded 0 l.2.2 = true

/-- The per-index leaf condition backing `fvarConsistent`. -/
def Expr.LeafCond (d : Nat) (n : Name) (ty : Expr) (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.1 = d → l.2.1 = n ∧ l.2.2 = ty

theorem Expr.fvarConsistent_of_leafCond {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr), Expr.LeafCond d n ty e → fvarConsistent d n ty e := by
  intro e
  induction e with
  | fvar idx n' ty' ih =>
    intro hc
    simp only [fvarConsistent]
    intro hd
    exact hc (idx, n', ty') (by simp [fvarLeaves]) hd
  | app f a ihf iha =>
    intro hc
    exact ⟨ihf (fun l hl => hc l (by simp [fvarLeaves, hl])),
      iha (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | lam n' ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | forallE n' ty' body m ihty ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | letE n' ty' val body ihty ihval ihbody =>
    intro hc
    exact ⟨ihty (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihval (fun l hl => hc l (by simp [fvarLeaves, hl])),
      ihbody (fun l hl => hc l (by simp [fvarLeaves, hl]))⟩
  | proj s i e ih =>
    intro hc
    exact ih (fun l hl => hc l (by simp [fvarLeaves, hl]))
  | _ => intro _; simp [fvarConsistent]

/-- The leaf condition holds for a freshly opened binder body. -/
theorem Expr.LeafCond_opened {d : Nat} {n : Name} {ty body : Expr}
    (hwty : WScoped d ty) (hwbody : WScoped d body) (k : Nat) :
    Expr.LeafCond d n ty (body.instantiate1 (.fvar d n ty) k) := by
  intro l hl hld
  rcases fvarLeaves_instantiate1 body k hl with hl' | hl'
  · obtain ⟨hlt, -⟩ := WScoped_leaves body hwbody l hl'
    omega
  · simp only [fvarLeaves, List.mem_cons] at hl'
    rcases hl' with rfl | hl'
    · exact ⟨rfl, rfl⟩
    · obtain ⟨hlt, -⟩ := WScoped_leaves ty hwty l hl'
      omega

/-- Abstraction removes exactly the index-`d` leaves (for scoped terms). -/
theorem Expr.fvarLeaves_abstract1_ne {D : Nat} :
    ∀ (e : Expr) (k : Nat), WScoped (D + 1) e →
      ∀ l ∈ (e.abstract1 D k).fvarLeaves, l ∈ e.fvarLeaves ∧ l.1 ≠ D := by
  intro e
  induction e with
  | fvar idx n ty ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1] at hl
    split at hl
    · simp [fvarLeaves] at hl
    · next hne =>
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨by simp [fvarLeaves], hne⟩
      · obtain ⟨hlt, -⟩ := WScoped_leaves ty hw.2 l hl
        exact ⟨by simp [fvarLeaves, hl], by omega⟩
  | app f a ihf iha =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihf k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := iha k hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | lam n ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | forallE n ty body m ihty ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with hl | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves, List.mem_append] at hl ⊢
    rcases hl with (hl | hl) | hl
    · obtain ⟨h1, h2⟩ := ihty k hw.1 l hl
      exact ⟨Or.inl (Or.inl h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihval k hw.2.1 l hl
      exact ⟨Or.inl (Or.inr h1), h2⟩
    · obtain ⟨h1, h2⟩ := ihbody (k + 1) hw.2.2 l hl
      exact ⟨Or.inr h1, h2⟩
  | proj s i e ih =>
    intro k hw l hl
    simp only [WScoped] at hw
    simp only [abstract1, fvarLeaves] at hl ⊢
    exact ih k hw l hl
  | bvar i => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | sort u => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | const n us => intro k _ l hl; simp [abstract1, fvarLeaves] at hl
  | lit ll => intro k _ l hl; simp [abstract1, fvarLeaves] at hl

theorem Expr.LeavesBounded.of_not_hasFvar {e : Expr} (h : e.hasFvar = false) :
    Expr.LeavesBounded e := by
  intro l hl
  rw [fvarLeaves_eq_nil_of_not_hasFvar h] at hl
  cases hl

theorem fvarLeaves_getAppArgs :
    ∀ {e x : Expr}, x ∈ e.getAppArgs → ∀ l ∈ x.fvarLeaves, l ∈ e.fvarLeaves := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro x hx l hl
    simp only [getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [fvarLeaves, List.mem_append]
    rcases hx with hx | rfl
    · exact Or.inl (ihf hx l hl)
    · exact Or.inr hl
  | _ => intro x hx; simp [getAppArgs] at hx

theorem looseBVarsBounded_mkAppN {k : Nat} : ∀ {xs : List Expr} {f : Expr},
    f.looseBVarsBounded k = true → (∀ x ∈ xs, x.looseBVarsBounded k = true) →
    (Expr.mkAppN f xs).looseBVarsBounded k = true := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    simp only [Expr.mkAppN]
    refine ih ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [looseBVarsBounded, Bool.and_eq_true]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem fvarLeaves_mkAppN : ∀ {xs : List Expr} {f : Expr}
    {l : Nat × Name × Expr},
    l ∈ (Expr.mkAppN f xs).fvarLeaves →
    l ∈ f.fvarLeaves ∨ ∃ x, x ∈ xs ∧ l ∈ x.fvarLeaves := by
  intro xs
  induction xs with
  | nil => intro f l hl; exact Or.inl hl
  | cons x xs ih =>
    intro f l hl
    simp only [Expr.mkAppN] at hl
    rcases ih hl with hl' | ⟨y, hy, hly⟩
    · simp only [fvarLeaves, List.mem_append] at hl'
      rcases hl' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨x, List.mem_cons_self, h⟩
    · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩

/-! ## Preservation through `whnf` -/

/-- The constructor form of a literal has no leaves. -/
theorem natLitToConstructor_fvarLeaves (n : Nat) :
    (natLitToConstructor n).fvarLeaves = [] := by
  cases n <;> simp [natLitToConstructor, Expr.fvarLeaves]

/-- The constructor form of a literal has no loose bvars. -/
theorem natLitToConstructor_looseBVars (n : Nat) {k : Nat} :
    (natLitToConstructor n).looseBVarsBounded k = true := by
  cases n <;> simp [natLitToConstructor, Expr.looseBVarsBounded]

/-- The literal-major conversion only shrinks the leaf closure. -/
theorem litToCtorIfNat_fvarLeaves {env : Env} {e : Expr} :
    ∀ l ∈ (litToCtorIfNat env e).fvarLeaves, l ∈ e.fvarLeaves := by
  intro l hl
  match e, hl with
  | .lit (.natVal n), hl =>
    rw [litToCtorIfNat] at hl
    split at hl
    · rw [natLitToConstructor_fvarLeaves] at hl
      cases hl
    · exact hl
  | .lit (.strVal _), hl => exact hl
  | .bvar _, hl | .fvar _ _ _, hl | .sort _, hl | .const _ _, hl
  | .app _ _, hl | .lam _ _ _ _, hl | .forallE _ _ _ _, hl
  | .letE _ _ _ _, hl | .proj _ _ _, hl => exact hl

/-- The literal-major conversion preserves the bvar bound. -/
theorem litToCtorIfNat_looseBVars {env : Env} {e : Expr} {k : Nat}
    (hb : e.looseBVarsBounded k = true) :
    (litToCtorIfNat env e).looseBVarsBounded k = true := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · exact natLitToConstructor_looseBVars n
    · exact hb
  | .lit (.strVal _) => exact hb
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _ | .proj _ _ _ =>
    exact hb

/-- Unfolding a definition at the head only shrinks the leaf
closure. -/
theorem unfoldDefinition_fvarLeaves {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} (h : unfoldDefinition env e = some e₂) :
    ∀ l ∈ e₂.fvarLeaves, l ∈ e.fvarLeaves := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    intro l hl
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨hvc, -, -, -⟩ := hval cv value hint rfl
    rcases fvarLeaves_mkAppN hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar
        (by rw [hasFvar_instantiateLevelParams]; exact hvc)] at hl'
      cases hl'
    · exact fvarLeaves_getAppArgs hx l hlx
  · intro h; exact nomatch h

/-- Unfolding a definition at the head preserves the bvar bound. -/
theorem unfoldDefinition_looseBVars {env : Env} (henv : EnvWF env)
    {e e₂ : Expr} (h : unfoldDefinition env e = some e₂)
    (hb : e.looseBVarsBounded 0 = true) :
    e₂.looseBVarsBounded 0 = true := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨-, -, -, -, hval, -⟩ := henv _ (find?_mem hf)
    obtain ⟨-, -, -, hvb⟩ := hval cv value hint rfl
    refine looseBVarsBounded_mkAppN ?_ ?_
    · rw [looseBVarsBounded_instantiateLevelParams]
      exact hvb
    · intro x hx
      exact looseBVarsBounded_getAppArgs hb x hx
  · intro h; exact nomatch h

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop only shrink the leaf
closure. -/
theorem whnfPres_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf env fuel d e = .ok e' →
        ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves)
  | 0 => ⟨(fun {_ _ _} h => nomatch h), (fun {_ _ _} h => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_fvarLeaves henv fuel
    constructor
    · -- whnfCore
      intro d e e' h
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | fvar idx n ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | forallE n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | lam n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | lit l0 =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ fun l hl => hl
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE nn tt vv bb =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | app f a =>
        intro l hl
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        simp only [fvarLeaves, List.mem_append]
        rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · have hl' := ihCore hbeta l hl
          rcases fvarLeaves_instantiate1 body 0 hl' with hb | hb
          · exact Or.inl (ihCore hwf l (by simp [fvarLeaves, hb]))
          · exact Or.inr hb
        · -- iota step
          obtain ⟨c, us, cv, nP, nM, nm, ni, rules, major₀, major, cj, usj,
            cvj, cnP, cnF, r, -, -, -, -, -, hfn, hfc, hlen, hmaj, hsub, hmfn, hfj,
            hrule,
            hml1, hml2, har1, har2, hlev, hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ :=
            iotaRec_inv hio
          have hsubM : ∀ l ∈ major.fvarLeaves, l ∈ major₀.fvarLeaves := by
            rcases majorToCtor_inv hsub with rfl | ⟨-, -, hall, -⟩
            · exact fun l' hl' => litToCtorIfNat_fvarLeaves l' hl'
            · intro l' hl'
              have := List.all_eq_true.mp hall l' hl'
              exact litToCtorIfNat_fvarLeaves l' (by simpa using this)
          have hl2 := ihCore hwe'' l hl
          rcases fvarLeaves_mkAppN hl2 with hrl | ⟨x, hx, hlx⟩
          · obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
            obtain ⟨hrf, -, -, -⟩ := hrules cv nP nM nm ni rules rfl r
              (List.mem_of_find?_eq_some hrule)
            rw [fvarLeaves_eq_nil_of_not_hasFvar
              (by rw [hasFvar_instantiateLevelParams]; exact hrf)] at hrl
            cases hrl
          · rcases List.mem_append.mp hx with hx | hx
            · have hll := fvarLeaves_getAppArgs (List.mem_of_mem_take hx)
                l hlx
              simp only [fvarLeaves, List.mem_append] at hll
              rcases hll with hll | hll
              · exact Or.inl (ihCore hwf l hll)
              · exact Or.inr hll
            · have hxa := fvarLeaves_getAppArgs (List.mem_of_mem_drop hx)
                l hlx
              have hmj := ihLoop hmaj l (hsubM l hxa)
              have hll := fvarLeaves_getAppArgs
                (getD_mem (l := (Expr.app f' a).getAppArgs) (by omega)) l hmj
              simp only [fvarLeaves, List.mem_append] at hll
              rcases hll with hll | hll
              · exact Or.inl (ihCore hwf l hll)
              · exact Or.inr hll
        · simp only [fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact Or.inl (ihCore hwf l hl)
          · exact Or.inr hl
      | proj sn i pe =>
        intro l hl
        obtain ⟨e₂, he, hcase⟩ := whnf_proj_inv h
        simp only [fvarLeaves]
        rcases hcase with rfl |
          ⟨us, cv, nP, nF, hfn, hf, hi, hlen, hus, hred, -⟩
        · simp only [fvarLeaves] at hl
          exact ihLoop he l hl
        · have hl2 := ihCore hred l hl
          exact ihLoop he l
            (fvarLeaves_getAppArgs (getD_mem (by omega)) l hl2)
    · -- whnf loop
      intro d e e' h l hl
      obtain ⟨e₁, hwc, hcase⟩ := whnf_loop_inv h
      rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
      · rcases reduceNat_inv hrn with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
        · have := ihLoop hcont l hl
          simp [Expr.fvarLeaves] at this
      · exact ihCore hwc l
          (unfoldDefinition_fvarLeaves henv hu l (ihLoop hcont l hl))
      · exact ihCore hwc l hl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
/-- Head normalization and the reduction loop preserve the bvar
bound. -/
theorem whnfPres_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat),
      (∀ {d : Nat} {e e' : Expr}, whnfCore env fuel d e = .ok e' →
        e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf env fuel d e = .ok e' →
        e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true)
  | 0 => ⟨(fun {_ _ _} h _ => nomatch h), (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1 => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_looseBVars henv fuel
    constructor
    · -- whnfCore
      intro d e e' h hb
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | fvar idx n ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | forallE n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | lam n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | lit l0 =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
        exact h ▸ hb
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE nn tt vv bb =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | app f a =>
        simp only [looseBVarsBounded, Bool.and_eq_true] at hb
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hbf' := ihCore hwf hb.1
        rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · simp only [looseBVarsBounded, Bool.and_eq_true] at hbf'
          exact ihCore hbeta
            (looseBVarsBounded_instantiate1_gen hb.2 hbf'.2)
        · -- iota step
          obtain ⟨c, us, cv, nP, nM, nm, ni, rules, major₀, major, cj, usj,
            cvj, cnP, cnF, r, -, -, -, -, -, hfn, hfc, hlen, hmaj, hsub, hmfn, hfj,
            hrule,
            hml1, hml2, har1, har2, hlev, hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ :=
            iotaRec_inv hio
          have hbapp : (Expr.app f' a).looseBVarsBounded 0 = true := by
            simp only [looseBVarsBounded, Bool.and_eq_true]
            exact ⟨hbf', hb.2⟩
          have hbmaj0 : major₀.looseBVarsBounded 0 = true :=
            ihLoop hmaj
              (looseBVarsBounded_getAppArgs hbapp _ (getD_mem (by omega)))
          have hbmaj : major.looseBVarsBounded 0 = true := by
            rcases majorToCtor_inv hsub with rfl | ⟨-, hbM, -, -⟩
            · exact litToCtorIfNat_looseBVars hbmaj0
            · exact hbM
          refine ihCore hwe'' ?_
          refine looseBVarsBounded_mkAppN ?_ ?_
          · obtain ⟨-, -, -, -, -, hrules⟩ := henv _ (find?_mem hfc)
            obtain ⟨-, -, -, hrb⟩ := hrules cv nP nM nm ni rules rfl r
              (List.mem_of_find?_eq_some hrule)
            rw [looseBVarsBounded_instantiateLevelParams]
            exact hrb
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact looseBVarsBounded_getAppArgs hbapp _
                (List.mem_of_mem_take hx)
            · exact looseBVarsBounded_getAppArgs hbmaj _
                (List.mem_of_mem_drop hx)
        · simp only [looseBVarsBounded, Bool.and_eq_true]
          exact ⟨hbf', hb.2⟩
      | proj sn i pe =>
        simp only [looseBVarsBounded] at hb
        obtain ⟨e₂, he, hcase⟩ := whnf_proj_inv h
        have hbe₂ := ihLoop he hb
        rcases hcase with rfl |
          ⟨us, cv, nP, nF, hfn, hf, hi, hlen, hus, hred, -⟩
        · simpa [looseBVarsBounded] using hbe₂
        · exact ihCore hred
            (looseBVarsBounded_getAppArgs hbe₂ _ (getD_mem (by omega)))
    · -- whnf loop
      intro d e e' h hb
      obtain ⟨e₁, hwc, hcase⟩ := whnf_loop_inv h
      have hbe₁ := ihCore hwc hb
      rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
      · rcases reduceNat_inv hrn with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;>
          exact ihLoop hcont (by simp [looseBVarsBounded])
      · exact ihLoop hcont (unfoldDefinition_looseBVars henv hu hbe₁)
      · exact hbe₁

/-- Head normalization only shrinks the leaf closure. -/
theorem whnfCore_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_fvarLeaves henv fuel).1 h

/-- The reduction loop only shrinks the leaf closure. -/
theorem whnf_fvarLeaves {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf env fuel d e = .ok e') :
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves :=
  (whnfPres_fvarLeaves henv fuel).2 h

/-- Head normalization preserves the bvar bound. -/
theorem whnfCore_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnfCore env fuel d e = .ok e')
    (hb : e.looseBVarsBounded 0 = true) : e'.looseBVarsBounded 0 = true :=
  (whnfPres_looseBVars henv fuel).1 h hb

/-- The reduction loop preserves the bvar bound. -/
theorem whnf_looseBVars {env : Env} (henv : EnvWF env)
    (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf env fuel d e = .ok e')
    (hb : e.looseBVarsBounded 0 = true) : e'.looseBVarsBounded 0 = true :=
  (whnfPres_looseBVars henv fuel).2 h hb

/-! ## Preservation through `inferTypeCore` -/

theorem inferTypeCore_WScoped {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e → WScoped d t
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [WScoped]
    | fvar idx n ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [WScoped] at hw
      exact hw.2.mono (by omega)
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          exact WScoped.of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?_
      | .strVal s, h =>
        simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [Except.ok.injEq] at h
        subst h; simp [WScoped]
    | forallE n ty body m =>
      cases hc : m.cod with
      | none =>
        rw [inferTypeCore_succ] at h
        simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, hc] at h
        exact nomatch h
      | some v =>
      obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hc h
      simp [WScoped]
    | lam n ty body m =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, -, -, hbt, -, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      simp only [WScoped]
      exact ⟨hw.1, WScoped.abstract1 0 hwbt⟩
    | app f a =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, -, -, rfl⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      have hwtf := inferTypeCore_WScoped henv fuel htf hw.1
      have hwPi := whnf_WScoped henv fuel hwh hwtf
      simp only [WScoped] at hwPi
      exact WScoped.instantiate1_gen hw.2 0 hwPi.2
    | proj sn i pe =>
      obtain ⟨te, us, A, B, cv2, caps2, hte, hwt, hfind2, hcase⟩ :=
        inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      have hwte := inferTypeCore_WScoped henv fuel hte hw
      have hwPi := whnf_WScoped henv fuel hwt hwte
      simp only [WScoped] at hwPi
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hwPi.1.2
      · simp only [WScoped]
        exact ⟨hwPi.2, hw⟩
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

theorem inferTypeCore_fvarLeaves {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e →
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves
  | 0, d, e, t, h, _ => nomatch h
  | fuel + 1, d, e, t, h, hw => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; intro l hl; simp [fvarLeaves] at hl
    | fvar idx n ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro l hl
      simp [fvarLeaves, hl]
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨htc, -, -, -, -⟩ := henv _ (find?_mem hf)
          intro l hl
          rw [fvarLeaves_eq_nil_of_not_hasFvar
            (by rw [hasFvar_instantiateLevelParams]; exact htc)] at hl
          cases hl
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?_
      | .strVal s, h =>
        simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [Except.ok.injEq] at h
        subst h; intro l hl; simp [fvarLeaves] at hl
    | forallE n ty body m =>
      cases hc : m.cod with
      | none =>
        rw [inferTypeCore_succ] at h
        simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, hc] at h
        exact nomatch h
      | some v =>
      obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hc h
      intro l hl
      simp [fvarLeaves] at hl
    | lam n ty body m =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, -, -, hbt, -, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hwbt := inferTypeCore_WScoped henv fuel hbt hwo
      intro l hl
      simp only [fvarLeaves, List.mem_append] at hl ⊢
      rcases hl with hl | hl
      · exact Or.inl hl
      · obtain ⟨hlbt, hlne⟩ := fvarLeaves_abstract1_ne bt 0 hwbt l hl
        have hlo := inferTypeCore_fvarLeaves henv fuel hbt hwo l hlbt
        rcases fvarLeaves_instantiate1 body 0 hlo with hb | hb
        · exact Or.inr hb
        · simp only [fvarLeaves, List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact absurd rfl hlne
          · exact Or.inl hb
    | app f a =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, -, -, rfl⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves, List.mem_append]
      rcases fvarLeaves_instantiate1 body' 0 hl with hb | hb
      · refine Or.inl (inferTypeCore_fvarLeaves henv fuel htf hw.1 l ?_)
        refine whnf_fvarLeaves henv fuel hwh l ?_
        simp [fvarLeaves, hb]
      · exact Or.inr hb
    | proj sn i pe =>
      obtain ⟨te, us, A, B, cv2, caps2, hte, hwt, hfind2, hcase⟩ :=
        inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      intro l hl
      simp only [fvarLeaves]
      have hsub : ∀ l', l' ∈
          (Expr.app (Expr.app (.const psigmaName us) A) B).fvarLeaves →
          l' ∈ pe.fvarLeaves := fun l' hl' =>
        inferTypeCore_fvarLeaves henv fuel hte hw l'
          (whnf_fvarLeaves henv fuel hwt l' hl')
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hsub l (by simp [fvarLeaves, hl])
      · simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hsub l (by simp [fvarLeaves, hl])
        · simpa [fvarLeaves] using hl
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

theorem inferTypeCore_looseBVars {env : Env} (henv : EnvWF env) :
    ∀ (fuel : Nat) {d : Nat} {e t : Expr},
      inferTypeCore env fuel d e = .ok t → WScoped d e →
      e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      t.looseBVarsBounded 0 = true
  | 0, d, e, t, h, _, _, _ => nomatch h
  | fuel + 1, d, e, t, h, hw, hb, hLb => by
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; simp [looseBVarsBounded]
    | fvar idx n ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hLb (idx, n, ty) (by simp [fvarLeaves])
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨-, -, -, htb, -⟩ := henv _ (find?_mem hf)
          rw [looseBVarsBounded_instantiateLevelParams]
          exact htb
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?_
      | .strVal s, h =>
        simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue =>
        intro h
        simp only [Except.ok.injEq] at h
        subst h; simp [looseBVarsBounded]
    | forallE n ty body m =>
      cases hc : m.cod with
      | none =>
        rw [inferTypeCore_succ] at h
        simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, hc] at h
        exact nomatch h
      | some v =>
      obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hc h
      simp [looseBVarsBounded]
    | lam n ty body m =>
      obtain ⟨v, tty, u, bt, tbt, v', hc, -, -, hbt, -, -, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
        hw.1.instantiate1 0 hw.2
      have hbo : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0
          = true := looseBVarsBounded_instantiate1 body 0 hb.2
      have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
        · exact hLb l (by simp [fvarLeaves, hb'])
        · simp only [fvarLeaves, List.mem_cons] at hb'
          rcases hb' with rfl | hb'
          · exact hb.1
          · exact hLb l (by simp [fvarLeaves, hb'])
      have hbbt := inferTypeCore_looseBVars henv fuel hbt hwo hbo hLbo
      simp only [looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hb.1, looseBVarsBounded_abstract1 bt 0 hbbt⟩
    | app f a =>
      obtain ⟨tf, n', ty', body', m', ta, htf, hwh, -, -, rfl⟩ :=
        inferTypeCore_app_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      have hLbf : Expr.LeavesBounded f := fun l hl =>
        hLb l (by simp [fvarLeaves, hl])
      have hbtf := inferTypeCore_looseBVars henv fuel htf hw.1 hb.1 hLbf
      have hbPi := whnf_looseBVars henv fuel hwh hbtf
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      exact looseBVarsBounded_instantiate1_gen hb.2 hbPi.2
    | proj sn i pe =>
      obtain ⟨te, us, A, B, cv2, caps2, hte, hwt, hfind2, hcase⟩ :=
        inferTypeCore_proj_inv h
      simp only [WScoped] at hw
      simp only [looseBVarsBounded] at hb
      have hLbe : Expr.LeavesBounded pe := fun l hl => hLb l (by
        simp only [fvarLeaves]; exact hl)
      have hbte := inferTypeCore_looseBVars henv fuel hte hw hb hLbe
      have hbPi := whnf_looseBVars henv fuel hwt hbte
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
      rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hbPi.1.2
      · simp only [looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hbPi.2, hb⟩
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h

end Setlec
