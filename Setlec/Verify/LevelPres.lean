import Setlec.Verify.BinderLoop
import Setlec.Verify.InferLeaves
import Setlec.Verify.InstLevels

/-!
# Level-parameter preservation for `whnf` and `inferTypeCore`

The level-side twin of `InferLeaves.lean`'s families: reduction and
inference introduce **no level parameter the subject does not already
have** — over a well-formed environment, and now with no exception at
all (`whnf_lvlParamsW`, `inferTypeCore_lvlParamsW`,
`iotaRec_lvlParamsW`).

Every site that could introduce a parameter instantiates a *stored*
expression at the level arguments of a `.const` node, and `EnvWF`
(`ConstWF`'s second conjunct) says a stored expression's parameters lie
among its declaration's own.  `Level.subst` then keeps them inside the
subject's — **provided the two lists have the same length**, which is
what `Level.allParamsDefined_subst` asks for and what a ragged
substitution really does lose (`subst.go` falls through to
`.param n`).

All four sites check that length themselves:

* `unfoldDefinition` (`Kernel/Core.lean:174`) — the delta step,
* `inferBody`'s `.const` clause (`Kernel/Core.lean:1566`),
* `inferBody`'s `.proj` clause (`us.length = entry.levelParams.length`),
* `iotaRec` — **since checker change #9**.  It used to guard only the
  spine length, the rule lookup, `Level.isEquivList` on the
  *constructor's* levels, the two `iotaCerts` and the index
  comparison, none of which relates `us` to `cv.levelParams`; the
  reduct `r.rhs.instantiateLevelParams cv.levelParams us` could then
  carry a parameter out of a short `us`.  That was a real countermodel
  (`Setlec/SetR/Interp2/IotaArity.lean`), and the guard closes it.

So the entry points here are unconditional.  The internal `hiota`
hypotheses are *fuel-bounded* — `whnf`/`inferTypeCore` at fuel `F` use
the iota fact only strictly below `F` — which is exactly what lets
`iotaRec_lvlParams_lt` tie the knot at the end of this file.
-/

namespace Setlec

open Expr

variable {mode : CheckMode}

section Kit
variable {ps : List Name}

/-- `substFn` reads the assignment only through the substituted levels'
parameters — the `ps`-indexed form (no length condition: a ragged
list falls through to the assignment itself, where the agreement
hypothesis answers directly). -/
theorem Level.substFn_agree {φ₁ φ₂ : Name → Nat} {ps : List Name}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ {ks : List Name} {us : List Level},
      (∀ u ∈ us, u.allParamsDefined ps = true) →
      ∀ p ∈ ps,
        Level.substFn φ₁ ks us p = Level.substFn φ₂ ks us p := by
  intro ks
  induction ks with
  | nil => intro us _ p hp; exact hφ p hp
  | cons k ks ih =>
    intro us hus p hp
    cases us with
    | nil => exact hφ p hp
    | cons u us =>
      simp only [Level.substFn]
      split
      · exact Level.eval_ext (hus u (by simp)) hφ
      · exact ih (fun x hx => hus x (by simp [hx])) p hp

/-- Opening a binder keeps the level parameters bounded. -/
theorem Expr.allLevelParamsDefined_instantiate1_gen {ps : List Name}
    {v : Expr} (hv : v.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 v k).allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | fvar idx n ty _ => intro k h; exact h
  | sort u => intro k h; exact h
  | const n us => intro k h; exact h
  | lit l => intro k h; exact h
  | app f a ihf iha =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihf k h.1, iha k h.2⟩
  | lam n ty body m ihty ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | forallE n ty body m ihty ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihty k h.1, ihbody (k + 1) h.2⟩
  | letE n ty val body ihty ihval ihbody =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined,
      Bool.and_eq_true] at h ⊢
    exact ⟨⟨ihty k h.1.1, ihval k h.1.2⟩, ihbody (k + 1) h.2⟩
  | proj s i e ih =>
    intro k h
    simp only [Expr.instantiate1, Expr.allLevelParamsDefined] at h ⊢
    exact ih k h

/-- The binder-opening form `denote2` uses: the substituted term is the
`fvar` carrying the binder's own type. -/
theorem Expr.allLevelParamsDefined_open {ps : List Name}
    {ty body : Expr} {d : Nat} {n : Name}
    (hty : ty.allLevelParamsDefined ps = true)
    (hbody : body.allLevelParamsDefined ps = true) :
    (body.instantiate1 (.fvar d n ty)).allLevelParamsDefined ps
      = true :=
  Expr.allLevelParamsDefined_instantiate1_gen
    (v := .fvar d n ty) hty 0 hbody


theorem allLevelParamsDefined_mkAppN : ∀ {xs : List Expr} {f : Expr},
    f.allLevelParamsDefined ps = true →
    (∀ x ∈ xs, x.allLevelParamsDefined ps = true) →
    (Expr.mkAppN f xs).allLevelParamsDefined ps = true := by
  intro xs
  induction xs with
  | nil => intro f hf _; exact hf
  | cons x xs ih =>
    intro f hf hxs
    simp only [Expr.mkAppN]
    refine ih ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem allLevelParamsDefined_getAppFn :
    ∀ {e : Expr}, e.allLevelParamsDefined ps = true →
      e.getAppFn.allLevelParamsDefined ps = true := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h
    simp only [allLevelParamsDefined, Bool.and_eq_true] at h
    exact ihf h.1
  | _ => intro h; exact h

theorem allLevelParamsDefined_abstract1 :
    ∀ {e : Expr} (d k : Nat), e.allLevelParamsDefined ps = true →
      (e.abstract1 d k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro d k h <;>
    simp_all [Expr.abstract1, allLevelParamsDefined]
  case fvar i n ty _ => split <;> simp [allLevelParamsDefined, h]

open Expr in
theorem piResidual_lvlParams :
    ∀ {as : List Expr} {t res : Expr}, piResidual t as = some res →
      t.allLevelParamsDefined ps = true →
      (∀ x ∈ as, x.allLevelParamsDefined ps = true) →
      res.allLevelParamsDefined ps = true
  | [], t, res, h, hw, _ => by
    simp only [piResidual, Option.some.injEq] at h
    exact h ▸ hw
  | a :: as, t, res, h, hw, has => by
    match t, h with
    | .forallE n ty body mb, h =>
      have hw' : ty.allLevelParamsDefined ps = true ∧
          body.allLevelParamsDefined ps = true := by
        simpa only [allLevelParamsDefined, Bool.and_eq_true] using hw
      have h' : piResidual (body.instantiate1 a) as = some res := h
      exact piResidual_lvlParams h'
        (Expr.allLevelParamsDefined_instantiate1_gen
          (has a (List.mem_cons_self ..)) 0 hw'.2)
        (fun x hx => has x (List.mem_cons_of_mem _ hx))

theorem natLitToConstructor_lvlParams (n : Nat) :
    (natLitToConstructor n).allLevelParamsDefined ps = true := by
  cases n <;> simp [natLitToConstructor, allLevelParamsDefined]

theorem litToCtorIfNat_lvlParams {env : Env} {e : Expr}
    (h : e.allLevelParamsDefined ps = true) :
    (litToCtorIfNat env e).allLevelParamsDefined ps = true := by
  cases e with
  | lit l =>
    cases l with
    | natVal n =>
      simp only [litToCtorIfNat]
      split
      · exact natLitToConstructor_lvlParams n
      · exact h
    | strVal s => exact h
  | _ => exact h

theorem strLitToConstructor_lvlParams (s : String) :
    (strLitToConstructor s).allLevelParamsDefined ps = true := by
  have hspine : ∀ cs : List Char,
      (cs.foldr
        (init := Expr.app (.const listNilName [.zero])
          (.const charName []))
        (fun c e =>
          .app (.app (.app (.const listConsName [.zero])
            (.const charName []))
            (.app (.const charOfNatName []) (.lit (.natVal c.toNat))))
            e)).allLevelParamsDefined ps = true := by
    intro cs
    induction cs with
    | nil => simp [allLevelParamsDefined, Level.allParamsDefined]
    | cons c cs ih =>
      simp [allLevelParamsDefined, Level.allParamsDefined, ih]
  simp [strLitToConstructor, allLevelParamsDefined, hspine]

theorem etaFabArgs_lvlParams {T : Name} {ust : List Level}
    {targs : List Expr} {major : Expr} {nF : Nat}
    (hust : ∀ u ∈ ust, u.allParamsDefined ps = true)
    (htargs : ∀ x ∈ targs, x.allLevelParamsDefined ps = true)
    (hmajor : major.allLevelParamsDefined ps = true) :
    ∀ x ∈ etaFabArgs T ust targs major nF,
      x.allLevelParamsDefined ps = true := by
  intro x hx
  simp only [etaFabArgs, List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨j, -, rfl⟩
  · exact htargs x hx
  · refine allLevelParamsDefined_mkAppN ?_ ?_
    · simpa [allLevelParamsDefined, List.all_eq_true] using hust
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact htargs y hy
      · simpa [List.mem_singleton.mp hy] using hmajor

theorem unfoldDefinition_lvlParams {env : Env} (henv : EnvWF env)
    {e e' : Expr} (h : unfoldDefinition env e = some e')
    (hp : e.allLevelParamsDefined ps = true) :
    e'.allLevelParamsDefined ps = true := by
  unfold unfoldDefinition at h
  have hfn := allLevelParamsDefined_getAppFn hp
  cases hga : e.getAppFn with
  | const n us =>
    rw [hga] at h hfn
    dsimp only at h
    have hus : ∀ u ∈ us, u.allParamsDefined ps = true := by
      simpa [allLevelParamsDefined, List.all_eq_true] using hfn
    cases hf : env.find? n with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv value hint =>
        simp only [] at h
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen] at h
          obtain rfl := Option.some.inj h
          obtain ⟨-, -, -, -, hdefn, -, -⟩ := henv _ (find?_mem hf)
          obtain ⟨-, hvp, -, -⟩ := hdefn cv value hint rfl
          exact allLevelParamsDefined_mkAppN
            (allLevelParamsDefined_instantiateLevelParams hlen hus hvp)
            (allLevelParamsDefined_getAppArgs hp)
        · rw [if_neg hlen] at h; exact nomatch h
      | thmInfo cv value =>
        simp only [] at h
        by_cases hlen : us.length = cv.levelParams.length
        · rw [if_pos hlen] at h
          obtain rfl := Option.some.inj h
          obtain ⟨-, -, -, -, -, -, hthm⟩ := henv _ (find?_mem hf)
          obtain ⟨-, hvp, -, -⟩ := hthm cv value rfl
          exact allLevelParamsDefined_mkAppN
            (allLevelParamsDefined_instantiateLevelParams hlen hus hvp)
            (allLevelParamsDefined_getAppArgs hp)
        · rw [if_neg hlen] at h; exact nomatch h
      | axiomInfo cv => exact nomatch h
      | indInfo cv caps => exact nomatch h
      | ctorInfo cv a b => exact nomatch h
      | recInfo cv a b c => exact nomatch h
      | projInfo entry => exact nomatch h
  | bvar i => rw [hga] at h; exact nomatch h
  | sort u => rw [hga] at h; exact nomatch h
  | fvar i n ty => rw [hga] at h; exact nomatch h
  | app f a => rw [hga] at h; exact nomatch h
  | lam n ty b m => rw [hga] at h; exact nomatch h
  | forallE n ty b m => rw [hga] at h; exact nomatch h
  | letE n ty v b => rw [hga] at h; exact nomatch h
  | lit l => rw [hga] at h; exact nomatch h
  | proj s i x => rw [hga] at h; exact nomatch h

end Kit


/-! ## The reduction side -/

theorem whnfPres_lvlParams {env : Env} (henv : EnvWF env)
    {ps : List Name} :
    ∀ (fuel : Nat),
      (∀ (F d : Nat) (e t : Expr), F < fuel →
        e.allLevelParamsDefined ps = true →
        iotaRecP mode env F d e = .ok (some t) →
        t.allLevelParamsDefined ps = true) →
      (∀ {d : Nat} {e e' : Expr}, whnfCore mode env fuel d e = .ok e' →
        e.allLevelParamsDefined ps = true →
        e'.allLevelParamsDefined ps = true) ∧
      (∀ {d : Nat} {e e' : Expr}, whnf mode env fuel d e = .ok e' →
        e.allLevelParamsDefined ps = true →
        e'.allLevelParamsDefined ps = true)
  | 0, _ => ⟨(fun {_ _ _} h _ => nomatch h),
      (fun {_ _ _} h _ => nomatch h)⟩
  | fuel + 1, hiota => by
    obtain ⟨ihCore, ihLoop⟩ := whnfPres_lvlParams henv fuel
      (fun F d e t hF => hiota F d e t (Nat.lt_succ_of_lt hF))
    constructor
    · -- whnfCore
      intro d e e' h hb
      cases e with
      | sort u =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | fvar idx n ty =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | forallE n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | lam n ty body bi =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | const n ws =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | lit l =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, pure, Except.pure,
          Except.ok.injEq] at h
        exact h ▸ hb
      | bvar i =>
        rw [whnfCore_succ] at h
        simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
      | letE nn tt vv bb =>
        rw [whnfCore_succ] at h
        simp only [whnfCoreBody, whnfCore_def] at h
        simp only [allLevelParamsDefined, Bool.and_eq_true] at hb
        exact ihCore h
          (Expr.allLevelParamsDefined_instantiate1_gen hb.1.2 0 hb.2)
      | app f a =>
        simp only [allLevelParamsDefined, Bool.and_eq_true] at hb
        obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
        have hbf' := ihCore hwf hb.1
        rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, -⟩ |
          ⟨e'', hio, hwe''⟩ | rfl
        · simp only [allLevelParamsDefined, Bool.and_eq_true] at hbf'
          exact ihCore hbeta
            (Expr.allLevelParamsDefined_instantiate1_gen hb.2 0 hbf'.2)
        · refine ihCore hwe''
            (hiota fuel d _ _ (Nat.lt_succ_self fuel) ?_ hio)
          simp only [allLevelParamsDefined, Bool.and_eq_true]
          exact ⟨hbf', hb.2⟩
        · simp only [allLevelParamsDefined, Bool.and_eq_true]
          exact ⟨hbf', hb.2⟩
      | proj sn i pe =>
        simp only [allLevelParamsDefined] at hb
        obtain ⟨e₂, e₃, he, hlit, hcase⟩ := whnf_proj_inv h
        have hbe₂ := ihLoop he hb
        have hbe₃ : e₃.allLevelParamsDefined ps = true := by
          rcases projLitToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
          · exact hbe₂
          · exact ihLoop hred (strLitToConstructor_lvlParams s)
        rcases hcase with rfl |
          ⟨us, entry, hfn, hf, hnat, hi, hlen, hus, hred, -, -⟩
        · simpa [allLevelParamsDefined] using hbe₃
        · exact ihCore hred
            (allLevelParamsDefined_getAppArgs hbe₃ _
              (getD_mem (by omega)))
    · -- the reduction loop
      have hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr},
          whnfLoop (pureFns mode env fuel) env d n e = .ok e' →
          e.allLevelParamsDefined ps = true →
          e'.allLevelParamsDefined ps = true := by
        intro n
        induction n with
        | zero => intro _ _ _ h _; exact nomatch h
        | succ n ihN =>
          intro d e e' h hb
          obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
          have hbe₁ := ihCore hwc hb
          rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ |
            ⟨-, -, rfl⟩
          · rcases reduceNat_inv hrn with ⟨k, rfl⟩ | ⟨bn, rfl⟩ <;>
              exact ihN hcont (by simp [allLevelParamsDefined])
          · exact ihN hcont (unfoldDefinition_lvlParams henv hu hbe₁)
          · exact hbe₁
      intro d e e' h hb
      exact hloop whnfLoopFuel h hb


/-! ## The inference side -/

/-- Head normalisation keeps the parameters bounded. -/
theorem whnf_lvlParams {env : Env} (henv : EnvWF env) {ps : List Name}
    (fuel : Nat)
    (hiota : ∀ (F d : Nat) (e t : Expr), F < fuel →
      e.allLevelParamsDefined ps = true →
      iotaRecP mode env F d e = .ok (some t) →
      t.allLevelParamsDefined ps = true)
    {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e')
    (hp : e.allLevelParamsDefined ps = true) :
    e'.allLevelParamsDefined ps = true :=
  (whnfPres_lvlParams henv fuel hiota).2 h hp

/-- …and so does `whnfCore`. -/
theorem whnfCore_lvlParams {env : Env} (henv : EnvWF env)
    {ps : List Name} (fuel : Nat)
    (hiota : ∀ (F d : Nat) (e t : Expr), F < fuel →
      e.allLevelParamsDefined ps = true →
      iotaRecP mode env F d e = .ok (some t) →
      t.allLevelParamsDefined ps = true)
    {d : Nat} {e e' : Expr}
    (h : whnfCore mode env fuel d e = .ok e')
    (hp : e.allLevelParamsDefined ps = true) :
    e'.allLevelParamsDefined ps = true :=
  (whnfPres_lvlParams henv fuel hiota).1 h hp

theorem ensureSortCore_lvlParams {env : Env} (henv : EnvWF env)
    {ps : List Name} (fuel : Nat)
    (hiota : ∀ (F d : Nat) (e t : Expr), F < fuel →
      e.allLevelParamsDefined ps = true →
      iotaRecP mode env F d e = .ok (some t) →
      t.allLevelParamsDefined ps = true)
    {d : Nat} {e : Expr} {u : Level}
    (h : ensureSortCore mode env fuel d e = .ok u)
    (hp : e.allLevelParamsDefined ps = true) :
    u.allParamsDefined ps = true := by
  rw [ensureSortCore_eq] at h
  obtain ⟨w, hwe, hmatch⟩ := bind_okB h
  have hwp := whnf_lvlParams henv fuel hiota hwe hp
  cases w with
  | sort v =>
    simp only [pure, Except.pure, Except.ok.injEq] at hmatch
    rw [← hmatch]
    simpa [allLevelParamsDefined] using hwp
  | bvar i => exact nomatch hmatch
  | fvar i n ty => exact nomatch hmatch
  | const n us => exact nomatch hmatch
  | app f a => exact nomatch hmatch
  | lam n ty b m => exact nomatch hmatch
  | forallE n ty b m => exact nomatch hmatch
  | letE n ty v b => exact nomatch hmatch
  | lit l => exact nomatch hmatch
  | proj sn i x => exact nomatch hmatch

theorem inferTypeCore_lvlParams {env : Env} (henv : EnvWF env)
    {ps : List Name} :
    ∀ (fuel : Nat),
      (∀ (F d : Nat) (e t : Expr), F < fuel →
        e.allLevelParamsDefined ps = true →
        iotaRecP mode env F d e = .ok (some t) →
        t.allLevelParamsDefined ps = true) →
      ∀ {d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t →
      e.allLevelParamsDefined ps = true →
      t.allLevelParamsDefined ps = true
  | 0, _, d, e, t, h, _ => nomatch h
  | fuel + 1, hiota', d, e, t, h, hp => by
    have hiota : ∀ (F d : Nat) (e t : Expr), F < fuel →
        e.allLevelParamsDefined ps = true →
        iotaRecP mode env F d e = .ok (some t) →
        t.allLevelParamsDefined ps = true :=
      fun F d e t hF => hiota' F d e t (Nat.lt_succ_of_lt hF)
    have ihI : ∀ {d' : Nat} {e' t' : Expr},
        inferTypeCore mode env fuel d' e' = .ok t' →
        e'.allLevelParamsDefined ps = true →
        t'.allLevelParamsDefined ps = true :=
      fun {_ _ _} hh hpp =>
        inferTypeCore_lvlParams henv fuel hiota hh hpp
    cases e with
    | sort u =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at h
      subst h
      simpa [allLevelParamsDefined, Level.allParamsDefined] using hp
    | fvar idx n ty =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      split
      · intro h
        simp only [Except.ok.injEq] at h
        subst h
        simpa [allLevelParamsDefined] using hp
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | const n ws =>
      rw [inferTypeCore_succ] at h
      simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind,
        pure, Except.pure] at h
      revert h
      cases hf : env.find? n with
      | none => intro h; exact nomatch h
      | some ci =>
        intro h
        dsimp only at h
        revert h
        split
        · next hlen =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h
          obtain ⟨-, htp, -, -, -, -, -⟩ := henv _ (find?_mem hf)
          exact allLevelParamsDefined_instantiateLevelParams hlen
            (by simpa [allLevelParamsDefined, List.all_eq_true]
              using hp) htp
        · intro h; exact nomatch h
    | lit l0 =>
      rw [inferTypeCore_succ] at h
      match l0, h with
      | .natVal n, h => ?natCase
      | .strVal s, h => ?strCase
      case strCase =>
        dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [allLevelParamsDefined]
      case natCase =>
        dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind,
          pure, Except.pure] at h
        revert h
        split
        case isFalse =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        case isTrue =>
          intro h
          simp only [Except.ok.injEq] at h
          subst h; simp [allLevelParamsDefined]
    | forallE n ty body m =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, rfl⟩ :=
        inferTypeCore_forall_inv h
      simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
      have hu : u.allParamsDefined ps = true := by
        simpa [allLevelParamsDefined]
          using whnf_lvlParams henv fuel hiota hwt (ihI hty hp.1)
      have hbtp := ihI hbt
        (Expr.allLevelParamsDefined_instantiate1_gen
          (v := .fvar d n ty) hp.1 0 hp.2)
      have hv := ensureSortCore_lvlParams henv fuel hiota hes hbtp
      simp [allLevelParamsDefined, Level.allParamsDefined, hu, hv]
    | lam n ty body m =>
      obtain ⟨tty, u, bt, -, -, hbt, -, rfl⟩ :=
        inferTypeCore_lam_inv h
      simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
      have hbtp := ihI hbt
        (Expr.allLevelParamsDefined_instantiate1_gen
          (v := .fvar d n ty) hp.1 0 hp.2)
      simp only [allLevelParamsDefined, Bool.and_eq_true]
      exact ⟨hp.1, allLevelParamsDefined_abstract1 d 0 hbtp⟩
    | app f a =>
      obtain ⟨tf, n', ty', body', m', htf, hwh, rfl, -⟩ :=
        inferTypeCore_app_inv h
      simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
      have hPi := whnf_lvlParams henv fuel hiota hwh (ihI htf hp.1)
      simp only [allLevelParamsDefined, Bool.and_eq_true] at hPi
      exact Expr.allLevelParamsDefined_instantiate1_gen hp.2 0 hPi.2
    | proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hfp, hnat, hlen,
        hus, -, hres⟩ := inferTypeCore_proj_inv h
      simp only [allLevelParamsDefined] at hp
      have hte' := whnf_lvlParams henv fuel hiota hwt (ihI hte hp)
      have hfnp :
          (Expr.const T us).allLevelParamsDefined ps = true := by
        rw [← hfn]; exact allLevelParamsDefined_getAppFn hte'
      obtain ⟨-, hep, -, -, -, -, -⟩ :=
        henv _ (find?_mem (Env.findProj?_some hfp))
      refine piResidual_lvlParams hres
        (allLevelParamsDefined_instantiateLevelParams hus
          (by simpa [allLevelParamsDefined, List.all_eq_true]
            using hfnp) hep) ?_
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact allLevelParamsDefined_getAppArgs hte' x hx
      · rcases List.mem_singleton.mp hx with rfl
        exact hp
    | bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure,
        Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    | letE n' t' v' b' =>
      obtain ⟨-, -, -, -, -, -, -, h'⟩ := inferTypeCore_letE_inv h
      simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
      exact ihI h'
        (Expr.allLevelParamsDefined_instantiate1_gen hp.1.2 0 hp.2)


/-! ## The iota case, closed by checker change #9

`iotaRec` now guards `us.length = cv.levelParams.length` alongside the
spine length (`Kernel/Core.lean`, mirroring `unfoldDefinition`), so the
arity the reduct needs comes straight out of `iotaRec_inv`.  What used
to be the hypothesis `harity` is now the inversion's own `hlus`. -/

theorem iotaRec_lvlParams {env : Env} (henv : EnvWF env)
    {ps : List Name} (F : Nat)
    (hwF : ∀ {d : Nat} {a b : Expr}, whnf mode env F d a = .ok b →
      a.allLevelParamsDefined ps = true →
      b.allLevelParamsDefined ps = true)
    (hiF : ∀ {d : Nat} {a b : Expr},
      inferTypeCore mode env F d a = .ok b →
      a.allLevelParamsDefined ps = true →
      b.allLevelParamsDefined ps = true)
    {d : Nat} {e t : Expr} (hp : e.allLevelParamsDefined ps = true)
    (h : iotaRecP mode env F d e = .ok (some t)) :
    t.allLevelParamsDefined ps = true := by
  obtain ⟨c, us, cv, mI, rP, rules, major₀, major₁, major, cj, usj,
    cvj, cnP, cnF, r, cbinders, cbody, residual, cr, usr, hfn, hfc,
    hlen, hlus, hmaj, hlit, hsub, hmfn, hfj, hrule, hml, har1, har2, -,
    hlev, hpeq, hcerts, hmcerts, -, -, -, -, rfl⟩ := iotaRec_inv h
  have hargs := allLevelParamsDefined_getAppArgs hp
  -- the major premise, through the three conversion steps
  have hmaj0 : major₀.allLevelParamsDefined ps = true :=
    hwF hmaj (hargs _ (getD_mem (by omega)))
  have hmaj1 : major₁.allLevelParamsDefined ps = true := by
    rcases litMajorToCtorP_inv hlit with rfl | ⟨s, -, -, hred⟩
    · exact litToCtorIfNat_lvlParams hmaj0
    · exact hwF hred (strLitToConstructor_lvlParams s)
  have hmajor : major.allLevelParamsDefined ps = true := by
    rcases majorToCtor_inv hsub with rfl | ⟨-, -, -, rl, cvj', cnP',
      cnF', tmaj₀, tmaj, T, us₀, ust, cvT, caps, -, -, -, -, hinf,
      hwhnf, hTfn, hbranch⟩
    · exact hmaj1
    · have htmaj : tmaj.allLevelParamsDefined ps = true :=
        hwF hwhnf (hiF hinf hmaj1)
      have hust : ∀ u ∈ ust, u.allParamsDefined ps = true := by
        have := allLevelParamsDefined_getAppFn htmaj
        rw [hTfn] at this
        simpa [allLevelParamsDefined, List.all_eq_true] using this
      have hctor : ∀ (nm : Name),
          (Expr.const nm ust).allLevelParamsDefined ps = true := by
        intro nm
        simpa [allLevelParamsDefined, List.all_eq_true] using hust
      rcases hbranch with ⟨-, -, -, -, -, rfl, -, -, -⟩ |
        ⟨-, -, -, -, -, -, -, -, rfl, -, -⟩
      · exact allLevelParamsDefined_mkAppN (hctor _)
          (fun x hx => allLevelParamsDefined_getAppArgs htmaj x
            (List.mem_of_mem_take hx))
      · exact allLevelParamsDefined_mkAppN (hctor _)
          (etaFabArgs_lvlParams hust
            (fun x hx => allLevelParamsDefined_getAppArgs htmaj x hx)
            hmaj1)
  -- the rule's right-hand side, at the recursor's own levels
  obtain ⟨-, -, -, -, -, hrules, -⟩ := henv _ (find?_mem hfc)
  obtain ⟨-, hrhs, -, -, -⟩ := hrules cv mI rP rules rfl r
    (List.mem_of_find?_eq_some hrule)
  have hus : ∀ u ∈ us, u.allParamsDefined ps = true := by
    have := allLevelParamsDefined_getAppFn hp
    rw [hfn] at this
    simpa [allLevelParamsDefined, List.all_eq_true] using this
  refine allLevelParamsDefined_mkAppN
    (allLevelParamsDefined_instantiateLevelParams hlus hus hrhs) ?_
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hargs x (List.mem_of_mem_take hx)
  · exact allLevelParamsDefined_getAppArgs hmajor x
      (List.mem_of_mem_drop hx)


/-! ## Tying the knot

`whnf`/`inferTypeCore` at fuel `F` consume the iota fact only at fuels
*strictly below* `F` (every clause recurses one fuel down — that is why
their `hiota` hypotheses are bounded), while `iotaRec_lvlParams` at
fuel `F` consumes reduction and inference at `F` itself.  So one
induction on a bound closes the cycle, and the iota fact holds
outright: no residue, no hypothesis. -/

theorem iotaRec_lvlParams_lt {env : Env} (henv : EnvWF env)
    {ps : List Name} :
    ∀ (n F d : Nat) (e t : Expr), F < n →
      e.allLevelParamsDefined ps = true →
      iotaRecP mode env F d e = .ok (some t) →
      t.allLevelParamsDefined ps = true
  | 0, _, _, _, _, hF, _, _ => absurd hF (Nat.not_lt_zero _)
  | n + 1, F, d, e, t, hF, hp, h => by
    have ih : ∀ (F' d' : Nat) (e' t' : Expr), F' < F →
        e'.allLevelParamsDefined ps = true →
        iotaRecP mode env F' d' e' = .ok (some t') →
        t'.allLevelParamsDefined ps = true :=
      fun F' d' e' t' hF' =>
        iotaRec_lvlParams_lt henv n F' d' e' t'
          (Nat.lt_of_lt_of_le hF' (Nat.le_of_lt_succ hF))
    exact iotaRec_lvlParams henv F
      (fun hw hpw => whnf_lvlParams henv F ih hw hpw)
      (fun hi hpi => inferTypeCore_lvlParams henv F ih hi hpi) hp h

/-- **Iota keeps the subject's level parameters** — unconditionally,
at every fuel.  This is what checker change #9 bought. -/
theorem iotaRec_lvlParamsW {env : Env} (henv : EnvWF env)
    {ps : List Name} (F d : Nat) (e t : Expr)
    (hp : e.allLevelParamsDefined ps = true)
    (h : iotaRecP mode env F d e = .ok (some t)) :
    t.allLevelParamsDefined ps = true :=
  iotaRec_lvlParams_lt henv (F + 1) F d e t (Nat.lt_succ_self F) hp h

/-- Head normalisation keeps the parameters bounded — no hypothesis. -/
theorem whnf_lvlParamsW {env : Env} (henv : EnvWF env)
    {ps : List Name} (fuel : Nat) {d : Nat} {e e' : Expr}
    (h : whnf mode env fuel d e = .ok e')
    (hp : e.allLevelParamsDefined ps = true) :
    e'.allLevelParamsDefined ps = true :=
  whnf_lvlParams henv fuel
    (fun F d e t _ => iotaRec_lvlParamsW henv F d e t) h hp

/-- Inference keeps the parameters bounded — no hypothesis. -/
theorem inferTypeCore_lvlParamsW {env : Env} (henv : EnvWF env)
    {ps : List Name} (fuel : Nat) {d : Nat} {e t : Expr}
    (h : inferTypeCore mode env fuel d e = .ok t)
    (hp : e.allLevelParamsDefined ps = true) :
    t.allLevelParamsDefined ps = true :=
  inferTypeCore_lvlParams henv fuel
    (fun F d e t _ => iotaRec_lvlParamsW henv F d e t) h hp

end Setlec
