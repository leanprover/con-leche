module

public import InLeanProof.StateOpsI
import ConLeche.Verify.Cached.DiscC1
/- `Lean.mkAppN`'s body is not exposed by `Lean.Expr`; the application
spine's translation unfolds it. -/
import all Lean.Expr

/-!
# InLean's body walks, part 1: list helpers and small twins (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC1.lean`'s walks: each InLean body
(`InLean/CoreC.lean`) simulates con-leche's pure fueled original at the
translation, under `KnotSpecI` of its callback record, proved by the cached
twin's `sym … => vcgen … <;> finish` script with the translation's vocabulary
(`InLeanProof/GrindI.lean`) in the `grind` set.  This module adds the
vocabulary its walks need beyond `GrindI` (the spine's length, the
`eagerReduce` head, application spines, `Nat` literals and operations), and
the O4 hypotheses its walks read the environment through (`EnvDomI`,
`EnvDefnI`, beside `StateOpsI`'s `EnvRelI`).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary -/

section Vocab
variable (s : InLean.CState)

theorem appArgs_go_length : ∀ (e : Expr) (acc : List Expr),
    (appArgs.go e acc).length = Expr.getAppNumArgsT e + acc.length := by
  intro e
  induction e with
  | app f a ihf _ => intro acc; simp only [appArgs.go, ihf, Expr.getAppNumArgsT, List.length_cons]; omega
  | mdata _ x ih => intro acc; simp only [appArgs.go, ih, Expr.getAppNumArgsT]
  | _ => intro acc; simp [appArgs.go, Expr.getAppNumArgsT]

/-- The spine's length, read through `mdata`, is the translation's. -/
@[conleche_grind =] theorem TrS_getAppArgs_length (e : Expr) :
    (TrS s e).getAppArgs.length = Expr.getAppNumArgsT e := by
  rw [← TrSL_appArgs s e, TrSL, List.length_map, appArgs, appArgs_go_length]; rfl

/-- The spine's head, read through `mdata`, is never `mdata`. -/
theorem getAppFnT_ne_mdata : ∀ {e : Expr} {m : MData} {x : Expr}, Expr.getAppFnT e = .mdata m x → False
  | .app f _, m, x, h => by rw [Expr.getAppFnT] at h; exact getAppFnT_ne_mdata h
  | .mdata _ y, m, x, h => by rw [Expr.getAppFnT] at h; exact getAppFnT_ne_mdata h
  | .bvar _, _, _, h | .fvar _, _, _, h | .mvar _, _, _, h | .sort _, _, _, h
  | .const .., _, _, h | .lam .., _, _, h | .forallE .., _, _, h | .letE .., _, _, h
  | .lit _, _, _, h | .proj .., _, _, h => by simp [Expr.getAppFnT] at h

/-- con-leche's `eagerReduce` test as a head and an argument count. -/
theorem cl_isEagerReduce_eq (x : ConLeche.Expr) :
    x.isEagerReduce = (x.getAppArgs.length == 2 &&
      match x.getAppFn with
      | .const c _ => c == ConLeche.eagerReduceName
      | _ => false) := by
  rcases x with _ | _ | _ | _ | ⟨_ | _ | _ | _ | ⟨_ | _ | _ | _ | ⟨g, _⟩ | _ | _ | _ | _, _⟩ |
    _ | _ | _ | _ | _, _⟩ | _ | _ | _ | _ | _ <;>
    simp [ConLeche.Expr.isEagerReduce, ConLeche.Expr.getAppArgs, ConLeche.Expr.getAppFn]

theorem toName_eagerReduceName : toName InLean.eagerReduceName = ConLeche.eagerReduceName := rfl

/-- The `eagerReduce` head, read through the translation. -/
@[conleche_grind =] theorem TrS_isEagerReduce (e : Expr) :
    (TrS s e).isEagerReduce = Expr.isEagerReduce e := by
  unfold Expr.isEagerReduce
  rw [← TrS_getAppArgs_length s e, cl_isEagerReduce_eq, ← TrS_getAppFnT s e]
  congr 1
  generalize hh : Expr.getAppFnT e = h
  cases h with
  | const c us =>
    simp only [TrS_const, ← toName_eagerReduceName]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun h => toName_inj h, fun h => h ▸ rfl⟩
  | fvar id =>
    simp only [TrS, trE]
    cases h : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
      rfl
  | mdata _ x => exact (getAppFnT_ne_mdata hh).elim
  | _ => rfl

/-- A list's reading and translation are stable along the run. -/
theorem okSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List Expr}, OkSL s₀ l = true → OkSL s₁ l = true
  | [], _ => rfl
  | a :: l, hl => by
    simp only [OkSL_cons, Bool.and_eq_true] at hl ⊢
    exact ⟨okS_of_tabLe h hl.1, okSL_of_tabLe h hl.2⟩
grind_pattern [conleche_grind] okSL_of_tabLe => TabLe s₀ s₁, OkSL s₁ l

theorem TrSL_of_tabLe {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {l : List Expr}, OkSL s₀ l = true → TrSL s₁ l = TrSL s₀ l
  | [], _ => rfl
  | a :: l, hl => by
    simp only [OkSL_cons, Bool.and_eq_true] at hl
    simp only [TrSL_cons, TrS_of_tabLe h hl.1, TrSL_of_tabLe h hl.2]
grind_pattern [conleche_grind] TrSL_of_tabLe => TabLe s₀ s₁, TrSL s₁ l

@[conleche_grind =] theorem AllClosed_nil : AllClosed [] = true := rfl
@[conleche_grind =] theorem AllClosed_cons (a : ConLeche.Expr) (l : List ConLeche.Expr) :
    AllClosed (a :: l) = (a.looseBVarsBounded 0 && AllClosed l) := rfl

theorem all_okL_of_okLv {us : List Level} (h : us.all okLv = true) : us.all okL = true := by
  simp only [List.all_eq_true, okLv, Bool.and_eq_true] at h ⊢; exact fun u hu => (h u hu).1
grind_pattern [conleche_grind] all_okL_of_okLv => us.all okLv

@[conleche_grind =] theorem TrSL_reverse (s : InLean.CState) (l : List Expr) :
    TrSL s l.reverse = (TrSL s l).reverse := by simp [TrSL, List.map_reverse]

end Vocab

/-! ## Literals and the environment's domain -/

section Lits

/-- **The environment's domain** (O4 with `EnvRelI`, P3's): InLean finds a
name exactly where con-leche finds its translation. -/
@[expose] def EnvDomI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop :=
  ∀ n, (fe.find? n).isSome = (env.find? (toName n)).isSome

theorem natLitStoredF_I {fe : InLean.FEnv} (h : EnvDomI fe env) :
    InLean.natLitStoredF fe = ConLeche.natLitStored env := by
  simp only [InLean.natLitStoredF, ConLeche.natLitStored, h InLean.natName, h InLean.natZeroName,
    h InLean.natSuccName]; rfl

theorem strLitStoredF_I {fe : InLean.FEnv} (h : EnvDomI fe env) :
    InLean.strLitStoredF fe = ConLeche.strLitStored env := by
  simp only [InLean.strLitStoredF, ConLeche.strLitStored, natLitStoredF_I h, h InLean.stringName,
    h InLean.stringOfListName, h InLean.listName, h InLean.listNilName, h InLean.listConsName,
    h InLean.charName, h InLean.charOfNatName]; rfl

variable (s : InLean.CState)

@[conleche_grind =] theorem toLit_natVal (n : Nat) : toLit (.natVal n) = .natVal n := rfl
@[conleche_grind =] theorem toLit_strVal (t : String) : toLit (.strVal t) = .strVal t := rfl

@[conleche_grind =] theorem TrS_natLitToConstructor (n : Nat) :
    TrS s (InLean.natLitToConstructor n) = ConLeche.natLitToConstructor n := by
  cases n <;> rfl

@[conleche_grind =] theorem OkS_natLitToConstructor (n : Nat) :
    OkS s (InLean.natLitToConstructor n) = true := by
  cases n <;> rfl

theorem TrS_strFold (l : List Char) :
    TrS s (l.foldr (init := .app (.const InLean.listNilName [.zero]) (.const InLean.charName []))
      fun c e => .app (.app (.app (.const InLean.listConsName [.zero]) (.const InLean.charName []))
        (.app (.const InLean.charOfNatName []) (.lit (.natVal c.toNat)))) e) =
    l.foldr (init := .app (.const ConLeche.listNilName [.zero]) (.const ConLeche.charName []))
      fun c e => .app (.app (.app (.const ConLeche.listConsName [.zero]) (.const ConLeche.charName []))
        (.app (.const ConLeche.charOfNatName []) (.lit (.natVal c.toNat)))) e := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.foldr_cons, TrS_app, ih]; rfl

theorem OkS_strFold (l : List Char) :
    OkS s (l.foldr (init := .app (.const InLean.listNilName [.zero]) (.const InLean.charName []))
      fun c e => .app (.app (.app (.const InLean.listConsName [.zero]) (.const InLean.charName []))
        (.app (.const InLean.charOfNatName []) (.lit (.natVal c.toNat)))) e) = true := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.foldr_cons, OkS_app, ih]; rfl

@[conleche_grind =] theorem TrS_strLitToConstructor (t : String) :
    TrS s (InLean.strLitToConstructor t) = ConLeche.strLitToConstructor t := by
  simp only [InLean.strLitToConstructor, ConLeche.strLitToConstructor, TrS_app, TrS_strFold]; rfl

@[conleche_grind =] theorem OkS_strLitToConstructor (t : String) :
    OkS s (InLean.strLitToConstructor t) = true := by
  simp only [InLean.strLitToConstructor, OkS_app, OkS_strFold]; rfl

/-- A term whose top is no `Nat` literal translates to one con-leche's
conversion leaves alone. -/
theorem litToCtorIfNat_TrS_other {e : Expr} (h : ∀ n, EO.stripTop e ≠ .lit (.natVal n)) :
    ConLeche.litToCtorIfNat env (TrS s e) = TrS s e := by
  rw [← TrS_stripTop s e]
  generalize hx : EO.stripTop e = x at h
  cases x with
  | lit l => cases l with
    | natVal n => exact absurd rfl (h n)
    | strVal t => rfl
  | fvar id =>
    simp only [TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rfl

end Lits

/-- **`litToCtorIfNatI`** (`litToCtorIfNatC_spec`'s twin): its answer is
con-leche's `litToCtorIfNat` at the translation. -/
theorem litToCtorIfNatI_specI {fe : InLean.FEnv} (hdom : EnvDomI fe env) {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) {e : Expr} (he : OkS s₀ e = true) :
    ⦃fun s => s = s₀⦄ InLean.litToCtorIfNatI fe e
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = ConLeche.litToCtorIfNat env (TrS s₀ e); ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  by_cases hn : ∃ n, EO.stripTop e = .lit (.natVal n)
  · obtain ⟨n, hn⟩ := hn
    have hT : TrS s₀ e = .lit (.natVal n) := by rw [← TrS_stripTop, hn]; rfl
    by_cases hst : InLean.natLitStoredF fe = true
    · simp only [InLean.litToCtorIfNatI, hn, hst, ↓reduceIte, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs, TabLe.refl _, OkS_natLitToConstructor _ _, ?_⟩
      rw [hT, TrS_natLitToConstructor]
      simp [ConLeche.litToCtorIfNat, ← natLitStoredF_I hdom, hst]
    · simp only [InLean.litToCtorIfNatI, hn, hst, Bool.false_eq_true, ↓reduceIte, pure,
        StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs, TabLe.refl _, he, ?_⟩
      rw [hT]
      simp [ConLeche.litToCtorIfNat, ← natLitStoredF_I hdom, hst]
  · have hn' : ∀ n, EO.stripTop e ≠ .lit (.natVal n) := fun n h => hn ⟨n, h⟩
    have hr' : InLean.litToCtorIfNatI fe e s₀ = .ok (e, s₀) := by
      unfold InLean.litToCtorIfNatI
      generalize hx : EO.stripTop e = x at hn'
      cases x with
      | lit l => cases l with
        | natVal n => exact absurd rfl (hn' n)
        | strVal t => rfl
      | _ => rfl
    rw [hr'] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, he, (litToCtorIfNat_TrS_other s₀ hn').symm⟩

/-- A term whose top is no `String` literal translates to none. -/
theorem TrS_ne_strLit (s : InLean.CState) {e : Expr} (h : ∀ t, EO.stripTop e ≠ .lit (.strVal t)) :
    ∀ t, TrS s e ≠ .lit (.strVal t) := by
  intro t ht
  rw [← TrS_stripTop s e] at ht
  generalize hx : EO.stripTop e = x at h ht
  cases x with
  | lit l => cases l with
    | strVal u => exact h u rfl
    | natVal n => simp [TrS, trE, toLit] at ht
  | fvar id =>
    simp only [TrS, trE] at ht
    cases hf : FVarTable.trans (tableOf s) id with
    | none => simp [hf] at ht
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf
      simp [hf] at ht
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => simp [TrS, trE] at ht

theorem projLitToCtor_other {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m) (d : Nat)
    {x : ConLeche.Expr} (h : ∀ t, x ≠ .lit (.strVal t)) :
    ConLeche.projLitToCtor r env d x = pure x := by
  cases x with
  | lit l => cases l with
    | strVal t => exact absurd rfl (h t)
    | natVal _ => rfl
  | _ => rfl

theorem litMajorToCtor_other {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m) (d : Nat)
    {x : ConLeche.Expr} (h : ∀ t, x ≠ .lit (.strVal t)) :
    ConLeche.litMajorToCtor r env d x = pure (ConLeche.litToCtorIfNat env x) := by
  cases x with
  | lit l => cases l with
    | strVal t => exact absurd rfl (h t)
    | natVal _ => rfl
  | _ => rfl

/-- The string-literal branch the two conversions share: a stored `String`
support runs the knot's `whnf` on the constructor form. -/
theorem strLit_whnf_run {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat}
    {s₀ s' : InLean.CState} (hs : CSOKI mode eager env s₀) {t : String} {v : Expr}
    (hrun : r.whnf d (InLean.strLitToConstructor t) s₀ = .ok (v, s')) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).whnf d (ConLeche.strLitToConstructor t)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true := by
  have h := tripleI_iff_run.1 (ih.whnf (i := InLean.strLitToConstructor t) hs
    (OkS_strLitToConstructor s₀ t)
    (by rw [TrS_strLitToConstructor]; exact ConLeche.strLitToConstructor_WScoped t d)
    (by rw [TrS_strLitToConstructor]; exact ConLeche.strLitToConstructor_looseBVars t 0)) v s' hrun
  rw [TrS_strLitToConstructor] at h
  exact h

/-- **`projLitToCtorI`** (`projLitToCtorC_spec`'s twin). -/
theorem projLitToCtorI_specI {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    {fe : InLean.FEnv} (hdom : EnvDomI fe env) {d : Nat} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) {e : Expr} (he : OkS s₀ e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ e)) (hc : (TrS s₀ e).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.projLitToCtorI r fe d e
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.projLitToCtor (ConLeche.fueledFns mode eager env) env d (TrS s₀ e)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  by_cases hn : ∃ t, EO.stripTop e = .lit (.strVal t)
  · obtain ⟨t, hn⟩ := hn
    have hT : TrS s₀ e = .lit (.strVal t) := by rw [← TrS_stripTop, hn]; rfl
    rw [hT]
    by_cases hst : InLean.strLitStoredF fe = true
    · simp only [InLean.projLitToCtorI, hn, hst, ↓reduceIte] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := strLit_whnf_run ih hs hr
      refine ⟨h1, h2, h3, ?_, h5, h6⟩
      simp only [ConLeche.projLitToCtor, ← strLitStoredF_I hdom, hst, ↓reduceIte]
      exact h4
    · simp only [InLean.projLitToCtorI, hn, hst, Bool.false_eq_true, ↓reduceIte, pure,
        StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs, TabLe.refl _, he, ?_, hw, hc⟩
      simp only [ConLeche.projLitToCtor, ← strLitStoredF_I hdom, hst, Bool.false_eq_true,
        ↓reduceIte, hT]
      exact Runs.pure _
  · have hn' : ∀ t, EO.stripTop e ≠ .lit (.strVal t) := fun t h => hn ⟨t, h⟩
    have hr' : InLean.projLitToCtorI r fe d e s₀ = .ok (e, s₀) := by
      unfold InLean.projLitToCtorI
      generalize hx : EO.stripTop e = x at hn'
      cases x with
      | lit l => cases l with
        | strVal t => exact absurd rfl (hn' t)
        | natVal _ => rfl
      | _ => rfl
    rw [hr'] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs, TabLe.refl _, he, ?_, hw, hc⟩
    rw [projLitToCtor_other _ _ (TrS_ne_strLit s₀ hn')]
    exact Runs.pure _

/-- **`litMajorToCtorI`** (`litMajorToCtorC_spec`'s twin). -/
theorem litMajorToCtorI_specI {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    {fe : InLean.FEnv} (hdom : EnvDomI fe env) {d : Nat} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) {e : Expr} (he : OkS s₀ e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ e)) (hc : (TrS s₀ e).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.litMajorToCtorI r fe d e
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.litMajorToCtor (ConLeche.fueledFns mode eager env) env d (TrS s₀ e)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  by_cases hn : ∃ t, EO.stripTop e = .lit (.strVal t)
  · obtain ⟨t, hn⟩ := hn
    have hT : TrS s₀ e = .lit (.strVal t) := by rw [← TrS_stripTop, hn]; rfl
    rw [hT]
    by_cases hst : InLean.strLitStoredF fe = true
    · simp only [InLean.litMajorToCtorI, hn, hst, ↓reduceIte] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := strLit_whnf_run ih hs hr
      refine ⟨h1, h2, h3, ?_, h5, h6⟩
      simp only [ConLeche.litMajorToCtor, ← strLitStoredF_I hdom, hst, ↓reduceIte]
      exact h4
    · simp only [InLean.litMajorToCtorI, hn, hst, Bool.false_eq_true, ↓reduceIte, pure,
        StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs, TabLe.refl _, he, ?_, hw, hc⟩
      simp only [ConLeche.litMajorToCtor, ← strLitStoredF_I hdom, hst, Bool.false_eq_true,
        ↓reduceIte, hT]
      exact Runs.pure _
  · have hn' : ∀ t, EO.stripTop e ≠ .lit (.strVal t) := fun t h => hn ⟨t, h⟩
    have hr' : InLean.litMajorToCtorI r fe d e s₀ = InLean.litToCtorIfNatI fe e s₀ := by
      unfold InLean.litMajorToCtorI
      generalize hx : EO.stripTop e = x at hn'
      cases x with
      | lit l => cases l with
        | strVal t => exact absurd rfl (hn' t)
        | natVal _ => rfl
      | _ => rfl
    rw [hr'] at hr
    obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 (litToCtorIfNatI_specI hdom hs he) v s' hr
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · rw [litMajorToCtor_other _ _ (TrS_ne_strLit s₀ hn'), h4]; exact Runs.pure _
    · rw [h4]; exact ConLeche.litToCtorIfNat_WScoped hw
    · rw [h4]
      unfold ConLeche.litToCtorIfNat
      split
      · cases ‹Nat› <;> split <;> rfl
      · exact hc

/-! ## The walks -/

section Walks

variable {r : InLean.CoreFnsI}

/-- **The full-grade argument check** (`defeqArgC_spec`'s twin): the same
argument, so the same tower. -/
theorem defeqArgI_spec (ih : KnotSpecI mode eager env r) {s₀ : InLean.CState} {d : Nat}
    {a ta ty : Expr} (hs : CSOKI mode eager env s₀) (hta : OkS s₀ ta = true)
    (hty : OkS s₀ ty = true) (hwta : ConLeche.Expr.WScoped d (TrS s₀ ta))
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty)) (hcta : (TrS s₀ ta).looseBVarsBounded 0 = true)
    (hcty : (TrS s₀ ty).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ defeqArgI r d a ta ty
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqArg (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ ta)
        (TrS s₀ ty)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.defeqArg] =>
    vcgen [InLean.defeqArgI, ih.defeq hs hta hty hwta hwty hcta hcty,
      ih.defeqE hs hta hty hwta hwty hcta hcty] <;> finish

/-- **The pairwise definitional-equality helper** (`defEqListC_spec`'s twin). -/
theorem defEqListI_spec (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ {args brgs : List Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ →
      OkSL s₀ args = true → OkSL s₀ brgs = true →
      AllWS d (TrSL s₀ args) → AllWS d (TrSL s₀ brgs) →
      AllClosed (TrSL s₀ args) = true → AllClosed (TrSL s₀ brgs) = true →
      ⦃fun s => s = s₀⦄ defEqListI r d args brgs
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
          Runs (ConLeche.defEqList (ConLeche.fueledFns mode eager env) env d (TrSL s₀ args)
            (TrSL s₀ brgs)) v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList.eq_1] =>
        vcgen [InLean.defEqListI] <;> finish
    | cons _ _ =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList] =>
        vcgen [InLean.defEqListI.eq_def] <;> finish
  | cons a as ihA =>
    intro brgs
    cases brgs with
    | nil =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList] =>
        vcgen [InLean.defEqListI.eq_def] <;> finish
    | cons b bs =>
      intro _ _ _ _ _ _ _ _
      sym only [conleche_grind, ConLeche.defEqList.eq_2] =>
        vcgen [InLean.defEqListI, ih.defeq, ihA] <;> finish

/-- A `const` spine head translates to one. -/
theorem TrS_getAppFn_const (s : InLean.CState) {e : Expr} {n : Name} {us : List Level}
    (h : Expr.getAppFnT e = .const n us) :
    (TrS s e).getAppFn = .const (toName n) (us.map trL) := by
  rw [← TrS_getAppFnT, h]; rfl

/-- A head that is no `const` translates to none. -/
theorem TrS_getAppFn_notConst (s : InLean.CState) {e : Expr}
    (h : ∀ n us, Expr.getAppFnT e ≠ .const n us) :
    ∀ n us, (TrS s e).getAppFn ≠ .const n us := by
  intro n us ht
  rw [← TrS_getAppFnT] at ht
  generalize hx : Expr.getAppFnT e = x at h ht
  cases x with
  | const c ls => exact h c ls rfl
  | fvar id =>
    simp only [TrS, trE] at ht
    cases hf : FVarTable.trans (tableOf s) id with
    | none => simp [hf] at ht
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf
      simp [hf] at ht
  | mdata _ y => exact (getAppFnT_ne_mdata hx).elim
  | _ => simp [TrS, trE] at ht

theorem defeqSpine_notConstA {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m) (d : Nat)
    {a b : ConLeche.Expr} (h : ∀ n us, a.getAppFn ≠ .const n us) :
    ConLeche.defeqSpine r env d a b = pure false := by
  unfold ConLeche.defeqSpine
  split
  · rename_i n us hh; exact absurd hh (h n us)
  · rfl

theorem defeqSpine_notConstB {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m) (d : Nat)
    {a b : ConLeche.Expr} {n : ConLeche.Name} {us : List ConLeche.Level}
    (ha : a.getAppFn = .const n us) (h : ∀ n us, b.getAppFn ≠ .const n us) :
    ConLeche.defeqSpine r env d a b = pure false := by
  unfold ConLeche.defeqSpine
  rw [ha]
  generalize hb : b.getAppFn = x at h
  cases x <;> first | rfl | exact absurd rfl (h _ _)

/-- **The same-head spine comparison** (`defeqSpineC_spec`'s twin). -/
theorem defeqSpineI_specI (ih : KnotSpecI mode eager env r) {d : Nat} {a b : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true)
    (hokb : OkS s₀ b = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hwb : ConLeche.Expr.WScoped d (TrS s₀ b)) (hca : (TrS s₀ a).looseBVarsBounded 0 = true)
    (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.defeqSpineI r d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqSpine (ConLeche.fueledFns mode eager env) env d (TrS s₀ a) (TrS s₀ b)) v;
        ⊤⦄ := by
  refine tripleI_iff_run.2 fun v s' hr => ?_
  by_cases hA : ∃ n us, Expr.getAppFnT a = .const n us
  · obtain ⟨n, us, hA⟩ := hA
    by_cases hB : ∃ n us, Expr.getAppFnT b = .const n us
    · obtain ⟨n', us', hB⟩ := hB
      have hTA := TrS_getAppFn_const s₀ hA
      have hTB := TrS_getAppFn_const s₀ hB
      have hokA : us.all okL = true := by
        have := OkS_getAppFnT s₀ hoka; rw [hA] at this; exact all_okL_of_okLv this
      have hokB : us'.all okL = true := by
        have := OkS_getAppFnT s₀ hokb; rw [hB] at this; exact all_okL_of_okLv this
      have hlenA : (appArgs a).length = (TrS s₀ a).getAppArgs.length := by
        rw [← TrSL_appArgs s₀ a, TrSL, List.length_map]
      have hlenB : (appArgs b).length = (TrS s₀ b).getAppArgs.length := by
        rw [← TrSL_appArgs s₀ b, TrSL, List.length_map]
      have hcond : ((n == n') = true ∧ (appArgs a).length = (appArgs b).length) ↔
          (toName n = toName n' ∧ (TrS s₀ a).getAppArgs.length = (TrS s₀ b).getAppArgs.length) := by
        rw [hlenA, hlenB, beq_iff_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 ▸ rfl, h2⟩, fun ⟨h1, h2⟩ => ⟨toName_inj h1, h2⟩⟩
      have hpure : ConLeche.defeqSpine (ConLeche.fueledFns mode eager env) env d (TrS s₀ a) (TrS s₀ b) =
          if toName n = toName n' ∧ (TrS s₀ a).getAppArgs.length = (TrS s₀ b).getAppArgs.length then
            match ConLeche.Level.isEquivList (us.map trL) (us'.map trL) with
            | some true => ConLeche.defEqList (ConLeche.fueledFns mode eager env) env d
                (TrS s₀ a).getAppArgs.reverse (TrS s₀ b).getAppArgs.reverse
            | _ => pure false
          else pure false := by
        unfold ConLeche.defeqSpine; rw [hTA, hTB]; rfl
      rw [hpure]
      by_cases hc : (n == n') = true ∧ (appArgs a).length = (appArgs b).length
      · have hc' := hcond.1 hc
        simp only [hc', and_self, ↓reduceIte]
        simp only [InLean.defeqSpineI, hA, hB, hc, and_self, ↓reduceIte, bind, StateT.bind,
          Except.bind] at hr
        cases hq : isEquivListLM us us' s₀ with
        | error x => simp [hq] at hr
        | ok p =>
          obtain ⟨ob, s₁⟩ := p
          obtain ⟨hs₁, ht₁, hob⟩ := tripleI_iff_run.1 (isEquivListLM_specI hs hokA hokB) ob s₁ hq
          rw [← hob]
          simp only [hq] at hr
          cases ob with
          | some bb =>
            cases bb with
            | true =>
              simp only at hr
              have hlA : OkSL s₀ (appArgs a) = true := OkSL_appArgs s₀ hoka
              have hlB : OkSL s₀ (appArgs b) = true := OkSL_appArgs s₀ hokb
              have hrevA : OkSL s₁ (appArgs a).reverse = true := by
                have := okSL_of_tabLe ht₁ hlA
                simp only [OkSL, List.all_reverse] at this ⊢; exact this
              have hrevB : OkSL s₁ (appArgs b).reverse = true := by
                have := okSL_of_tabLe ht₁ hlB
                simp only [OkSL, List.all_reverse] at this ⊢; exact this
              have eA : TrSL s₁ (appArgs a).reverse = (TrS s₀ a).getAppArgs.reverse := by
                rw [TrSL_reverse, TrSL_of_tabLe ht₁ hlA, TrSL_appArgs]
              have eB : TrSL s₁ (appArgs b).reverse = (TrS s₀ b).getAppArgs.reverse := by
                rw [TrSL_reverse, TrSL_of_tabLe ht₁ hlB, TrSL_appArgs]
              have hwsA : AllWS d (TrSL s₁ (appArgs a).reverse) := by
                rw [eA]; intro x hx; exact allWS_getAppArgs hwa x (List.mem_reverse.1 hx)
              have hwsB : AllWS d (TrSL s₁ (appArgs b).reverse) := by
                rw [eB]; intro x hx; exact allWS_getAppArgs hwb x (List.mem_reverse.1 hx)
              have hclA : AllClosed (TrSL s₁ (appArgs a).reverse) = true := by
                rw [eA]; have := allClosed_getAppArgs hca
                simp only [AllClosed, List.all_reverse] at this ⊢; exact this
              have hclB : AllClosed (TrSL s₁ (appArgs b).reverse) = true := by
                rw [eB]; have := allClosed_getAppArgs hcb
                simp only [AllClosed, List.all_reverse] at this ⊢; exact this
              obtain ⟨hs₂, ht₂, hrun⟩ := tripleI_iff_run.1
                (defEqListI_spec ih hs₁ hrevA hrevB hwsA hwsB hclA hclB) v s' hr
              rw [eA, eB] at hrun
              exact ⟨hs₂, ht₁.trans ht₂, hrun⟩
            | false =>
              simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              exact ⟨hs₁, ht₁, Runs.pure _⟩
          | none =>
            simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact ⟨hs₁, ht₁, Runs.pure _⟩
      · have hc' : ¬ (toName n = toName n' ∧
            (TrS s₀ a).getAppArgs.length = (TrS s₀ b).getAppArgs.length) := fun h => hc (hcond.2 h)
        simp only [hc', ↓reduceIte]
        simp only [InLean.defeqSpineI, hA, hB, hc, ↓reduceIte, pure, StateT.pure, Except.pure,
          Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨hs, TabLe.refl _, Runs.pure _⟩
    · have hB' : ∀ n us, Expr.getAppFnT b ≠ .const n us := fun n us h => hB ⟨n, us, h⟩
      rw [defeqSpine_notConstB _ _ (TrS_getAppFn_const s₀ hA) (TrS_getAppFn_notConst s₀ hB')]
      have hr' : InLean.defeqSpineI r d a b s₀ = .ok (false, s₀) := by
        unfold InLean.defeqSpineI
        rw [hA]; simp only
        generalize hx : Expr.getAppFnT b = x at hB'
        cases x with
        | const c ls => exact absurd rfl (hB' c ls)
        | _ => rfl
      rw [hr'] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  · have hA' : ∀ n us, Expr.getAppFnT a ≠ .const n us := fun n us h => hA ⟨n, us, h⟩
    rw [defeqSpine_notConstA _ _ (TrS_getAppFn_notConst s₀ hA')]
    have hr' : InLean.defeqSpineI r d a b s₀ = .ok (false, s₀) := by
      unfold InLean.defeqSpineI
      generalize hx : Expr.getAppFnT a = x at hA'
      cases x with
      | const c ls => exact absurd rfl (hA' c ls)
      | _ => rfl
    rw [hr'] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩

end Walks

/-! ## The last `DiscC1` twins: unfolding, the certificate loop, `Nat` literals -/

section DiscC1Rest

variable {r : InLean.CoreFnsI}

theorem TrS_mkAppN (s : InLean.CState) : ∀ (args : List Expr) (f : Expr),
    TrS s (mkAppN f args.toArray) = ConLeche.Expr.mkAppN (TrS s f) (TrSL s args)
  | [], f => rfl
  | a :: as, f => by
    have := TrS_mkAppN s as (.app f a)
    simp only [Lean.mkAppN, List.foldl_toArray', List.foldl_cons, Lean.mkApp] at this ⊢
    rw [this]; rfl

theorem OkS_mkAppN (s : InLean.CState) : ∀ (args : List Expr) (f : Expr),
    OkS s (mkAppN f args.toArray) = (OkS s f && OkSL s args)
  | [], f => by simp [Lean.mkAppN, OkSL_nil]
  | a :: as, f => by
    have := OkS_mkAppN s as (.app f a)
    simp only [Lean.mkAppN, List.foldl_toArray', List.foldl_cons, Lean.mkApp] at this ⊢
    rw [this, OkS_app, OkSL_cons, Bool.and_assoc]

/-- **InLean sees a stored definition wherever con-leche does** (O4, P3's;
the converse direction is `EnvRelI.val`). -/
@[expose] def EnvDefnI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop :=
  ∀ n cv v h, env.find? (toName n) = some (.defnInfo cv v h) → (fe.defnView? n).isSome = true

theorem unfoldDefinition_notConst {e : ConLeche.Expr} (h : ∀ n us, e.getAppFn ≠ .const n us) :
    ConLeche.unfoldDefinition env e = none := by
  unfold ConLeche.unfoldDefinition
  split
  · rename_i n us hh; exact absurd hh (h n us)
  · rfl

/-- **`unfoldDefinitionI`** (`unfoldDefinitionC_spec`'s twin): its answer is
con-leche's `unfoldDefinition` at the translation. -/
theorem unfoldDefinitionI_specI {fe : InLean.FEnv} (hfe : EnvRelI fe env) (hdef : EnvDefnI fe env)
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) {e : Expr} (he : OkS s₀ e = true) :
    ⦃fun s => s = s₀⦄ InLean.unfoldDefinitionI fe e
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      TrO s' o = ConLeche.unfoldDefinition env (TrS s₀ e); ⊤⦄ := by
  refine tripleI_iff_run.2 fun o s' hr => ?_
  by_cases hA : ∃ n us, Expr.getAppFnT e = .const n us
  · obtain ⟨n, us, hA⟩ := hA
    have hTA := TrS_getAppFn_const s₀ hA
    have hus : us.all okLv = true := by
      have := OkS_getAppFnT s₀ he; rw [hA] at this; exact this
    cases hv : fe.defnView? n with
    | none =>
      simp only [InLean.unfoldDefinitionI, hA, hv, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs, TabLe.refl _, rfl, ?_⟩
      unfold ConLeche.unfoldDefinition
      rw [hTA]
      simp only
      split
      · rename_i cv v h hf
        have := hdef n cv v h hf
        rw [hv] at this; exact absurd this (by simp)
      · rfl
    | some t =>
      obtain ⟨cv, v, hh⟩ := t
      obtain ⟨ccv, cvv, ch, hfind, -, hlp, -, -⟩ := hfe.val n cv v hh hv
      have hpure : ConLeche.unfoldDefinition env (TrS s₀ e) =
          if (us.map trL).length = ccv.levelParams.length then
            some (ConLeche.Expr.mkAppN (cvv.instantiateLevelParams ccv.levelParams (us.map trL))
              (TrS s₀ e).getAppArgs)
          else none := by
        unfold ConLeche.unfoldDefinition; rw [hTA]; simp only [hfind]
      rw [hpure]
      have hlen : ((us.map trL).length = ccv.levelParams.length) ↔
          (us.length = cv.levelParams.length) := by simp [hlp]
      by_cases hl : us.length = cv.levelParams.length
      · simp only [hlen.2 hl, ↓reduceIte]
        simp only [InLean.unfoldDefinitionI, hA, hv, hl, ↓reduceIte, bind, StateT.bind,
          Except.bind] at hr
        cases hq : constValAtM fe n us s₀ with
        | error x => simp [hq] at hr
        | ok p =>
          obtain ⟨t, s₁⟩ := p
          obtain ⟨hs₁, ht₁, hokt, hval⟩ :=
            tripleI_iff_run.1 (constValAtM_specI hfe hs n hus) t s₁ hq
          simp only [hq, InLean.mkAppNM, InLean.pollC, pure, StateT.pure, Except.pure] at hr
          have hr : (some (mkAppN t (appArgs e).toArray), s₁) = (o, s') := by
            generalize fe.limits.poll = q at hr
            cases q with
            | none => exact Except.ok.inj hr
            | some p =>
              dsimp only at hr
              generalize p (.unfold n) = q' at hr
              cases q' with
              | some l => exact nomatch hr
              | none => exact Except.ok.inj hr
          obtain ⟨rfl, rfl⟩ := hr
          have hargs : OkSL s₀ (appArgs e) = true := OkSL_appArgs s₀ he
          refine ⟨hs₁, ht₁, ?_, ?_⟩
          · rw [OkO_some, OkS_mkAppN, hokt, okSL_of_tabLe ht₁ hargs]; rfl
          · rw [TrO_some, TrS_mkAppN, TrSL_of_tabLe ht₁ hargs, TrSL_appArgs]
            simp only [ConLeche.Cached.constValAt?, hfind, Option.some.injEq] at hval
            rw [← hval]
      · simp only [mt hlen.1 hl, ↓reduceIte]
        simp only [InLean.unfoldDefinitionI, hA, hv, hl, ↓reduceIte, pure, StateT.pure,
          Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  · have hA' : ∀ n us, Expr.getAppFnT e ≠ .const n us := fun n us h => hA ⟨n, us, h⟩
    rw [unfoldDefinition_notConst (TrS_getAppFn_notConst s₀ hA')]
    have hr' : InLean.unfoldDefinitionI fe e s₀ = .ok (none, s₀) := by
      unfold InLean.unfoldDefinitionI
      generalize hx : Expr.getAppFnT e = x at hA'
      cases x with
      | const c ls => exact absurd rfl (hA' c ls)
      | _ => rfl
    rw [hr'] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, rfl, rfl⟩

@[conleche_grind =] theorem OkS_mvar (s : InLean.CState) (m : MVarId) : OkS s (.mvar m) = false := rfl

/-- The domain of a closed instantiated `∀` is closed. -/
theorem lbb_piDom {dom body : ConLeche.Expr} {acc : List ConLeche.Expr}
    (h : ((ConLeche.Expr.forallE dom body).instantiateList acc).looseBVarsBounded 0 = true) :
    (dom.instantiateList acc).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
  exact h.1
grind_pattern [conleche_grind] lbb_piDom =>
  ((ConLeche.Expr.forallE dom body).instantiateList acc).looseBVarsBounded 0, dom.instantiateList acc

/-- The peel step keeps a closed instantiated `∀` closed at a closed value. -/
theorem lbb_piPeel {dom body a : ConLeche.Expr} {acc : List ConLeche.Expr}
    (h : ((ConLeche.Expr.forallE dom body).instantiateList acc).looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) :
    (body.instantiateList (a :: acc)).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
  rw [ConLeche.Expr.instantiateList_cons]
  exact lbb_instantiate1 ha h.2
grind_pattern [conleche_grind] lbb_piPeel =>
  ((ConLeche.Expr.forallE dom body).instantiateList acc).looseBVarsBounded 0,
  body.instantiateList (a :: acc)

/-- The pure certificate loop at a translated, bulk-instantiated telescope,
stepped in InLean's shape (`iotaCertsFull_instList_cons`'s twin, its match on
InLean's `stripTop`). -/
theorem iotaCertsFull_TrS_cons {m : Type → Type} [Monad m] (r : ConLeche.CoreFns m)
    (d : Nat) (s : InLean.CState) {ty : Expr} (hty : OkS s ty = true) (acc : List Expr) (a : Expr)
    (rest : List Expr) :
    ConLeche.iotaCertsFull r env d ((TrS s ty).instantiateList (TrSL s acc)) (TrS s a :: TrSL s rest) =
      match EO.stripTop ty, acc with
      | .forallE _ dom body _, acc =>
          r.infer d (TrS s a) >>= fun ta =>
          r.defeq d ta ((TrS s dom).instantiateList (TrSL s acc)) >>= fun c =>
          if c then ConLeche.iotaCertsFull r env d ((TrS s body).instantiateList (TrSL s (a :: acc)))
            (TrSL s rest)
          else pure false
      | .bvar _, [] => pure false
      | .bvar k, _ :: _ =>
          ConLeche.iotaCertsFull r env d ((ConLeche.Expr.bvar k).instantiateList (TrSL s acc))
            (TrS s a :: TrSL s rest)
      | _, _ => pure false := by
  rw [← TrS_stripTop s ty]
  rw [← OkS_stripTop s ty] at hty
  generalize hx : EO.stripTop ty = x at hty
  cases x with
  | forallE n dom body bi =>
    rw [TrS_forallE, ConLeche.Cached.iotaCertsFull_instList_cons]; rfl
  | bvar k => cases acc with
    | nil => simp [TrS_bvar, TrSL_nil, ConLeche.Expr.instantiateList, ConLeche.iotaCertsFull]
    | cons => rfl
  | fvar id =>
    rw [TrS_fvar hty]
    cases acc <;> simp [ConLeche.Expr.instantiateList, ConLeche.iotaCertsFull]
  | mvar id => simp [OkS_mvar] at hty
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => cases acc <;> simp [TrS, trE, ConLeche.Expr.instantiateList, ConLeche.iotaCertsFull]

theorem iotaCertsFullIAux_specI (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : List Expr} {s₀ : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ ty = true → OkSL s₀ acc = true →
      AllClosed (TrSL s₀ acc) = true →
      ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc)) →
      ((TrS s₀ ty).instantiateList (TrSL s₀ acc)).looseBVarsBounded 0 = true →
      OkSL s₀ args = true → AllWS d (TrSL s₀ args) → AllClosed (TrSL s₀ args) = true →
      ⦃fun s => s = s₀⦄ InLean.iotaCertsFullIAux r d ty acc args
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
          Runs (ConLeche.iotaCertsFull (ConLeche.fueledFns mode eager env) env d
            ((TrS s₀ ty).instantiateList (TrSL s₀ acc)) (TrSL s₀ args)) v; ⊤⦄
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by
    sym only [conleche_grind, ConLeche.iotaCertsFull.eq_1] =>
      vcgen [InLean.iotaCertsFullIAux.eq_1] <;> finish
  | _ :: as, _, [], _, hs, _, _, _, _, _, _, _, _ => by
    sym only [conleche_grind, iotaCertsFull_TrS_cons] =>
      vcgen [InLean.iotaCertsFullIAux.eq_def, instListM_specI hs, ih.infer, ih.defeq,
        iotaCertsFullIAux_specI ih (args := as)] <;> finish
  | a :: as, _, _ :: _, _, hs, _, _, _, _, _, _, _, _ => by
    sym only [conleche_grind, iotaCertsFull_TrS_cons, ConLeche.Expr.instantiateList_nil] =>
      vcgen [InLean.iotaCertsFullIAux.eq_def, instListM_specI hs, ih.infer, ih.defeq,
        iotaCertsFullIAux_specI ih (args := as),
        iotaCertsFullIAux_specI ih (args := a :: as) (acc := [])] <;> finish
termination_by args _ acc => (args.length, acc.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- **`iotaCertsFullI`** (`iotaCertsFullC_spec`'s twin). -/
theorem iotaCertsFullI_specI (ih : KnotSpecI mode eager env r) {d : Nat} {args : List Expr}
    {ty : Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hty : OkS s₀ ty = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ ty)) (hc : (TrS s₀ ty).looseBVarsBounded 0 = true)
    (hargs : OkSL s₀ args = true) (hwa : AllWS d (TrSL s₀ args))
    (hca : AllClosed (TrSL s₀ args) = true) :
    ⦃fun s => s = s₀⦄ InLean.iotaCertsFullI r d ty args
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.iotaCertsFull (ConLeche.fueledFns mode eager env) env d (TrS s₀ ty)
          (TrSL s₀ args)) v; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.Expr.instantiateList_nil] =>
    vcgen [InLean.iotaCertsFullI, iotaCertsFullIAux_specI ih] <;> finish

/-! ### `reduceNat`'s vocabulary -/

theorem toName_eq_iff {a b : Name} : toName a = toName b ↔ a = b :=
  ⟨toName_inj, fun h => h ▸ rfl⟩

theorem cl_natPredName : ConLeche.natPredName = toName InLean.natPredName := rfl
theorem cl_natAddName : ConLeche.natAddName = toName InLean.natAddName := rfl
theorem cl_natSubName : ConLeche.natSubName = toName InLean.natSubName := rfl
theorem cl_natMulName : ConLeche.natMulName = toName InLean.natMulName := rfl
theorem cl_natPowName : ConLeche.natPowName = toName InLean.natPowName := rfl
theorem cl_natDivName : ConLeche.natDivName = toName InLean.natDivName := rfl
theorem cl_natModName : ConLeche.natModName = toName InLean.natModName := rfl
theorem cl_natGcdName : ConLeche.natGcdName = toName InLean.natGcdName := rfl
theorem cl_natLandName : ConLeche.natLandName = toName InLean.natLandName := rfl
theorem cl_natLorName : ConLeche.natLorName = toName InLean.natLorName := rfl
theorem cl_natXorName : ConLeche.natXorName = toName InLean.natXorName := rfl
theorem cl_natShiftLeftName : ConLeche.natShiftLeftName = toName InLean.natShiftLeftName := rfl
theorem cl_natShiftRightName : ConLeche.natShiftRightName = toName InLean.natShiftRightName := rfl
theorem cl_natBeqName : ConLeche.natBeqName = toName InLean.natBeqName := rfl
theorem cl_natBleName : ConLeche.natBleName = toName InLean.natBleName := rfl
theorem cl_natSuccName : ConLeche.natSuccName = toName InLean.natSuccName := rfl
theorem cl_natZeroName : ConLeche.natZeroName = toName InLean.natZeroName := rfl
theorem cl_boolTrueName : ConLeche.boolTrueName = toName InLean.boolTrueName := rfl
theorem cl_boolFalseName : ConLeche.boolFalseName = toName InLean.boolFalseName := rfl

@[conleche_grind =] theorem rawNatLit_TrS (s : InLean.CState) {e : Expr} (h : OkS s e = true) :
    ConLeche.rawNatLit? (TrS s e) = InLean.rawNatLitC? e := by
  rw [← TrS_stripTop s e]
  rw [← OkS_stripTop s e] at h
  unfold InLean.rawNatLitC?
  generalize hx : EO.stripTop e = x at h
  cases x with
  | lit l => cases l <;> rfl
  | const c us =>
    cases us with
    | nil =>
      simp only [TrS_const, List.map_nil, ConLeche.rawNatLit?]
      simp [cl_natZeroName, toName_eq_iff]
    | cons => rfl
  | fvar id => rw [TrS_fvar h]; rfl
  | mvar _ => simp [OkS_mvar] at h
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rfl

theorem natOpResult_TrO (s : InLean.CState) (c : Name) (a b : Nat) :
    TrO s (InLean.natOpResult c a b) = ConLeche.natOpResult (toName c) a b ∧
      OkO s (InLean.natOpResult c a b) = true := by
  simp only [InLean.natOpResult, ConLeche.natOpResult, cl_natPredName, cl_natAddName, cl_natSubName, cl_natMulName, cl_natPowName, cl_natDivName, cl_natModName, cl_natGcdName, cl_natLandName, cl_natLorName, cl_natXorName, cl_natShiftLeftName, cl_natShiftRightName, cl_natBeqName, cl_natBleName, cl_boolTrueName, cl_boolFalseName, toName_eq_iff, beq_iff_eq]
  refine ⟨?_, ?_⟩ <;> (
    by_cases h0 : c = InLean.natPredName
    · simp only [h0, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h0, ↓reduceIte]
    by_cases h1 : c = InLean.natAddName
    · simp only [h1, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h1, ↓reduceIte]
    by_cases h2 : c = InLean.natSubName
    · simp only [h2, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h2, ↓reduceIte]
    by_cases h3 : c = InLean.natMulName
    · simp only [h3, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h3, ↓reduceIte]
    by_cases h4 : c = InLean.natPowName
    · simp only [h4, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h4, ↓reduceIte]
    by_cases h5 : c = InLean.natDivName
    · simp only [h5, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h5, ↓reduceIte]
    by_cases h6 : c = InLean.natModName
    · simp only [h6, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h6, ↓reduceIte]
    by_cases h7 : c = InLean.natGcdName
    · simp only [h7, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h7, ↓reduceIte]
    by_cases h8 : c = InLean.natLandName
    · simp only [h8, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h8, ↓reduceIte]
    by_cases h9 : c = InLean.natLorName
    · simp only [h9, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h9, ↓reduceIte]
    by_cases h10 : c = InLean.natXorName
    · simp only [h10, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h10, ↓reduceIte]
    by_cases h11 : c = InLean.natShiftLeftName
    · simp only [h11, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h11, ↓reduceIte]
    by_cases h12 : c = InLean.natShiftRightName
    · simp only [h12, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h12, ↓reduceIte]
    by_cases h13 : c = InLean.natBeqName
    · simp only [h13, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h13, ↓reduceIte]
    by_cases h14 : c = InLean.natBleName
    · simp only [h14, ↓reduceIte]; first | rfl | (split <;> rfl)
    simp only [h14, ↓reduceIte]
    rfl)

@[conleche_grind =] theorem TrO_natOpResult (s : InLean.CState) (c : Name) (a b : Nat) :
    TrO s (InLean.natOpResult c a b) = ConLeche.natOpResult (toName c) a b :=
  (natOpResult_TrO s c a b).1

@[conleche_grind =] theorem OkO_natOpResult (s : InLean.CState) (c : Name) (a b : Nat) :
    OkO s (InLean.natOpResult c a b) = true :=
  (natOpResult_TrO s c a b).2

@[conleche_grind =] theorem lbb_lit (k : Nat) (l : ConLeche.Literal) :
    (ConLeche.Expr.lit l).looseBVarsBounded k = true := rfl

/-- A native `Nat` operation's answer is closed. -/
@[conleche_grind .] theorem optClosed_natOpResult (c : ConLeche.Name) (a b : Nat) :
    OptClosed (ConLeche.natOpResult c a b) = true := by
  cases h : ConLeche.natOpResult c a b with
  | none => rfl
  | some e =>
    rcases ConLeche.natOpResult_shape h with ⟨n, rfl⟩ | ⟨bn, rfl⟩ <;> rfl

theorem natOpWfNames_contains (c : Name) :
    ConLeche.natOpWfNames.contains (toName c) = InLean.natOpWfNames.contains c := by
  have hm : ConLeche.natOpWfNames = InLean.natOpWfNames.map toName := rfl
  rw [hm, Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨a, ha, h⟩ => toName_inj h ▸ ha, fun h => ⟨c, h, rfl⟩⟩

/-- `reduceNat` at a translation, in InLean's nested shape (one constructor
per level, the head read through `stripTop`). -/
theorem reduceNat_TrS {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (s : InLean.CState) {e : Expr} (h : OkS s e = true) :
    ConLeche.reduceNat r env d (TrS s e) =
      match EO.stripTop e with
      | .app f₁ b =>
        match EO.stripTop f₁ with
        | .const c us =>
          match us with
          | [] => ConLeche.reduceNat r env d (.app (.const (toName c) []) (TrS s b))
          | _ :: _ => pure none
        | .app f₂ a =>
          match EO.stripTop f₂ with
          | .const c us =>
            match us with
            | [] => ConLeche.reduceNat r env d (.app (.app (.const (toName c) []) (TrS s a)) (TrS s b))
            | _ :: _ => pure none
          | _ => pure none
        | _ => pure none
      | _ => pure none := by
  rw [← TrS_stripTop s e]; rw [← OkS_stripTop s e] at h
  generalize hx : EO.stripTop e = x at h
  cases x with
  | app f₁ b =>
    dsimp only
    simp only [OkS_app, Bool.and_eq_true] at h
    obtain ⟨h1, -⟩ := h
    rw [TrS_app, ← TrS_stripTop s f₁]; rw [← OkS_stripTop s f₁] at h1
    generalize hy : EO.stripTop f₁ = y at h1
    cases y with
    | const c us => cases us <;> rfl
    | app f₂ a =>
      dsimp only
      simp only [OkS_app, Bool.and_eq_true] at h1
      obtain ⟨h2, -⟩ := h1
      rw [TrS_app, ← TrS_stripTop s f₂]; rw [← OkS_stripTop s f₂] at h2
      generalize hz : EO.stripTop f₂ = z at h2
      cases z with
      | const c us => cases us <;> rfl
      | fvar id => rw [TrS_fvar h2]; rfl
      | mvar _ => simp [OkS_mvar] at h2
      | mdata _ y => exact (stripTop_ne_mdata hz).elim
      | _ => rfl
    | fvar id => rw [TrS_fvar h1]; rfl
    | mvar _ => simp [OkS_mvar] at h1
    | mdata _ y => exact (stripTop_ne_mdata hy).elim
    | _ => rfl
  | fvar id => rw [TrS_fvar h]; rfl
  | mvar _ => simp [OkS_mvar] at h
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rfl

/-- **`reduceNatI`** (`reduceNatC_spec`'s twin). -/
theorem reduceNatI_specI (ih : KnotSpecI mode eager env r) {fe : InLean.FEnv}
    (hdom : EnvDomI fe env) {d : Nat} {e : Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (he : OkS s₀ e = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ e)) (hc : (TrS s₀ e).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.reduceNatI r fe d e
    ⦃fun o s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.reduceNat (ConLeche.fueledFns mode eager env) env d (TrS s₀ e)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄ := by
  sym only [conleche_grind, reduceNat_TrS (env := env) (ConLeche.fueledFns mode eager env) d s₀ he, ConLeche.reduceNat.eq_1,
      ConLeche.reduceNat.eq_2, natLitStoredF_I hdom, cl_natSuccName, cl_natAddName, cl_natSubName,
      cl_natMulName, cl_natPowName, cl_natBeqName, cl_natBleName, cl_natDivName, cl_natModName,
      cl_natGcdName, cl_natLandName, cl_natLorName, cl_natXorName, cl_natShiftLeftName,
      cl_natShiftRightName, toName_eq_iff, natOpWfNames_contains] =>
    -- `gen := 10`: `reduceNat_TrS`'s three nested matches on InLean's `stripTop`
    -- are reduced by grind's match congruence, which names the arms' fields
    -- afresh and equates them with the split's by injectivity; the binary
    -- arm's comparands sit two generations past the default 8.
    vcgen [InLean.reduceNatI, ih.whnf] <;> finish (gen := 10)

end DiscC1Rest

end InLeanProof
