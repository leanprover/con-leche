module

public import InLeanProof.KnotI
public import ConLeche.Verify.Cached.SimCEff
import ConLeche.Verify.Level
/- `Expr`'s hash and `hasLooseBVars` read the computed field; their bodies are
not exposed by `Lean.Expr`. -/
import all Lean.Expr

/-!
# The state operations' triples (task #451, lane P2-whnf)

One `Std.WP` triple per `InLean/StateC.lean` (and `CoreC.lean`) state
operation the body walks call: the twins of `Verify/Cached/SimCEff.lean`'s
`…_spec` lemmas.  The post of each is what `KnotSpecI`'s posts carry: the
invariant `CSOKI` at the final state, the table grown (`TabLe`), the answer
has a reading (`OkS`), and its translation is con-leche's operation on the
inputs' translations.

The pure wrappers (`inst1M`, `instListRevM`, `abstractRangeM`,
`instLevelParamsM`, `liftFueled`) leave the state alone: their triples are
P1's operation lemmas (`InLeanProof/Ops.lean`) through the bridge
`TransS_of_ok`.  Interning (`mkFVarM`) is P1's `mkFVarM_ok`.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## A triple is a statement about the successful runs -/

/-- **An InLean triple from a fixed state is a statement about its
successful runs** (`triple_iff_run`'s twin). -/
theorem tripleI_iff_run {β : Type} {s₀ : InLean.CState} {c : InLean.CheckCM β}
    {Q : β → InLean.CState → Prop} :
    (⦃fun s => s = s₀⦄ c ⦃fun v s' => Q v s'; ⊤⦄) ↔
      ∀ v s', c s₀ = .ok (v, s') → Q v s' := by
  constructor
  · intro ⟨h⟩ v s' hr
    have := h s₀ rfl
    rw [StateT.wp_apply_eq, StateT.run, hr] at this
    exact this
  · intro h
    refine ⟨fun s hs => ?_⟩
    obtain rfl : s = s₀ := hs
    rw [StateT.wp_apply_eq, StateT.run]
    cases hc : c s with
    | ok r => obtain ⟨v, s'⟩ := r; exact h v s' hc
    | error e =>
      show (⊤ : InLean.CheckError → Prop) e
      rw [Lean.Order.top_apply, Lean.Order.top_prop_eq]; trivial

/-! ## The pure syntactic wrappers -/

section Pure

variable {s₀ : InLean.CState}

/-- **One-value instantiation** (`inst1M_spec`'s twin), at a closed value. -/
theorem inst1M_specI (hs : CSOKI mode eager env s₀) {e v : Expr} (he : OkS s₀ e = true)
    (hv : OkS s₀ v = true) (hcl : (TrS s₀ v).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inst1M e v
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).instantiate1 (TrS s₀ v) 0; ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  simp only [inst1M, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨hs, TabLe.refl _, (TrS_inst1 he hv hcl).1, (TrS_inst1 he hv hcl).2⟩

/-- A list of values read at a state, closed and in range, as P1's
`SubstReads` wants it. -/
theorem substReads_of_ok {s : InLean.CState} {vs : Array Expr} (hv : OkSL s vs.toList = true)
    (hcl : AllClosed (TrSL s vs.toList) = true) :
    SubstReads (FVarTable.trans (tableOf s)) vs (TrSL s vs.toList) where
  len := by simp [TrSL]
  entry j hj := by
    have hj' : vs[j] ∈ vs.toList := Array.getElem_mem_toList hj
    have hok : OkS s vs[j] = true := by
      simp only [OkSL, List.all_eq_true] at hv; exact hv _ hj'
    rw [show (TrSL s vs.toList)[j]'(by simp [TrSL]; exact hj) = TrS s vs[j] by simp [TrSL]]
    exact TransS_of_ok hok
  closed cv hcv := by
    simp only [AllClosed, List.all_eq_true] at hcl; exact hcl cv hcv
  range j hj := by
    have hj' : vs[j] ∈ vs.toList := Array.getElem_mem_toList hj
    simp only [OkSL, List.all_eq_true] at hv
    exact RangeOk_of_OkS (hv _ hj')

/-- **Bulk instantiation, innermost first** (`instListRevM_spec`'s twin), at
closed values. -/
theorem instListRevM_specI (hs : CSOKI mode eager env s₀) {e : Expr} {vs : Array Expr}
    (he : OkS s₀ e = true) (hv : OkSL s₀ vs.toList = true)
    (hcl : AllClosed (TrSL s₀ vs.toList) = true) :
    ⦃fun s => s = s₀⦄ instListRevM e vs
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).instantiateList (TrSL s₀ vs.toList).reverse 0; ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  simp only [instListRevM, pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  have hsr := substReads_of_ok hv hcl
  have h := toExpr_instantiateRev (FVarTable.trans_fvarsOnly _) hsr (RangeOk_of_OkS he)
    (TransS_of_ok he)
  have hmem : ∀ x ∈ vs.toList, Expr.RangeOk x ∧ x.looseBVarRange = 0 := by
    intro x hx
    have hok : OkS s₀ x = true := by
      simp only [OkSL, List.all_eq_true] at hv; exact hv x hx
    have hcx : (TrS s₀ x).looseBVarsBounded 0 = true := by
      simp only [AllClosed, TrSL, List.all_eq_true, List.mem_map] at hcl
      exact hcl _ ⟨x, hx, rfl⟩
    refine ⟨RangeOk_of_OkS hok, ?_⟩
    rw [looseBVarRange_toExpr (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS hok) (TransS_of_ok hok)]
    have := ConLeche.Expr.looseBVarsBounded_iff.1 hcx
    omega
  have hmemR : ∀ j (hj : j < vs.reverse.size), vs.reverse[j] ∈ vs.toList := by
    intro j hj
    exact Array.mem_toList_iff.2 (Array.mem_reverse.1 (Array.getElem_mem hj))
  have hr' : Expr.RangeOk (EO.instantiateRev e vs) := instantiateRev_eq e vs ▸
    RangeOk_instantiate (RangeOk_of_OkS he)
      (fun j hj => (hmem _ (hmemR j hj)).1) (fun j hj => (hmem _ (hmemR j hj)).2)
  obtain ⟨hok, htr⟩ := ok_of_TransS hr' h
  exact ⟨hs, TabLe.refl _, hok, htr⟩

/-- **Abstraction by depth** (`abstractRangeM_spec`'s twin): a run succeeds
only where no index left the range, and then reads as con-leche's. -/
theorem abstractRangeM_specI (hs : CSOKI mode eager env s₀) {e : Expr} (he : OkS s₀ e = true)
    (d k : Nat) :
    ⦃fun s => s = s₀⦄ abstractRangeM e d k
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).abstractRange d k 0; ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  by_cases hm : (EO.abstractDepths e d k).hasExprMVar = true
  · simp [abstractRangeM, hm, bind, StateT.bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, StateT.lift] at hr
  · simp only [abstractRangeM, hm, pure, StateT.pure, Except.pure, Bool.false_eq_true,
      ↓reduceIte] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hrr : Expr.RangeOk (EO.abstractDepthsFrom e d k 0) :=
      RangeOk_abstractDepthsFrom (RangeOk_of_OkS he) d k 0
    have hm' : emvarS (EO.abstractDepthsFrom e d k 0) = false := by
      rw [← Expr.hasExprMVar_eq hrr]; simpa [EO.abstractDepths] using hm
    have h := toExpr_abstractDepthsFrom (FVarTable.trans_depthOK _) (RangeOk_of_OkS he)
      (TransS_of_ok he) d k 0 hm'
    obtain ⟨hok, htr⟩ := ok_of_TransS hrr h
    exact ⟨hs, TabLe.refl _, hok, htr⟩

/-- **The level-depth checked instantiation of level parameters**
(`instLevelParams_spec`'s twin), on a term without free variables at levels
with a reading. -/
theorem instLevelParamsM_specI (hs : CSOKI mode eager env s₀) {ks : List Name} {us : List Level}
    {e : Expr} (he : OkS s₀ e = true) (hf : fvarS e = false) (hus : us.all okLv = true) :
    ⦃fun s => s = s₀⦄ instLevelParamsM ks us e
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).instantiateLevelParams (ks.map toName) (us.map trL); ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  cases hc : EO.instLevelParamsChecked? e ks us with
  | none =>
    simp [instLevelParamsM, hc, throw, throwThe, MonadExceptOf.throw, StateT.lift,
      Functor.map, Except.map] at hr
  | some r' =>
    simp only [instLevelParamsM, hc, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hus' : ∀ u ∈ us, depthS u ≤ maxLevelDepth := by
      intro u hu
      simp only [List.all_eq_true, okLv, Bool.and_eq_true, decide_eq_true_eq] at hus
      exact (hus u hu).2
    have hl : toLevels us = some (us.map trL) := toLevels_of_all (by
      simp only [List.all_eq_true, okLv, Bool.and_eq_true] at hus ⊢; exact fun u hu => (hus u hu).1)
    obtain ⟨rfl, hrr, hm⟩ := instLevelParamsChecked_ok (RangeOk_of_OkS he) hus' hc
    have h := toExpr_instantiateLevelParams (fv := FVarTable.trans (tableOf s₀))
      (RangeOk_of_OkS he) hf (TransS_of_ok he) ks hl hm
    obtain ⟨hok, htr⟩ := ok_of_TransS hrr h
    exact ⟨hs, TabLe.refl _, hok, htr⟩

/-- **An exhausted level comparison is a decline** (`liftFueled_spec`'s
twin): a run succeeds only on `some a`, with `a`. -/
theorem liftFueled_specI {α : Type} (hs : CSOKI mode eager env s₀) (what : String)
    (o : Option α) :
    ⦃fun s => s = s₀⦄ (liftFueled what o : InLean.CheckCM α)
    ⦃fun a s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ o = some a; ⊤⦄ := by
  refine tripleI_iff_run.2 fun a s' hr => ?_
  cases o with
  | some x =>
    simp only [liftFueled, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, rfl⟩
  | none =>
    simp [liftFueled, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map,
      Except.map] at hr

end Pure

/-! ## The invariant along a growing table

Every `CSOKI` clause states the translations it reads as facts, so a later
state with a larger table keeps it (`toExpr_mono`). -/

section Grow

/-- A list's translation, read at a smaller table, is read the same at a larger
one. -/
theorem mapM_toExpr_mono {fv₁ fv₂ : FVarId → Option ConLeche.Expr} (hle : FvLe fv₁ fv₂) :
    ∀ (vs : List Expr) (cvs : List ConLeche.Expr),
      vs.mapM (toExpr fv₁) = some cvs → vs.mapM (toExpr fv₂) = some cvs
  | [], cvs, h => h
  | v :: vs, cvs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨cv, hv, cvs', hvs, rfl⟩ := h
    exact ⟨cv, toExpr_mono hle v cv hv, cvs', mapM_toExpr_mono hle vs cvs' hvs, rfl⟩

theorem UnaryOK.of_tabLe {s₁ s₂ : InLean.CState} (h : TabLe s₁ s₂)
    {spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr} {k v : Expr}
    (hk : UnaryOK s₁ spec k v) : UnaryOK s₂ spec k v := by
  obtain ⟨ck, cv, hck, hcv, hr, hc, hF⟩ := hk
  exact ⟨ck, cv, toExpr_mono h k ck hck, toExpr_mono h v cv hcv, hr, hc, hF⟩

theorem BinaryOK.of_tabLe {s₁ s₂ : InLean.CState} (h : TabLe s₁ s₂)
    {spec : Nat → Nat → ConLeche.Expr → ConLeche.Expr → ConLeche.CheckM Bool} {a b : Expr}
    {r : Bool} (hk : BinaryOK s₁ spec a b r) : BinaryOK s₂ spec a b r := by
  obtain ⟨ca, cb, hca, hcb, hF⟩ := hk
  exact ⟨ca, cb, toExpr_mono h a ca hca, toExpr_mono h b cb hcb, hF⟩

theorem ModeMemosOKI.of_tabLe {s₁ s₂ : InLean.CState} (h : TabLe s₁ s₂) {mm : InLean.ModeMemos}
    (hm : ModeMemosOKI mode env s₁ mm) : ModeMemosOKI mode env s₂ mm where
  whnfCoreC k v hl := (hm.whnfCoreC k v hl).of_tabLe h
  whnfCoreCheapC k v hl := (hm.whnfCoreCheapC k v hl).of_tabLe h
  whnfC k v hl := (hm.whnfC k v hl).of_tabLe h
  inferC k v hl := (hm.inferC k v hl).of_tabLe h
  inferIOC k v hl := (hm.inferIOC k v hl).of_tabLe h
  defeqC a b r hl := (hm.defeqC a b r hl).of_tabLe h

/-- **The invariant survives interning**: a state that differs only in the
free-variable table, a larger one that keeps its own invariant. -/
theorem CSOKI.of_tabLe {s : InLean.CState} (hs : CSOKI mode eager env s) {seen cls tys}
    (h : TabLe s { s with fvSeen := seen, fvCls := cls, fvTys := tys })
    (hfv : FVTableOK { s with fvSeen := seen, fvCls := cls, fvTys := tys })
    (hcl : ∀ (n : Nat) (ty : Expr) (cty : ConLeche.Expr), tys[n]? = some ty →
      TransS { s with fvSeen := seen, fvCls := cls, fvTys := tys } ty = some cty →
      cty.looseBVarsBounded 0 = true) :
    CSOKI mode eager env { s with fvSeen := seen, fvCls := cls, fvTys := tys } where
  fv := hfv
  fvClosed := hcl
  whnfCoreC k v hl := (hs.whnfCoreC k v hl).of_tabLe h
  whnfCoreCheapC k v hl := (hs.whnfCoreCheapC k v hl).of_tabLe h
  whnfC k v hl := (hs.whnfC k v hl).of_tabLe h
  inferC k v hl := (hs.inferC k v hl).of_tabLe h
  inferIOC k v hl := (hs.inferIOC k v hl).of_tabLe h
  defeqC a b r hl := (hs.defeqC a b r hl).of_tabLe h
  constTy n us i hl := by
    obtain ⟨cus, ci, ct, h1, h2, h3, h4, h5⟩ := hs.constTy n us i hl
    exact ⟨cus, ci, ct, h1, h2, toExpr_mono h i ct h3, h4, h5⟩
  constVal n us i hl := by
    obtain ⟨cus, cv, v, hh, cval, h1, h2, h3, h4, h5⟩ := hs.constVal n us i hl
    exact ⟨cus, cv, v, hh, cval, h1, h2, toExpr_mono h i cval h3, h4, h5⟩
  ruleRhs c j us i hl := by
    obtain ⟨cus, cv, mI, rP, isK, rules, rl, cr, h1, h2, h3, h4, h5, h6⟩ := hs.ruleRhs c j us i hl
    exact ⟨cus, cv, mI, rP, isK, rules, rl, cr, h1, h2, h3, toExpr_mono h i cr h4, h5, h6⟩
  lsimp := hs.lsimp
  eqv := hs.eqv
  instC k vs r hl := by
    obtain ⟨ck, cvs, cr, h1, h2, h3, h4, h5, h6⟩ := hs.instC k vs r hl
    exact ⟨ck, cvs, cr, toExpr_mono h k ck h1, mapM_toExpr_mono h vs cvs h2,
      toExpr_mono h r cr h3, h4, h5, h6⟩
  eager := hs.eager.of_tabLe h

end Grow

/-! ## Interning (O3's triple) -/

/-- What translates to a free variable is in range (a free variable, possibly
under `mdata`). -/
theorem rangeOk_of_toExpr_fvar {fv : FVarId → Option ConLeche.Expr} :
    ∀ {e : Expr} {d : Nat} {c : ConLeche.Expr}, toExpr fv e = some (.fvar d c) → Expr.RangeOk e := by
  intro e
  induction e with
  | fvar _ => intro _ _ _; trivial
  | mdata _ x ih => intro d c h; exact ih (d := d) (c := c) (by simpa [toExpr] using h)
  | bvar _ => intro _ _ h; simp [toExpr] at h
  | lit _ => intro _ _ h; simp [toExpr] at h
  | mvar _ => intro _ _ h; simp [toExpr] at h
  | sort _ => intro _ _ h; simp [toExpr] at h
  | const _ _ => intro _ _ h; simp [toExpr] at h
  | app f a _ _ =>
    intro _ _ h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | lam _ t b _ _ _ =>
    intro _ _ h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | forallE _ t b _ _ _ =>
    intro _ _ h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | letE _ t v b _ _ _ _ =>
    intro _ _ h
    simp only [toExpr, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, h⟩ := h; cases h
  | proj _ _ x _ =>
    intro _ _ h
    simp only [toExpr, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h; cases h

/-- Interning keeps the type table or pushes the type. -/
theorem mkFVarM_tys {s s' : InLean.CState} {d : Nat} {ty r : Expr}
    (hrun : mkFVarM d ty s = .ok (r, s')) : s'.fvTys = s.fvTys ∨ s'.fvTys = s.fvTys.push ty := by
  simp only [mkFVarM, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    Except.pure] at hrun
  split at hrun
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact .inl rfl
  · split at hrun
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact .inl rfl
    · simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact .inr rfl

/-- **Interning a free variable** (`.fvar d ty`'s twin): the answer reads as
con-leche's free variable at depth `d` with the type's translation, and the
table grows. -/
theorem mkFVarM_specI {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (d : Nat) {ty : Expr}
    (hty : OkS s₀ ty = true) (htc : (TrS s₀ ty).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ mkFVarM d ty
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = .fvar d (TrS s₀ ty); ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  have htys := mkFVarM_tys hr
  obtain ⟨hfv, htr, hle, seen, cls, tys, rfl⟩ := mkFVarM_ok hs.fv (TransS_of_ok hty) (RangeOk_of_OkS hty) hr
  have hr' : Expr.RangeOk r := rangeOk_of_toExpr_fvar htr
  obtain ⟨hok, htr'⟩ := ok_of_TransS hr' htr
  -- an old number reads its old (closed) type; a new one reads `ty`
  have hold : ∀ (n : Nat) (ty' : Expr) (cty : ConLeche.Expr), s₀.fvTys[n]? = some ty' →
      TransS { s₀ with fvSeen := seen, fvCls := cls, fvTys := tys } ty' = some cty →
      cty.looseBVarsBounded 0 = true := by
    intro n ty' cty hn hc
    obtain ⟨c0, hc0⟩ := hs.fv.ty n ty' hn
    have h1 := toExpr_mono ((tableOf s₀).inner_le_trans n) ty' c0 hc0
    have h2 := toExpr_mono hle ty' c0 h1
    unfold TransS at hc
    rw [h2] at hc
    obtain rfl := Option.some.inj hc
    exact hs.fvClosed n ty' c0 hn h1
  have hcl : ∀ (n : Nat) (ty' : Expr) (cty : ConLeche.Expr), tys[n]? = some ty' →
      TransS { s₀ with fvSeen := seen, fvCls := cls, fvTys := tys } ty' = some cty →
      cty.looseBVarsBounded 0 = true := by
    intro n ty' cty hn hc
    rcases htys with htys | htys
    · simp only at htys; subst htys; exact hold n ty' cty hn hc
    · simp only at htys; subst htys
      rw [Array.getElem?_push] at hn
      split at hn
      · obtain rfl := (Option.some.inj hn).symm
        have h2 := toExpr_mono hle ty' _ (TransS_of_ok hty)
        unfold TransS at hc
        rw [h2] at hc
        obtain rfl := Option.some.inj hc
        exact htc
      · exact hold n ty' cty hn hc
  exact ⟨CSOKI.of_tabLe hs hle hfv hcl, hle, hok, htr'⟩

/-! ## Terms without free variables

A stored constant's type, value or rule has no free variable: it reads the
same under every table. -/

theorem toExpr_noFVar {fv₁ fv₂ : FVarId → Option ConLeche.Expr} :
    ∀ e : Expr, fvarS e = false → toExpr fv₁ e = toExpr fv₂ e := by
  intro e
  induction e with
  | fvar id => intro h; simp [fvarS] at h
  | app f a ihf iha =>
    intro h; simp only [fvarS, Bool.or_eq_false_iff] at h; simp [toExpr, ihf h.1, iha h.2]
  | lam _ t b _ iht ihb =>
    intro h; simp only [fvarS, Bool.or_eq_false_iff] at h; simp [toExpr, iht h.1, ihb h.2]
  | forallE _ t b _ iht ihb =>
    intro h; simp only [fvarS, Bool.or_eq_false_iff] at h; simp [toExpr, iht h.1, ihb h.2]
  | letE _ t v b _ iht ihv ihb =>
    intro h; simp only [fvarS, Bool.or_eq_false_iff] at h
    simp [toExpr, iht h.1.1, ihv h.1.2, ihb h.2]
  | mdata _ x ih => intro h; simp only [fvarS] at h; simp [toExpr, ih h]
  | proj _ _ x ih => intro h; simp only [fvarS] at h; simp [toExpr, ih h]
  | _ => intro _; rfl

/-- A term without free variables that translates (as a closed term) has a
reading at every state, with that translation. -/
theorem okS_of_toExprC {s : InLean.CState} {e : Expr} {c : ConLeche.Expr} (hf : fvarS e = false)
    (hr : Expr.RangeOk e) (h : toExprC e = some c) : OkS s e = true ∧ TrS s e = c := by
  have : TransS s e = some c := by
    unfold TransS; rw [toExpr_noFVar e hf]; exact h
  exact ok_of_TransS hr this

/-! ## The bulk-instantiation memo

`InstKey` compares by `keyEq` (binder data erased) term and values, and hashes
by Lean's cached hash, which reads no binder data: the keys are lawful.  A hit
is the stored value, right by the `instC` clause at the query key; a miss
instantiates and inserts. -/

section InstMemo

theorem keyEqList_iff : ∀ {as bs : List Expr}, keyEqList as bs = true ↔ as.map eraseK = bs.map eraseK
  | [], [] => by simp [keyEqList]
  | [], _ :: _ => by simp [keyEqList]
  | _ :: _, [] => by simp [keyEqList]
  | a :: as, b :: bs => by
    simp only [keyEqList, Bool.and_eq_true, Expr.keyEq, decide_eq_true_eq, List.map_cons,
      List.cons.injEq, keyEqList_iff]

theorem instKey_beq_iff {a b : InstKey} :
    (a == b) = true ↔ eraseK a.e = eraseK b.e ∧ a.vs.map eraseK = b.vs.map eraseK := by
  show (Expr.keyEq a.e b.e && keyEqList a.vs b.vs) = true ↔ _
  simp only [Bool.and_eq_true, Expr.keyEq, decide_eq_true_eq, keyEqList_iff]

instance : EquivBEq InstKey where
  rfl := by intro a; exact instKey_beq_iff.2 ⟨rfl, rfl⟩
  symm h := by
    obtain ⟨h1, h2⟩ := instKey_beq_iff.1 h; exact instKey_beq_iff.2 ⟨h1.symm, h2.symm⟩
  trans h₁ h₂ := by
    obtain ⟨h1, h2⟩ := instKey_beq_iff.1 h₁; obtain ⟨h3, h4⟩ := instKey_beq_iff.1 h₂
    exact instKey_beq_iff.2 ⟨h1.trans h3, h2.trans h4⟩

theorem hash_list_of_erase : ∀ {as bs : List Expr} (acc : UInt64), as.map eraseK = bs.map eraseK →
    as.foldl (fun r a => mixHash r (hash a)) acc = bs.foldl (fun r a => mixHash r (hash a)) acc
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, acc, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab : hash a = hash b := by
      show a.data.hash = b.data.hash; rw [← data_eraseK a, h.1, data_eraseK]
    simp only [List.foldl_cons, hab]
    exact hash_list_of_erase _ h.2

instance : LawfulHashable InstKey where
  hash_eq a b h := by
    obtain ⟨h1, h2⟩ := instKey_beq_iff.1 h
    show mixHash (hash a.e) (hash a.vs) = mixHash (hash b.e) (hash b.vs)
    have he : hash a.e = hash b.e := by
      show a.e.data.hash = b.e.data.hash; rw [← data_eraseK a.e, h1, data_eraseK]
    have hv : hash a.vs = hash b.vs := hash_list_of_erase 7 h2
    rw [he, hv]

/-- A list of terms with a reading translates, entry by entry. -/
theorem mapM_TransS_of_ok {s : InLean.CState} :
    ∀ {vs : List Expr}, OkSL s vs = true → vs.mapM (TransS s) = some (TrSL s vs)
  | [], _ => rfl
  | v :: vs, h => by
    simp only [OkSL, List.all_cons, Bool.and_eq_true] at h
    simp only [List.mapM_cons, TransS_of_ok h.1, mapM_TransS_of_ok (vs := vs) h.2, TrSL_cons,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- `keyEq`-equal value lists translate alike. -/
theorem mapM_toExpr_of_erase {fv : FVarId → Option ConLeche.Expr} :
    ∀ {as bs : List Expr}, as.map eraseK = bs.map eraseK → as.mapM (toExpr fv) = bs.mapM (toExpr fv)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have hab : toExpr fv a = toExpr fv b := by rw [← toExpr_eraseK fv a, h.1, toExpr_eraseK]
    simp only [List.mapM_cons, hab, mapM_toExpr_of_erase h.2]

/-- Values with a reading, closed: their array is a substitution P1's lemma
reads, and its entries are in range with no loose variable. -/
theorem closed_entries {s : InLean.CState} {vs : List Expr} (hv : OkSL s vs = true)
    (hcl : AllClosed (TrSL s vs) = true) :
    ∀ x ∈ vs, Expr.RangeOk x ∧ x.looseBVarRange = 0 := by
  intro x hx
  have hok : OkS s x = true := by simp only [OkSL, List.all_eq_true] at hv; exact hv x hx
  have hcx : (TrS s x).looseBVarsBounded 0 = true := by
    simp only [AllClosed, TrSL, List.all_eq_true, List.mem_map] at hcl
    exact hcl _ ⟨x, hx, rfl⟩
  refine ⟨RangeOk_of_OkS hok, ?_⟩
  rw [looseBVarRange_toExpr (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS hok) (TransS_of_ok hok)]
  have := ConLeche.Expr.looseBVarsBounded_iff.1 hcx
  omega

/-- **The invariant with the bulk-instantiation memo replaced**: the other
clauses read nothing of it. -/
theorem CSOKI.setInstC {s : InLean.CState} (hs : CSOKI mode eager env s)
    {mp : Std.HashMap InstKey Expr}
    (h : ∀ k vs r, mp[InstKey.mk k vs]? = some r → ∃ ck cvs cr,
      TransS s k = some ck ∧ vs.mapM (TransS s) = some cvs ∧ TransS s r = some cr ∧
      Expr.RangeOk r ∧ (∀ cv ∈ cvs, cv.looseBVarsBounded 0 = true) ∧
      cr = ck.instantiateList cvs 0) :
    CSOKI mode eager env { s with instC := mp } where
  fv := ⟨hs.fv.cls, hs.fv.distinct, hs.fv.ty, hs.fv.seen, hs.fv.range⟩
  fvClosed := hs.fvClosed
  whnfCoreC := hs.whnfCoreC
  whnfCoreCheapC := hs.whnfCoreCheapC
  whnfC := hs.whnfC
  inferC := hs.inferC
  inferIOC := hs.inferIOC
  defeqC := hs.defeqC
  constTy := hs.constTy
  constVal := hs.constVal
  ruleRhs := hs.ruleRhs
  lsimp := hs.lsimp
  eqv := hs.eqv
  instC := h
  eager := ⟨hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC, hs.eager.whnfC, hs.eager.inferC,
    hs.eager.inferIOC, hs.eager.defeqC⟩

/-- **Bulk instantiation through the persistent memo** (`instListM_spec`'s
twin), at closed values. -/
theorem instListM_specI {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) {e : Expr}
    {vs : List Expr} (he : OkS s₀ e = true) (hv : OkSL s₀ vs = true)
    (hcl : AllClosed (TrSL s₀ vs) = true) :
    ⦃fun s => s = s₀⦄ instListM e vs
    ⦃fun r s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' r = true ∧
      TrS s' r = (TrS s₀ e).instantiateList (TrSL s₀ vs) 0; ⊤⦄ := by
  refine tripleI_iff_run.2 fun r s' hr => ?_
  have hmem := closed_entries hv hcl
  -- the computed instance, read through P1's lemma
  have hsr : SubstReads (FVarTable.trans (tableOf s₀)) vs.toArray (TrSL s₀ vs) := by
    have := substReads_of_ok (s := s₀) (vs := vs.toArray) (by simpa using hv) (by simpa using hcl)
    simpa using this
  have hcomp : OkS s₀ (e.instI vs.toArray) = true ∧
      TrS s₀ (e.instI vs.toArray) = (TrS s₀ e).instantiateList (TrSL s₀ vs) 0 := by
    have h := toExpr_instantiate (FVarTable.trans_fvarsOnly _) hsr (RangeOk_of_OkS he)
      (TransS_of_ok he)
    have hr' : Expr.RangeOk (EO.instantiate e vs.toArray) :=
      RangeOk_instantiate (RangeOk_of_OkS he)
        (fun j hj => (hmem _ (by simp)).1) (fun j hj => (hmem _ (by simp)).2)
    exact ok_of_TransS hr' h
  simp only [instListM, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    Except.pure] at hr
  split at hr
  · -- no loose variable: the term is its own instance
    rename_i hnl
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨hs, TabLe.refl _, he, ?_⟩
    have h0 : e.looseBVarRange = 0 := by
      simp only [Bool.not_eq_true', Expr.hasLooseBVars] at hnl
      simpa using hnl
    rw [looseBVarRange_toExpr (FVarTable.trans_fvarsOnly _) (RangeOk_of_OkS he) (TransS_of_ok he)]
      at h0
    exact (ConLeche.Expr.instantiateList_eq_self
      (ConLeche.Expr.looseBVarsBounded_iff.2 (by omega))).symm
  · split at hr
    · -- a hit: the clause at the query key
      rename_i r' hl
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨ck, cvs, cr, h1, h2, h3, h4, -, h6⟩ := hs.instC e vs _ hl
      rw [TransS_of_ok he] at h1; cases h1
      rw [mapM_TransS_of_ok hv] at h2; cases h2
      obtain ⟨hok, htr⟩ := ok_of_TransS h4 h3
      exact ⟨hs, TabLe.refl _, hok, htr.trans h6⟩
    · -- a miss: insert the computed instance
      rename_i hl
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      refine ⟨hs.setInstC ?_, TabLe.refl _, hcomp.1, hcomp.2⟩
      intro k vs' r' hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      split at hl'
      · rename_i hk
        simp only [Option.some.injEq] at hl'; subst hl'
        obtain ⟨hk1, hk2⟩ := instKey_beq_iff.1 hk
        have he' : TransS s₀ k = TransS s₀ e := by
          unfold TransS; rw [← toExpr_eraseK _ k, ← hk1, toExpr_eraseK]
        have hv' : vs'.mapM (TransS s₀) = vs.mapM (TransS s₀) :=
          (mapM_toExpr_of_erase hk2).symm
        refine ⟨TrS s₀ e, TrSL s₀ vs, TrS s₀ (e.instI vs.toArray), he'.trans (TransS_of_ok he),
          hv'.trans (mapM_TransS_of_ok hv), TransS_of_ok hcomp.1, RangeOk_of_OkS hcomp.1, ?_,
          hcomp.2⟩
        simpa [AllClosed] using hcl
      · split at hl'
        · exact hs.instC k vs' r' hl'
        · simp at hl'

end InstMemo

/-! ## The stored-constant caches

InLean reads a stored constant off Lean's entry (`FEnv.find?`,
`defnView?`, `recAt?`); the cached twin off con-leche's environment.  What
relates the two is O4, lane P3's: here it is the named hypothesis
`EnvRelI fe env` (every entry InLean reads translates, as a closed term in
range, to con-leche's entry at the translated name, with the translated level
parameters).  A hit is right by the cache's `CSOKI` clause, a miss reads the
entry through `EnvRelI` and instantiates (`instLevelParamsM_specI`). -/

section Caches

/-- **The environment relation the caches read** (O4, P3's to establish for
the environment `InLean` checks against): every stored type, definition value
and recursor rule InLean reads is a term without free variables, in range,
that translates (`toExprC`) to con-leche's at the translated name, under the
translated level parameters. -/
structure EnvRelI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  ty : ∀ n ci, fe.find? n = some ci → ∃ cci cty, env.find? (toName n) = some cci ∧
    toExprC ci.type = some cty ∧ cci.toConstantVal.type = cty ∧
    cci.toConstantVal.levelParams = ci.levelParams.map toName ∧
    fvarS ci.type = false ∧ Expr.RangeOk ci.type
  val : ∀ n cv v h, fe.defnView? n = some (cv, v, h) → ∃ ccv cvv ch,
    env.find? (toName n) = some (.defnInfo ccv cvv ch) ∧ toExprC v = some cvv ∧
    ccv.levelParams = cv.levelParams.map toName ∧ fvarS v = false ∧ Expr.RangeOk v
  rule : ∀ c rv b j rl, fe.recAt? c = some (rv, b) →
    rv.rules.find? (fun r' => r'.ctor == j) = some rl →
    ∃ ccv mI rP isK crules crl, env.find? (toName c) = some (.recInfo ccv mI rP isK crules) ∧
      crules.find? (fun r' => r'.ctor == toName j) = some crl ∧ toExprC rl.rhs = some crl.rhs ∧
      ccv.levelParams = rv.levelParams.map toName ∧ fvarS rl.rhs = false ∧ Expr.RangeOk rl.rhs

/-- Levels with a reading translate to their total translation. -/
theorem toLevels_of_okLv {us : List Level} (hus : us.all okLv = true) :
    toLevels us = some (us.map trL) :=
  toLevels_of_all (by
    simp only [List.all_eq_true, okLv, Bool.and_eq_true] at hus ⊢; exact fun u hu => (hus u hu).1)

/-- The invariant with the type cache replaced. -/
theorem CSOKI.setConstTy {s : InLean.CState} (hs : CSOKI mode eager env s)
    {mp : Std.HashMap (Name × List Level) Expr}
    (h : ∀ n us i, mp[(n, us)]? = some i → ∃ cus ci ct,
      toLevels us = some cus ∧ env.find? (toName n) = some ci ∧ TransS s i = some ct ∧
      Expr.RangeOk i ∧
      ct = ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams cus) :
    CSOKI mode eager env { s with constTyAt := mp } where
  fv := ⟨hs.fv.cls, hs.fv.distinct, hs.fv.ty, hs.fv.seen, hs.fv.range⟩
  fvClosed := hs.fvClosed
  whnfCoreC := hs.whnfCoreC
  whnfCoreCheapC := hs.whnfCoreCheapC
  whnfC := hs.whnfC
  inferC := hs.inferC
  inferIOC := hs.inferIOC
  defeqC := hs.defeqC
  constTy := h
  constVal := hs.constVal
  ruleRhs := hs.ruleRhs
  lsimp := hs.lsimp
  eqv := hs.eqv
  instC := hs.instC
  eager := ⟨hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC, hs.eager.whnfC, hs.eager.inferC,
    hs.eager.inferIOC, hs.eager.defeqC⟩

/-- The invariant with the value cache replaced. -/
theorem CSOKI.setConstVal {s : InLean.CState} (hs : CSOKI mode eager env s)
    {mp : Std.HashMap (Name × List Level) Expr}
    (h : ∀ n us i, mp[(n, us)]? = some i → ∃ cus cv v h cval,
      toLevels us = some cus ∧ env.find? (toName n) = some (.defnInfo cv v h) ∧
      TransS s i = some cval ∧ Expr.RangeOk i ∧ cval = v.instantiateLevelParams cv.levelParams cus) :
    CSOKI mode eager env { s with constValAt := mp } where
  fv := ⟨hs.fv.cls, hs.fv.distinct, hs.fv.ty, hs.fv.seen, hs.fv.range⟩
  fvClosed := hs.fvClosed
  whnfCoreC := hs.whnfCoreC
  whnfCoreCheapC := hs.whnfCoreCheapC
  whnfC := hs.whnfC
  inferC := hs.inferC
  inferIOC := hs.inferIOC
  defeqC := hs.defeqC
  constTy := hs.constTy
  constVal := h
  ruleRhs := hs.ruleRhs
  lsimp := hs.lsimp
  eqv := hs.eqv
  instC := hs.instC
  eager := ⟨hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC, hs.eager.whnfC, hs.eager.inferC,
    hs.eager.inferIOC, hs.eager.defeqC⟩

/-- The invariant with the rule cache replaced. -/
theorem CSOKI.setRuleRhs {s : InLean.CState} (hs : CSOKI mode eager env s)
    {mp : Std.HashMap (Name × Name × List Level) Expr}
    (h : ∀ c j us i, mp[(c, j, us)]? = some i → ∃ cus cv mI rP isK rules rl cr,
      toLevels us = some cus ∧ env.find? (toName c) = some (.recInfo cv mI rP isK rules) ∧
      rules.find? (fun r' => r'.ctor == toName j) = some rl ∧
      TransS s i = some cr ∧ Expr.RangeOk i ∧ cr = rl.rhs.instantiateLevelParams cv.levelParams cus) :
    CSOKI mode eager env { s with ruleRhsAt := mp } where
  fv := ⟨hs.fv.cls, hs.fv.distinct, hs.fv.ty, hs.fv.seen, hs.fv.range⟩
  fvClosed := hs.fvClosed
  whnfCoreC := hs.whnfCoreC
  whnfCoreCheapC := hs.whnfCoreCheapC
  whnfC := hs.whnfC
  inferC := hs.inferC
  inferIOC := hs.inferIOC
  defeqC := hs.defeqC
  constTy := hs.constTy
  constVal := hs.constVal
  ruleRhs := h
  lsimp := hs.lsimp
  eqv := hs.eqv
  instC := hs.instC
  eager := ⟨hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC, hs.eager.whnfC, hs.eager.inferC,
    hs.eager.inferIOC, hs.eager.defeqC⟩

/-- The level-checked instantiation leaves the state alone. -/
theorem instLevelParamsM_state {ks : List Name} {us : List Level} {e r : Expr}
    {s₀ s₁ : InLean.CState} (h : instLevelParamsM ks us e s₀ = .ok (r, s₁)) : s₁ = s₀ := by
  cases hc : EO.instLevelParamsChecked? e ks us with
  | none =>
    simp [instLevelParamsM, hc, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map,
      Except.map] at h
  | some r' =>
    simp only [instLevelParamsM, hc, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    exact h.2.symm

variable {fe : InLean.FEnv} {s₀ : InLean.CState}

/-- **A constant's type at levels `us`** (`constTyAtM_spec`'s twin): its
translation is con-leche's stored type at the translated name and levels. -/
theorem constTyAtM_specI (hfe : EnvRelI fe env) (hs : CSOKI mode eager env s₀) (n : Name)
    {us : List Level} (hus : us.all okLv = true) :
    ⦃fun s => s = s₀⦄ constTyAtM fe n us
    ⦃fun t s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' t = true ∧
      TrS s' t = ConLeche.Cached.constTyOf env (toName n) (us.map trL); ⊤⦄ := by
  refine tripleI_iff_run.2 fun t s' hr => ?_
  have hl := toLevels_of_okLv hus
  cases hlook : s₀.constTyAt[(n, us)]? with
  | some i =>
    simp only [constTyAtM, hlook, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨cus, ci, ct, h1, h2, h3, h4, h5⟩ := hs.constTy n us i hlook
    rw [hl] at h1; cases h1
    obtain ⟨hok, htr⟩ := ok_of_TransS h4 h3
    refine ⟨hs, TabLe.refl _, hok, ?_⟩
    rw [htr, h5]; simp [ConLeche.Cached.constTyOf, h2]
  | none =>
    cases hf : fe.find? n with
    | none =>
      simp [constTyAtM, hlook, hf, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.pure, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hr
    | some ci =>
      cases hi : instLevelParamsM ci.levelParams us ci.type s₀ with
      | error x =>
        simp [constTyAtM, hlook, hf, hi, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, Except.pure, Except.bind] at hr
      | ok p =>
        obtain ⟨i, s₁⟩ := p
        rw [instLevelParamsM_state hi] at hi
        simp [constTyAtM, hlook, hf, hi, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, modify] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨cci, cty, he, hct, hty, hlp, hfv, hrg⟩ := hfe.ty n ci hf
        obtain ⟨hokT, htrT⟩ := okS_of_toExprC (s := s₀) hfv hrg hct
        obtain ⟨-, -, hok, htr⟩ :=
          tripleI_iff_run.1 (instLevelParamsM_specI (ks := ci.levelParams) hs hokT hfv hus) i s₀ hi
        have hval : TrS s₀ i = ConLeche.Cached.constTyOf env (toName n) (us.map trL) := by
          rw [htr, htrT]; simp [ConLeche.Cached.constTyOf, he, hty, hlp]
        refine ⟨hs.setConstTy ?_, TabLe.refl _, hok, hval⟩
        intro n' us' i' hl'
        rw [Std.HashMap.getElem?_insert] at hl'
        split at hl'
        · rename_i hk
          simp only [Option.some.injEq] at hl'; subst hl'
          have hk' := eq_of_beq hk
          simp only [Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          exact ⟨us.map trL, cci, TrS s₀ i, hl, he, TransS_of_ok hok, RangeOk_of_OkS hok,
            by rw [hval]; simp [ConLeche.Cached.constTyOf, he]⟩
        · exact hs.constTy n' us' i' hl'

/-- **A definition's value at levels `us`** (`constValAtM_spec`'s twin): a run
succeeds at a stored definition, and the value's translation is con-leche's. -/
theorem constValAtM_specI (hfe : EnvRelI fe env) (hs : CSOKI mode eager env s₀) (n : Name)
    {us : List Level} (hus : us.all okLv = true) :
    ⦃fun s => s = s₀⦄ constValAtM fe n us
    ⦃fun t s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' t = true ∧
      ConLeche.Cached.constValAt? env (toName n) (us.map trL) = some (TrS s' t); ⊤⦄ := by
  refine tripleI_iff_run.2 fun t s' hr => ?_
  have hl := toLevels_of_okLv hus
  cases hlook : s₀.constValAt[(n, us)]? with
  | some i =>
    simp only [constValAtM, hlook, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨cus, cv, v, hh, cval, h1, h2, h3, h4, h5⟩ := hs.constVal n us i hlook
    rw [hl] at h1; cases h1
    obtain ⟨hok, htr⟩ := ok_of_TransS h4 h3
    refine ⟨hs, TabLe.refl _, hok, ?_⟩
    rw [htr, h5]; simp [ConLeche.Cached.constValAt?, h2]
  | none =>
    cases hf : fe.defnView? n with
    | none =>
      simp [constValAtM, hlook, hf, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.pure, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hr
    | some p =>
      obtain ⟨cv, v, hint⟩ := p
      cases hi : instLevelParamsM cv.levelParams us v s₀ with
      | error x =>
        simp [constValAtM, hlook, hf, hi, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, Except.pure, Except.bind] at hr
      | ok p =>
        obtain ⟨i, s₁⟩ := p
        rw [instLevelParamsM_state hi] at hi
        simp [constValAtM, hlook, hf, hi, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, modify] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨ccv, cvv, ch, he, hcv, hlp, hfv, hrg⟩ := hfe.val n cv v hint hf
        obtain ⟨hokV, htrV⟩ := okS_of_toExprC (s := s₀) hfv hrg hcv
        obtain ⟨-, -, hok, htr⟩ :=
          tripleI_iff_run.1 (instLevelParamsM_specI (ks := cv.levelParams) hs hokV hfv hus) i s₀ hi
        have hval : TrS s₀ i = cvv.instantiateLevelParams ccv.levelParams (us.map trL) := by
          rw [htr, htrV, hlp]
        refine ⟨hs.setConstVal ?_, TabLe.refl _, hok, by
          show _ = some (TrS s₀ i); rw [hval]; simp [ConLeche.Cached.constValAt?, he]⟩
        intro n' us' i' hl'
        rw [Std.HashMap.getElem?_insert] at hl'
        split at hl'
        · rename_i hk
          simp only [Option.some.injEq] at hl'; subst hl'
          have hk' := eq_of_beq hk
          simp only [Prod.mk.injEq] at hk'
          obtain ⟨rfl, rfl⟩ := hk'
          exact ⟨us.map trL, ccv, cvv, ch, TrS s₀ i, hl, he, TransS_of_ok hok,
            RangeOk_of_OkS hok, hval⟩
        · exact hs.constVal n' us' i' hl'

/-- **A recursor's rule right-hand side for a constructor at levels `us`**
(`ruleRhsAtM_spec`'s twin): its translation is con-leche's stored rule. -/
theorem ruleRhsAtM_specI (hfe : EnvRelI fe env) (hs : CSOKI mode eager env s₀) (c j : Name)
    {us : List Level} (hus : us.all okLv = true) :
    ⦃fun s => s = s₀⦄ ruleRhsAtM fe c j us
    ⦃fun t s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' t = true ∧
      ConLeche.Cached.ruleRhsOf env (toName c) (toName j) (us.map trL) = some (TrS s' t); ⊤⦄ := by
  refine tripleI_iff_run.2 fun t s' hr => ?_
  have hl := toLevels_of_okLv hus
  cases hlook : s₀.ruleRhsAt[(c, j, us)]? with
  | some i =>
    simp only [ruleRhsAtM, hlook, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨cus, cv, mI, rP, isK, rules, rl, cr, h1, h2, h3, h4, h5, h6⟩ :=
      hs.ruleRhs c j us i hlook
    rw [hl] at h1; cases h1
    obtain ⟨hok, htr⟩ := ok_of_TransS h5 h4
    refine ⟨hs, TabLe.refl _, hok, ?_⟩
    rw [htr, h6]
    simp [ConLeche.Cached.ruleRhsOf, ConLeche.Cached.findRule, h2, h3]
  | none =>
    cases hf : fe.recAt? c with
    | none =>
      simp [ruleRhsAtM, hlook, hf, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Except.pure, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift] at hr
    | some p =>
      obtain ⟨rv, b⟩ := p
      cases hrl : rv.rules.find? (fun r' => r'.ctor == j) with
      | none =>
        simp [ruleRhsAtM, hlook, hf, hrl, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, Except.pure, Except.bind, throw, throwThe,
          MonadExceptOf.throw, StateT.lift] at hr
      | some rl =>
        cases hi : instLevelParamsM rv.levelParams us rl.rhs s₀ with
        | error x =>
          simp [ruleRhsAtM, hlook, hf, hrl, hi, bind, StateT.bind, modifyGet,
            MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
            Except.bind] at hr
        | ok p =>
          obtain ⟨i, s₁⟩ := p
          rw [instLevelParamsM_state hi] at hi
          simp [ruleRhsAtM, hlook, hf, hrl, hi, bind, StateT.bind, modifyGet,
            MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, Except.bind,
            modify] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨ccv, mI, rP, isK, crules, crl, he, hcrl, hcr, hlp, hfv, hrg⟩ :=
            hfe.rule c rv b j rl hf hrl
          obtain ⟨hokR, htrR⟩ := okS_of_toExprC (s := s₀) hfv hrg hcr
          obtain ⟨-, -, hok, htr⟩ := tripleI_iff_run.1
            (instLevelParamsM_specI (ks := rv.levelParams) hs hokR hfv hus) i s₀ hi
          have hval : TrS s₀ i = crl.rhs.instantiateLevelParams ccv.levelParams (us.map trL) := by
            rw [htr, htrR, hlp]
          refine ⟨hs.setRuleRhs ?_, TabLe.refl _, hok, by
            show _ = some (TrS s₀ i); rw [hval]
            simp [ConLeche.Cached.ruleRhsOf, ConLeche.Cached.findRule, he, hcrl]⟩
          intro c' j' us' i' hl'
          rw [Std.HashMap.getElem?_insert] at hl'
          split at hl'
          · rename_i hk
            simp only [Option.some.injEq] at hl'; subst hl'
            have hk' := eq_of_beq hk
            simp only [Prod.mk.injEq] at hk'
            obtain ⟨rfl, rfl, rfl⟩ := hk'
            exact ⟨us.map trL, ccv, mI, rP, isK, crules, crl, TrS s₀ i, hl, he, hcrl,
              TransS_of_ok hok, RangeOk_of_OkS hok, hval⟩
          · exact hs.ruleRhs c' j' us' i' hl'

end Caches

/-! ## The level operations commute with the translation

InLean's level operations (`InLean/Basic.lean`, `Lvl.*`) are line-by-line
twins of con-leche's (`ConLeche/Kernel/Level.lean`); on levels without
metavariables (`okL`), `trL` is injective and carries each to its twin. -/

section LevelOps

theorem trL_inj : ∀ {a b : Level}, okL a = true → okL b = true → trL a = trL b → a = b
  | .zero, .zero, _, _, _ => rfl
  | .succ a, .succ b, ha, hb, h => by
    simp only [okL] at ha hb; simp only [trL, ConLeche.Level.succ.injEq] at h
    rw [trL_inj ha hb h]
  | .max a a', .max b b', ha, hb, h => by
    simp only [okL, Bool.and_eq_true] at ha hb
    simp only [trL, ConLeche.Level.max.injEq] at h
    rw [trL_inj ha.1 hb.1 h.1, trL_inj ha.2 hb.2 h.2]
  | .imax a a', .imax b b', ha, hb, h => by
    simp only [okL, Bool.and_eq_true] at ha hb
    simp only [trL, ConLeche.Level.imax.injEq] at h
    rw [trL_inj ha.1 hb.1 h.1, trL_inj ha.2 hb.2 h.2]
  | .param n, .param m, _, _, h => by
    simp only [trL, ConLeche.Level.param.injEq] at h; rw [toName_inj h]
  | .mvar _, _, ha, _, _ => by simp [okL] at ha
  | _, .mvar _, _, hb, _ => by simp [okL] at hb
  | .zero, .succ _, _, _, h | .zero, .max .., _, _, h | .zero, .imax .., _, _, h
  | .zero, .param _, _, _, h | .succ _, .zero, _, _, h | .succ _, .max .., _, _, h
  | .succ _, .imax .., _, _, h | .succ _, .param _, _, _, h | .max .., .zero, _, _, h
  | .max .., .succ _, _, _, h | .max .., .imax .., _, _, h | .max .., .param _, _, _, h
  | .imax .., .zero, _, _, h | .imax .., .succ _, _, _, h | .imax .., .max .., _, _, h
  | .imax .., .param _, _, _, h | .param _, .zero, _, _, h | .param _, .succ _, _, _, h
  | .param _, .max .., _, _, h | .param _, .imax .., _, _, h => by simp [trL] at h

/-- On levels without metavariables, InLean's equality is that of the
translations. -/
theorem beq_iff_trL {a b : Level} (ha : okL a = true) (hb : okL b = true) :
    (a == b) = true ↔ trL a = trL b := by
  constructor
  · intro h; rw [eq_of_beq h]
  · intro h; rw [trL_inj ha hb h]; exact beq_self_eq_true _

theorem okL_combining : ∀ {l r : Level}, okL l = true → okL r = true →
    okL (Lvl.combining l r) = true
  | .zero, r, _, hr => by simpa [Lvl.combining] using hr
  | .succ l, .zero, hl, _ => by simpa [Lvl.combining] using hl
  | .succ l, .succ r, hl, hr => by
    simp only [okL] at hl hr; simp only [Lvl.combining, okL]; exact okL_combining hl hr
  | .succ l, .max .., hl, hr | .succ l, .imax .., hl, hr | .succ l, .param _, hl, hr
  | .succ l, .mvar _, hl, hr | .max .., .zero, hl, hr | .max .., .succ _, hl, hr
  | .max .., .max .., hl, hr | .max .., .imax .., hl, hr | .max .., .param _, hl, hr
  | .max .., .mvar _, hl, hr | .imax .., .zero, hl, hr | .imax .., .succ _, hl, hr
  | .imax .., .max .., hl, hr | .imax .., .imax .., hl, hr | .imax .., .param _, hl, hr
  | .imax .., .mvar _, hl, hr | .param _, .zero, hl, hr | .param _, .succ _, hl, hr
  | .param _, .max .., hl, hr | .param _, .imax .., hl, hr | .param _, .param _, hl, hr
  | .param _, .mvar _, hl, hr | .mvar _, _, hl, hr => by
    simp_all [Lvl.combining, okL]

theorem trL_combining : ∀ {l r : Level}, okL l = true → okL r = true →
    trL (Lvl.combining l r) = ConLeche.Level.combining (trL l) (trL r)
  | .zero, r, _, _ => by simp [Lvl.combining, trL, ConLeche.Level.combining]
  | .succ l, .zero, _, _ => by simp [Lvl.combining, trL, ConLeche.Level.combining]
  | .succ l, .succ r, hl, hr => by
    simp only [okL] at hl hr
    simp only [Lvl.combining, trL, ConLeche.Level.combining, trL_combining hl hr]
  | .mvar _, _, hl, _ => by simp [okL] at hl
  | _, .mvar _, _, hr => by simp [okL] at hr
  | .succ _, .max .., _, _ | .succ _, .imax .., _, _ | .succ _, .param _, _, _
  | .max .., .zero, _, _ | .max .., .succ _, _, _ | .max .., .max .., _, _
  | .max .., .imax .., _, _ | .max .., .param _, _, _ | .imax .., .zero, _, _
  | .imax .., .succ _, _, _ | .imax .., .max .., _, _ | .imax .., .imax .., _, _
  | .imax .., .param _, _, _ | .param _, .zero, _, _ | .param _, .succ _, _, _
  | .param _, .max .., _, _ | .param _, .imax .., _, _ | .param _, .param _, _, _ => by
    simp [Lvl.combining, trL, ConLeche.Level.combining]

theorem okL_simplify : ∀ {u : Level}, okL u = true → okL (Lvl.simplify u) = true
  | .zero, _ => rfl
  | .param _, _ => rfl
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by simp only [okL] at h; simp only [Lvl.simplify, okL]; exact okL_simplify h
  | .max u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    exact okL_combining (okL_simplify h.1) (okL_simplify h.2)
  | .imax u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    have hu := okL_simplify h.1; have hv := okL_simplify h.2
    simp only [Lvl.simplify]
    split
    · exact hv
    · split
      · rfl
      · exact okL_combining hu hv
      · simp [okL, hu, hv]

theorem trL_simplify : ∀ {u : Level}, okL u = true →
    trL (Lvl.simplify u) = ConLeche.Level.simplify (trL u)
  | .zero, _ => rfl
  | .param _, _ => rfl
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by
    simp only [okL] at h; simp only [Lvl.simplify, trL, ConLeche.Level.simplify, trL_simplify h]
  | .max u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.simplify, trL, ConLeche.Level.simplify,
      trL_combining (okL_simplify h.1) (okL_simplify h.2), trL_simplify h.1, trL_simplify h.2]
  | .imax u v, h => by
    simp only [okL, Bool.and_eq_true] at h
    have hu := okL_simplify h.1; have hv := okL_simplify h.2
    have e1 : (Lvl.simplify u == .zero) = true ↔ ConLeche.Level.simplify (trL u) = .zero := by
      rw [beq_iff_trL hu rfl, trL_simplify h.1]; rfl
    have e2 : (Lvl.simplify u == .succ .zero) = true ↔
        ConLeche.Level.simplify (trL u) = .succ .zero := by
      rw [beq_iff_trL hu rfl, trL_simplify h.1]; rfl
    simp only [Lvl.simplify, trL, ConLeche.Level.simplify, ← trL_simplify h.1,
      ← trL_simplify h.2]
    by_cases c : ((Lvl.simplify u == .zero) || (Lvl.simplify u == .succ .zero)) = true
    · have c' : (decide (trL (Lvl.simplify u) = .zero) || decide (trL (Lvl.simplify u) = .succ .zero))
          = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at c ⊢
        rw [trL_simplify h.1]
        rcases c with c | c
        · exact Or.inl (e1.1 c)
        · exact Or.inr (e2.1 c)
      simp only [c, c', ↓reduceIte]
    · have c' : (decide (trL (Lvl.simplify u) = .zero) || decide (trL (Lvl.simplify u) = .succ .zero))
          = false := by
        simp only [Bool.or_eq_true, not_or] at c
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
        rw [trL_simplify h.1]
        exact ⟨fun h' => c.1 (e1.2 h'), fun h' => c.2 (e2.2 h')⟩
      simp only [Bool.not_eq_true] at c
      simp only [c, c', Bool.false_eq_true, ↓reduceIte]
      cases hs : Lvl.simplify v with
      | zero => simp [trL]
      | succ w => rw [hs] at hv; rw [trL_combining hu hv]; rfl
      | max a b => simp [trL]
      | imax a b => simp [trL]
      | param n => simp [trL]
      | mvar m => rw [hs] at hv; simp [okL] at hv

theorem trL_substGo {v : Level} {p : Name} :
    ∀ n : Name, trL (Lvl.substGo [p] [v] n) = ConLeche.Level.subst.go [toName p] [trL v] (toName n) := by
  intro n
  simp only [Lvl.substGo, ConLeche.Level.subst.go]
  by_cases h : p = n
  · subst h; simp
  · have h' : ¬ toName p = toName n := fun h'' => h (toName_inj h'')
    simp [h, h', trL]

theorem okL_substGo {v : Level} {p : Name} (hv : okL v = true) :
    ∀ n : Name, okL (Lvl.substGo [p] [v] n) = true := by
  intro n
  simp only [Lvl.substGo]
  split
  · exact hv
  · rfl

theorem okL_subst1 {v : Level} {p : Name} (hv : okL v = true) :
    ∀ {u : Level}, okL u = true → okL (Lvl.subst [p] [v] u) = true
  | .zero, _ => rfl
  | .param n, _ => okL_substGo hv n
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by simp only [okL] at h; simp only [Lvl.subst, okL]; exact okL_subst1 hv h
  | .max u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, okL, okL_subst1 hv h.1, okL_subst1 hv h.2, Bool.and_self]
  | .imax u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, okL, okL_subst1 hv h.1, okL_subst1 hv h.2, Bool.and_self]

theorem trL_subst1 {v : Level} {p : Name} :
    ∀ {u : Level}, okL u = true →
      trL (Lvl.subst [p] [v] u) = ConLeche.Level.subst [toName p] [trL v] (trL u)
  | .zero, _ => rfl
  | .param n, _ => trL_substGo n
  | .mvar _, h => by simp [okL] at h
  | .succ u, h => by
    simp only [okL] at h; simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst1 h]
  | .max u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst1 h.1, trL_subst1 h.2]
  | .imax u w, h => by
    simp only [okL, Bool.and_eq_true] at h
    simp only [Lvl.subst, trL, ConLeche.Level.subst, trL_subst1 h.1, trL_subst1 h.2]

/-- The comparison at a fuel, translated. -/
@[expose] def LeqAt (f : Nat) : Prop :=
  ∀ l r diff, okL l = true → okL r = true →
    Lvl.leqCore f l r diff = ConLeche.Level.leqCore f (trL l) (trL r) diff

theorem byCases_trL {f : Nat} (ih : LeqAt f) {p : Name} {l r : Level} {diff : Int}
    (hl : okL l = true) (hr : okL r = true) :
    Lvl.byCases f p l r diff = ConLeche.Level.byCases f (toName p) (trL l) (trL r) diff := by
  have z : okL (Level.zero) = true := rfl
  have sp : okL (Level.succ (.param p)) = true := rfl
  simp only [Lvl.byCases, ConLeche.Level.byCases]
  rw [ih _ _ _ (okL_simplify (okL_subst1 z hl)) (okL_simplify (okL_subst1 z hr)),
    ih _ _ _ (okL_simplify (okL_subst1 sp hl)) (okL_simplify (okL_subst1 sp hr)),
    trL_simplify (okL_subst1 z hl), trL_simplify (okL_subst1 z hr),
    trL_simplify (okL_subst1 sp hl), trL_simplify (okL_subst1 sp hr),
    trL_subst1 hl, trL_subst1 hr, trL_subst1 hl, trL_subst1 hr]
  rfl

theorem beq_eq_decide_trL {a b : Level} (ha : okL a = true) (hb : okL b = true) :
    (a == b) = decide (trL a = trL b) := by
  rw [Bool.eq_iff_iff, beq_iff_trL ha hb, decide_eq_true_eq]

theorem name_beq_eq_decide (a b : Name) : (a == b) = decide (toName a = toName b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro h; rw [eq_of_beq h]
  · intro h; rw [toName_inj h]; exact beq_self_eq_true _

theorem imaxRules_trL {f : Nat} (ih : LeqAt f) {l r : Level} {diff : Int}
    (hl : okL l = true) (hr : okL r = true) :
    Lvl.imaxRules f l r diff = ConLeche.Level.imaxRules f (trL l) (trL r) diff := by
  unfold LeqAt at ih
  rcases l with _ | a | ⟨a, b⟩ | ⟨a, _ | b | ⟨b, c⟩ | ⟨b, c⟩ | p | m⟩ | p | m <;>
  rcases r with _ | x | ⟨x, y⟩ | ⟨x, _ | y | ⟨y, z⟩ | ⟨y, z⟩ | q | n⟩ | q | n <;>
  simp only [okL, Bool.and_eq_true, Bool.false_eq_true, and_false] at hl hr <;>
  simp only [Lvl.imaxRules, ConLeche.Level.imaxRules, trL] <;>
  (try rw [byCases_trL ih]) <;> (try rw [ih]) <;> (try rw [trL_simplify]) <;>
  first
  | rfl
  | simp [okL, hl, hr]
  | (apply okL_simplify; simp [okL, hl, hr])

theorem rest_trL {f : Nat} (ih : LeqAt f) {l r : Level} {diff : Int}
    (hl : okL l = true) (hr : okL r = true) :
    Lvl.rest f l r diff = ConLeche.Level.rest f (trL l) (trL r) diff := by
  have hi : ∀ {l r : Level}, okL l = true → okL r = true →
      Lvl.imaxRules f l r diff = ConLeche.Level.imaxRules f (trL l) (trL r) diff :=
    fun hl hr => imaxRules_trL ih hl hr
  unfold LeqAt at ih
  rcases l with _ | a | ⟨a, b⟩ | ⟨a, b⟩ | p | m <;>
  rcases r with _ | x | ⟨x, y⟩ | ⟨x, y⟩ | q | n <;>
  simp only [okL, Bool.and_eq_true, Bool.false_eq_true] at hl hr <;>
  simp only [Lvl.rest, ConLeche.Level.rest, trL, name_beq_eq_decide] <;>
  (repeat (rw [ih])) <;> (repeat (rw [beq_eq_decide_trL])) <;> (try rw [hi]) <;>
  first
  | rfl
  | simp [okL, hl, hr]

theorem zero_beq_iff {l : Level} (hl : okL l = true) :
    (l == .zero) = true ↔ trL l = .zero := beq_iff_trL hl rfl

/-- **The level comparison commutes with the translation**, at every fuel. -/
theorem leqCore_trL : ∀ f, LeqAt f
  | 0 => fun l r diff _ _ => by simp [Lvl.leqCore, ConLeche.Level.leqCore]
  | f + 1 => fun l r diff hl hr => by
    have ih := leqCore_trL f
    simp only [Lvl.leqCore, ConLeche.Level.leqCore, zero_beq_iff hl, zero_beq_iff hr,
      rest_trL ih hl hr]

end LevelOps

/-! ## The level memos

`isEquivLM` restated through a named `simplify`-with-memo step
(`isEquivLM_eqI`, by `rfl`), as master's `isEquivLM_eq` does; the memo's
entries are the translated `simplify`, and the comparison is con-leche's
cascade (`isEquiv_cascade_eq`) at the translation. -/

section LevelMemos

/-- The inlined `simplify`-with-memo step of `isEquivLM`. -/
@[expose] def simpMemoI (mp : Std.HashMap Level Level) (u : Level) : Level × Std.HashMap Level Level :=
  match mp[u]? with
  | some x => (x, mp)
  | none => let x := Lvl.simplify u; (x, mp.insert u x)

/-- The body of `isEquivLM` past the syntactic shortcut. -/
@[expose] def isEquivStepI (l r : Level) (s : InLean.CState) : Option Bool × InLean.CState :=
  match s.eqvC[(l, r)]? with
  | some b => (some b, s)
  | none =>
    let mp := s.lsimpC
    let ec := s.eqvC
    let s := { s with lsimpC := {}, eqvC := {} }
    let (ls, mp) := simpMemoI mp l
    let (rs, mp) := simpMemoI mp r
    if ls == rs then
      (some true, { s with lsimpC := mp, eqvC := ec.insert (l, r) true })
    else
      match Lvl.leqCore Lvl.defaultFuel ls rs 0 with
      | some false =>
        (some false, { s with lsimpC := mp, eqvC := ec.insert (l, r) false })
      | some true =>
        match Lvl.leqCore Lvl.defaultFuel rs ls 0 with
        | some b => (some b, { s with lsimpC := mp, eqvC := ec.insert (l, r) b })
        | none => (none, { s with lsimpC := mp, eqvC := ec })
      | none => (none, { s with lsimpC := mp, eqvC := ec })

theorem isEquivLM_eqI (l r : Level) :
    isEquivLM l r = (if l == r then pure (some true) else modifyGet (isEquivStepI l r)) := rfl

/-- Every entry of a `simplify` memo is the translated `simplify`. -/
@[expose] def LsimpI (mp : Std.HashMap Level Level) : Prop :=
  ∀ u v, mp[u]? = some v → ∀ cu, toLevel u = some cu → toLevel v = some (ConLeche.Level.simplify cu)

theorem simpMemoI_ok {mp : Std.HashMap Level Level} (h : LsimpI mp) {u : Level} (hu : okL u = true) :
    okL (simpMemoI mp u).1 = true ∧
      trL (simpMemoI mp u).1 = ConLeche.Level.simplify (trL u) ∧ LsimpI (simpMemoI mp u).2 := by
  unfold simpMemoI
  split
  · rename_i x hx
    obtain ⟨h1, h2⟩ := okL_of_toLevel (h u x hx (trL u) (toLevel_of_okL hu))
    exact ⟨h1, h2, h⟩
  · refine ⟨okL_simplify hu, trL_simplify hu, ?_⟩
    intro u' v hl cu hcu
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i he
      obtain rfl := eq_of_beq he
      simp only [Option.some.injEq] at hl; subst hl
      obtain ⟨-, rfl⟩ := okL_of_toLevel hcu
      rw [toLevel_of_okL (okL_simplify hu), trL_simplify hu]
    · exact h u' v hl cu hcu

/-- The invariant with the level memos replaced. -/
theorem CSOKI.setLevel {s : InLean.CState} (hs : CSOKI mode eager env s)
    {ls : Std.HashMap Level Level} {ec : Std.HashMap (Level × Level) Bool} (hl : LsimpI ls)
    (he : ∀ l r b, ec[(l, r)]? = some b → ∀ cl cr, toLevel l = some cl → toLevel r = some cr →
      ConLeche.Level.isEquiv cl cr = some b) :
    CSOKI mode eager env { s with lsimpC := ls, eqvC := ec } where
  fv := ⟨hs.fv.cls, hs.fv.distinct, hs.fv.ty, hs.fv.seen, hs.fv.range⟩
  fvClosed := hs.fvClosed
  whnfCoreC := hs.whnfCoreC
  whnfCoreCheapC := hs.whnfCoreCheapC
  whnfC := hs.whnfC
  inferC := hs.inferC
  inferIOC := hs.inferIOC
  defeqC := hs.defeqC
  constTy := hs.constTy
  constVal := hs.constVal
  ruleRhs := hs.ruleRhs
  lsimp := hl
  eqv := he
  instC := hs.instC
  eager := ⟨hs.eager.whnfCoreC, hs.eager.whnfCoreCheapC, hs.eager.whnfC, hs.eager.inferC,
    hs.eager.inferIOC, hs.eager.defeqC⟩

/-- Inserting a certified verdict keeps the `isEquiv` clause. -/
theorem eqv_insert {ec : Std.HashMap (Level × Level) Bool}
    (he : ∀ l r b, ec[(l, r)]? = some b → ∀ cl cr, toLevel l = some cl → toLevel r = some cr →
      ConLeche.Level.isEquiv cl cr = some b)
    {l r : Level} {b : Bool} (hl : okL l = true) (hr : okL r = true)
    (hb : ConLeche.Level.isEquiv (trL l) (trL r) = some b) :
    ∀ l' r' b', (ec.insert (l, r) b)[(l', r')]? = some b' → ∀ cl cr, toLevel l' = some cl →
      toLevel r' = some cr → ConLeche.Level.isEquiv cl cr = some b' := by
  intro l' r' b' hlk cl cr hcl hcr
  rw [Std.HashMap.getElem?_insert] at hlk
  split at hlk
  · rename_i hk
    have hk' := eq_of_beq hk
    simp only [Prod.mk.injEq] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    simp only [Option.some.injEq] at hlk; subst hlk
    rw [toLevel_of_okL hl] at hcl; rw [toLevel_of_okL hr] at hcr
    cases hcl; cases hcr; exact hb
  · exact he l' r' b' hlk cl cr hcl hcr

theorem defaultFuel_eq : Lvl.defaultFuel = ConLeche.Level.defaultFuel := rfl

/-- **The level-equivalence memo** (`isEquivLM_spec`'s twin): the verdict is
con-leche's `isEquiv` at the translation. -/
theorem isEquivLM_specI {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) {l r : Level}
    (hl : okL l = true) (hr : okL r = true) :
    ⦃fun s => s = s₀⦄ isEquivLM l r
    ⦃fun ob s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      ob = ConLeche.Level.isEquiv (trL l) (trL r); ⊤⦄ := by
  refine tripleI_iff_run.2 fun ob s' hrun => ?_
  rw [isEquivLM_eqI] at hrun
  by_cases hlr : (l == r) = true
  · simp only [hlr, ↓reduceIte, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    refine ⟨hs, TabLe.refl _, ?_⟩
    rw [eq_of_beq hlr]
    exact (ConLeche.Level.isEquiv_of_beq (beq_self_eq_true _)).symm
  · simp only [hlr, Bool.false_eq_true, ↓reduceIte, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, Except.pure, Except.ok.injEq] at hrun
    rw [ConLeche.Cached.isEquiv_cascade_eq]
    unfold isEquivStepI at hrun
    cases hlook : s₀.eqvC[(l, r)]? with
    | some b =>
      simp only [hlook, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨hs, TabLe.refl _, ?_⟩
      rw [← ConLeche.Cached.isEquiv_cascade_eq]
      exact (hs.eqv l r b hlook _ _ (toLevel_of_okL hl) (toLevel_of_okL hr)).symm
    | none =>
      simp only [hlook] at hrun
      have hL : LsimpI s₀.lsimpC := hs.lsimp
      obtain ⟨hl1, hl2, hL1⟩ := simpMemoI_ok hL hl
      generalize simpMemoI s₀.lsimpC l = p1 at hrun hl1 hl2 hL1
      obtain ⟨ls, mp1⟩ := p1
      obtain ⟨hr1, hr2, hL2⟩ := simpMemoI_ok hL1 hr
      generalize simpMemoI mp1 r = p2 at hrun hr1 hr2 hL2
      obtain ⟨rs, mp2⟩ := p2
      simp only at hrun hl1 hl2 hL1 hr1 hr2 hL2
      have hcl := ConLeche.Cached.isEquiv_cascade_eq (trL l) (trL r)
      rw [← hl2, ← hr2]
      by_cases hsr : (ls == rs) = true
      · simp only [hsr, ↓reduceIte, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have hsr' : trL ls = trL rs := (beq_iff_trL hl1 hr1).1 hsr
        simp only [hsr', ↓reduceIte]
        refine ⟨hs.setLevel hL2 (eqv_insert hs.eqv hl hr ?_), TabLe.refl _, trivial⟩
        rw [hcl, ← hl2, ← hr2, hsr']; simp
      · have hsr' : ¬ trL ls = trL rs := fun h => hsr ((beq_iff_trL hl1 hr1).2 h)
        simp only [hsr, Bool.false_eq_true, ↓reduceIte] at hrun
        simp only [hsr', ↓reduceIte]
        rw [leqCore_trL _ _ _ _ hl1 hr1, leqCore_trL _ _ _ _ hr1 hl1] at hrun
        try rw [defaultFuel_eq] at hrun
        have hcas : ConLeche.Level.isEquiv (trL l) (trL r) =
            match ConLeche.Level.leqCore ConLeche.Level.defaultFuel (trL ls) (trL rs) 0 with
            | none => none
            | some false => some false
            | some true => ConLeche.Level.leqCore ConLeche.Level.defaultFuel (trL rs) (trL ls) 0 := by
          rw [hcl, ← hl2, ← hr2]; simp only [hsr', ↓reduceIte]; rfl
        split at hrun
        · rename_i h1
          simp only [Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          have hv : ConLeche.Level.isEquiv (trL l) (trL r) = some false := by simp only [hcas, h1]
          exact ⟨hs.setLevel hL2 (eqv_insert hs.eqv hl hr hv), TabLe.refl _, by simp only [h1]⟩
        · rename_i h1
          split at hrun
          · rename_i b h2
            simp only [Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hv : ConLeche.Level.isEquiv (trL l) (trL r) = some b := by simp only [hcas, h1, h2]
            exact ⟨hs.setLevel hL2 (eqv_insert hs.eqv hl hr hv), TabLe.refl _, by simp only [h1, h2]⟩
          · rename_i h2
            simp only [Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            exact ⟨hs.setLevel hL2 hs.eqv, TabLe.refl _, by simp only [h1, h2]⟩
        · rename_i h1
          simp only [Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          exact ⟨hs.setLevel hL2 hs.eqv, TabLe.refl _, by simp only [h1]⟩

/-- **Pointwise level equivalence** (`isEquivListLM_spec`'s twin). -/
theorem isEquivListLM_specI :
    ∀ {ls rs : List Level} {s₀ : InLean.CState}, CSOKI mode eager env s₀ →
      ls.all okL = true → rs.all okL = true →
      ⦃fun s => s = s₀⦄ isEquivListLM ls rs
      ⦃fun ob s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        ob = ConLeche.Level.isEquivList (ls.map trL) (rs.map trL); ⊤⦄
  | [], [], s₀, hs, _, _ => by
    refine tripleI_iff_run.2 fun ob s' hr => ?_
    simp only [isEquivListLM, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, by simp [ConLeche.Level.isEquivList]⟩
  | [], _ :: _, s₀, hs, _, _ | _ :: _, [], s₀, hs, _, _ => by
    refine tripleI_iff_run.2 fun ob s' hr => ?_
    simp only [isEquivListLM, pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hs, TabLe.refl _, by simp [ConLeche.Level.isEquivList]⟩
  | l :: ls, r :: rs, s₀, hs, hls, hrs => by
    simp only [List.all_cons, Bool.and_eq_true] at hls hrs
    refine tripleI_iff_run.2 fun ob s' hrun => ?_
    cases hq : isEquivLM l r s₀ with
    | error x => simp [isEquivListLM, hq, bind, StateT.bind, Except.bind] at hrun
    | ok p =>
      obtain ⟨b, s₁⟩ := p
      obtain ⟨hs₁, ht₁, hb⟩ := tripleI_iff_run.1 (isEquivLM_specI hs hls.1 hrs.1) b s₁ hq
      have hcons : ConLeche.Level.isEquivList (trL l :: ls.map trL) (trL r :: rs.map trL) =
          match ConLeche.Level.isEquiv (trL l) (trL r) with
          | none => none
          | some false => some false
          | some true => ConLeche.Level.isEquivList (ls.map trL) (rs.map trL) :=
        ConLeche.Cached.isEquivList_cons _ _ _ _
      simp only [List.map_cons, hcons, ← hb]
      cases b with
      | none =>
        simp [isEquivListLM, hq, bind, StateT.bind, Except.bind, pure, StateT.pure,
          Except.pure] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨hs₁, ht₁, rfl⟩
      | some c =>
        cases c with
        | false =>
          simp [isEquivListLM, hq, bind, StateT.bind, Except.bind, pure, StateT.pure,
            Except.pure] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          exact ⟨hs₁, ht₁, rfl⟩
        | true =>
          simp only [isEquivListLM, hq, bind, StateT.bind, Except.bind] at hrun
          obtain ⟨hs₂, ht₂, hb₂⟩ :=
            tripleI_iff_run.1 (isEquivListLM_specI hs₁ hls.2 hrs.2) ob s' hrun
          exact ⟨hs₂, ht₁.trans ht₂, hb₂⟩

end LevelMemos

end InLeanProof
