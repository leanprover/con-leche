module

public import InLeanProof.StateOpsI
public import ConLeche.Verify.Cached.KnotC

/-!
# The knot assembly: memo wrappers, the eager memos, the knot step (task #451, lane P2-infer)

`KnotC.lean`'s twin.  A memo wrapper at fuel `f + 1` simulates its slot
from its body's simulation at fuel `f` (`BodySpecI`/`BodySpecBI`): a hit
answers by the memo's `CSOKI` clause (`UnaryOK`/`BinaryOK` at the query, which
reads the stored value), a miss runs the body and the insert keeps the
clause, backed one fuel up at every depth by the pure checker's depth
invariance.  `withEagerMemos` swaps the eager tower's memos in (the
invariant at `eager := true`) and out (`ModeMemosOKI`).  `ssimI_succ` ties
the slots to the bodies, `ssimI` by fuel induction.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {eager : Bool} {env : ConLeche.Env}

/-! ## The memo maps' updates leave the table alone -/

section Setters
variable (s : InLean.CState)

@[conleche_grind =] theorem TrS_setInferC (m : Std.HashMap EKey Expr) (e : Expr) :
    TrS { s with inferC := m } e = TrS s e := rfl
@[conleche_grind =] theorem OkS_setInferC (m : Std.HashMap EKey Expr) (e : Expr) :
    OkS { s with inferC := m } e = OkS s e := rfl
@[conleche_grind =] theorem TabLe_setInferC (s₀ : InLean.CState) (m : Std.HashMap EKey Expr) :
    TabLe s₀ { s with inferC := m } = TabLe s₀ s := rfl
@[conleche_grind =] theorem TrS_setWhnfCoreC (m : Std.HashMap EKey Expr) (e : Expr) :
    TrS { s with whnfCoreC := m } e = TrS s e := rfl
@[conleche_grind =] theorem OkS_setWhnfCoreC (m : Std.HashMap EKey Expr) (e : Expr) :
    OkS { s with whnfCoreC := m } e = OkS s e := rfl
@[conleche_grind =] theorem TabLe_setWhnfCoreC (s₀ : InLean.CState) (m : Std.HashMap EKey Expr) :
    TabLe s₀ { s with whnfCoreC := m } = TabLe s₀ s := rfl
@[conleche_grind =] theorem TrS_setWhnfCoreCheapC (m : Std.HashMap EKey Expr) (e : Expr) :
    TrS { s with whnfCoreCheapC := m } e = TrS s e := rfl
@[conleche_grind =] theorem OkS_setWhnfCoreCheapC (m : Std.HashMap EKey Expr) (e : Expr) :
    OkS { s with whnfCoreCheapC := m } e = OkS s e := rfl
@[conleche_grind =] theorem TabLe_setWhnfCoreCheapC (s₀ : InLean.CState)
    (m : Std.HashMap EKey Expr) : TabLe s₀ { s with whnfCoreCheapC := m } = TabLe s₀ s := rfl
@[conleche_grind =] theorem TrS_setWhnfC (m : Std.HashMap EKey Expr) (e : Expr) :
    TrS { s with whnfC := m } e = TrS s e := rfl
@[conleche_grind =] theorem OkS_setWhnfC (m : Std.HashMap EKey Expr) (e : Expr) :
    OkS { s with whnfC := m } e = OkS s e := rfl
@[conleche_grind =] theorem TabLe_setWhnfC (s₀ : InLean.CState) (m : Std.HashMap EKey Expr) :
    TabLe s₀ { s with whnfC := m } = TabLe s₀ s := rfl
@[conleche_grind =] theorem TrS_setInferIOC (m : Std.HashMap EKey Expr) (e : Expr) :
    TrS { s with inferIOC := m } e = TrS s e := rfl
@[conleche_grind =] theorem OkS_setInferIOC (m : Std.HashMap EKey Expr) (e : Expr) :
    OkS { s with inferIOC := m } e = OkS s e := rfl
@[conleche_grind =] theorem TabLe_setInferIOC (s₀ : InLean.CState) (m : Std.HashMap EKey Expr) :
    TabLe s₀ { s with inferIOC := m } = TabLe s₀ s := rfl
@[conleche_grind =] theorem TabLe_setDefeqC (s₀ : InLean.CState)
    (m : Std.HashMap (EKey × EKey) Bool) : TabLe s₀ { s with defeqC := m } = TabLe s₀ s := rfl

end Setters

/-! ## The invariant at a state with other memo maps

`CSOKIMemos s s'`: `s'` has `s`'s table and stored-constant, level and
bulk-instantiation caches, so every clause but the six entry-point memos'
and the eager tower's carries over. -/

/-- Every `CSOKI` clause that reads no entry-point memo. -/
structure CSOKIRest (eager : Bool) (env : ConLeche.Env) (s : InLean.CState) : Prop where
  fv : FVTableOK s
  fvClosed : ∀ (n : Nat) (ty : Expr) (cty : ConLeche.Expr), s.fvTys[n]? = some ty →
    TransS s ty = some cty → cty.looseBVarsBounded 0 = true
  constTy : ∀ n us i, s.constTyAt[(n, us)]? = some i → ∃ cus ci ct,
    toLevels us = some cus ∧ env.find? (toName n) = some ci ∧ TransS s i = some ct ∧
    Expr.RangeOk i ∧
    ct = ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams cus
  constVal : ∀ n us i, s.constValAt[(n, us)]? = some i → ∃ cus cv v h cval,
    toLevels us = some cus ∧ env.find? (toName n) = some (.defnInfo cv v h) ∧
    TransS s i = some cval ∧ Expr.RangeOk i ∧ cval = v.instantiateLevelParams cv.levelParams cus
  ruleRhs : ∀ c j us i, s.ruleRhsAt[(c, j, us)]? = some i → ∃ cus cv mI rP isK rules rl cr,
    toLevels us = some cus ∧ env.find? (toName c) = some (.recInfo cv mI rP isK rules) ∧
    rules.find? (fun r' => r'.ctor == toName j) = some rl ∧
    TransS s i = some cr ∧ Expr.RangeOk i ∧ cr = rl.rhs.instantiateLevelParams cv.levelParams cus
  lsimp : ∀ u v, s.lsimpC[u]? = some v → ∀ cu, toLevel u = some cu →
    toLevel v = some (ConLeche.Level.simplify cu)
  eqv : ∀ l r b, s.eqvC[(l, r)]? = some b → ∀ cl cr, toLevel l = some cl → toLevel r = some cr →
    ConLeche.Level.isEquiv cl cr = some b
  instC : ∀ k vs r, s.instC[InstKey.mk k vs]? = some r → ∃ ck cvs cr,
    TransS s k = some ck ∧ vs.mapM (TransS s) = some cvs ∧ TransS s r = some cr ∧
    Expr.RangeOk r ∧ (∀ cv ∈ cvs, cv.looseBVarsBounded 0 = true) ∧
    cr = ck.instantiateList cvs 0

theorem CSOKI.keepMemos {mode : ConLeche.CheckMode} {s : InLean.CState} (hs : CSOKI mode eager env s) :
    CSOKIRest eager env s :=
  ⟨hs.fv, hs.fvClosed, hs.constTy, hs.constVal, hs.ruleRhs, hs.lsimp, hs.eqv, hs.instC⟩

/-- The rest of the invariant at a state whose entry-point memos alone differ. -/
theorem CSOKIRest.memos {s : InLean.CState} (h : CSOKIRest eager env s)
    (mwc mwcc mw mi mio : Std.HashMap EKey Expr) (mdq : Std.HashMap (EKey × EKey) Bool)
    (mem : InLean.ModeMemos) :
    CSOKIRest eager env { s with
      whnfCoreC := mwc
      whnfCoreCheapC := mwcc
      whnfC := mw
      inferC := mi
      inferIOC := mio
      defeqC := mdq
      eagerMemos := mem } :=
  ⟨⟨h.fv.cls, h.fv.distinct, h.fv.ty, h.fv.seen⟩, h.fvClosed, h.constTy, h.constVal, h.ruleRhs,
    h.lsimp, h.eqv, h.instC⟩

/-- The eager tower's clause reads only the table. -/
theorem ModeMemosOKI.sameTab {mode : ConLeche.CheckMode} {s s' : InLean.CState} {mm : InLean.ModeMemos}
    (h : ModeMemosOKI mode env s mm) (ht : tableOf s' = tableOf s) : ModeMemosOKI mode env s' mm :=
  h.of_tabLe (by intro id c hc; unfold tableOf at ht; simp only [tableOf, ht] at hc ⊢; exact hc)

/-- `CSOKI` from the rest and the memo clauses. -/
theorem CSOKI.ofRest {mode : ConLeche.CheckMode} {s : InLean.CState} (h : CSOKIRest eager env s)
    (wc : ∀ k v, s.whnfCoreC[EKey.mk k]? = some v →
      UnaryOK s (fun F d e => ConLeche.whnfCore mode eager env F d e) k v)
    (wcc : ∀ k v, s.whnfCoreCheapC[EKey.mk k]? = some v →
      UnaryOK s (fun F d e => ConLeche.whnfCore mode eager env F d e true) k v)
    (w : ∀ k v, s.whnfC[EKey.mk k]? = some v →
      UnaryOK s (fun F d e => ConLeche.whnf mode eager env F d e) k v)
    (i : ∀ k v, s.inferC[EKey.mk k]? = some v →
      UnaryOK s (fun F d e => ConLeche.inferTypeCore mode eager env F d e) k v)
    (io : ∀ k v, s.inferIOC[EKey.mk k]? = some v →
      UnaryOK s (fun F d e => ConLeche.inferTypeIO mode eager env F d e) k v)
    (dq : ∀ a b r, s.defeqC[(EKey.mk a, EKey.mk b)]? = some r →
      BinaryOK s (fun F d x y => ConLeche.isDefEqCore mode eager env F d x y) a b r)
    {mm : InLean.ModeMemos} (em : ModeMemosOKI mode env s mm) (hmm : s.eagerMemos = mm) :
    CSOKI mode eager env s :=
  ⟨h.fv, h.fvClosed, wc, wcc, w, i, io, dq, h.constTy, h.constVal, h.ruleRhs, h.lsimp, h.eqv,
    h.instC, hmm ▸ em⟩

/-! ## The bodies' specs as triples -/

theorem BodySpecI.triple {mode : ConLeche.CheckMode} {body : Nat → Expr → InLean.CheckCM Expr}
    {spec : Nat → ConLeche.Expr → ConLeche.FueledM ConLeche.Expr}
    (h : BodySpecI mode eager env body spec) {s₀ : InLean.CState} {d : Nat} {i : Expr}
    (hs : CSOKI mode eager env s₀) (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (spec d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ :=
  h hs hok hw hc

theorem BodySpecBI.triple {mode : ConLeche.CheckMode} {body : Nat → Expr → Expr → InLean.CheckCM Bool}
    {spec : Nat → ConLeche.Expr → ConLeche.Expr → ConLeche.FueledM Bool}
    (h : BodySpecBI mode eager env body spec) {s₀ : InLean.CState} {d : Nat} {a b : Expr}
    (hs : CSOKI mode eager env s₀) (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true)
    (hwa : ConLeche.Expr.WScoped d (TrS s₀ a)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ b))
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ body d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ Runs (spec d (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄ :=
  h hs hoka hokb hwa hwb hca hcb

/-! ## The unary clause's hit and insert -/

/-- A hit answers by the clause: the stored value has a reading, is closed,
and a run of the pure function at the query's translation answers it at the
query's depth. -/
theorem UnaryOK.hit {s : InLean.CState}
    {spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr} {k v : Expr} {d : Nat}
    (hU : UnaryOK s spec k v) (hok : OkS s k = true) (hw : ConLeche.Expr.WScoped d (TrS s k)) :
    OkS s v = true ∧ (TrS s v).looseBVarsBounded 0 = true ∧ ∃ F, spec F d (TrS s k) = .ok (TrS s v) := by
  obtain ⟨ck, cv, hck, hcv, hr, hc, F, hF⟩ := hU
  rw [TransS_of_ok hok] at hck
  obtain rfl := Option.some.inj hck
  obtain ⟨hokv, htr⟩ := ok_of_TransS hr hcv
  subst htr
  exact ⟨hokv, hc, F, hF _ hw.to_wscopedB⟩

/-- Inserting an answer backed at one depth keeps a unary clause, given the
pure function's depth invariance. -/
theorem UnaryOK.insert {s : InLean.CState}
    {spec : Nat → Nat → ConLeche.Expr → ConLeche.CheckM ConLeche.Expr}
    (hdi : ∀ F d₁ d₂ e, e.wscopedB d₁ = true → e.wscopedB d₂ = true → spec F d₁ e = spec F d₂ e)
    {mp : Std.HashMap EKey Expr} (hmp : ∀ k v, mp[EKey.mk k]? = some v → UnaryOK s spec k v)
    {i r : Expr} {d F : Nat} (hok : OkS s i = true) (hw : ConLeche.Expr.WScoped d (TrS s i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (hF : spec F d (TrS s i) = .ok (TrS s r)) :
    ∀ k v, (mp.insert (EKey.mk i) r)[EKey.mk k]? = some v → UnaryOK s spec k v := by
  intro k v h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hk
    obtain rfl := Option.some.inj h
    have hk' : Expr.keyEq i k = true := hk
    have htk : TransS s k = some (TrS s i) := by
      unfold TransS; rw [← toExpr_of_keyEq _ hk']; exact TransS_of_ok hok
    exact ⟨TrS s i, TrS s r, htk, TransS_of_ok hr, RangeOk_of_OkS hr, hc, F,
      fun d' hd' => by rw [hdi F d' d _ hd' hw.to_wscopedB]; exact hF⟩
  · exact hmp k v h

/-! ## The infer memo -/

section Infer
variable {fe : InLean.FEnv} {f : Nat}

theorem coreKnotI_infer_succ (d : Nat) (i : Expr) :
    (coreKnotI .verified eager fe (f + 1)).infer d i =
      memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI (coreKnotI .verified eager fe f) fe d e) d i := by
  cases eager <;> rfl

/-- An infer memo hit answers the pure infer. -/
theorem CSOKI.infer_hit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (hl : s.inferC[EKey.mk i]? = some r) (hok : OkS s i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s i)) :
    OkS s r = true ∧ Runs ((ConLeche.fueledFns .verified eager env).infer d (TrS s i)) (TrS s r) ∧
      ConLeche.Expr.WScoped d (TrS s r) ∧ (TrS s r).looseBVarsBounded 0 = true := by
  obtain ⟨hokr, hc, F, hF⟩ := (hs.inferC i r hl).hit hok hw
  exact ⟨hokr, ⟨F, hF⟩, ConLeche.inferTypeCore_WScoped henv F hF hw, hc⟩
grind_pattern [conleche_grind] CSOKI.infer_hit =>
  CSOKI .verified eager env s, s.inferC[EKey.mk i]?, TrS s r, ConLeche.Expr.WScoped d (TrS s i)

/-- Inserting a body's answer keeps the invariant; the query is read at the
run's initial state `s₀`, the answer at the insert's `s`. -/
theorem CSOKI.infer_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (h : Runs ((ConLeche.fueledFns .verified eager env).infer d (TrS s₀ i)) (TrS s r)) :
    CSOKI .verified eager env { s with inferC := s.inferC.insert (EKey.mk i) r } := by
  obtain ⟨F, hF⟩ := h
  have hok' := okS_of_tabLe htab hok
  rw [← TrS_of_tabLe htab hok] at hw hF
  exact CSOKI.ofRest (hs.keepMemos.memos s.whnfCoreC s.whnfCoreCheapC s.whnfC _ s.inferIOC s.defeqC
      s.eagerMemos) hs.whnfCoreC hs.whnfCoreCheapC hs.whnfC
    (UnaryOK.insert (spec := fun F d e => ConLeche.inferTypeCore .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.inferTypeCore_depth_inv henv F h₁ h₂)
      hs.inferC hok' hw hr hc hF) hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl
grind_pattern [conleche_grind] CSOKI.infer_insert =>
  CSOKI .verified eager env { s with inferC := s.inferC.insert (EKey.mk i) r },
  (ConLeche.fueledFns .verified eager env).infer d (TrS s₀ i)

/-- The infer memo wrapper simulates the pure infer at one fuel more than its
body. -/
theorem memoEI_infer_specI (henv : ConLeche.EnvWF env)
    (hbody : BodySpecI .verified eager env (inferBodyI (coreKnotI .verified eager fe f) fe)
      (ConLeche.inferBody (ConLeche.fueledFns .verified eager env) env))
    {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified eager fe (f + 1)).infer d i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).infer d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [coreKnotI_infer_succ, InLean.memoEI, hbody.triple] <;> finish

end Infer

/-! ## The whnfCore memos (one map per mode; `vcgen` splits the knot's `if c`) -/

section WhnfCore
variable {fe : InLean.FEnv} {f : Nat}

theorem coreKnotI_whnfCore_succ (c : Bool) (d : Nat) (i : Expr) :
    (coreKnotI .verified eager fe (f + 1)).whnfCore c d i =
      if c then
        memoEI (·.whnfCoreCheapC) (fun st mp => { st with whnfCoreCheapC := mp })
          (fun d e => whnfCoreBodyI .verified (coreKnotI .verified eager fe f) fe true d e) d i
      else
        memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
          (fun d e => whnfCoreBodyI .verified (coreKnotI .verified eager fe f) fe false d e) d i := by
  cases eager <;> cases c <;> rfl

theorem CSOKI.whnfCore_hit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (hl : s.whnfCoreC[EKey.mk i]? = some r) (hok : OkS s i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s i)) :
    OkS s r = true ∧ Runs ((ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s i)) (TrS s r) ∧
      ConLeche.Expr.WScoped d (TrS s r) ∧ (TrS s r).looseBVarsBounded 0 = true := by
  obtain ⟨hokr, hc, F, hF⟩ := (hs.whnfCoreC i r hl).hit hok hw
  exact ⟨hokr, ⟨F, hF⟩, ConLeche.whnfCore_WScoped henv F hF hw, hc⟩
grind_pattern [conleche_grind] CSOKI.whnfCore_hit =>
  CSOKI .verified eager env s, s.whnfCoreC[EKey.mk i]?, TrS s r, ConLeche.Expr.WScoped d (TrS s i)

theorem CSOKI.whnfCoreCheap_hit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (hl : s.whnfCoreCheapC[EKey.mk i]? = some r)
    (hok : OkS s i = true) (hw : ConLeche.Expr.WScoped d (TrS s i)) :
    OkS s r = true ∧ Runs ((ConLeche.fueledFns .verified eager env).whnfCore true d (TrS s i)) (TrS s r) ∧
      ConLeche.Expr.WScoped d (TrS s r) ∧ (TrS s r).looseBVarsBounded 0 = true := by
  obtain ⟨hokr, hc, F, hF⟩ := (hs.whnfCoreCheapC i r hl).hit hok hw
  exact ⟨hokr, ⟨F, hF⟩, ConLeche.whnfCore_WScoped henv F hF hw, hc⟩
grind_pattern [conleche_grind] CSOKI.whnfCoreCheap_hit =>
  CSOKI .verified eager env s, s.whnfCoreCheapC[EKey.mk i]?, TrS s r, ConLeche.Expr.WScoped d (TrS s i)

theorem CSOKI.whnfCore_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat}
    {i r : Expr} (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (h : Runs ((ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s₀ i)) (TrS s r)) :
    CSOKI .verified eager env { s with whnfCoreC := s.whnfCoreC.insert (EKey.mk i) r } := by
  obtain ⟨F, hF⟩ := h
  have hok' := okS_of_tabLe htab hok
  rw [← TrS_of_tabLe htab hok] at hw hF
  exact CSOKI.ofRest (hs.keepMemos.memos _ s.whnfCoreCheapC s.whnfC s.inferC s.inferIOC s.defeqC
      s.eagerMemos)
    (UnaryOK.insert (spec := fun F d e => ConLeche.whnfCore .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnfCore_depth_inv henv F h₁ h₂)
      hs.whnfCoreC hok' hw hr hc hF)
    hs.whnfCoreCheapC hs.whnfC hs.inferC hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl
grind_pattern [conleche_grind] CSOKI.whnfCore_insert =>
  CSOKI .verified eager env { s with whnfCoreC := s.whnfCoreC.insert (EKey.mk i) r },
  (ConLeche.fueledFns .verified eager env).whnfCore false d (TrS s₀ i)

theorem CSOKI.whnfCoreCheap_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat}
    {i r : Expr} (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (h : Runs ((ConLeche.fueledFns .verified eager env).whnfCore true d (TrS s₀ i)) (TrS s r)) :
    CSOKI .verified eager env { s with whnfCoreCheapC := s.whnfCoreCheapC.insert (EKey.mk i) r } := by
  obtain ⟨F, hF⟩ := h
  have hok' := okS_of_tabLe htab hok
  rw [← TrS_of_tabLe htab hok] at hw hF
  exact CSOKI.ofRest (hs.keepMemos.memos s.whnfCoreC _ s.whnfC s.inferC s.inferIOC s.defeqC
      s.eagerMemos) hs.whnfCoreC
    (UnaryOK.insert (spec := fun F d e => ConLeche.whnfCore .verified eager env F d e true)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnfCore_depth_inv henv F h₁ h₂)
      hs.whnfCoreCheapC hok' hw hr hc hF)
    hs.whnfC hs.inferC hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl
grind_pattern [conleche_grind] CSOKI.whnfCoreCheap_insert =>
  CSOKI .verified eager env { s with whnfCoreCheapC := s.whnfCoreCheapC.insert (EKey.mk i) r },
  (ConLeche.fueledFns .verified eager env).whnfCore true d (TrS s₀ i)

/-- The whnfCore memo wrappers simulate the pure whnfCore at one fuel more
than their bodies. -/
theorem memoEI_whnfCore_specI (henv : ConLeche.EnvWF env)
    (hbody : ∀ c, BodySpecI .verified eager env
      (whnfCoreBodyI .verified (coreKnotI .verified eager fe f) fe c)
      (ConLeche.whnfCoreBody .verified (ConLeche.fueledFns .verified eager env) env c))
    {c : Bool} {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI .verified eager env s₀)
    (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified eager fe (f + 1)).whnfCore c d i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [coreKnotI_whnfCore_succ, InLean.memoEI, BodySpecI.triple (hbody true), BodySpecI.triple (hbody false)] <;>
      finish

end WhnfCore

/-! ## The whnf memo -/

section Whnf
variable {fe : InLean.FEnv} {f : Nat}

theorem coreKnotI_whnf_succ (d : Nat) (i : Expr) :
    (coreKnotI .verified eager fe (f + 1)).whnf d i =
      memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotI .verified eager fe f) fe d e) d i := by
  cases eager <;> rfl

theorem CSOKI.whnf_hit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (hl : s.whnfC[EKey.mk i]? = some r) (hok : OkS s i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s i)) :
    OkS s r = true ∧ Runs ((ConLeche.fueledFns .verified eager env).whnf d (TrS s i)) (TrS s r) ∧
      ConLeche.Expr.WScoped d (TrS s r) ∧ (TrS s r).looseBVarsBounded 0 = true := by
  obtain ⟨hokr, hc, F, hF⟩ := (hs.whnfC i r hl).hit hok hw
  exact ⟨hokr, ⟨F, hF⟩, ConLeche.whnf_WScoped henv F hF hw, hc⟩
grind_pattern [conleche_grind] CSOKI.whnf_hit =>
  CSOKI .verified eager env s, s.whnfC[EKey.mk i]?, TrS s r, ConLeche.Expr.WScoped d (TrS s i)

theorem CSOKI.whnf_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (h : Runs ((ConLeche.fueledFns .verified eager env).whnf d (TrS s₀ i)) (TrS s r)) :
    CSOKI .verified eager env { s with whnfC := s.whnfC.insert (EKey.mk i) r } := by
  obtain ⟨F, hF⟩ := h
  have hok' := okS_of_tabLe htab hok
  rw [← TrS_of_tabLe htab hok] at hw hF
  exact CSOKI.ofRest (hs.keepMemos.memos s.whnfCoreC s.whnfCoreCheapC _ s.inferC s.inferIOC s.defeqC
      s.eagerMemos) hs.whnfCoreC hs.whnfCoreCheapC
    (UnaryOK.insert (spec := fun F d e => ConLeche.whnf .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.whnf_depth_inv henv F h₁ h₂)
      hs.whnfC hok' hw hr hc hF) hs.inferC hs.inferIOC hs.defeqC (hs.eager.sameTab rfl) rfl
grind_pattern [conleche_grind] CSOKI.whnf_insert =>
  CSOKI .verified eager env { s with whnfC := s.whnfC.insert (EKey.mk i) r },
  (ConLeche.fueledFns .verified eager env).whnf d (TrS s₀ i)

/-- The whnf memo wrapper simulates the pure whnf at one fuel more than its
body. -/
theorem memoEI_whnf_specI (henv : ConLeche.EnvWF env)
    (hbody : BodySpecI .verified eager env (whnfBodyI (coreKnotI .verified eager fe f) fe)
      (ConLeche.whnfBody (ConLeche.fueledFns .verified eager env) env))
    {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI .verified eager env s₀)
    (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified eager fe (f + 1)).whnf d i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).whnf d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [coreKnotI_whnf_succ, InLean.memoEI, hbody.triple] <;> finish

end Whnf

/-! ## The io memo -/

section InferIO
variable {fe : InLean.FEnv} {f : Nat}

theorem coreKnotI_inferIO_succ (d : Nat) (i : Expr) :
    (coreKnotI .verified eager fe (f + 1)).inferIO d i =
      memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
        (fun d e => inferBodyIOI (CoreFnsI.ioView (coreKnotI .verified eager fe f)) fe d e) d i := by
  cases eager <;> rfl

theorem CSOKI.inferIO_hit (henv : ConLeche.EnvWF env) {s : InLean.CState} {d : Nat} {i r : Expr}
    (hs : CSOKI .verified eager env s) (hl : s.inferIOC[EKey.mk i]? = some r) (hok : OkS s i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s i)) :
    OkS s r = true ∧ Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s i)) (TrS s r) ∧
      ConLeche.Expr.WScoped d (TrS s r) ∧ (TrS s r).looseBVarsBounded 0 = true := by
  obtain ⟨hokr, hc, F, hF⟩ := (hs.inferIOC i r hl).hit hok hw
  exact ⟨hokr, ⟨F, hF⟩, ConLeche.inferTypeIO_WScoped henv F hF hw, hc⟩
grind_pattern [conleche_grind] CSOKI.inferIO_hit =>
  CSOKI .verified eager env s, s.inferIOC[EKey.mk i]?, TrS s r, ConLeche.Expr.WScoped d (TrS s i)

theorem CSOKI.inferIO_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat}
    {i r : Expr} (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hr : OkS s r = true) (hc : (TrS s r).looseBVarsBounded 0 = true)
    (h : Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ i)) (TrS s r)) :
    CSOKI .verified eager env { s with inferIOC := s.inferIOC.insert (EKey.mk i) r } := by
  obtain ⟨F, hF⟩ := h
  have hok' := okS_of_tabLe htab hok
  rw [← TrS_of_tabLe htab hok] at hw hF
  exact CSOKI.ofRest (hs.keepMemos.memos s.whnfCoreC s.whnfCoreCheapC s.whnfC s.inferC _ s.defeqC
      s.eagerMemos) hs.whnfCoreC hs.whnfCoreCheapC hs.whnfC hs.inferC
    (UnaryOK.insert (spec := fun F d e => ConLeche.inferTypeIO .verified eager env F d e)
      (fun F _ _ _ h₁ h₂ => ConLeche.inferTypeIO_depth_inv henv F h₁ h₂)
      hs.inferIOC hok' hw hr hc hF) hs.defeqC (hs.eager.sameTab rfl) rfl
grind_pattern [conleche_grind] CSOKI.inferIO_insert =>
  CSOKI .verified eager env { s with inferIOC := s.inferIOC.insert (EKey.mk i) r },
  (ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ i)

/-- The io memo wrapper simulates the pure io slot at one fuel more than its
body. -/
theorem memoEI_inferIO_specI (henv : ConLeche.EnvWF env)
    (hbody : BodySpecI .verified eager env
      (inferBodyIOI (CoreFnsI.ioView (coreKnotI .verified eager fe f)) fe)
      (ConLeche.inferBodyIO (ConLeche.CoreFns.ioView (ConLeche.fueledFns .verified eager env)) env))
    {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI .verified eager env s₀)
    (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified eager fe (f + 1)).inferIO d i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [coreKnotI_inferIO_succ, InLean.memoEI, hbody.triple] <;> finish

end InferIO

/-! ## The defeq memo -/

section Defeq
variable {fe : InLean.FEnv} {f : Nat}

theorem coreKnotI_defeq_succ (d : Nat) (a b : Expr) :
    (coreKnotI .verified eager fe (f + 1)).defeq d a b =
      memoBI (fun d a b => defeqBodyI .verified eager (coreKnotI .verified eager fe f) fe d a b)
        d a b := by
  cases eager <;> rfl

theorem CSOKI.defeq_hit {s : InLean.CState} {d : Nat} {a b : Expr} {r : Bool}
    (hs : CSOKI .verified eager env s) (hl : s.defeqC[(EKey.mk a, EKey.mk b)]? = some r)
    (hoka : OkS s a = true) (hokb : OkS s b = true)
    (hwa : ConLeche.Expr.WScoped d (TrS s a)) (hwb : ConLeche.Expr.WScoped d (TrS s b)) :
    Runs ((ConLeche.fueledFns .verified eager env).defeq d (TrS s a) (TrS s b)) r := by
  obtain ⟨ca, cb, hca, hcb, F, hF⟩ := hs.defeqC a b r hl
  rw [TransS_of_ok hoka] at hca
  rw [TransS_of_ok hokb] at hcb
  obtain rfl := Option.some.inj hca
  obtain rfl := Option.some.inj hcb
  exact ⟨F, hF d hwa.to_wscopedB hwb.to_wscopedB⟩
grind_pattern [conleche_grind] CSOKI.defeq_hit =>
  CSOKI .verified eager env s, s.defeqC[(EKey.mk a, EKey.mk b)]?, some r,
  ConLeche.Expr.WScoped d (TrS s a), ConLeche.Expr.WScoped d (TrS s b)

theorem CSOKI.defeq_insert (henv : ConLeche.EnvWF env) {s₀ s : InLean.CState} {d : Nat}
    {a b : Expr} {r : Bool} (hs : CSOKI .verified eager env s) (htab : TabLe s₀ s)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true)
    (hwa : ConLeche.Expr.WScoped d (TrS s₀ a)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ b))
    (h : Runs ((ConLeche.fueledFns .verified eager env).defeq d (TrS s₀ a) (TrS s₀ b)) r) :
    CSOKI .verified eager env { s with defeqC := s.defeqC.insert (EKey.mk a, EKey.mk b) r } := by
  obtain ⟨F, hF⟩ := h
  have hoka' := okS_of_tabLe htab hoka
  have hokb' := okS_of_tabLe htab hokb
  rw [← TrS_of_tabLe htab hoka, ← TrS_of_tabLe htab hokb] at hF
  rw [← TrS_of_tabLe htab hoka] at hwa
  rw [← TrS_of_tabLe htab hokb] at hwb
  refine CSOKI.ofRest (hs.keepMemos.memos s.whnfCoreC s.whnfCoreCheapC s.whnfC s.inferC s.inferIOC _
      s.eagerMemos) hs.whnfCoreC hs.whnfCoreCheapC hs.whnfC hs.inferC hs.inferIOC ?_
    (hs.eager.sameTab rfl) rfl
  intro a' b' r' hl
  rw [Std.HashMap.getElem?_insert] at hl
  split at hl
  · rename_i hk
    obtain rfl := Option.some.inj hl
    have hk' : Expr.keyEq a a' = true ∧ Expr.keyEq b b' = true := by
      simpa [BEq.beq] using hk
    have hta : TransS s a' = some (TrS s a) := by
      unfold TransS; rw [← toExpr_of_keyEq _ hk'.1]; exact TransS_of_ok hoka'
    have htb : TransS s b' = some (TrS s b) := by
      unfold TransS; rw [← toExpr_of_keyEq _ hk'.2]; exact TransS_of_ok hokb'
    exact ⟨TrS s a, TrS s b, hta, htb, F, fun d' hda hdb => by
      show ConLeche.isDefEqCore _ _ _ _ _ _ _ = _; rw [ConLeche.isDefEqCore_depth_inv henv F hda hdb hwa.to_wscopedB hwb.to_wscopedB]; exact hF⟩
  · exact hs.defeqC a' b' r' hl
grind_pattern [conleche_grind] CSOKI.defeq_insert =>
  CSOKI .verified eager env { s with defeqC := s.defeqC.insert (EKey.mk a, EKey.mk b) r },
  (ConLeche.fueledFns .verified eager env).defeq d (TrS s₀ a) (TrS s₀ b)

/-- The defeq memo wrapper simulates the pure defeq at one fuel more than its
body. -/
theorem memoBI_defeq_specI (henv : ConLeche.EnvWF env)
    (hbody : BodySpecBI .verified eager env
      (defeqBodyI .verified eager (coreKnotI .verified eager fe f) fe)
      (ConLeche.defeqBody .verified eager (ConLeche.fueledFns .verified eager env) env))
    {s₀ : InLean.CState} {d : Nat} {a b : Expr} (hs : CSOKI .verified eager env s₀)
    (hoka : OkS s₀ a = true) (hokb : OkS s₀ b = true)
    (hwa : ConLeche.Expr.WScoped d (TrS s₀ a)) (hwb : ConLeche.Expr.WScoped d (TrS s₀ b))
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hcb : (TrS s₀ b).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (coreKnotI .verified eager fe (f + 1)).defeq d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs ((ConLeche.fueledFns .verified eager env).defeq d (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄ := by
  sym only [conleche_grind] =>
    vcgen [coreKnotI_defeq_succ, InLean.memoBI, hbody.triple] <;> finish

end Defeq

end InLeanProof
