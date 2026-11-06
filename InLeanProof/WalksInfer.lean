module

public import InLeanProof.StateOpsI
public import ConLeche.Verify.Cached.DiscC4

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Lists along the run -/

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

/-! ## The accumulator arrays through the translation -/

section Arrays
variable (s : InLean.CState)

@[conleche_grind =] theorem TrSL_push_rev (fvs : Array Expr) (a : Expr) :
    (TrSL s (fvs.push a).toList).reverse = TrS s a :: (TrSL s fvs.toList).reverse := by
  simp [TrSL]

@[conleche_grind =] theorem OkSL_push (fvs : Array Expr) (a : Expr) :
    OkSL s (fvs.push a).toList = (OkSL s fvs.toList && OkS s a) := by
  simp [OkSL, List.all_append, Bool.and_comm]

@[conleche_grind =] theorem AllClosed_push (fvs : Array Expr) (a : Expr) :
    AllClosed (TrSL s (fvs.push a).toList) =
      (AllClosed (TrSL s fvs.toList) && (TrS s a).looseBVarsBounded 0) := by
  simp [AllClosed, TrSL, List.all_append]

@[conleche_grind =] theorem TrSL_singleton_rev (a : Expr) :
    (TrSL s (#[a] : Array Expr).toList).reverse = [TrS s a] := by
  simp [TrSL]

@[conleche_grind =] theorem TrSL_empty_rev :
    (TrSL s (#[] : Array Expr).toList).reverse = [] := by
  simp [TrSL]

@[conleche_grind =] theorem OkSL_singleton (a : Expr) :
    OkSL s (#[a] : Array Expr).toList = OkS s a := by
  simp [OkSL]

@[conleche_grind =] theorem OkSL_empty : OkSL s (#[] : Array Expr).toList = true := by
  simp [OkSL]

@[conleche_grind =] theorem AllClosed_singleton (a : Expr) :
    AllClosed (TrSL s (#[a] : Array Expr).toList) = (TrS s a).looseBVarsBounded 0 := by
  simp [AllClosed, TrSL]

@[conleche_grind =] theorem AllClosed_empty : AllClosed (TrSL s (#[] : Array Expr).toList) = true := by
  simp [AllClosed, TrSL]

end Arrays

/-! ## Closedness, one constructor at a time, and through the walks' operations -/

section Closed
open ConLeche.Expr

@[conleche_grind =] theorem lbb_lam (k : Nat) (t b : ConLeche.Expr) :
    (ConLeche.Expr.lam t b).looseBVarsBounded k = (t.looseBVarsBounded k && b.looseBVarsBounded (k + 1)) :=
  rfl
@[conleche_grind =] theorem lbb_forallE (k : Nat) (t b : ConLeche.Expr) :
    (ConLeche.Expr.forallE t b).looseBVarsBounded k =
      (t.looseBVarsBounded k && b.looseBVarsBounded (k + 1)) := rfl
@[conleche_grind =] theorem lbb_fvar (k i : Nat) (t : ConLeche.Expr) :
    (ConLeche.Expr.fvar i t).looseBVarsBounded k = true := rfl
@[conleche_grind =] theorem lbb_sort (k : Nat) (u : ConLeche.Level) :
    (ConLeche.Expr.sort u).looseBVarsBounded k = true := rfl
@[conleche_grind =] theorem lbb_const (k : Nat) (n : ConLeche.Name) (us : List ConLeche.Level) :
    (ConLeche.Expr.const n us).looseBVarsBounded k = true := rfl
@[conleche_grind =] theorem lbb_lit (k : Nat) (l : ConLeche.Literal) :
    (ConLeche.Expr.lit l).looseBVarsBounded k = true := rfl
@[conleche_grind =] theorem lbb_bvar (k i : Nat) :
    (ConLeche.Expr.bvar i).looseBVarsBounded k = decide (i < k) := rfl

/-- One binder opened at a closed value: the body, instantiated with it in
front of the accumulator, is closed (`wscoped_open_binder`'s twin). -/
theorem lbb_open_binder {a body : ConLeche.Expr} {ws : List ConLeche.Expr}
    (ha : a.looseBVarsBounded 0 = true) (hb : (body.instantiateList ws 1).looseBVarsBounded 1 = true) :
    (body.instantiateList (a :: ws)).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList_cons]
  exact looseBVarsBounded_instantiate1_gen ha hb
grind_pattern [conleche_grind] lbb_open_binder => body.instantiateList (a :: ws)

/-- Abstracting a closed term at a depth leaves one loose index. -/
theorem lbb_abstract1 {d : Nat} {e : ConLeche.Expr} (h : e.looseBVarsBounded 0 = true) :
    (e.abstract1 d).looseBVarsBounded 1 = true :=
  ConLeche.looseBVarsBounded_abstract1 e 0 h
grind_pattern [conleche_grind] lbb_abstract1 => e.looseBVarsBounded 0, e.abstract1 d

end Closed

theorem inferLamsOutI_spec {d : Nat} :
    ∀ {stk : List Expr} {j : Nat} {cur : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ →
      OkS s₀ cur = true → OkSL s₀ stk = true →
      ⦃fun s => s = s₀⦄ inferLamsOutI d stk j cur
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs (ConLeche.inferLamsOut (m := ConLeche.FueledM) d (TrSL s₀ stk) j (TrS s₀ cur))
          (TrS s' v); ⊤⦄ := by
  intro stk
  induction stk with
  | nil =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferLamsOut.eq_1] => vcgen [InLean.inferLamsOutI] <;> finish
  | cons _ rest ih =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferLamsOut.eq_2] =>
      vcgen [InLean.inferLamsOutI, abstractRangeM_specI (mode := mode) (eager := eager) (env := env), ih]
          <;> finish

/-! ## A binder's translation is a binder

The pure mirrors match the translation on `.lam`/`.forallE`, InLean matches
`EO.stripTop` of the term: where InLean falls through, so does the mirror.
Stated forward, keyed by the translation's binder: the stripped node is the
binder its total readers (`binderNameOf`, …) read, which the fall-through
hypothesis refutes. -/

/-- A binder's name (total). -/
@[expose] def binderNameOf : Expr → Name
  | .lam n _ _ _ | .forallE n _ _ _ => n
  | _ => .anonymous

/-- A binder's domain (total). -/
@[expose] def binderDomOf : Expr → Expr
  | .lam _ t _ _ | .forallE _ t _ _ => t
  | _ => .bvar 0

/-- A binder's body (total). -/
@[expose] def binderBodyOf : Expr → Expr
  | .lam _ _ b _ | .forallE _ _ b _ => b
  | _ => .bvar 0

/-- A binder's info (total). -/
@[expose] def binderInfoOf : Expr → BinderInfo
  | .lam _ _ _ bi | .forallE _ _ _ bi => bi
  | _ => .default

theorem trans_getD_ne_binder (s : InLean.CState) (id : FVarId) :
    (∀ a b, (FVarTable.trans (tableOf s) id).getD (.bvar 0) ≠ .lam a b) ∧
      (∀ a b, (FVarTable.trans (tableOf s) id).getD (.bvar 0) ≠ .forallE a b) := by
  cases h : FVarTable.trans (tableOf s) id with
  | none => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | some c =>
    obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c h
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- The translation is a lambda (a test the fall-through refutation reads). -/
@[expose] def isLamC : ConLeche.Expr → Bool
  | .lam .. => true
  | _ => false

/-- The translation is a ∀. -/
@[expose] def isForallC : ConLeche.Expr → Bool
  | .forallE .. => true
  | _ => false

@[conleche_grind =] theorem isLamC_lam (a b : ConLeche.Expr) : isLamC (.lam a b) = true := rfl
@[conleche_grind =] theorem isForallC_forallE (a b : ConLeche.Expr) :
    isForallC (.forallE a b) = true := rfl

/-- Keyed by the translation alone, guarded by the Boolean test: the
stripped node is a lambda only where the translation is one (a pattern on
the translation's binder would pair every translation with every binder). -/
theorem stripTop_of_TrS_lam {s : InLean.CState} {e : Expr} (h : isLamC (TrS s e) = true) :
    EO.stripTop e = .lam (binderNameOf (EO.stripTop e)) (binderDomOf (EO.stripTop e))
      (binderBodyOf (EO.stripTop e)) (binderInfoOf (EO.stripTop e)) := by
  induction e with
  | mdata _ x ih => exact ih h
  | lam => rfl
  | fvar id =>
    simp only [TrS, trE] at h
    cases hc : FVarTable.trans (tableOf s) id with
    | none => simp [hc, isLamC] at h
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hc
      simp [hc, isLamC] at h
  | _ => simp [TrS, trE, isLamC] at h
grind_pattern [conleche_grind] stripTop_of_TrS_lam => EO.stripTop e, TrS s e

theorem stripTop_of_TrS_forallE {s : InLean.CState} {e : Expr} (h : isForallC (TrS s e) = true) :
    EO.stripTop e = .forallE (binderNameOf (EO.stripTop e)) (binderDomOf (EO.stripTop e))
      (binderBodyOf (EO.stripTop e)) (binderInfoOf (EO.stripTop e)) := by
  induction e with
  | mdata _ x ih => exact ih h
  | forallE => rfl
  | fvar id =>
    simp only [TrS, trE] at h
    cases hc : FVarTable.trans (tableOf s) id with
    | none => simp [hc, isForallC] at h
    | some c =>
      obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hc
      simp [hc, isForallC] at h
  | _ => simp [TrS, trE, isForallC] at h
grind_pattern [conleche_grind] stripTop_of_TrS_forallE => EO.stripTop e, TrS s e

/-! ## The infer-λ loop walks (`BinderLoopC.lean`'s twins) -/

theorem inferLamsLeafI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat}
    {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (ht : OkS s₀ t = true) (hfv : OkSL s₀ fvs.toList = true)
    (hfc : AllClosed (TrSL s₀ fvs.toList) = true) (hstk : OkSL s₀ stk = true)
    (hw : ConLeche.Expr.WScoped (d + k) ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse))
    (hc : ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferLamsLeafI r d t k fvs stk
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferLamsLeaf (ConLeche.fueledFns mode eager env) d (TrS s₀ t) k
        (TrSL s₀ fvs.toList).reverse (TrSL s₀ stk)) (TrS s' v); ⊤⦄ := by
  sym only [conleche_grind, ConLeche.inferLamsLeaf.eq_1] =>
    vcgen [InLean.inferLamsLeafI, instListRevM_specI hs, ih.infer,
      abstractRangeM_specI (mode := mode) (eager := eager) (env := env),
      inferLamsOutI_spec (mode := mode) (eager := eager) (env := env)] <;> finish

theorem inferLamsI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Expr} {s₀ : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ t = true → OkSL s₀ fvs.toList = true →
      AllClosed (TrSL s₀ fvs.toList) = true → OkSL s₀ stk = true →
      ConLeche.Expr.WScoped (d + k) ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse) →
      ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ inferLamsI r d fuel t k fvs stk
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs (ConLeche.inferLams (ConLeche.fueledFns mode eager env) d fuel (TrS s₀ t) k
          (TrSL s₀ fvs.toList).reverse (TrSL s₀ stk)) (TrS s' v); ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ hs _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferLams.eq_3] =>
      vcgen [InLean.inferLamsI, inferLamsLeafI_spec ih] <;> finish
  | succ fuel ihFuel =>
    intro _ _ _ _ _ hs _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferLams.eq_1, ConLeche.inferLams.eq_2] =>
      vcgen [InLean.inferLamsI.eq_def, instListRevM_specI hs, ih.infer, ih.whnf,
        mkFVarM_specI (mode := mode) (eager := eager) (env := env), ihFuel,
        inferLamsLeafI_spec ih] <;> finish

/-! ## The infer-∀ loop walks

The ∀-loop's answer is a sort at an `imax` chain InLean builds; its
translation is the mirror's, but nothing bounds its depth (`okLv`), so
these posts state no reading of the answer: see the lane's record
(DESIGN.md, task #451, lane P2-infer). -/

/-- The `imax` fold is the mirror's, through the level translation. -/
theorem inferPisOut_trL :
    ∀ (stk : List Level) (v : Level),
      ConLeche.inferPisOut (m := ConLeche.FueledM) (stk.map trL) (trL v) =
        pure (trL (inferPisOutI stk v))
  | [], v => rfl
  | u :: rest, v => by
    rw [List.map_cons, ConLeche.inferPisOut, InLean.inferPisOutI]
    exact inferPisOut_trL rest (.imax u v)

theorem inferPisLeafI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat}
    {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Level} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (ht : OkS s₀ t = true) (hfv : OkSL s₀ fvs.toList = true)
    (hfc : AllClosed (TrSL s₀ fvs.toList) = true)
    (hw : ConLeche.Expr.WScoped (d + k) ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse))
    (hc : ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferPisLeafI r d t k fvs stk
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.inferPisLeaf (ConLeche.fueledFns mode eager env) d (TrS s₀ t) k
        (TrSL s₀ fvs.toList).reverse (stk.map trL)) (TrS s' v); ⊤⦄ := by
  sym only [conleche_grind, ConLeche.inferPisLeaf.eq_1, inferPisOut_trL] =>
    vcgen [InLean.inferPisLeafI, instListRevM_specI hs, ih.infer, ih.whnf] <;> finish

theorem inferPisI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ (fuel : Nat) {t : Expr} {k : Nat} {fvs : Array Expr} {stk : List Level} {s₀ : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ t = true → OkSL s₀ fvs.toList = true →
      AllClosed (TrSL s₀ fvs.toList) = true →
      ConLeche.Expr.WScoped (d + k) ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse) →
      ((TrS s₀ t).instantiateList (TrSL s₀ fvs.toList).reverse).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ inferPisI r d fuel t k fvs stk
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.inferPis (ConLeche.fueledFns mode eager env) d fuel (TrS s₀ t) k
          (TrSL s₀ fvs.toList).reverse (stk.map trL)) (TrS s' v); ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ hs _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferPis.eq_3] =>
      vcgen [InLean.inferPisI, inferPisLeafI_spec ih] <;> finish
  | succ fuel ihFuel =>
    intro _ _ _ _ _ hs _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferPis.eq_1, ConLeche.inferPis.eq_2, List.map_cons] =>
      vcgen [InLean.inferPisI.eq_def, instListRevM_specI hs, ih.infer, ih.whnf,
        mkFVarM_specI (mode := mode) (eager := eager) (env := env), ihFuel,
        inferPisLeafI_spec ih] <;> finish

/-! ## The inference spine loops (`DiscC4.lean`'s twins)

The argument check `defeqArgI` is P2-whnf's (`DiscC1`'s `defeqArgC_spec`):
its spec is a named hypothesis here. -/

/-- `defeqArgI`'s spec (`defeqArgC_spec`'s twin), P2-whnf's to prove. -/
@[expose] def DefeqArgSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) : Prop :=
  ∀ {s₀ : InLean.CState} {d : Nat} {a ta ty : Expr},
    CSOKI mode eager env s₀ → OkS s₀ a = true → OkS s₀ ta = true → OkS s₀ ty = true →
    ConLeche.Expr.WScoped d (TrS s₀ ta) → ConLeche.Expr.WScoped d (TrS s₀ ty) →
    (TrS s₀ ta).looseBVarsBounded 0 = true → (TrS s₀ ty).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ defeqArgI r d a ta ty
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqArg (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ ta)
        (TrS s₀ ty)) v; ⊤⦄

theorem DefeqArgSpecI.triple {r : InLean.CoreFnsI} (h : DefeqArgSpecI mode eager env r)
    {s₀ : InLean.CState} {d : Nat} {a ta ty : Expr}
    (hs : CSOKI mode eager env s₀) (ha : OkS s₀ a = true) (hta : OkS s₀ ta = true)
    (hty : OkS s₀ ty = true) (hwta : ConLeche.Expr.WScoped d (TrS s₀ ta))
    (hwty : ConLeche.Expr.WScoped d (TrS s₀ ty)) (hcta : (TrS s₀ ta).looseBVarsBounded 0 = true)
    (hcty : (TrS s₀ ty).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ defeqArgI r d a ta ty
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.defeqArg (ConLeche.fueledFns mode eager env) d (TrS s₀ a) (TrS s₀ ta)
        (TrS s₀ ty)) v; ⊤⦄ :=
  h hs ha hta hty hwta hwty hcta hcty

@[conleche_grind =] theorem reverse_singleton_eq {α : Type} (x : α) : [x].reverse = [x] := rfl

@[conleche_grind =] theorem instantiateList_nil_eq (e : ConLeche.Expr) (k : Nat) :
    e.instantiateList [] k = e := ConLeche.Expr.instantiateList_nil e k

@[conleche_grind =] theorem AllClosed_nil : AllClosed [] = true := rfl
@[conleche_grind =] theorem AllClosed_cons (a : ConLeche.Expr) (l : List ConLeche.Expr) :
    AllClosed (a :: l) = (a.looseBVarsBounded 0 && AllClosed l) := rfl

/-- A spine peeled at a scoped argument: the body, instantiated with it in
front of the accumulator, is scoped (`lbb_open_binder`'s twin for scope). -/
theorem wscoped_peel_cons {d : Nat} {a body : ConLeche.Expr} {ws : List ConLeche.Expr}
    (ha : ConLeche.Expr.WScoped d a) (hb : ConLeche.Expr.WScoped d (body.instantiateList ws 1)) :
    ConLeche.Expr.WScoped d (body.instantiateList (a :: ws)) := by
  rw [ConLeche.Expr.instantiateList_cons]
  exact ConLeche.Expr.WScoped.instantiate1_gen ha 0 hb
grind_pattern [conleche_grind] wscoped_peel_cons => ConLeche.Expr.WScoped d a, body.instantiateList (a :: ws)

/-! The spine's cons step, its two arms named (`inferSpinePi`/`inferSpineWhnf`'s
twins, `rfl` restatements of `inferSpineI`'s arms). -/

/-- The syntactic-∀ arm of `inferSpineI`. -/
@[expose] def inferSpinePiI (r : InLean.CoreFnsI) (d : Nat) (dom body : Expr) (acc : Array Expr)
    (a : Expr) (rest : List Expr) : InLean.CheckCM Expr := do
  let dom' ← instListRevM dom acc
  let ta ← r.infer d a
  unless ← defeqArgI r d a ta dom' do
    throw (.invalid "application type mismatch")
  inferSpineI r d body (acc.push a) rest

/-- The normalize-and-retry arm of `inferSpineI`. -/
@[expose] def inferSpineWhnfI (r : InLean.CoreFnsI) (d : Nat) (ty : Expr) (acc : Array Expr)
    (a : Expr) (rest : List Expr) : InLean.CheckCM Expr := do
  let ty' ← instListRevM ty acc
  match EO.stripTop (← r.whnf d ty') with
  | .forallE _ dom body _ => do
    let ta ← r.infer d a
    unless ← defeqArgI r d a ta dom do
      throw (.invalid "application type mismatch")
    inferSpineI r d body #[a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpineI_cons (r : InLean.CoreFnsI) (d : Nat) (ty : Expr) (acc : Array Expr) (a : Expr)
    (rest : List Expr) :
    inferSpineI r d ty acc (a :: rest) =
      match EO.stripTop ty with
      | .forallE _ dom body _ => inferSpinePiI r d dom body acc a rest
      | _ => inferSpineWhnfI r d ty acc a rest := by
  rw [InLean.inferSpineI]; rfl

/-- What the spine loop's spec states, for one argument list (the induction
hypothesis the arms take). -/
@[expose] def SpineSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) (d : Nat) (args : List Expr) : Prop :=
  ∀ {ty : Expr} {acc : Array Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ ty = true → OkSL s₀ acc.toList = true →
    AllClosed (TrSL s₀ acc.toList) = true → OkSL s₀ args = true →
    AllClosed (TrSL s₀ args) = true → AllWS d (TrSL s₀ args) →
    ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse) →
    ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ inferSpineI r d ty acc args
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpine (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrSL s₀ args)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄

theorem SpineSpecI.triple {r : InLean.CoreFnsI} {d : Nat} {args : List Expr}
    (h : SpineSpecI mode eager env r d args) {ty : Expr} {acc : Array Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hty : OkS s₀ ty = true) (hacc : OkSL s₀ acc.toList = true)
    (hcacc : AllClosed (TrSL s₀ acc.toList) = true) (hargs : OkSL s₀ args = true)
    (hcargs : AllClosed (TrSL s₀ args) = true) (hwargs : AllWS d (TrSL s₀ args))
    (hw : ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse))
    (hc : ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferSpineI r d ty acc args
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpine (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrSL s₀ args)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ :=
  h hs hty hacc hcacc hargs hcargs hwargs hw hc

theorem inferSpinePiI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    (harg : DefeqArgSpecI mode eager env r) {d : Nat} {rest : List Expr}
    (ihr : SpineSpecI mode eager env r d rest) {dom body : Expr} {acc : Array Expr} {a : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hdom : OkS s₀ dom = true)
    (hbody : OkS s₀ body = true) (hacc : OkSL s₀ acc.toList = true)
    (hcacc : AllClosed (TrSL s₀ acc.toList) = true) (ha : OkS s₀ a = true)
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hrest : OkSL s₀ rest = true) (hcrest : AllClosed (TrSL s₀ rest) = true)
    (hwrest : AllWS d (TrSL s₀ rest))
    (hw : ConLeche.Expr.WScoped d
      ((ConLeche.Expr.forallE (TrS s₀ dom) (TrS s₀ body)).instantiateList (TrSL s₀ acc.toList).reverse))
    (hc : ((ConLeche.Expr.forallE (TrS s₀ dom) (TrS s₀ body)).instantiateList
      (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferSpinePiI r d dom body acc a rest
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpinePi (ConLeche.fueledFns mode eager env) d (TrS s₀ dom) (TrS s₀ body)
        (TrSL s₀ acc.toList).reverse (TrS s₀ a) (TrSL s₀ rest)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.inferSpinePi] =>
    vcgen [inferSpinePiI, instListRevM_specI hs, ih.infer, harg.triple, ihr.triple] <;> finish

theorem inferSpineWhnfI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    (harg : DefeqArgSpecI mode eager env r) {d : Nat} {rest : List Expr}
    (ihr : SpineSpecI mode eager env r d rest) {ty : Expr} {acc : Array Expr} {a : Expr}
    {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hty : OkS s₀ ty = true)
    (hacc : OkSL s₀ acc.toList = true)
    (hcacc : AllClosed (TrSL s₀ acc.toList) = true) (ha : OkS s₀ a = true)
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hrest : OkSL s₀ rest = true) (hcrest : AllClosed (TrSL s₀ rest) = true)
    (hwrest : AllWS d (TrSL s₀ rest))
    (hw : ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse))
    (hc : ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferSpineWhnfI r d ty acc a rest
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpineWhnf (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrS s₀ a) (TrSL s₀ rest)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.inferSpineWhnf] =>
    vcgen [inferSpineWhnfI, instListRevM_specI hs, ih.infer, ih.whnf, harg.triple, ihr.triple] <;> finish

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    (harg : DefeqArgSpecI mode eager env r) {d : Nat} :
    ∀ args : List Expr, SpineSpecI mode eager env r d args := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferSpine.eq_1] =>
      vcgen [InLean.inferSpineI, instListRevM_specI hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ hs _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferSpine_pi, ConLeche.inferSpine_ne_pi] =>
      vcgen [inferSpineI_cons, inferSpinePiI_spec ih harg ihr hs,
        inferSpineWhnfI_spec ih harg ihr hs] <;> finish

/-! ### The io-grade spine loop -/

/-- The io view's whnf slot is the record's. -/
theorem KnotSpecI.ioWhnf {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI mode eager env s₀)
    (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (CoreFnsI.ioView r).whnf d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).whnf d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ :=
  ih.whnf hs hok hw hc

/-- The io view's infer slot is the record's io slot. -/
theorem KnotSpecI.ioInfer {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r)
    {s₀ : InLean.CState} {d : Nat} {i : Expr} (hs : CSOKI mode eager env s₀)
    (hok : OkS s₀ i = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ i))
    (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ (CoreFnsI.ioView r).infer d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).inferIO d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ :=
  ih.inferIO hs hok hw hc

/-- The normalize-and-retry arm of `inferSpineIOI`. -/
@[expose] def inferSpineIOWhnfI (r : InLean.CoreFnsI) (d : Nat) (ty : Expr) (acc : Array Expr)
    (a : Expr) (rest : List Expr) : InLean.CheckCM Expr := do
  let ty' ← instListRevM ty acc
  match EO.stripTop (← r.whnf d ty') with
  | .forallE _ _ body _ => inferSpineIOI r d body #[a] rest
  | _ => throw (.invalid "function expected")

theorem inferSpineIOI_cons (r : InLean.CoreFnsI) (d : Nat) (ty : Expr) (acc : Array Expr)
    (a : Expr) (rest : List Expr) :
    inferSpineIOI r d ty acc (a :: rest) =
      match EO.stripTop ty with
      | .forallE _ _ body _ => inferSpineIOI r d body (acc.push a) rest
      | _ => inferSpineIOWhnfI r d ty acc a rest := by
  rw [InLean.inferSpineIOI]; rfl

/-- What the io spine loop's spec states, for one argument list. -/
@[expose] def SpineIOSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (r : InLean.CoreFnsI) (d : Nat) (args : List Expr) : Prop :=
  ∀ {ty : Expr} {acc : Array Expr} {s₀ : InLean.CState},
    CSOKI mode eager env s₀ → OkS s₀ ty = true → OkSL s₀ acc.toList = true →
    AllClosed (TrSL s₀ acc.toList) = true → OkSL s₀ args = true →
    AllClosed (TrSL s₀ args) = true → AllWS d (TrSL s₀ args) →
    ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse) →
    ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ inferSpineIOI (CoreFnsI.ioView r) d ty acc args
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpineIO (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrSL s₀ args)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄

theorem SpineIOSpecI.triple {r : InLean.CoreFnsI} {d : Nat} {args : List Expr}
    (h : SpineIOSpecI mode eager env r d args) {ty : Expr} {acc : Array Expr} {s₀ : InLean.CState}
    (hs : CSOKI mode eager env s₀) (hty : OkS s₀ ty = true) (hacc : OkSL s₀ acc.toList = true)
    (hcacc : AllClosed (TrSL s₀ acc.toList) = true) (hargs : OkSL s₀ args = true)
    (hcargs : AllClosed (TrSL s₀ args) = true) (hwargs : AllWS d (TrSL s₀ args))
    (hw : ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse))
    (hc : ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferSpineIOI (CoreFnsI.ioView r) d ty acc args
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpineIO (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrSL s₀ args)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ :=
  h hs hty hacc hcacc hargs hcargs hwargs hw hc

theorem inferSpineIOWhnfI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat}
    {rest : List Expr} (ihr : SpineIOSpecI mode eager env r d rest) {ty : Expr} {acc : Array Expr}
    {a : Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hty : OkS s₀ ty = true)
    (hacc : OkSL s₀ acc.toList = true)
    (hcacc : AllClosed (TrSL s₀ acc.toList) = true) (ha : OkS s₀ a = true)
    (hca : (TrS s₀ a).looseBVarsBounded 0 = true) (hwa : ConLeche.Expr.WScoped d (TrS s₀ a))
    (hrest : OkSL s₀ rest = true) (hcrest : AllClosed (TrSL s₀ rest) = true)
    (hwrest : AllWS d (TrSL s₀ rest))
    (hw : ConLeche.Expr.WScoped d ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse))
    (hc : ((TrS s₀ ty).instantiateList (TrSL s₀ acc.toList).reverse).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ inferSpineIOWhnfI (CoreFnsI.ioView r) d ty acc a rest
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (ConLeche.inferSpineIOWhnf (ConLeche.fueledFns mode eager env) d (TrS s₀ ty)
        (TrSL s₀ acc.toList).reverse (TrS s₀ a) (TrSL s₀ rest)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.inferSpineIOWhnf] =>
    vcgen [inferSpineIOWhnfI, instListRevM_specI hs, ih.ioWhnf, ihr.triple] <;> finish

/-- The io-grade spine loop simulates its pure mirror. -/
theorem inferSpineIOI_spec {r : InLean.CoreFnsI} (ih : KnotSpecI mode eager env r) {d : Nat} :
    ∀ args : List Expr, SpineIOSpecI mode eager env r d args := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferSpineIO.eq_1] =>
      vcgen [InLean.inferSpineIOI, instListRevM_specI hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ hs _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.inferSpineIO_pi, ConLeche.inferSpineIO_ne_pi,
        ConLeche.inferSpineIOPi] =>
      vcgen [inferSpineIOI_cons, ihr.triple, inferSpineIOWhnfI_spec ih ihr hs] <;> finish

end InLeanProof
