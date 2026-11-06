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

theorem stripTop_of_TrS_lam {s : InLean.CState} {e : Expr} {a b : ConLeche.Expr}
    (h : TrS s e = .lam a b) :
    EO.stripTop e = .lam (binderNameOf (EO.stripTop e)) (binderDomOf (EO.stripTop e))
      (binderBodyOf (EO.stripTop e)) (binderInfoOf (EO.stripTop e)) := by
  induction e with
  | mdata _ x ih => exact ih h
  | lam => rfl
  | fvar id => exact absurd h ((trans_getD_ne_binder s id).1 a b)
  | _ => simp [TrS, trE] at h
grind_pattern [conleche_grind] stripTop_of_TrS_lam => TrS s e, ConLeche.Expr.lam a b

theorem stripTop_of_TrS_forallE {s : InLean.CState} {e : Expr} {a b : ConLeche.Expr}
    (h : TrS s e = .forallE a b) :
    EO.stripTop e = .forallE (binderNameOf (EO.stripTop e)) (binderDomOf (EO.stripTop e))
      (binderBodyOf (EO.stripTop e)) (binderInfoOf (EO.stripTop e)) := by
  induction e with
  | mdata _ x ih => exact ih h
  | forallE => rfl
  | fvar id => exact absurd h ((trans_getD_ne_binder s id).2 a b)
  | _ => simp [TrS, trE] at h
grind_pattern [conleche_grind] stripTop_of_TrS_forallE => TrS s e, ConLeche.Expr.forallE a b

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

end InLeanProof
