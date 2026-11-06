module

public import InLeanProof.WalksIota
import ConLeche.Verify.Cached.DiscC4

/-!
# InLean's body walks, part 3: the head-normalization loops (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC4.lean`'s whnf half: the reduction loop and
its body (`whnfLoopI`, `whnfBodyI`), the peel loop (`betaPeelI`), and the
head-normalization loop and body (`whnfCoreLoopI`, `whnfCoreBodyI`, over the
named step specs `WhnfAppSpecI`/`ReduceProjSpecI` of `KnotI.lean`), each by
its cached twin's `sym … => vcgen … <;> finish` script.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Vocabulary -/

theorem whnfLoopFuel_eq : InLean.whnfLoopFuel = ConLeche.whnfLoopFuel := by
  with_unfolding_all rfl

theorem whnfCoreLoopFuel_eq : InLean.whnfCoreLoopFuel = ConLeche.whnfCoreLoopFuel := by
  with_unfolding_all rfl

/-- A definition's unfolding of a closed term is closed (`EnvWF`'s). -/
theorem lbb_unfoldDefinition (henv : ConLeche.EnvWF env) {e e₂ : ConLeche.Expr}
    (h : ConLeche.unfoldDefinition env e = some e₂) (hb : e.looseBVarsBounded 0 = true) :
    e₂.looseBVarsBounded 0 = true :=
  ConLeche.unfoldDefinition_looseBVars henv h hb

/-! ## The reduction loop -/

section WhnfLoop

variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

/-- **The reduction loop** (`whnfLoopC_spec`'s twin), by induction on the
shared step budget. -/
theorem whnfLoopI_specI (ih : KnotSpecI mode eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hdom : EnvDomI fe env) (hdef : EnvDefnI fe env) {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : InLean.CState}, CSOKI mode eager env s₀ → OkS s₀ i = true →
      ConLeche.Expr.WScoped d (TrS s₀ i) → (TrS s₀ i).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.whnfLoopI r fe d n i
      ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs (ConLeche.whnfLoop (ConLeche.fueledFns mode eager env) env d n (TrS s₀ i)) (TrS s' v) ∧
        ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind] => vcgen [InLean.whnfLoopI] <;> finish
  | succ n ihn =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind, ConLeche.whnfLoop, ConLeche.whnfStep,
        ConLeche.unfoldDefinition_WScoped henv, lbb_unfoldDefinition henv] =>
      vcgen [InLean.whnfLoopI, InLean.whnfStepI, ih.whnfCore, reduceNatI_specI ih hdom,
        unfoldDefinitionI_specI (mode := mode) (eager := eager) hfe hdef, ihn] <;> finish

/-- **The reduction body** (`whnfBodyC_spec`'s twin). -/
theorem whnfBodyI_specI (ih : KnotSpecI mode eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) (hdom : EnvDomI fe env) (hdef : EnvDefnI fe env) :
    BodySpecI mode eager env (InLean.whnfBodyI r fe)
      (ConLeche.whnfBody (ConLeche.fueledFns mode eager env) env) := by
  intro s₀ d i hs hok hw hc
  sym only [conleche_grind, ConLeche.whnfBody, whnfLoopFuel_eq] =>
    vcgen [InLean.whnfBodyI, whnfLoopI_specI ih henv hfe hdom hdef] <;> finish

end WhnfLoop

/-! ## The peel loop -/

section Peel

variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

attribute [conleche_grind =] TrS_mkAppN OkS_mkAppN

/-- An application of a closed head to closed arguments is closed. -/
theorem lbb_mkAppN_closed {f : ConLeche.Expr} {xs : List ConLeche.Expr}
    (hf : f.looseBVarsBounded 0 = true) (hxs : AllClosed xs = true) :
    (ConLeche.Expr.mkAppN f xs).looseBVarsBounded 0 = true :=
  ConLeche.looseBVarsBounded_mkAppN hf (by
    simp only [AllClosed, List.all_eq_true] at hxs; exact hxs)
grind_pattern [conleche_grind] lbb_mkAppN_closed => f.looseBVarsBounded 0, ConLeche.Expr.mkAppN f xs

/-- The peel step keeps a closed instantiated lambda closed at a closed value. -/
theorem lbb_lamPeel {dom body a : ConLeche.Expr} {acc : List ConLeche.Expr}
    (h : ((ConLeche.Expr.lam dom body).instantiateList acc).looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) :
    (body.instantiateList (a :: acc)).looseBVarsBounded 0 = true := by
  rw [ConLeche.Expr.instantiateList, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
  rw [ConLeche.Expr.instantiateList_cons]
  exact lbb_instantiate1 ha h.2
grind_pattern [conleche_grind] lbb_lamPeel =>
  ((ConLeche.Expr.lam dom body).instantiateList acc).looseBVarsBounded 0,
  body.instantiateList (a :: acc)

/-- The pure peel loop at a translated head, stepped in InLean's shape (its
match on InLean's `stripTop`). -/
theorem betaPeelW_TrS_cons {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (s : InLean.CState) {t : Expr} (ht : OkS s t = true)
    (acc : List ConLeche.Expr) (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.betaPeelW mode r env d (TrS s t) acc (a :: rest) =
      match EO.stripTop t with
      | .lam _ _ body _ => ConLeche.betaPeelW mode r env d (TrS s body) (a :: acc) rest
      | _ => pure (.cont (ConLeche.Expr.mkAppN ((TrS s t).instantiateList acc) (a :: rest))) := by
  rw [← OkS_stripTop s t] at ht
  conv => lhs; rw [← TrS_stripTop s t]
  conv => rhs; rw [← TrS_stripTop s t]
  generalize hx : EO.stripTop t = x at ht
  cases x with
  | lam n dom body bi => rw [TrS_lam, ConLeche.betaPeelW.eq_2]
  | fvar id => rw [TrS_fvar ht, ConLeche.betaPeelW.eq_def]
  | mvar _ => rw [OkS_mvar] at ht; cases ht
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rw [ConLeche.betaPeelW.eq_def]; rfl

/-- **The peel loop** (`betaPeelC_spec`'s twin). -/
theorem betaPeelI_specI {d : Nat} :
    ∀ {args : List Expr} {t : Expr} {acc : List Expr} {s₀ : InLean.CState},
      CSOKI mode eager env s₀ → OkS s₀ t = true → OkSL s₀ acc = true →
      AllClosed (TrSL s₀ acc) = true →
      ConLeche.Expr.WScoped d ((TrS s₀ t).instantiateList (TrSL s₀ acc)) →
      ((TrS s₀ t).instantiateList (TrSL s₀ acc)).looseBVarsBounded 0 = true →
      OkSL s₀ args = true → AllWS d (TrSL s₀ args) → AllClosed (TrSL s₀ args) = true →
      ⦃fun s => s = s₀⦄ InLean.betaPeelI r fe d t acc args
      ⦃fun w s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkStep s' w = true ∧
          Runs (ConLeche.betaPeelW mode (ConLeche.fueledFns mode eager env) env d (TrS s₀ t)
            (TrSL s₀ acc) (TrSL s₀ args)) (TrStep s' w) ∧
          StepWS d (TrStep s' w) ∧ StepClosed (TrStep s' w) = true; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.betaPeelW.eq_1] =>
      vcgen [InLean.betaPeelI, instListM_specI hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ hs ht _ _ _ _ _ _ _
    sym only [conleche_grind, betaPeelW_TrS_cons _ _ _ ht] =>
      vcgen [InLean.betaPeelI.eq_def, InLean.mkAppNM, instListM_specI hs, ihr] <;> finish

end Peel

/-! ## The head-normalization loop -/

section CoreLoop

variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

/-- **The head-normalization loop** (`whnfCoreLoopC_spec`'s twin), over the
step's callee specs. -/
theorem whnfCoreLoopI_specI (ih : KnotSpecI .verified eager env r)
    (happ : WhnfAppSpecI eager env r fe) (hproj : ReduceProjSpecI eager env r fe) {c : Bool}
    {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : InLean.CState}, CSOKI .verified eager env s₀ → OkS s₀ i = true →
      ConLeche.Expr.WScoped d (TrS s₀ i) → (TrS s₀ i).looseBVarsBounded 0 = true →
      ⦃fun s => s = s₀⦄ InLean.whnfCoreLoopI .verified r fe c d n i
      ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
        Runs (ConLeche.whnfCoreLoopM .verified (ConLeche.fueledFns .verified eager env) env c d n
          (TrS s₀ i)) (TrS s' v) ∧
        ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind] => vcgen [InLean.whnfCoreLoopI] <;> finish
  | succ n ihn =>
    intro i s₀ hs hok hw hc
    sym only [conleche_grind, ConLeche.whnfCoreLoopM] =>
      vcgen [InLean.whnfCoreLoopI, whnfCoreStepI_spec ih happ hproj, ihn] <;> finish

/-- **The head-normalization body** (`whnfCoreBodyC_spec`'s twin). -/
theorem whnfCoreBodyI_specI (ih : KnotSpecI .verified eager env r)
    (happ : WhnfAppSpecI eager env r fe) (hproj : ReduceProjSpecI eager env r fe) (c : Bool) :
    BodySpecI .verified eager env (InLean.whnfCoreBodyI .verified r fe c)
      (ConLeche.whnfCoreBody .verified (ConLeche.fueledFns .verified eager env) env c) := by
  intro s₀ d i hs hok hw hc
  sym only [conleche_grind, whnfCoreLoopFuel_eq] =>
    vcgen [InLean.whnfCoreBodyI, whnfCoreLoopI_specI ih happ hproj] <;> finish

end CoreLoop

end InLeanProof
