module

public import InLeanProof.GrindI
public import ConLeche.Verify.BetaSpine
import ConLeche.Verify.Cached.DiscC4

/-!
# The knot's hypothesis in triple form, and the body template (task #451, lane P2-0)

`KnotSpecI mode mi eager env fe lv`: every entry point of InLean's knot at
mode `mi` and level `lv` (`whnfCoreI`, `whnfI`, `inferI` at both grades, `defeqI`,
`defeqEI`) simulates the pure fueled entry at the translation — the triple
forms of `Verify/Cached`'s `SSimC` fields (`SSimC.whnf_spec`, …), with
InLean's value read through `TrS` at the final state.  `SSimI` is it at
level `f`; the bodies (`InLeanProof/Walks*.lean`) take `KnotSpecI` of the
level they call, as the cached walks take `SSimC`.

**The post** (every entry and every walk): the invariant `CSOKI` at the
final state, the table grown (`TabLe`), the answer has a reading (`OkS`),
the pure entry at the input's translation answers the answer's
translation (`Runs`), and that translation is scoped at the depth and
closed.  Inputs are read at the initial state (`TrS s₀ i`); `TrS_of_tabLe`
moves them along.

**Closedness is InLean's own side condition** (con-leche's `SSimC` has no
such one): InLean's instantiation is Lean's, which lifts the loose variables
of a substituted value under binders, and con-leche's `instantiateList` does
not, so the two agree on closed values only (`toExpr_instantiate1`).  The
checker substitutes closed values only; the knot carries it.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {mi : InLean.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-- The pre of a unary slot: the invariant, a reading, scoped and closed. -/
@[expose] def PreI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env) (s : InLean.CState)
    (d : Nat) (i : Expr) : Prop :=
  CSOKI mode eager env s ∧ OkS s i = true ∧ ConLeche.Expr.WScoped d (TrS s i) ∧
    (TrS s i).looseBVarsBounded 0 = true

/-- **The knot's hypothesis in triple form**: every entry point at level `lv`
simulates the pure fueled slot at the translation. -/
structure KnotSpecI (mode : ConLeche.CheckMode) (mi : InLean.CheckMode) (eager : Bool)
    (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) : Prop where
  whnfCore : ∀ {c : Bool} {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.whnfCoreI mi fe eager lv c d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).whnfCore c d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄
  whnf : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.whnfI mi fe eager lv d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).whnf d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄
  infer : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.inferI mi fe eager lv false d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).infer d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄
  inferIO : ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.inferI mi fe eager lv true d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs ((ConLeche.fueledFns mode eager env).inferIO d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄
  defeq : ∀ {s₀ : InLean.CState} {d : Nat} {i j : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → OkS s₀ j = true →
    ConLeche.Expr.WScoped d (TrS s₀ i) → ConLeche.Expr.WScoped d (TrS s₀ j) →
    (TrS s₀ i).looseBVarsBounded 0 = true → (TrS s₀ j).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.defeqI mi fe eager lv d i j
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs ((ConLeche.fueledFns mode eager env).defeq d (TrS s₀ i) (TrS s₀ j)) v; ⊤⦄
  defeqE : ∀ {s₀ : InLean.CState} {d : Nat} {i j : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → OkS s₀ j = true →
    ConLeche.Expr.WScoped d (TrS s₀ i) → ConLeche.Expr.WScoped d (TrS s₀ j) →
    (TrS s₀ i).looseBVarsBounded 0 = true → (TrS s₀ j).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.defeqEI mi fe eager lv d i j
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧
      Runs ((ConLeche.fueledFns mode eager env).defeqE d (TrS s₀ i) (TrS s₀ j)) v; ⊤⦄

/-! ## The template: `ensureSortI` (the script of `ensureSortC_spec`) -/

/-- **`ensureSortI` simulates the pure `ensureSort`**, by the cached twin's
script: `sym only [conleche_grind, ensureSort] => vcgen [ensureSortI, ih.whnf_spec] <;> finish`,
with the knot's `whnf` triple at `ih.whnf hs`. -/
theorem ensureSortI_spec {fe : InLean.FEnv} {lv : Nat} (ih : KnotSpecI mode mi eager env fe lv) {d : Nat}
    {i : Expr} {s₀ : InLean.CState} (hs : CSOKI mode eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ ensureSortI mi fe eager lv d i
    ⦃fun u s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ okLv u = true ∧
      Runs (ConLeche.ensureSort (ConLeche.fueledFns mode eager env) env d (TrS s₀ i)) (trL u); ⊤⦄ := by
  sym only [conleche_grind, ConLeche.ensureSort] =>
    vcgen [InLean.ensureSortI.eq_def, ih.whnf hs hok hw hc] <;> finish

/-! ## The template: one head-normalization step (the script of `whnfCoreStepC_spec`)

Its two callees are P2-whnf's: their specs are named predicates here, the
statements that lane proves (`whnfAppC_spec`'s and `reduceProjCoreC_spec`'s
twins). -/

/-- `whnfAppI`'s spec (`whnfAppC_spec`'s twin), P2-whnf's to prove. -/
abbrev WhnfAppSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) :
    Prop :=
  ∀ {d : Nat} {v : Expr} {args : Array Expr} {i : Nat} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → OkS s₀ v = true → OkSL s₀ args.toList = true →
    ConLeche.Expr.WScoped d (TrS s₀ v) → AllWS d (TrSL s₀ args.toList) →
    (TrS s₀ v).looseBVarsBounded 0 = true → AllClosed (TrSL s₀ args.toList) = true →
    ⦃fun s => s = s₀⦄ whnfAppI .verified fe eager lv d v args i
    ⦃fun w s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkStep s' w = true ∧
      Runs (ConLeche.whnfAppW .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ v)
        (TrSL s₀ (args.toList.drop i))) (TrStep s' w) ∧
      StepWS d (TrStep s' w) ∧ StepClosed (TrStep s' w) = true; ⊤⦄

/-- `reduceProjCoreI`'s spec (`reduceProjCoreC_spec`'s twin), P2-whnf's to
prove. -/
abbrev ReduceProjSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) :
    Prop :=
  ∀ {d : Nat} {sn : Name} {i : Nat} {c : Expr} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → OkS s₀ c = true → ConLeche.Expr.WScoped d (TrS s₀ c) →
    (TrS s₀ c).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ reduceProjCoreI .verified fe eager lv d sn i c
    ⦃fun o s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.reduceProjCore .verified (ConLeche.fueledFns .verified eager env) env d
        (toName sn) i (TrS s₀ c)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄

/-- `whnfStuckI`'s spec (`whnfStuckC_spec`'s twin): a spine whose head is
its own head normal form simulates the mirror's application arm, the head's
`whnfCore` (the head itself) and the spine loop on the arguments. -/
abbrev WhnfStuckSpecI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (lv : Nat) :
    Prop :=
  ∀ {c : Bool} {d : Nat} {i : Expr} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true → isStuckHeadC i.getAppFnT = true →
    ⦃fun s => s = s₀⦄ whnfStuckI .verified fe eager lv d i.getAppFnT i
    ⦃fun w s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkStep s' w = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s₀ i).getAppFn >>= fun v =>
        ConLeche.whnfAppW .verified (ConLeche.fueledFns .verified eager env) env d v
          (TrS s₀ i).getAppArgs) (TrStep s' w) ∧
      StepWS d (TrStep s' w) ∧ StepClosed (TrStep s' w) = true; ⊤⦄

/-- **One head-normalization step simulates its pure mirror**: the script
of `whnfCoreStepC_spec`, verbatim but for the callees' names. -/
theorem whnfCoreStepI_spec {fe : InLean.FEnv} {lv : Nat}
    (ih : KnotSpecI .verified .verified eager env fe lv) (happ : WhnfAppSpecI eager env fe lv)
    (hstuck : WhnfStuckSpecI eager env fe lv)
    (hproj : ReduceProjSpecI eager env fe lv) {c : Bool} {d : Nat} {i : Expr}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ whnfCoreStepI .verified fe eager lv c d i.getAppFnT i
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkStep s' v = true ∧
      Runs (ConLeche.whnfCoreStepW .verified (ConLeche.fueledFns .verified eager env) env c d
        (TrS s₀ i)) (TrStep s' v) ∧
      StepWS d (TrStep s' v) ∧ StepClosed (TrStep s' v) = true; ⊤⦄ := by
  sym only [conleche_grind, ConLeche.whnfCoreStepW, getAppArgsArr_toList, List.drop_zero] =>
    vcgen [InLean.whnfCoreStepI.eq_def, ih.whnfCore, ih.whnf, hproj, happ, hstuck (c := c)] <;> finish

/-! ## The knot skeleton (`KnotC.lean`'s port)

`SSimI f`: the knot at level `f` meets `KnotSpecI`.  The base is proved
(`ssimI_zero`: every entry point throws).  The step, `ssimI_succ`, is P2's
assembly lane: from `SSimI f` and the bodies' specs at level `f`
(`BodySpecI`/`BodySpecBI`, one per slot, the three body lanes' results), the
memo wrappers (`memoEI_ok`/`memoBI_ok` in triple form, with the clauses'
insert lemmas) give `SSimI (f + 1)`; `withEagerMemos` swaps the eager
tower's memos in and out, its clause being `CSOKI.eager`. -/

/-- A unary body simulates its pure body (`BodySpec`'s twin). -/
@[expose] def BodySpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (body : Nat → Expr → InLean.CheckCM Expr)
    (spec : Nat → ConLeche.Expr → ConLeche.FueledM ConLeche.Expr) : Prop :=
  ∀ {s₀ : InLean.CState} {d : Nat} {i : Expr},
    CSOKI mode eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ body d i
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' v = true ∧
      Runs (spec d (TrS s₀ i)) (TrS s' v) ∧
      ConLeche.Expr.WScoped d (TrS s' v) ∧ (TrS s' v).looseBVarsBounded 0 = true; ⊤⦄

/-- A binary `Bool` body simulates its pure body (`BodySpecB`'s twin). -/
@[expose] def BodySpecBI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env)
    (body : Nat → Expr → Expr → InLean.CheckCM Bool)
    (spec : Nat → ConLeche.Expr → ConLeche.Expr → ConLeche.FueledM Bool) : Prop :=
  ∀ {s₀ : InLean.CState} {d : Nat} {a b : Expr},
    CSOKI mode eager env s₀ → OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ body d a b
    ⦃fun v s' => CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ Runs (spec d (TrS s₀ a) (TrS s₀ b)) v; ⊤⦄

/-- **The knot's simulation at level `f`** (`SSimC`'s twin, in triple form). -/
@[expose] def SSimI (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) (f : Nat) : Prop :=
  KnotSpecI .verified .verified eager env fe f

/-- A throwing program meets every partial-correctness triple. -/
theorem throw_triple {β : Type} {s₀ : InLean.CState} {Q : β → InLean.CState → Prop} (x : InLean.CheckError) :
    ⦃fun s => s = s₀⦄ (throw x : InLean.CheckCM β) ⦃fun v s' => Q v s'; ⊤⦄ := by
  sym only [conleche_grind] => vcgen <;> finish

/-- **The base**: at level `0` every entry point throws (`ssimC_zero`'s twin). -/
theorem ssimI_zero (eager : Bool) (env : ConLeche.Env) (fe : InLean.FEnv) : SSimI eager env fe 0 :=
  { whnfCore := fun _ _ _ _ => by rw [InLean.whnfCoreI.eq_def]; exact throw_triple _
    whnf := fun _ _ _ _ => by rw [InLean.whnfI.eq_def]; exact throw_triple _
    infer := fun _ _ _ _ => by rw [InLean.inferI.eq_def]; exact throw_triple _
    inferIO := fun _ _ _ _ => by rw [InLean.inferI.eq_def]; exact throw_triple _
    defeq := fun _ _ _ _ _ _ _ => by rw [InLean.defeqI.eq_def]; exact throw_triple _
    defeqE := fun _ _ _ _ _ _ _ => by rw [InLean.defeqEI.eq_def]; exact throw_triple _ }

end InLeanProof
