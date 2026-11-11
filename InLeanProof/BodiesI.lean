module

public import InLeanProof.KnotAssembly
public import InLeanProof.ProjGuardI
public import InLeanProof.WalksWhnfLoop
public import InLeanProof.WalksIotaRec

/-!
# The knot's five bodies, assembled (task #451, lane P2-close)

`BodiesI` (`KnotAssembly.lean`) from the three body lanes' theorems, so the
knot simulates at every fuel (`ssimI_of_env`) given only what the bodies
read of the environment (`EnvBodiesI`, O4, P3's); the projection guard's
spec comes from the same (`projGuardSpecI_of`).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

variable {env : ConLeche.Env} {fe : InLean.FEnv}

/-- **What the knot's bodies read of the environment** (O4, P3's): the
hypotheses the walks name, together. -/
structure EnvBodiesI (fe : InLean.FEnv) (env : ConLeche.Env) : Prop where
  wf : ConLeche.EnvWF env
  rel : EnvRelI fe env
  dom : EnvDomI fe env
  defn : EnvDefnI fe env
  view : EnvViewI fe env
  recs : EnvRecI fe env
  defeq : DefeqEnvI fe env
  proj : EnvProjI fe env

/-- A stuck head is an easy case of `whnfCore`. -/
theorem whnfCoreEasy_of_stuck {h : Expr} (hh : InLean.isStuckHeadC h = true) :
    InLean.whnfCoreEasy h = true := by
  cases h <;> first | rfl | simp [InLean.isStuckHeadC] at hh

/-- **The stuck arm simulates the mirror's application step**
(`whnfStuckC_spec`'s twin): the head is its own head normal form, and the
stuck arm is the spine loop on the rebuilt spine (`whnfStuckI_mkAppN`), its
finished answer the input (`whnfStuckI_relink`, `whnfStuckI_done`). -/
theorem whnfStuckI_specI_of {eager : Bool} {lv : Nat} (happ : WhnfAppSpecI eager env fe lv) :
    WhnfStuckSpecI eager env fe lv := by
  intro c d i s₀ hs hok hw hc hh
  rw [whnfStuckI_relink hh i, whnfStuckI_mkAppN hh]
  refine tripleI_iff_run.2 fun w s' hr => ?_
  obtain ⟨w₀, s₁, h1, hr⟩ := bind_run hr
  obtain ⟨rfl, rfl⟩ := pure_run hr
  have hokh : OkS s₀ (Expr.getAppFnT i) = true := OkS_getAppFnT s₀ hok
  have hokA : OkSL s₀ (appArgs i) = true := OkSL_appArgs s₀ hok
  have hwh : ConLeche.Expr.WScoped d (TrS s₀ (Expr.getAppFnT i)) := by
    rw [TrS_getAppFnT]; exact wscoped_getAppFn hw
  have hwA : AllWS d (TrSL s₀ (appArgs i)) := by rw [TrSL_appArgs]; exact allWS_getAppArgs hw
  have hch : (TrS s₀ (Expr.getAppFnT i)).looseBVarsBounded 0 = true := by
    rw [TrS_getAppFnT]; exact lbb_getAppFn hc
  have hcA : AllClosed (TrSL s₀ (appArgs i)) = true := by
    rw [TrSL_appArgs]; exact allClosed_getAppArgs hc
  obtain ⟨hs', hle, hokw, hrun, hws, hcl⟩ :=
    tripleI_iff_run.1 (happ hs hokh hokA hwh hwA hch hcA) w₀ s₁ h1
  have hspec : ∀ st, Runs (ConLeche.whnfAppW .verified (ConLeche.fueledFns .verified eager env) env d
        (TrS s₀ (Expr.getAppFnT i)) (TrSL s₀ (appArgs i))) st →
      Runs ((ConLeche.fueledFns .verified eager env).whnfCore c d (TrS s₀ i).getAppFn >>= fun v =>
        ConLeche.whnfAppW .verified (ConLeche.fueledFns .verified eager env) env d v
          (TrS s₀ i).getAppArgs) st := by
    intro st h
    rw [← TrS_getAppFnT, ← TrSL_appArgs]
    exact Runs.bind (Runs.whnfCore_easyI (whnfCoreEasy_of_stuck hh) hokh) h
  cases w₀ with
  | cont x => exact ⟨hs', hle, hokw, hspec _ hrun, hws, hcl⟩
  | done x =>
    rw [← whnfStuckI_mkAppN hh] at h1
    obtain rfl := whnfStuckI_done h1
    have hTi : TrS s₁ (mkAppN (Expr.getAppFnT i) (appArgs i).toArray) = TrS s₁ i := by
      rw [TrS_mkAppN, TrS_getAppFnT, TrSL_appArgs, ConLeche.Expr.mkAppN_getApp]
    have hT : TrS s₁ i = TrS s₀ i := TrS_of_tabLe hle hok
    rw [TrStep_done, hTi] at hrun hws hcl
    refine ⟨hs', hle, okS_of_tabLe hle hok, ?_, ?_, ?_⟩
    · rw [doneAs, TrStep_done]; exact hspec _ hrun
    · rw [doneAs, TrStep_done]; exact hws
    · rw [doneAs, TrStep_done]; exact hcl

/-- **The five bodies simulate** at level `f`, from the knot's
simulation there. -/
theorem bodiesI_of (h : EnvBodiesI fe env) {eager : Bool} {f : Nat} (ih : SSimI eager env fe f) :
    BodiesI eager env fe f := by
  have hpg : ProjGuardSpecI eager env fe f :=
    projGuardSpecI_of ih h.wf h.rel h.view
  have hpi : ProofIrrelSpecI eager env fe f :=
    fun hs ha hb hwa hwb hca hcb => proofIrrelI_spec ih hs ha hb hwa hwb hca hcb
  have happ : WhnfAppSpecI eager env fe f := whnfAppI_specI_of ih hpi h.wf h.view h.recs h.rel h.dom
  have hstuck : WhnfStuckSpecI eager env fe f := whnfStuckI_specI_of happ
  have hproj : ReduceProjSpecI eager env fe f :=
    reduceProjCoreI_specI ih h.dom h.view
  have hlist : DefEqListSpecI .verified .verified eager env fe f :=
    fun hs ha hb hwa hwb hca hcb => defEqListI_spec ih hs ha hb hwa hwb hca hcb
  have hspine : DefeqSpineSpecI .verified .verified eager env fe f :=
    fun hs ha hb hwa hwb hca hcb => defeqSpineI_specI ih hs ha hb hwa hwb hca hcb
  have hnat : ReduceNatSpecI .verified .verified eager env fe f :=
    fun hs hok hw hc => reduceNatI_specI ih h.dom hs hok hw hc
  have hunf : UnfoldDefSpecI .verified eager env fe := by
    intro e s₀ hs he hc
    refine tripleI_iff_run.2 fun o s' hr => ?_
    obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 (unfoldDefinitionI_specI h.rel h.defn hs he) o s' hr
    refine ⟨h1, h2, h3, h4, ?_⟩
    cases ho : TrO s' o with
    | none => rfl
    | some e₂ =>
      rw [ho] at h4
      exact lbb_unfoldDefinition h.wf h4.symm hc
  have harg : DefeqArgSpecI .verified .verified eager env fe f :=
    fun hs _ hta hty hwta hwty hcta hcty => defeqArgI_spec ih hs hta hty hwta hwty hcta hcty
  exact
    { whnfCore := fun c => whnfCoreBodyI_specI ih happ hstuck hproj c
      whnf := whnfBodyI_specI ih h.wf h.rel h.dom h.defn
      infer := inferBodyI_spec ih harg hpg h.wf h.rel h.dom h.proj
      inferIO := inferBodyIOI_spec ih hpg h.wf h.rel h.dom h.proj
      defeq := defeqBodyI_spec ih h.defeq h.wf hlist hunf hspine hnat hproj }

/-- **The knot simulates at every fuel**, given the environment hypotheses. -/
theorem ssimI_of_env (h : EnvBodiesI fe env) {eager : Bool} (f : Nat) : SSimI eager env fe f :=
  ssimI h.wf (fun _ _ ih => bodiesI_of h ih) f

end InLeanProof
