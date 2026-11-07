module

public import InLeanProof.KnotAssembly
public import InLeanProof.WalksInferBody
public import InLeanProof.WalksWhnfLoop
public import InLeanProof.WalksIotaRec

/-!
# The knot's five bodies, assembled (task #451, lane P2-close)

`BodiesI` (`KnotAssembly.lean`) from the three body lanes' theorems, so the
knot simulates at every fuel (`ssimI_of_env`) given only what the bodies
read of the environment (`EnvBodiesI`, O4, P3's) and the projection guard's
spec (`ProjGuardSpecI`, re-ported after task #492).
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

/-- **The five bodies simulate** at the knot of fuel `f`, from the knot's
simulation there. -/
theorem bodiesI_of (h : EnvBodiesI fe env) {eager : Bool} {f : Nat} (ih : SSimI eager env fe f)
    (hpg : ProjGuardSpecI eager env (coreKnotI .verified eager fe f) fe) :
    BodiesI eager env fe f := by
  have hpi : ProofIrrelSpecI eager env (coreKnotI .verified eager fe f) :=
    fun hs ha hb hwa hwb hca hcb => proofIrrelI_spec ih hs ha hb hwa hwb hca hcb
  have happ : WhnfAppSpecI eager env (coreKnotI .verified eager fe f) fe := whnfAppI_specI_of ih hpi h.wf h.view h.recs h.rel h.dom
  have hproj : ReduceProjSpecI eager env (coreKnotI .verified eager fe f) fe :=
    reduceProjCoreI_specI ih h.dom h.view
  have hlist : DefEqListSpecI .verified eager env (coreKnotI .verified eager fe f) :=
    fun hs ha hb hwa hwb hca hcb => defEqListI_spec ih hs ha hb hwa hwb hca hcb
  have hspine : DefeqSpineSpecI .verified eager env (coreKnotI .verified eager fe f) :=
    fun hs ha hb hwa hwb hca hcb => defeqSpineI_specI ih hs ha hb hwa hwb hca hcb
  have hnat : ReduceNatSpecI .verified eager env (coreKnotI .verified eager fe f) fe :=
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
  have harg : DefeqArgSpecI .verified eager env (coreKnotI .verified eager fe f) :=
    fun hs _ hta hty hwta hwty hcta hcty => defeqArgI_spec ih hs hta hty hwta hwty hcta hcty
  exact
    { whnfCore := fun c => whnfCoreBodyI_specI ih happ hproj c
      whnf := whnfBodyI_specI ih h.wf h.rel h.dom h.defn
      infer := inferBodyI_spec ih harg hpg h.wf h.rel h.dom h.proj
      inferIO := inferBodyIOI_spec ih hpg h.wf h.rel h.dom h.proj
      defeq := defeqBodyI_spec ih h.defeq h.wf hlist hunf hspine hnat hproj }

/-- **The knot simulates at every fuel**, given the environment hypotheses
and the projection guard's spec at every knot that simulates. -/
theorem ssimI_of_env (h : EnvBodiesI fe env)
    (hpg : ∀ b f, SSimI b env fe f → ProjGuardSpecI b env (coreKnotI .verified b fe f) fe)
    {eager : Bool} (f : Nat) : SSimI eager env fe f :=
  ssimI h.wf (fun b f ih => bodiesI_of h ih (hpg b f ih)) f

end InLeanProof
