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

/-- The ι target of a stuck head through the views. -/
theorem iotaTargetF_TrS (hrec : EnvRecI fe env) {s : InLean.CState} {h : Expr}
    (hh : InLean.isStuckHeadC h = true) (hok : OkS s h = true) :
    InLean.iotaTargetF fe h = ConLeche.Cached.iotaTargetF (ConLeche.mkFEnv env) (TrS s h) := by
  cases h with
  | const c us =>
    rw [TrS_const]
    unfold InLean.iotaTargetF ConLeche.Cached.iotaTargetF
    dsimp only
    rw [recArity_of_recAt, ConLeche.mkFEnv_find?]
    cases hra : fe.recAt? c with
    | none =>
      simp only [Option.map_none]
      split
      · rename_i cv mI rP isK rules hf; exact absurd hf (hrec.recNone c hra cv mI rP isK rules)
      · rfl
    | some p =>
      obtain ⟨rv, q⟩ := p
      obtain ⟨ccv, crules, hcv, hfc, -⟩ := hrec.recv c rv q hra
      simp only [Option.map_some, hfc, hcv.2.1, List.length_map]
  | fvar id => rw [TrS_fvar hok]; rfl
  | sort | forallE | lit => rfl
  | _ => simp [InLean.isStuckHeadC] at hh

/-- **The stuck arm simulates the mirror's application step**
(`whnfStuckC_spec`'s twin): the head is its own head normal form, and the
spine loop at it is the stuck arm's reading (`whnfAppW_stuck`): the ι step at
the target prefix of the argument array, else the input. -/
theorem whnfStuckI_specI_of {eager : Bool} {lv : Nat} (hiota : IotaRecSpecI eager env fe lv)
    (hrec : EnvRecI fe env) : WhnfStuckSpecI eager env fe lv := by
  intro c d i s₀ hs hok hw hc hh
  refine tripleI_iff_run.2 fun w s' hr => ?_
  have hokh : OkS s₀ (Expr.getAppFnT i) = true := OkS_getAppFnT s₀ hok
  have hhT : ConLeche.Cached.isStuckHeadC (TrS s₀ i).getAppFn = true := by
    rw [← TrS_getAppFnT]; exact isStuckHeadC_TrS hh hokh
  have hfixed : Expr.getAppFnT (Expr.getAppFnT i) = Expr.getAppFnT i := getAppFnT_getAppFnT i
  have hokA : OkSL s₀ (appArgs i) = true := OkSL_appArgs s₀ hok
  have hwA : AllWS d (TrSL s₀ (appArgs i)) := by rw [TrSL_appArgs]; exact allWS_getAppArgs hw
  have hcA : AllClosed (TrSL s₀ (appArgs i)) = true := by
    rw [TrSL_appArgs]; exact allClosed_getAppArgs hc
  have hTi : ConLeche.Expr.mkAppN (TrS s₀ i).getAppFn (TrS s₀ i).getAppArgs = TrS s₀ i :=
    ConLeche.Expr.mkAppN_getApp _
  have htarget := iotaTargetF_TrS hrec hh hokh
  rw [TrS_getAppFnT] at htarget
  rw [Runs.bind_eq _ (Runs.whnfCore_stuckHead (eager := eager) (env := env) (c := c) (d := d) hhT),
    whnfAppW_stuck hhT, ← htarget]
  rw [InLean.whnfStuckI.eq_def] at hr
  cases htk : InLean.iotaTargetF fe (Expr.getAppFnT i) with
  | none =>
    rw [htk] at hr
    obtain ⟨rfl, rfl⟩ := pure_run hr
    refine ⟨hs, TabLe.refl _, hok, ?_, ?_, ?_⟩
    · rw [TrStep_done, hTi]; exact Runs.pure _
    · rw [TrStep_done]; exact hw
    · rw [TrStep_done]; exact hc
  | some k =>
    rw [htk] at hr
    dsimp only at hr ⊢
    have hlen : InLean.iotaNumArgs i 0 = (TrS s₀ i).getAppArgs.length := by
      rw [iotaNumArgs_length, ← TrSL_appArgs, TrSL_length]
    by_cases hkn : k ≤ InLean.iotaNumArgs i 0
    · rw [ite_eq_left hkn] at hr
      rw [ite_eq_left (by rw [← hlen]; exact hkn)]
      obtain ⟨o, s₁, h1, hr⟩ := bind_run hr
      have hsz : k ≤ (InLean.getAppArgsArr i).size := by
        rw [getAppArgsArr_size, ← iotaNumArgs_length]; exact hkn
      obtain ⟨hs₁, ht₁, hoko, hruno, hwo, hco⟩ := tripleI_iff_run.1
        (hiota hs hfixed hsz hokh (by rw [getAppArgsArr_toList]; exact hokA)
          (by rw [getAppArgsArr_toList]; exact hwA) (by rw [getAppArgsArr_toList]; exact hcA))
        o s₁ h1
      rw [getAppArgsArr_toList, TrSL_take, TrSL_appArgs, TrS_getAppFnT] at hruno
      rw [Runs.bind_eq _ hruno]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pure_run hr
        refine ⟨hs₁, ht₁, okS_of_tabLe ht₁ hok, ?_, ?_, ?_⟩
        · rw [TrO_none, whnfStuckTail_none, TrStep_done, TrS_of_tabLe ht₁ hok, hTi]
          exact Runs.pure _
        · rw [TrStep_done, TrS_of_tabLe ht₁ hok]; exact hw
        · rw [TrStep_done, TrS_of_tabLe ht₁ hok]; exact hc
      | some e'' =>
        rw [TrO_some, whnfStuckTail_some]
        unfold InLean.pollC at hr
        have hA : OkSL s₁ (appArgs i) = true := okSL_of_tabLe ht₁ hokA
        have hTA : TrSL s₁ (appArgs i) = TrSL s₀ (appArgs i) := TrSL_of_tabLe ht₁ hokA
        have hok'' : OkS s₁ e'' = true := by rw [OkO_some] at hoko; exact hoko
        have hpost : CSOKI .verified eager env s₁ ∧ TabLe s₀ s₁ ∧
            OkStep s₁ (.cont (InLean.mkAppRange e'' (InLean.getAppArgsArr i) k
              (InLean.getAppArgsArr i).size)) = true ∧
            Runs (pure (ConLeche.WhnfStep.cont
              (ConLeche.Expr.mkAppN (TrS s₁ e'') ((TrS s₀ i).getAppArgs.drop k))) :
                ConLeche.FueledM ConLeche.WhnfStep)
              (TrStep s₁ (.cont (InLean.mkAppRange e'' (InLean.getAppArgsArr i) k
                (InLean.getAppArgsArr i).size))) ∧
            StepWS d (TrStep s₁ (.cont (InLean.mkAppRange e'' (InLean.getAppArgsArr i) k
              (InLean.getAppArgsArr i).size))) ∧
            StepClosed (TrStep s₁ (.cont (InLean.mkAppRange e'' (InLean.getAppArgsArr i) k
              (InLean.getAppArgsArr i).size))) = true := by
          rw [mkAppRange_rest, getAppArgsArr_toList, OkStep_cont, TrStep_cont, TrS_mkAppN,
            OkS_mkAppN, hok'', OkSL_drop s₁ hA, TrSL_drop, hTA, TrSL_appArgs]
          rw [TrO_some, OptWS] at hwo
          rw [TrO_some, OptClosed_some] at hco
          refine ⟨hs₁, ht₁, rfl, Runs.pure _, ?_, ?_⟩
          · exact wscoped_mkAppN hwo ((allWS_getAppArgs hw).drop k)
          · exact lbb_mkAppN_closed hco (AllClosed_drop (allClosed_getAppArgs hc) k)
        cases hp : fe.limits.poll with
        | none =>
          rw [hp] at hr
          obtain ⟨rfl, rfl⟩ := pure_run hr
          exact hpost
        | some p =>
          rw [hp] at hr
          dsimp only at hr
          cases hpe : p (.unfold (InLean.headConstName (Expr.getAppFnT i))) with
          | none =>
            rw [hpe] at hr
            obtain ⟨rfl, rfl⟩ := pure_run hr
            exact hpost
          | some l =>
            rw [hpe] at hr
            simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at hr
    · rw [ite_eq_right hkn] at hr
      rw [ite_eq_right (by rw [← hlen]; exact hkn)]
      obtain ⟨rfl, rfl⟩ := pure_run hr
      refine ⟨hs, TabLe.refl _, hok, ?_, ?_, ?_⟩
      · rw [TrStep_done, hTi]; exact Runs.pure _
      · rw [TrStep_done]; exact hw
      · rw [TrStep_done]; exact hc

/-- **The five bodies simulate** at level `f`, from the knot's
simulation there. -/
theorem bodiesI_of (h : EnvBodiesI fe env) {eager : Bool} {f : Nat} (ih : SSimI eager env fe f) :
    BodiesI eager env fe f := by
  have hpg : ProjGuardSpecI eager env fe f :=
    projGuardSpecI_of ih h.wf h.rel h.view
  have hpi : ProofIrrelSpecI eager env fe f :=
    fun hs ha hb hwa hwb hca hcb => proofIrrelI_spec ih hs ha hb hwa hwb hca hcb
  have happ : WhnfAppSpecI eager env fe f := whnfAppI_specI_of ih hpi h.wf h.view h.recs h.rel h.dom
  have hstuck : WhnfStuckSpecI eager env fe f :=
    whnfStuckI_specI_of (iotaRecI_specI ih hpi h.wf h.view h.recs h.rel h.dom) h.recs
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
    { whnfCore := fun c => whnfCoreBodyI_specI ih happ hstuck hproj h.wf c
      whnf := whnfBodyI_specI ih h.wf h.rel h.dom h.defn
      infer := inferBodyI_spec ih harg hpg h.wf h.rel h.dom h.proj
      inferIO := inferBodyIOI_spec ih hpg h.wf h.rel h.dom h.proj
      defeq := defeqBodyI_spec ih h.defeq h.wf hlist hunf hspine hnat hproj }

/-- **The knot simulates at every fuel**, given the environment hypotheses. -/
theorem ssimI_of_env (h : EnvBodiesI fe env) {eager : Bool} (f : Nat) : SSimI eager env fe f :=
  ssimI h.wf (fun _ _ ih => bodiesI_of h ih) f

end InLeanProof
