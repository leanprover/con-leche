module

public import InLeanProof.WalksIota
import ConLeche.Verify.Cached.DiscC4
/- `Lean.QuotKind`'s derived `BEq` is not exposed by `Lean.Declaration`; the
quotient eliminators' arity read compares kinds. -/
import all Lean.Declaration

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

/-- Opening a closed lambda at a closed value: the loop's first peel. -/
theorem lbb_lamOpen {dom body a : ConLeche.Expr}
    (h : (ConLeche.Expr.lam dom body).looseBVarsBounded 0 = true)
    (ha : a.looseBVarsBounded 0 = true) :
    (body.instantiateList [a]).looseBVarsBounded 0 = true :=
  lbb_lamPeel (acc := []) (by rw [ConLeche.Expr.instantiateList_nil]; exact h) ha
grind_pattern [conleche_grind] lbb_lamOpen =>
  (ConLeche.Expr.lam dom body).looseBVarsBounded 0, body.instantiateList [a]

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

/-! ## The argument loop -/

section AppLoop

variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

/-- **The ι step's spec** (`iotaRecC_spec`'s twin), this lane's to prove
(`WalksIota.lean`); the argument loop takes it as a named callee spec. -/
abbrev IotaRecSpecI (eager : Bool) (env : ConLeche.Env) (r : InLean.CoreFnsI) (fe : InLean.FEnv) :
    Prop :=
  ∀ {d : Nat} {i : Expr} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → OkS s₀ i = true → ConLeche.Expr.WScoped d (TrS s₀ i) →
    (TrS s₀ i).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.iotaRecI .verified r fe d i
    ⦃fun o s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (ConLeche.iotaRec .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ i))
        (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true; ⊤⦄

theorem iotaNumArgs_eq : ∀ (e : Expr) (n : Nat), InLean.iotaNumArgs e n = Expr.getAppNumArgsT e + n
  | .app f _, n => by rw [InLean.iotaNumArgs, iotaNumArgs_eq f, Expr.getAppNumArgsT]; omega
  | .mdata _ e, n => by rw [InLean.iotaNumArgs, iotaNumArgs_eq e, Expr.getAppNumArgsT]
  | .bvar _, _ | .fvar _, _ | .mvar _, _ | .sort _, _ | .const .., _ | .lam .., _
  | .forallE .., _ | .letE .., _ | .lit _, _ | .proj .., _ => by
    simp [InLean.iotaNumArgs, Expr.getAppNumArgsT]

/-- The arity read is the recursor view's. -/
theorem recArity_of_recAt (n : Name) :
    fe.recArity? n = (fe.recAt? n).map fun p => (majorIdxOf p.1, p.1.levelParams.length) := by
  unfold InLean.FEnv.recArity? InLean.FEnv.recAt?
  cases fe.find? n with
  | none => rfl
  | some ci =>
    cases ci with
    | recInfo rv => rfl
    | quotInfo q =>
      simp only [InLean.quotRecVal]
      cases hk : q.kind <;> simp [majorIdxOf] <;> decide
    | _ => rfl

/-- Where the arity pre-check fails, the ι step has nothing to do
(`iotaRecI_of_arityOk_false`'s twin). -/
theorem iotaRecI_of_arityOk_false {d : Nat} {e : Expr} (h : InLean.iotaArityOk fe e = false) :
    InLean.iotaRecI .verified r fe d e = pure none := by
  unfold InLean.iotaArityOk at h
  unfold InLean.iotaRecI
  cases hg : Expr.getAppFnT e with
  | const c us =>
    rw [hg] at h
    simp only [recArity_of_recAt] at h
    simp only
    cases hf : fe.recAt? c with
    | none => rfl
    | some p =>
      obtain ⟨rv, isQuot⟩ := p
      rw [hf] at h
      simp only [Option.map_some, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      simp only
      rw [ite_eq_right_iff.2 (fun hc => absurd hc ?_)]
      intro hc
      obtain ⟨hlen, hlvl, -⟩ := hc
      rw [iotaNumArgs_eq] at h
      have hl : (appArgs e).length = Expr.getAppNumArgsT e := by
        rw [appArgs, appArgs_go_length]; rfl
      rw [hl] at hlen
      exact h.elim (fun h' => h' (by rw [Nat.add_zero, hlen])) (fun h' => h' hlvl)
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
theorem iotaArityOk_guardI {d : Nat} {e : Expr} :
    (if InLean.iotaArityOk fe e then InLean.iotaRecI .verified r fe d e else pure none)
      = InLean.iotaRecI .verified r fe d e := by
  by_cases h : InLean.iotaArityOk fe e = true
  · rw [ite_eq_left_iff.2 (fun hc => absurd h hc)]
  · rw [ite_eq_right_iff.2 (fun hc => absurd hc h), iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

/-- The pure argument loop at a translated head, stepped in InLean's shape. -/
theorem whnfAppW_TrS_cons {m : Type → Type} [Monad m] [MonadExceptOf ConLeche.CheckError m]
    (r : ConLeche.CoreFns m) (d : Nat) (s : InLean.CState) {v : Expr} (hv : OkS s v = true)
    (a : ConLeche.Expr) (rest : List ConLeche.Expr) :
    ConLeche.whnfAppW mode r env d (TrS s v) (a :: rest) =
      match EO.stripTop v with
      | .lam _ _ body _ => ConLeche.betaPeelW mode r env d (TrS s body) [a] rest
      | _ => (do
        match ← ConLeche.iotaRec mode r env d (.app (TrS s v) a) with
        | some e'' => pure (.cont (ConLeche.Expr.mkAppN e'' rest))
        | none => ConLeche.whnfAppW mode r env d (.app (TrS s v) a) rest) := by
  rw [← OkS_stripTop s v] at hv
  conv => lhs; rw [← TrS_stripTop s v]
  conv => rhs; rw [← TrS_stripTop s v]
  generalize hx : EO.stripTop v = x at hv
  cases x with
  | lam n dom body bi => rw [TrS_lam, ConLeche.whnfAppW.eq_2]
  | fvar id => rw [TrS_fvar hv, ConLeche.whnfAppW.eq_def]; rfl
  | mvar _ => rw [OkS_mvar] at hv; cases hv
  | mdata _ y => exact (stripTop_ne_mdata hx).elim
  | _ => rw [ConLeche.whnfAppW.eq_def]; rfl

/-- **The bulk-beta argument loop** (`whnfAppC_spec`'s twin): it discharges
`WhnfAppSpecI` given the ι step's spec. -/
theorem whnfAppI_specI (hiota : IotaRecSpecI eager env r fe) : WhnfAppSpecI eager env r fe := by
  intro d v args
  induction args generalizing v with
  | nil =>
    intro _ _ _ _ _ _ _
    sym only [conleche_grind, ConLeche.whnfAppW.eq_1] =>
      vcgen [InLean.whnfAppI] <;> finish
  | cons _ rest ihr =>
    intro _ hs hv _ _ _ _ _
    rw [InLean.whnfAppI.eq_def]; simp only [iotaArityOk_guardI]
    sym only [conleche_grind, whnfAppW_TrS_cons _ _ _ hv] =>
      vcgen [InLean.mkAppNM, hiota, betaPeelI_specI (r := r) (fe := fe), ihr] <;> finish

end AppLoop

/-! ## The projection rule -/

section Proj

variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

theorem peelPis_TrS (s : InLean.CState) : ∀ (n : Nat) (t : Expr),
    (ConLeche.Expr.peelPis n (TrS s t)).isSome = (InLean.peelPis n t).isSome
  | 0, t => by simp [ConLeche.Expr.peelPis, InLean.peelPis]
  | n + 1, .forallE _ _ b _ => by
    rw [TrS_forallE, ConLeche.Expr.peelPis, InLean.peelPis, peelPis_TrS s n b]
  | n + 1, .mdata _ e => by rw [TrS_mdata, InLean.peelPis, peelPis_TrS s (n + 1) e]
  | n + 1, .fvar id => by
    simp only [InLean.peelPis, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | n + 1, .bvar _ | n + 1, .mvar _ | n + 1, .sort _ | n + 1, .const .. | n + 1, .app ..
  | n + 1, .lam .. | n + 1, .letE .. | n + 1, .lit _ | n + 1, .proj .. => rfl

/-- The projection certificate through the views. -/
theorem projCert_TrS (hv : EnvViewI fe env) (s : InLean.CState) (k : Name) (args : List Expr) :
    ConLeche.projCert env (toName k) (TrSL s args) = InLean.projCertF fe k args := by
  unfold ConLeche.projCert InLean.projCertF
  cases hc : fe.ctorView? k with
  | none =>
    split
    · rename_i cv nP nF hf; exact absurd hf (hv.ctorNone k hc cv nP nF)
    · rfl
  | some p =>
    obtain ⟨cv, nP, nF⟩ := p
    obtain ⟨ccv, hrel, hf⟩ := hv.ctor k cv nP nF hc
    rw [hf]
    simp only [ConLeche.teleArityOk, InLean.teleArityOk, TrSL, List.length_map]
    rw [← hrel.2.2.trS s, peelPis_TrS]

theorem ite_pos' {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem TrS_getD (s : InLean.CState) (l : List Expr) (n : Nat) :
    TrS s (l.getD n (.bvar 0)) = (TrSL s l).getD n (.bvar 0) := by
  simp only [List.getD, TrSL, List.getElem?_map]
  cases l[n]? <;> rfl

/-- **The projection rule** (`reduceProjCoreC_spec`'s twin): it discharges
`ReduceProjSpecI`. -/
theorem reduceProjCoreI_specI (ih : KnotSpecI .verified eager env r) (hdom : EnvDomI fe env)
    (hv : EnvViewI fe env) : ReduceProjSpecI eager env r fe := by
  intro d sn i c s₀ hs hok hw hcl
  refine tripleI_iff_run.2 fun o s' hr => ?_
  unfold InLean.reduceProjCoreI at hr
  obtain ⟨e', s₁, he', hr⟩ := bind_run hr
  obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ :=
    tripleI_iff_run.1 (projLitToCtorI_specI ih hdom hs hok hw hcl) e' s₁ he'
  unfold ConLeche.reduceProjCore
  have hfin : CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkO s' o = true ∧
      Runs (match env.findProj? (toName sn) i with
        | some entry =>
          match (TrS s₁ e').getAppFn with
          | .const k us =>
            if k = entry.ctor ∧ i < entry.numFields ∧
                (TrS s₁ e').getAppArgs.length = entry.numParams + entry.numFields ∧
                us.length = entry.levelParams.length then
              if ConLeche.projCertAt env ConLeche.CheckMode.verified.verifiedChecks k
                  (TrS s₁ e').getAppArgs then
                pure (some ((TrS s₁ e').getAppArgs.getD (entry.numParams + i) (.bvar 0)))
              else pure none
            else pure none
          | _ => pure none
        | none => pure none : ConLeche.FueledM (Option ConLeche.Expr)) (TrO s' o) ∧
      OptWS d (TrO s' o) ∧ OptClosed (TrO s' o) = true := by
    cases hp : fe.findProj? sn i with
    | none =>
      rw [hp] at hr
      obtain ⟨rfl, rfl⟩ := pure_run hr
      rw [hv.projNone sn i hp]
      exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
    | some entry =>
      rw [hp] at hr
      obtain ⟨ce, hce, hctor, hnF, hnP, hlps⟩ := hv.proj sn i entry hp
      rw [hce]
      simp only
      by_cases hA : ∃ k us, Expr.getAppFnT e' = .const k us
      · obtain ⟨k, us, hA⟩ := hA
        rw [TrS_getAppFn_const s₁ hA]
        rw [hA] at hr
        simp only at hr ⊢
        have hlen : (TrS s₁ e').getAppArgs.length = (appArgs e').length := by
          rw [← TrSL_appArgs, TrSL, List.length_map]
        have hcond : (toName k = ce.ctor ∧ i < ce.numFields ∧
            (TrS s₁ e').getAppArgs.length = ce.numParams + ce.numFields ∧
            (us.map trL).length = ce.levelParams.length) ↔
            ((k == entry.ctor) = true ∧ i < entry.numFields ∧
              (appArgs e').length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length) := by
          rw [hctor, hnF, hnP, hlps, hlen, toName_eq_iff, beq_iff_eq]; simp
        have hargs : OkSL s₁ (appArgs e') = true := OkSL_appArgs s₁ hok₁
        by_cases hc : (k == entry.ctor) = true ∧ i < entry.numFields ∧
            (appArgs e').length = entry.numParams + entry.numFields ∧
            us.length = entry.levelParams.length
        · rw [ite_pos' (hcond.2 hc)]
          rw [ite_pos' hc] at hr
          have hcert : ConLeche.projCertAt env ConLeche.CheckMode.verified.verifiedChecks (toName k)
              (TrS s₁ e').getAppArgs = InLean.projCertAtF fe
                InLean.CheckMode.verified.verifiedChecks k (appArgs e') := by
            simp only [ConLeche.projCertAt, InLean.projCertAtF, ConLeche.CheckMode.verifiedChecks,
              InLean.CheckMode.verifiedChecks, ↓reduceIte]
            rw [← TrSL_appArgs, projCert_TrS hv]
          rw [hcert]
          by_cases hpc : InLean.projCertAtF fe InLean.CheckMode.verified.verifiedChecks k
              (appArgs e') = true
          · rw [ite_pos' hpc]; rw [ite_pos' hpc] at hr
            obtain ⟨rfl, rfl⟩ := pure_run hr
            have hidx : entry.numParams + i < (appArgs e').length := by omega
            have hmem : (appArgs e').getD (entry.numParams + i) (.bvar 0) ∈ appArgs e' := by
              have : (appArgs e').getD (entry.numParams + i) (.bvar 0) =
                  (appArgs e')[entry.numParams + i] := by
                simp [List.getD, List.getElem?_eq_getElem hidx]
              rw [this]; exact List.getElem_mem hidx
            have htr : TrS s₁ ((appArgs e').getD (entry.numParams + i) (.bvar 0)) =
                (TrS s₁ e').getAppArgs.getD (ce.numParams + i) (.bvar 0) := by
              rw [TrS_getD, TrSL_appArgs, hnP]
            have hmemT : TrS s₁ ((appArgs e').getD (entry.numParams + i) (.bvar 0)) ∈
                (TrS s₁ e').getAppArgs := by
              rw [← TrSL_appArgs]; exact List.mem_map_of_mem hmem
            refine ⟨hs₁, ht₁, ?_, ?_, ?_, ?_⟩
            · rw [OkO_some]
              simp only [OkSL, List.all_eq_true] at hargs; exact hargs _ hmem
            · rw [TrO_some, htr, hnP]; exact Runs.pure _
            · exact allWS_getAppArgs hw₁ _ hmemT
            · rw [TrO_some, OptClosed_some]
              have := allClosed_getAppArgs hc₁
              simp only [AllClosed, List.all_eq_true] at this; exact this _ hmemT
          · rw [ite_neg' hpc]; rw [ite_neg' hpc] at hr
            obtain ⟨rfl, rfl⟩ := pure_run hr
            exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
        · rw [ite_neg' (fun h => hc (hcond.1 h))]
          rw [ite_neg' hc] at hr
          obtain ⟨rfl, rfl⟩ := pure_run hr
          exact ⟨hs₁, ht₁, rfl, Runs.pure _, trivial, rfl⟩
      · have hA' : ∀ k us, Expr.getAppFnT e' ≠ .const k us := fun k us h => hA ⟨k, us, h⟩
        have hT := TrS_getAppFn_notConst s₁ hA'
        have hr' : (pure none : InLean.CheckCM (Option Expr)) s₁ = .ok (o, s') := by
          rw [← hr]
          generalize hx : Expr.getAppFnT e' = x at hA'
          cases x with
          | const k us => exact absurd rfl (hA' k us)
          | _ => rfl
        obtain ⟨rfl, rfl⟩ := pure_run hr'
        refine ⟨hs₁, ht₁, rfl, ?_, trivial, rfl⟩
        generalize hx : (TrS s₁ e').getAppFn = x at hT
        cases x with
        | const k us => exact absurd rfl (hT k us)
        | _ => exact Runs.pure _
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hfin
  exact ⟨h1, h2, h3, Runs.bind hrun₁ h4, h5, h6⟩

end Proj

end InLeanProof
