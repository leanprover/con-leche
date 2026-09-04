import Setlec.Verify.Mono
import Setlec.Verify.Deep
import Setlec.Kernel.TypeCheckerC

/-!
# The cache-refinement bridge, part A: fueled families

`FueledM` packages a fuel-indexed family of pure computations that is
monotone in the fuel (monotonicity of the components is `Mono.lean`'s
result, carried pointwise through `bind`).  The `atF` battery relates
the core bodies instantiated at `FueledM` (with the fueled record) to
their plain instantiations at `pureFns mode env F` — the same projection
game as `PairM`, one component instead of two.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}
/- Task #172 B2: the ι cone's mode is decoupled from the knot's, so
that the `whnfCore` template's `cfg.iotaMode` can occupy it while the
knot stays at the tower's `mode`.  Generalization only — every landed
call site unifies `mi := mode`. -/
variable {mi : CheckMode}

/-- Monotone fuel-indexed families of pure computations. -/
def FueledM (α : Type) : Type :=
  {p : Nat → CheckM α //
    ∀ {f f' : Nat} {v : α}, f ≤ f' → p f = .ok v → p f' = .ok v}

namespace FueledM

instance : Monad FueledM where
  pure a := ⟨fun _ => pure a, fun _ h => h⟩
  bind x f :=
    ⟨fun F => x.val F >>= fun a => (f a).val F, by
      intro F F' v hle h
      simp only [Bind.bind] at h ⊢
      cases hx : x.val F with
      | error e => rw [hx] at h; exact nomatch h
      | ok a =>
        rw [hx] at h
        dsimp only [Except.bind] at h
        rw [x.property hle hx]
        dsimp only [Except.bind]
        exact (f a).property hle h⟩

instance : MonadExceptOf CheckError FueledM where
  throw e := ⟨fun _ => throw e, fun _ h => nomatch h⟩
  tryCatch _ _ :=
    ⟨fun _ => throw (.internal "tryCatch unsupported"), fun _ h => nomatch h⟩

@[simp] theorem atF_bind {α β : Type} (x : FueledM α) (f : α → FueledM β)
    (F : Nat) :
    (x >>= f).val F = x.val F >>= fun a => (f a).val F := rfl

@[simp] theorem atF_pure {α : Type} (a : α) (F : Nat) :
    (pure a : FueledM α).val F = pure a := rfl

@[simp] theorem atF_throw {α : Type} (e : CheckError) (F : Nat) :
    (throw e : FueledM α).val F = throw e := rfl

@[simp] theorem atF_ite {α : Type} {c : Prop} [Decidable c]
    (x y : FueledM α) (F : Nat) :
    (if c then x else y).val F = if c then x.val F else y.val F := by
  by_cases hc : c <;> simp [hc]

end FueledM

/-- The fueled record: each entry is the family of its fueled runs,
monotone by `Mono.lean`. -/
def fueledFns (mode : CheckMode) (env : Env) : CoreFns FueledM where
  whnfCore d e := ⟨fun F => whnfCore mode env F d e, fun hle h => whnfCore_mono hle h⟩
  whnf d e := ⟨fun F => whnf mode env F d e, fun hle h => whnf_mono hle h⟩
  infer d e := ⟨fun F => inferTypeCore mode env F d e,
    fun hle h => inferTypeCore_mono hle h⟩
  defeq d a b := ⟨fun F => isDefEqCore mode env F d a b,
    fun hle h => isDefEqCore_mono hle h⟩
  annotate d e := ⟨fun F => annotateCore mode env F d e,
    fun hle h => annotateCore_mono hle h⟩
  inferIO d e := ⟨fun F => inferTypeIO mode env F d e,
    fun hle h => inferTypeIO_mono hle h⟩

section AtF

variable {env : Env}

theorem liftFueled_atF {α : Type} (what : String) (o : Option α) (F : Nat) :
    (liftFueled what o : FueledM α).val F = liftFueled what o := by
  cases o <;> rfl

theorem iotaCerts_atF (d : Nat) (F : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (fueledFns mode env) env d ty args).val F =
        iotaCerts (pureFns mode env F) env d ty args
  | _, [] => rfl
  | .forallE n ty body mb, arg :: rest => by
    show ((do
        let ta ← (fueledFns mode env).infer d arg
        if ← (fueledFns mode env).defeq d ta ty then
          iotaCerts (fueledFns mode env) env d (body.instantiate1 arg) rest
        else pure false : FueledM Bool)).val F = (do
        let ta ← (pureFns mode env F).infer d arg
        if ← (pureFns mode env F).defeq d ta ty then
          iotaCerts (pureFns mode env F) env d (body.instantiate1 arg) rest
        else pure false)
    rw [FueledM.atF_bind]
    congr 1
    funext ta
    rw [FueledM.atF_bind]
    congr 1
    funext b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact iotaCerts_atF d F (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem defEqList_atF (d : Nat) (F : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (fueledFns mode env) env d as bs).val F =
        defEqList (pureFns mode env F) env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (fueledFns mode env).defeq d a b then
          defEqList (fueledFns mode env) env d as bs
        else pure false : FueledM Bool)).val F = (do
        if ← (pureFns mode env F).defeq d a b then
          defEqList (pureFns mode env F) env d as bs
        else pure false)
    rw [FueledM.atF_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_atF d F as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem structEtaProjCerts_atF (d : Nat) (F : Nat) (T : Name)
    (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name) :
    ∀ (idxs : List Nat),
      (structEtaProjCerts (fueledFns mode env) env d T us' targs b lpsT
        idxs).val F =
      structEtaProjCerts (pureFns mode env F) env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (fueledFns mode env) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (fueledFns mode env) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : FueledM Bool)).val F = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pureFns mode env F) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pureFns mode env F) env d T us' targs b lpsT
                rest
            else pure false
          else pure false
        | _ => pure false)
    cases hf : env.find? (projFnName T i) with
    | none => rfl
    | some ci =>
      cases ci with
      | recInfo cvp mI rP rules =>
        dsimp only
        split
        · rw [FueledM.atF_bind, iotaCerts_atF]
          congr 1
          funext r
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCerts_atF d F T us' targs b lpsT rest
          | false => rfl
        · rfl
      | axiomInfo cv => rfl
      | projInfo _ => rfl
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

theorem defeqSpine_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqSpine (fueledFns mode env) env d a b).val F =
      defeqSpine (pureFns mode env F) env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

macro "atF_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_atF])
    | (rw [iotaCerts_atF])
    | (rw [defEqList_atF])
    | (rw [structEtaProjCerts_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac" : tactic =>
  `(tactic| atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step <;> atF_step <;>
    atF_step <;> atF_step <;> atF_step)

theorem reduceNat_atF (d : Nat) (e : Expr) (F : Nat) :
    (reduceNat (fueledFns mode env) env d e).val F =
      reduceNat (pureFns mode env F) env d e := by
  unfold reduceNat
  atF_tac

theorem ensureSort_atF (d : Nat) (e : Expr) (F : Nat) :
    (ensureSort (fueledFns mode env) env d e).val F =
      ensureSort (pureFns mode env F) env d e := by
  unfold ensureSort
  atF_tac

/-- Task #161 P5: the ∀/λ writes at a fixed fuel.  Both are the chain
read, or `infer`/`ensureSort` calls the cascade already knows. -/
theorem annotPwPi_atF {env : Env} (d : Nat) (e : Expr) (F : Nat) :
    (annotPwPi (fueledFns mode env) env d e).val F =
      annotPwPi (pureFns mode env F) env d e := by
  unfold annotPwPi
  atF_tac <;> exact ensureSort_atF _ _ _

theorem annotPwLam_atF {env : Env} (d : Nat) (e : Expr) (F : Nat) :
    (annotPwLam (fueledFns mode env) env d e).val F =
      annotPwLam (pureFns mode env F) env d e := by
  unfold annotPwLam
  atF_tac <;> exact ensureSort_atF _ _ _

theorem proofIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (proofIrrel (fueledFns mode env) env d a b).val F =
      proofIrrel (pureFns mode env F) env d a b := by
  unfold proofIrrel
  atF_tac

theorem pairEtaCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (pairEtaCert mi (fueledFns mode env) env d a b).val F =
      pairEtaCert mi (pureFns mode env F) env d a b := by
  unfold pairEtaCert
  atF_tac

theorem structEtaCertWith_atF (d : Nat) (a b wtb : Expr) (F : Nat) :
    (structEtaCertWith mi (fueledFns mode env) env d a b wtb).val F =
      structEtaCertWith mi (pureFns mode env F) env d a b wtb := by
  unfold structEtaCertWith
  atF_tac

theorem structUnitCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (structUnitCert (fueledFns mode env) env d a b).val F =
      structUnitCert (pureFns mode env F) env d a b := by
  unfold structUnitCert
  atF_tac

theorem etaCert_atF (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) (b : Expr) (F : Nat) :
    (etaCert mi (fueledFns mode env) env d n ty body mb b).val F =
      etaCert mi (pureFns mode env F) env d n ty body mb b := by
  unfold etaCert
  atF_tac

theorem projCert_atF (d : Nat) (e₂ : Expr) (i : Nat) (nP : Nat) (F : Nat) :
    (projCert (fueledFns mode env) env d e₂ i nP).val F =
      projCert (pureFns mode env F) env d e₂ i nP := by
  unfold projCert
  atF_tac

macro "atF_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_atF])
    | (rw [iotaCerts_atF])
    | (rw [defEqList_atF])
    | (rw [structEtaProjCerts_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [proofIrrel_atF])
    | (rw [pairEtaCert_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | (rw [projCert_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac2" : tactic =>
  `(tactic| atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2 <;> atF_step2 <;>
    atF_step2 <;> atF_step2 <;> atF_step2)

theorem structEtaCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (structEtaCert mi (fueledFns mode env) env d a b).val F =
      structEtaCert mi (pureFns mode env F) env d a b := by
  unfold structEtaCert
  atF_tac2

-- Outer casing peeled by hand (as in `Setlec/Verify/PairM.lean`): the
-- body outgrew the split-driven macro.
set_option maxHeartbeats 800000 in
theorem majorToCtor_atF (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) (F : Nat) :
    (majorToCtor mi (fueledFns mode env) env d c rules e).val F =
      majorToCtor mi (pureFns mode env F) env d c rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [if_pos hca, if_pos hca]; rfl
  rw [if_neg hca, if_neg hca]
  match rules with
  | [] => rfl
  | _ :: _ :: _ => rfl
  | [rl] =>
    dsimp only
    cases hfr : env.find? rl.ctor <;> try rfl
    case some ci =>
    cases ci <;> try rfl
    case ctorInfo cvj cnP cnF =>
    dsimp only
    cases (cvj.type.piResult).getAppFn <;> try rfl
    case const T us₀ =>
    dsimp only
    cases env.find? T <;> try rfl
    case some ciT =>
    cases ciT <;> try rfl
    case indInfo cvT caps =>
    dsimp only
    by_cases hK : caps.ruleK = true ∧ cnF = 0
    · rw [if_pos hK, if_pos hK]
      atF_tac2
    rw [if_neg hK, if_neg hK]
    by_cases hE : caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
        Name.isProjFnShape c = false
    · rw [if_pos hE, if_pos hE]
      atF_tac2
    rw [if_neg hE, if_neg hE]
    rfl

theorem litMajorToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (litMajorToCtor (fueledFns mode env) env d e).val F =
      litMajorToCtor (pureFns mode env F) env d e := by
  unfold litMajorToCtor
  atF_tac2

theorem projLitToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (projLitToCtor (fueledFns mode env) env d e).val F =
      projLitToCtor (pureFns mode env F) env d e := by
  unfold projLitToCtor
  atF_tac2

theorem isPropType_atF (d : Nat) (ty : Expr) (F : Nat) :
    (isPropType (fueledFns mode env) env d ty).val F =
      isPropType (pureFns mode env F) env d ty := by
  unfold isPropType
  atF_tac2

theorem projFieldDom_atF (structProp : Bool) (sn : Name) (e₂ : Expr) :
    ∀ (k j d : Nat) (tel : Expr) (F : Nat),
      (projFieldDom (fueledFns mode env) env d structProp sn e₂ j k tel).val F =
        projFieldDom (pureFns mode env F) env d structProp sn e₂ j k tel := by
  intro k
  induction k with
  | zero =>
    intro j d tel F
    cases tel <;> dsimp only [projFieldDom] <;> rfl
  | succ k ih =>
    intro j d tel F
    cases tel <;> dsimp only [projFieldDom] <;> try rfl
    repeat (first
      | rfl
      | (rw [ih])
      | (rw [isPropType_atF])
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (dsimp only [])
      | split)

theorem annotateProjRec_atF (d : Nat) (entry : ProjEntry) (i : Nat)
    (te e₂ : Expr) (us : List Level) (F : Nat) :
    (annotateProjRec (fueledFns mode env) env d entry i te e₂ us).val F =
      annotateProjRec (pureFns mode env F) env d entry i te e₂ us := by
  unfold annotateProjRec
  repeat (first
    | rfl
    | (rw [isPropType_atF])
    | (rw [projFieldDom_atF])
    | (rw [ensureSort_atF])
    | (rw [liftFueled_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem annotateProjElim_atF (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) (F : Nat) :
    (annotateProjElim (fueledFns mode env) env d sn i te e₂).val F =
      annotateProjElim (pureFns mode env F) env d sn i te e₂ := by
  unfold annotateProjElim
  repeat (first
    | rfl
    | (rw [annotateProjRec_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

macro "atF_step3" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_atF])
    | (rw [iotaCerts_atF])
    | (rw [defEqList_atF])
    | (rw [structEtaProjCerts_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [proofIrrel_atF])
    | (rw [pairEtaCert_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | (rw [projCert_atF])
    | (rw [structEtaCert_atF])
    | (rw [majorToCtor_atF])
    | (rw [litMajorToCtor_atF])
    | (rw [annotateProjElim_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac3" : tactic =>
  `(tactic| atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3 <;> atF_step3 <;>
    atF_step3 <;> atF_step3 <;> atF_step3)

theorem stuckIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (stuckIrrel mi (fueledFns mode env) env d a b).val F =
      stuckIrrel mi (pureFns mode env F) env d a b := by
  unfold stuckIrrel
  atF_tac3

theorem iotaRec_atF (d : Nat) (e : Expr) (F : Nat) :
    (iotaRec mi (fueledFns mode env) env d e).val F =
      iotaRec mi (pureFns mode env F) env d e := by
  unfold iotaRec
  atF_tac3

/-- The level-4 cascade, parameterized over one extra alternative so
that the loop-body lemmas can feed in their continuation hypothesis
(`atF_step4k`) without duplicating the rewrite list. -/
macro "atF_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_atF])
    | (rw [iotaCerts_atF])
    | (rw [defEqList_atF])
    | (rw [structEtaProjCerts_atF])
    | (rw [reduceNat_atF])
    | (rw [ensureSort_atF])
    | (rw [proofIrrel_atF])
    | (rw [pairEtaCert_atF])
    | (rw [structEtaCertWith_atF])
    | (rw [structUnitCert_atF])
    | (rw [etaCert_atF])
    | (rw [projCert_atF])
    | (rw [structEtaCert_atF])
    | (rw [majorToCtor_atF])
    | (rw [annotateProjElim_atF])
    | (rw [stuckIrrel_atF])
    | (rw [iotaRec_atF])
    | (rw [projLitToCtor_atF])
    | (rw [defeqSpine_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- task #161: the β gate's dead branch — unfolding the *one* gate
    -- primitive hands both arms back to the cascade's own `split`
    | ((rw [FueledM.atF_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "atF_step4" : tactic => `(tactic| atF_core4 (fail))

macro "atF_step4k" hk:ident : tactic =>
  `(tactic| atF_core4 (rw [$hk:ident]))

macro "atF_tac4k" hk:ident : tactic =>
  `(tactic| atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk <;>
    atF_step4k $hk <;> atF_step4k $hk <;> atF_step4k $hk)

macro "atF_tac4" : tactic =>
  `(tactic| atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4)

theorem whnfCoreBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (whnfCoreBody mode (fueledFns mode env) env d e).val F =
      whnfCoreBody mode (pureFns mode env F) env d e := by
  unfold whnfCoreBody
  atF_tac4

theorem whnfStep_atF (d : Nat) (k : Expr → FueledM Expr)
    (kF : Expr → CheckM Expr) (hk : ∀ e, (k e).val F = kF e) (e : Expr) :
    (whnfStep (fueledFns mode env) env d k e).val F =
      whnfStep (pureFns mode env F) env d kF e := by
  unfold whnfStep
  atF_tac4k hk

theorem whnfLoop_atF (d : Nat) (F : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (fueledFns mode env) env d n e).val F =
        whnfLoop (pureFns mode env F) env d n e
  | 0, _ => rfl
  | n + 1, e => whnfStep_atF d _ _ (fun e' => whnfLoop_atF d F n e') e

theorem whnfBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (whnfBody (fueledFns mode env) env d e).val F =
      whnfBody (pureFns mode env F) env d e :=
  whnfLoop_atF d F whnfLoopFuel e

theorem inferBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (inferBody mode (fueledFns mode env) env d e).val F =
      inferBody mode (pureFns mode env F) env d e := by
  unfold inferBody
  atF_tac4

theorem defeqStep_atF (d : Nat) (k : Expr → Expr → FueledM Bool)
    (kF : Expr → Expr → CheckM Bool)
    (hk : ∀ a b, (k a b).val F = kF a b) (a b : Expr) :
    (defeqStep mode (fueledFns mode env) env d k a b).val F =
      defeqStep mode (pureFns mode env F) env d kF a b := by
  unfold defeqStep
  atF_tac4k hk

theorem defeqLoop_atF (d : Nat) (F : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (defeqLoop mode (fueledFns mode env) env d n a b).val F =
        defeqLoop mode (pureFns mode env F) env d n a b
  | 0, _, _ => rfl
  | n + 1, a, b =>
    defeqStep_atF d _ _ (fun x y => defeqLoop_atF d F n x y) a b

theorem defeqBody_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqBody mode (fueledFns mode env) env d a b).val F =
      defeqBody mode (pureFns mode env F) env d a b :=
  defeqLoop_atF d F defeqLoopFuel a b

theorem annotateBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (annotateBody mode (fueledFns mode env) env d e).val F =
      annotateBody mode (pureFns mode env F) env d e := by
  -- task #161 P5: `annotPwPi`/`annotPwLam` unfold alongside the body,
  -- as in `PairM.lean` — the writes are infer + `ensureSort` calls the
  -- cascade already commutes.
  unfold annotateBody annotPwPi annotPwLam
  atF_tac4

end AtF

end Setlec
