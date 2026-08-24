import Setlec.Verify.Mono
import Setlec.Verify.Deep
import Setlec.Kernel.TypeCheckerC

/-!
# The cache-refinement bridge, part A: fueled families

`FueledM` packages a fuel-indexed family of pure computations that is
monotone in the fuel (monotonicity of the components is `Mono.lean`'s
result, carried pointwise through `bind`).  The `atF` battery relates
the core bodies instantiated at `FueledM` (with the fueled record) to
their plain instantiations at `pureFns env F` — the same projection
game as `PairM`, one component instead of two.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

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
def fueledFns (env : Env) : CoreFns FueledM where
  whnfCore d e := ⟨fun F => whnfCore env F d e, fun hle h => whnfCore_mono hle h⟩
  whnf d e := ⟨fun F => whnf env F d e, fun hle h => whnf_mono hle h⟩
  infer d e := ⟨fun F => inferTypeCore env F d e,
    fun hle h => inferTypeCore_mono hle h⟩
  defeq d a b := ⟨fun F => isDefEqCore env F d a b,
    fun hle h => isDefEqCore_mono hle h⟩
  annotate d e := ⟨fun F => annotateCore env F d e,
    fun hle h => annotateCore_mono hle h⟩

section AtF

variable {env : Env}

theorem liftFueled_atF {α : Type} (what : String) (o : Option α) (F : Nat) :
    (liftFueled what o : FueledM α).val F = liftFueled what o := by
  cases o <;> rfl

theorem iotaCerts_atF (d : Nat) (F : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (fueledFns env) env d ty args).val F =
        iotaCerts (pureFns env F) env d ty args
  | _, [] => rfl
  | .forallE n ty body mb, arg :: rest => by
    show ((do
        let ta ← (fueledFns env).infer d arg
        if ← (fueledFns env).defeq d ta ty then
          iotaCerts (fueledFns env) env d (body.instantiate1 arg) rest
        else pure false : FueledM Bool)).val F = (do
        let ta ← (pureFns env F).infer d arg
        if ← (pureFns env F).defeq d ta ty then
          iotaCerts (pureFns env F) env d (body.instantiate1 arg) rest
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
      (defEqList (fueledFns env) env d as bs).val F =
        defEqList (pureFns env F) env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (fueledFns env).defeq d a b then
          defEqList (fueledFns env) env d as bs
        else pure false : FueledM Bool)).val F = (do
        if ← (pureFns env F).defeq d a b then
          defEqList (pureFns env F) env d as bs
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
      (structEtaProjCerts (fueledFns env) env d T us' targs b lpsT
        idxs).val F =
      structEtaProjCerts (pureFns env F) env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (fueledFns env) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (fueledFns env) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : FueledM Bool)).val F = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pureFns env F) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pureFns env F) env d T us' targs b lpsT
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
    (defeqSpine (fueledFns env) env d a b).val F =
      defeqSpine (pureFns env F) env d a b := by
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
    (reduceNat (fueledFns env) env d e).val F =
      reduceNat (pureFns env F) env d e := by
  unfold reduceNat
  atF_tac

theorem ensureSort_atF (d : Nat) (e : Expr) (F : Nat) :
    (ensureSort (fueledFns env) env d e).val F =
      ensureSort (pureFns env F) env d e := by
  unfold ensureSort
  atF_tac

/-- The codomain-sort family (task #100): `ensureSort ∘ infer`, the
fueled comparand of the interned `codOfI` memo. -/
def codOfF (env : Env) (d : Nat) (e : Expr) : FueledM Level :=
  (fueledFns env).infer d e >>= fun t => ensureSort (fueledFns env) env d t

theorem codOfF_atF (d : Nat) (e : Expr) (F : Nat) :
    (codOfF env d e).val F = codOfCore env F d e := by
  show (inferTypeCore env F d e >>=
    fun t => (ensureSort (fueledFns env) env d t).val F) = _
  simp only [ensureSort_atF]
  rfl

/-- Fuel monotonicity of `codOfCore`, from the family's. -/
theorem codOfCore_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr}
    {u : Level} (h : codOfCore env f d e = .ok u) :
    codOfCore env f' d e = .ok u := by
  rw [← codOfF_atF] at h ⊢
  exact (codOfF env d e).property hle h

theorem proofIrrel_atF (d : Nat) (a b : Expr) (F : Nat) :
    (proofIrrel (fueledFns env) env d a b).val F =
      proofIrrel (pureFns env F) env d a b := by
  unfold proofIrrel
  atF_tac

theorem pairEtaCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (pairEtaCert (fueledFns env) env d a b).val F =
      pairEtaCert (pureFns env F) env d a b := by
  unfold pairEtaCert
  atF_tac

theorem structEtaCertWith_atF (d : Nat) (a b wtb : Expr) (F : Nat) :
    (structEtaCertWith (fueledFns env) env d a b wtb).val F =
      structEtaCertWith (pureFns env F) env d a b wtb := by
  unfold structEtaCertWith
  atF_tac

theorem structUnitCert_atF (d : Nat) (a b : Expr) (F : Nat) :
    (structUnitCert (fueledFns env) env d a b).val F =
      structUnitCert (pureFns env F) env d a b := by
  unfold structUnitCert
  atF_tac

theorem etaCert_atF (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) (b : Expr) (F : Nat) :
    (etaCert (fueledFns env) env d n ty body mb b).val F =
      etaCert (pureFns env F) env d n ty body mb b := by
  unfold etaCert
  atF_tac

theorem projCert_atF (d : Nat) (e₂ : Expr) (i : Nat)
    (fieldLvl structLvl : Level) (nP : Nat) (F : Nat) :
    (projCert (fueledFns env) env d e₂ i fieldLvl structLvl nP).val F =
      projCert (pureFns env F) env d e₂ i fieldLvl structLvl nP := by
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
    (structEtaCert (fueledFns env) env d a b).val F =
      structEtaCert (pureFns env F) env d a b := by
  unfold structEtaCert
  atF_tac2

-- Outer casing peeled by hand (as in `Setlec/Verify/PairM.lean`): the
-- body outgrew the split-driven macro.
set_option maxHeartbeats 800000 in
theorem majorToCtor_atF (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) (F : Nat) :
    (majorToCtor (fueledFns env) env d c rules e).val F =
      majorToCtor (pureFns env F) env d c rules e := by
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
        Name.isProjFnShape c = false ∧ piResultIsProp cvT.type = false
    · rw [if_pos hE, if_pos hE]
      atF_tac2
    rw [if_neg hE, if_neg hE]
    rfl

theorem litMajorToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (litMajorToCtor (fueledFns env) env d e).val F =
      litMajorToCtor (pureFns env F) env d e := by
  unfold litMajorToCtor
  atF_tac2

theorem projLitToCtor_atF (d : Nat) (e : Expr) (F : Nat) :
    (projLitToCtor (fueledFns env) env d e).val F =
      projLitToCtor (pureFns env F) env d e := by
  unfold projLitToCtor
  atF_tac2

theorem isPropType_atF (d : Nat) (ty : Expr) (F : Nat) :
    (isPropType (fueledFns env) env d ty).val F =
      isPropType (pureFns env F) env d ty := by
  unfold isPropType
  atF_tac2

theorem projFieldDom_atF (structProp : Bool) (sn : Name) (e₂ : Expr) :
    ∀ (k j d : Nat) (tel : Expr) (F : Nat),
      (projFieldDom (fueledFns env) env d structProp sn e₂ j k tel).val F =
        projFieldDom (pureFns env F) env d structProp sn e₂ j k tel := by
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
    (annotateProjRec (fueledFns env) env d entry i te e₂ us).val F =
      annotateProjRec (pureFns env F) env d entry i te e₂ us := by
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
    (annotateProjElim (fueledFns env) env d sn i te e₂).val F =
      annotateProjElim (pureFns env F) env d sn i te e₂ := by
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
    (stuckIrrel (fueledFns env) env d a b).val F =
      stuckIrrel (pureFns env F) env d a b := by
  unfold stuckIrrel
  atF_tac3

theorem iotaRec_atF (d : Nat) (e : Expr) (F : Nat) :
    (iotaRec (fueledFns env) env d e).val F =
      iotaRec (pureFns env F) env d e := by
  unfold iotaRec
  atF_tac3

macro "atF_step4" : tactic =>
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
    | (rw [annotateProjElim_atF])
    | (rw [stuckIrrel_atF])
    | (rw [iotaRec_atF])
    | (rw [projLitToCtor_atF])
    | (rw [defeqSpine_atF])
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "atF_tac4" : tactic =>
  `(tactic| atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4 <;> atF_step4 <;>
    atF_step4 <;> atF_step4 <;> atF_step4)

theorem whnfCoreBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (whnfCoreBody (fueledFns env) env d e).val F =
      whnfCoreBody (pureFns env F) env d e := by
  unfold whnfCoreBody
  atF_tac4

theorem whnfBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (whnfBody (fueledFns env) env d e).val F =
      whnfBody (pureFns env F) env d e := by
  unfold whnfBody
  atF_tac4

theorem inferBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (inferBody (fueledFns env) env d e).val F =
      inferBody (pureFns env F) env d e := by
  unfold inferBody
  atF_tac4

theorem defeqBody_atF (d : Nat) (a b : Expr) (F : Nat) :
    (defeqBody (fueledFns env) env d a b).val F =
      defeqBody (pureFns env F) env d a b := by
  unfold defeqBody
  atF_tac4

theorem annotateBody_atF (d : Nat) (e : Expr) (F : Nat) :
    (annotateBody (fueledFns env) env d e).val F =
      annotateBody (pureFns env F) env d e := by
  unfold annotateBody
  atF_tac4

end AtF

end Setlec
