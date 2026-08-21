import Setlec.Verify.Mono
import Setlec.Kernel.TypeCheckerC
import Setlec.Kernel.Checker

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
        | some (.recInfo cvp _ _ _ _ _) =>
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
        | some (.recInfo cvp _ _ _ _ _) =>
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
      | recInfo cvp nP nM nm ni rules =>
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
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

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

theorem projCert_atF (d : Nat) (e₂ : Expr) (i : Nat) (us : List Level) (nP : Nat) (F : Nat) :
    (projCert (fueledFns env) env d e₂ i us nP).val F =
      projCert (pureFns env F) env d e₂ i us nP := by
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

theorem majorToCtor_atF (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) (F : Nat) :
    (majorToCtor (fueledFns env) env d c rules e).val F =
      majorToCtor (pureFns env F) env d c rules e := by
  unfold majorToCtor
  atF_tac2

theorem annotateProjElim_atF (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) (F : Nat) :
    (annotateProjElim (fueledFns env) env d sn i te e₂).val F =
      annotateProjElim (pureFns env F) env d sn i te e₂ := by
  unfold annotateProjElim
  atF_tac2

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

/-! ## Part B: the cache invariant and the simulation -/

/-- Every cache entry is backed by a pure run at some fuel. -/
def CacheOK (env : Env) (σ : KCache) : Prop :=
  (∀ d e r, σ.whnfCore[((d, e) : Nat × Expr)]? = some r →
    ∃ F, whnfCore env F d e = .ok r) ∧
  (∀ d e r, σ.whnf[((d, e) : Nat × Expr)]? = some r →
    ∃ F, whnf env F d e = .ok r) ∧
  (∀ d e r, σ.infer[((d, e) : Nat × Expr)]? = some r →
    ∃ F, inferTypeCore env F d e = .ok r) ∧
  (∀ d a b r, σ.defeq[((d, a, b) : Nat × Expr × Expr)]? = some r →
    ∃ F, isDefEqCore env F d a b = .ok r) ∧
  (∀ d e r, σ.annot[((d, e) : Nat × Expr)]? = some r →
    ∃ F, annotateCore env F d e = .ok r)

theorem CacheOK.empty (env : Env) : CacheOK env {} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro d e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro d e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro d e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro d a b r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl
  · intro d e r hl
    rw [Std.HashMap.getElem?_empty] at hl
    exact nomatch hl

/-- The simulation relation: from a backed cache, a successful cached
run yields a value backed by some pure fuel, and the cache stays
backed. -/
def simRel (env : Env) : MonadRel FueledM CheckSM where
  R p c := ∀ σ, CacheOK env σ → ∀ v σ', c σ = .ok (v, σ') →
    (∃ F, p.val F = .ok v) ∧ CacheOK env σ'
  pure_rel a := by
    intro σ hσ v σ' h
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨⟨0, rfl⟩, hσ⟩
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro σ hσ v σ' h
    simp only [Bind.bind, StateT.bind] at h
    cases hx2 : x₂ σ with
    | error e =>
      rw [hx2] at h
      exact nomatch h
    | ok p =>
      obtain ⟨a, σ₁⟩ := p
      rw [hx2] at h
      dsimp only [Except.bind] at h
      obtain ⟨⟨F₁, hp1⟩, hσ₁⟩ := hx σ hσ a σ₁ hx2
      obtain ⟨⟨F₂, hp2⟩, hσ'⟩ := hf a σ₁ hσ₁ v σ' h
      refine ⟨⟨max F₁ F₂, ?_⟩, hσ'⟩
      rw [FueledM.atF_bind]
      simp only [Bind.bind]
      rw [x₁.property (Nat.le_max_left F₁ F₂) hp1]
      dsimp only [Except.bind]
      exact (f₁ a).property (Nat.le_max_right F₁ F₂) hp2
  throw_rel e := by
    intro σ hσ v σ' h
    exact nomatch h

/-! ## The memoized knot simulates the fueled families -/

theorem cached_whnfCore_sim (env : Env) (f : Nat)
    (ih : FnsRel (simRel env) (fueledFns env) (cachedFns env f))
    (d : Nat) (e : Expr) :
    (simRel env).R ((fueledFns env).whnfCore d e)
      ((cachedFns env (f + 1)).whnfCore d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns env (f + 1)).whnfCore d e =
    memoE (·.whnfCore) (fun st mp => { st with whnfCore := mp })
      (fun d e => whnfCoreBody (cachedFns env f) env d e) d e from rfl]
    at hrun
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.whnfCore[((d, e) : Nat × Expr)]? with
  | some r =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hF⟩ := hσ.1 d e r hl
    exact ⟨⟨F, hF⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [StateT.bind] at hrun
    cases hb : whnfCoreBody (cachedFns env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok p =>
      obtain ⟨r, σ₁⟩ := p
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hpair := (whnfCoreBody
        (pairFns (fueledFns env) (cachedFns env f) ih) env d e).property
      rw [whnfCoreBody_fst_proj, whnfCoreBody_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ r σ₁ hb
      rw [whnfCoreBody_atF] at hF
      have hpure : whnfCore env (F + 1) d e = .ok r := hF
      refine ⟨⟨F + 1, hpure⟩, ?_, hσ₁.2.1, hσ₁.2.2.1, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2⟩
      intro d' e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((d, e) : Nat × Expr) == (d', e')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl⟩ : d = d' ∧ e = e' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain rfl : r = r' := by injection hl'
        exact ⟨F + 1, hpure⟩
      · rw [if_neg hk] at hl'
        exact hσ₁.1 d' e' r' hl'

theorem cached_whnf_sim (env : Env) (f : Nat)
    (ih : FnsRel (simRel env) (fueledFns env) (cachedFns env f))
    (d : Nat) (e : Expr) :
    (simRel env).R ((fueledFns env).whnf d e)
      ((cachedFns env (f + 1)).whnf d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns env (f + 1)).whnf d e =
    memoE (·.whnf) (fun st mp => { st with whnf := mp })
      (fun d e => whnfBody (cachedFns env f) env d e) d e from rfl]
    at hrun
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.whnf[((d, e) : Nat × Expr)]? with
  | some r =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hF⟩ := hσ.2.1 d e r hl
    exact ⟨⟨F, hF⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [StateT.bind] at hrun
    cases hb : whnfBody (cachedFns env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok p =>
      obtain ⟨r, σ₁⟩ := p
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hpair := (whnfBody
        (pairFns (fueledFns env) (cachedFns env f) ih) env d e).property
      rw [whnfBody_fst_proj, whnfBody_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ r σ₁ hb
      rw [whnfBody_atF] at hF
      have hpure : whnf env (F + 1) d e = .ok r := hF
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, ?_, hσ₁.2.2.1, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2⟩
      intro d' e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((d, e) : Nat × Expr) == (d', e')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl⟩ : d = d' ∧ e = e' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain rfl : r = r' := by injection hl'
        exact ⟨F + 1, hpure⟩
      · rw [if_neg hk] at hl'
        exact hσ₁.2.1 d' e' r' hl'

theorem cached_infer_sim (env : Env) (f : Nat)
    (ih : FnsRel (simRel env) (fueledFns env) (cachedFns env f))
    (d : Nat) (e : Expr) :
    (simRel env).R ((fueledFns env).infer d e)
      ((cachedFns env (f + 1)).infer d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns env (f + 1)).infer d e =
    memoE (·.infer) (fun st mp => { st with infer := mp })
      (fun d e => inferBody (cachedFns env f) env d e) d e from rfl]
    at hrun
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.infer[((d, e) : Nat × Expr)]? with
  | some r =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hF⟩ := hσ.2.2.1 d e r hl
    exact ⟨⟨F, hF⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [StateT.bind] at hrun
    cases hb : inferBody (cachedFns env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok p =>
      obtain ⟨r, σ₁⟩ := p
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hpair := (inferBody
        (pairFns (fueledFns env) (cachedFns env f) ih) env d e).property
      rw [inferBody_fst_proj, inferBody_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ r σ₁ hb
      rw [inferBody_atF] at hF
      have hpure : inferTypeCore env (F + 1) d e = .ok r := hF
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, ?_, hσ₁.2.2.2.1,
        hσ₁.2.2.2.2⟩
      intro d' e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((d, e) : Nat × Expr) == (d', e')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl⟩ : d = d' ∧ e = e' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain rfl : r = r' := by injection hl'
        exact ⟨F + 1, hpure⟩
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.1 d' e' r' hl'

theorem cached_annotate_sim (env : Env) (f : Nat)
    (ih : FnsRel (simRel env) (fueledFns env) (cachedFns env f))
    (d : Nat) (e : Expr) :
    (simRel env).R ((fueledFns env).annotate d e)
      ((cachedFns env (f + 1)).annotate d e) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns env (f + 1)).annotate d e =
    memoE (·.annot) (fun st mp => { st with annot := mp })
      (fun d e => annotateBody (cachedFns env f) env d e) d e from rfl]
    at hrun
  simp only [memoE, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.annot[((d, e) : Nat × Expr)]? with
  | some r =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hF⟩ := hσ.2.2.2.2 d e r hl
    exact ⟨⟨F, hF⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [StateT.bind] at hrun
    cases hb : annotateBody (cachedFns env f) env d e σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok p =>
      obtain ⟨r, σ₁⟩ := p
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hpair := (annotateBody
        (pairFns (fueledFns env) (cachedFns env f) ih) env d e).property
      rw [annotateBody_fst_proj, annotateBody_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ r σ₁ hb
      rw [annotateBody_atF] at hF
      have hpure : annotateCore env (F + 1) d e = .ok r := hF
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, hσ₁.2.2.1, hσ₁.2.2.2.1,
        ?_⟩
      intro d' e' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((d, e) : Nat × Expr) == (d', e')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl⟩ : d = d' ∧ e = e' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        obtain rfl : r = r' := by injection hl'
        exact ⟨F + 1, hpure⟩
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.2.2 d' e' r' hl'

theorem cached_defeq_sim (env : Env) (f : Nat)
    (ih : FnsRel (simRel env) (fueledFns env) (cachedFns env f))
    (d : Nat) (a b : Expr) :
    (simRel env).R ((fueledFns env).defeq d a b)
      ((cachedFns env (f + 1)).defeq d a b) := by
  intro σ hσ v σ' hrun
  rw [show (cachedFns env (f + 1)).defeq d a b =
    memoB (fun d a b => defeqBody (cachedFns env f) env d a b) d a b
      from rfl] at hrun
  simp only [memoB, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind] at hrun
  cases hl : σ.defeq[((d, a, b) : Nat × Expr × Expr)]? with
  | some r =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨F, hF⟩ := hσ.2.2.2.1 d a b r hl
    exact ⟨⟨F, hF⟩, hσ⟩
  | none =>
    rw [hl] at hrun
    dsimp only at hrun
    simp only [StateT.bind] at hrun
    cases hb : defeqBody (cachedFns env f) env d a b σ with
    | error err =>
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind] at hrun
      exact nomatch hrun
    | ok p =>
      obtain ⟨r, σ₁⟩ := p
      rw [hb] at hrun
      simp only [Bind.bind, Except.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, StateT.pure, pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have hpair := (defeqBody
        (pairFns (fueledFns env) (cachedFns env f) ih) env d a b).property
      rw [defeqBody_fst_proj, defeqBody_snd_proj] at hpair
      obtain ⟨⟨F, hF⟩, hσ₁⟩ := hpair σ hσ r σ₁ hb
      rw [defeqBody_atF] at hF
      have hpure : isDefEqCore env (F + 1) d a b = .ok r := hF
      refine ⟨⟨F + 1, hpure⟩, hσ₁.1, hσ₁.2.1, hσ₁.2.2.1, ?_,
        hσ₁.2.2.2.2⟩
      intro d' a' b' r' hl'
      simp only at hl'
      rw [Std.HashMap.getElem?_insert] at hl'
      by_cases hk : ((d, a, b) : Nat × Expr × Expr) == (d', a', b')
      · rw [if_pos hk] at hl'
        obtain ⟨rfl, rfl, rfl⟩ : d = d' ∧ a = a' ∧ b = b' := by
          have := eq_of_beq hk
          exact ⟨congrArg Prod.fst this,
            congrArg (fun p => p.snd.fst) this,
            congrArg (fun p => p.snd.snd) this⟩
        obtain rfl : r = r' := by injection hl'
        exact ⟨F + 1, hpure⟩
      · rw [if_neg hk] at hl'
        exact hσ₁.2.2.2.1 d' a' b' r' hl'

/-- The memoized knot simulates the fueled families at every level. -/
theorem cachedFns_sim (env : Env) :
    ∀ f, FnsRel (simRel env) (fueledFns env) (cachedFns env f)
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e σ hσ v σ' hrun
      exact nomatch hrun
    · intro d e σ hσ v σ' hrun
      exact nomatch hrun
    · intro d e σ hσ v σ' hrun
      exact nomatch hrun
    · intro d a b σ hσ v σ' hrun
      exact nomatch hrun
    · intro d e σ hσ v σ' hrun
      exact nomatch hrun
  | f + 1 =>
    ⟨cached_whnfCore_sim env f (cachedFns_sim env f),
     cached_whnf_sim env f (cachedFns_sim env f),
     cached_infer_sim env f (cachedFns_sim env f),
     cached_defeq_sim env f (cachedFns_sim env f),
     cached_annotate_sim env f (cachedFns_sim env f)⟩

/-! ## From the executable entry points to pure runs at some fuel -/

private theorem run'_inv {α : Type} {c : CheckSM α} {v : α}
    (h : c.run' {} = .ok v) : ∃ σ', c.run {} = .ok (v, σ') := by
  simp only [StateT.run', StateT.run, Functor.map, Except.map] at h
  revert h
  cases hc : c {} with
  | error e => intro h; exact nomatch h
  | ok p =>
    intro h
    obtain ⟨a, σ'⟩ := p
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨σ', by rw [show c.run {} = c {} from rfl, hc, h]⟩

theorem cachedOps_whnf_bridge {env : Env} {d : Nat} {e v : Expr}
    (h : cachedOps.whnf env d e = .ok v) :
    ∃ F, whnf env F d e = .ok v := by
  obtain ⟨σ', hrun⟩ := run'_inv h
  exact ((cachedFns_sim env checkFuel).2.1 d e {} (CacheOK.empty env)
    v σ' hrun).1

theorem cachedOps_inferType_bridge {env : Env} {d : Nat} {e v : Expr}
    (h : cachedOps.inferType env d e = .ok v) :
    ∃ F, inferTypeCore env F d e = .ok v := by
  obtain ⟨σ', hrun⟩ := run'_inv h
  exact ((cachedFns_sim env checkFuel).2.2.1 d e {} (CacheOK.empty env)
    v σ' hrun).1

theorem cachedOps_isDefEq_bridge {env : Env} {d : Nat} {a b : Expr}
    {v : Bool} (h : cachedOps.isDefEq env d a b = .ok v) :
    ∃ F, isDefEqCore env F d a b = .ok v := by
  obtain ⟨σ', hrun⟩ := run'_inv h
  exact ((cachedFns_sim env checkFuel).2.2.2.1 d a b {}
    (CacheOK.empty env) v σ' hrun).1

theorem cachedOps_annotate_bridge {env : Env} {d : Nat} {e v : Expr}
    (h : cachedOps.annotate env d e = .ok v) :
    ∃ F, annotateCore env F d e = .ok v := by
  obtain ⟨σ', hrun⟩ := run'_inv h
  exact ((cachedFns_sim env checkFuel).2.2.2.2 d e {} (CacheOK.empty env)
    v σ' hrun).1

theorem cachedOps_ensureSort_bridge {env : Env} {d : Nat} {e : Expr}
    {u : Level} (h : cachedOps.ensureSort env d e = .ok u) :
    ∃ F, ensureSortCore env F d e = .ok u := by
  obtain ⟨σ', hrun⟩ := run'_inv h
  have hpair := (ensureSort
    (pairFns (fueledFns env) (cachedFns env checkFuel)
      (cachedFns_sim env checkFuel)) env d e).property
  rw [ensureSort_fst_proj, ensureSort_snd_proj] at hpair
  obtain ⟨⟨F, hF⟩, -⟩ := hpair {} (CacheOK.empty env) u σ' hrun
  rw [ensureSort_atF] at hF
  exact ⟨F, hF⟩

end Setlec
