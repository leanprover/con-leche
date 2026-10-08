module

public import ConLeche.Cached.ParInstall
import ConLeche.Cached.KnotCongr
import ConLeche.Cached.BlockOverlay

/-!
# Every install step reads its index only through `find?` (task #329)

The parallel install's workers install every record — blocks, axioms,
basis blocks and the pinned declarations too — at a WORKER VIEW
(`workerView`, `ConLeche/Cached/ParInstall.lean`): an index with no
constants of its own, answering from the frozen base layer, whose
lookups are the serial index's (`ViewAgrees`).  For the commit thread
to add the serial fold's step, the install at the view must BE the
install at the serial index, push for push.  This file proves it:
`checkDeclStepC_twin` — from two indices that answer alike, grow alike
and hold nothing above their counters (`Twin`), the step fails alike
or pushes the same constants onto each.

Two kinds of lemma, bottom-up through the install code:

* **Congruence**: a stage that only READS its index gives the same
  result at two indices with the same `find?`.  The cached operations
  (`sharedOpsC`) ignore the `Env` argument every operation call carries
  (`EnvFree`), so the environments the stages pass along do not matter
  either — every operation call is normalised to `Env.empty`.
* **Pushes**: a stage that extends its index pushes the same list onto
  both (`TwinOut`), and the indices stay twins.

Nothing here is about the model; it is the install code's own
discipline — reads through `find?`, writes by `push` — made a theorem,
and self-contained (the cached checker, `KnotCongr`, `BlockOverlay`),
which is the exception CLAUDE.md makes for a self-contained
verification living with the implementation (the driver carries it).
-/

public section

namespace ConLeche.Cached

open ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Operations that ignore their environment -/

/-- The operations ignore the `Env` argument of every call. -/
structure EnvFree (ops : CheckerOps m) : Prop where
  annotate : ∀ e, ops.annotate e = ops.annotate Env.empty
  inferType : ∀ e, ops.inferType e = ops.inferType Env.empty
  isDefEq : ∀ e, ops.isDefEq e = ops.isDefEq Env.empty
  ensureSort : ∀ e, ops.ensureSort e = ops.ensureSort Env.empty
  whnf : ∀ e, ops.whnf e = ops.whnf Env.empty

theorem sharedOpsC_envFree (mode : CheckMode) (fe : FEnv) : EnvFree (sharedOpsC mode fe) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem sharedOpsRuleR_envFree (mode : CheckMode) (fe : FEnv) :
    EnvFree (sharedOpsRuleR mode fe) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The cached operations read their index through `find?` alone. -/
theorem sharedOpsC_congr {mode : CheckMode} {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    sharedOpsC mode fe₁ = sharedOpsC mode fe₂ := by
  unfold sharedOpsC opE opB opS
  simp only [coreKnotI_congr hfe]

/-! ## Twin indices -/

/-- **Two indices that answer alike and grow alike**: the same
lookups, the same counter, every entry below it and no overlay. -/
structure Twin (fe₁ fe₂ : FEnv) : Prop where
  find : fe₁.find? = fe₂.find?
  vis : fe₁.visibleBelow = fe₂.visibleBelow
  idx₁ : IdxBelow fe₁
  idx₂ : IdxBelow fe₂

theorem Twin.push {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) (ci : ConstantInfo) :
    Twin (fe₁.push ci) (fe₂.push ci) := by
  refine ⟨?_, ?_, h.idx₁.push ci, h.idx₂.push ci⟩
  · funext n
    rw [h.idx₁.find?_push, h.idx₂.find?_push, h.find]
  · show fe₁.visibleBelow + 1 = fe₂.visibleBelow + 1
    rw [h.vis]

theorem Twin.pushAll {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) :
    ∀ L : List ConstantInfo, Twin (FEnv.pushAll L fe₁) (FEnv.pushAll L fe₂)
  | [] => h
  | ci :: L => Twin.pushAll (h.push ci) L

theorem FEnv.pushAll_append :
    ∀ (L L' : List ConstantInfo) (fe : FEnv),
      FEnv.pushAll L' (FEnv.pushAll L fe) = FEnv.pushAll (L ++ L') fe
  | [], _, _ => rfl
  | ci :: L, L', fe => FEnv.pushAll_append L L' (fe.push ci)

/-! ## Read-only guards over the index -/

theorem constsResolveF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    ∀ e : Expr, e.constsResolveF fe₁ = e.constsResolveF fe₂
  | .bvar _ | .sort _ => rfl
  | .lit (.natVal _) | .lit (.strVal _) | .const _ _ => by
    simp only [Expr.constsResolveF, hfe]
  | .fvar _ ty => by simp only [Expr.constsResolveF, constsResolveF_congr hfe ty]
  | .app f a => by
    simp only [Expr.constsResolveF, constsResolveF_congr hfe f, constsResolveF_congr hfe a]
  | .lam ty b _ | .forallE ty b _ => by
    simp only [Expr.constsResolveF, constsResolveF_congr hfe ty, constsResolveF_congr hfe b]
  | .letE ty v b => by
    simp only [Expr.constsResolveF, constsResolveF_congr hfe ty, constsResolveF_congr hfe v,
      constsResolveF_congr hfe b]
  | .proj s _ e => by simp only [Expr.constsResolveF, hfe, constsResolveF_congr hfe e]

theorem constsResolveF_congr' {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    (fun e : Expr => e.constsResolveF fe₁) = (fun e => e.constsResolveF fe₂) :=
  funext (constsResolveF_congr hfe)

theorem natOpGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    natOpGuardF fe₁ c = natOpGuardF fe₂ c := by
  simp only [natOpGuardF, natLitSupportedF_congr hfe, hfe]

theorem natOpCodF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) (e : Expr) :
    natOpCodF fe₁ c e = natOpCodF fe₂ c e := by
  simp only [natOpCodF, hfe]

theorem natOpTyPinnedF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name)
    (ty : Expr) : natOpTyPinnedF fe₁ c ty = natOpTyPinnedF fe₂ c ty := by
  unfold natOpTyPinnedF
  split <;> split <;> simp only [natOpCodF_congr hfe]

theorem natOpStoredOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (n : Name) :
    natOpStoredOkF fe₁ n = natOpStoredOkF fe₂ n := by
  unfold natOpStoredOkF
  rw [hfe]
  split <;> simp only [natOpTyPinnedF_congr hfe]

theorem natOpStoredOkF_congr' {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    natOpStoredOkF fe₁ = natOpStoredOkF fe₂ :=
  funext (natOpStoredOkF_congr hfe)

theorem stdAxiomOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (cv : ConstantVal) :
    stdAxiomOkF fe₁ cv = stdAxiomOkF fe₂ cv := by
  simp only [stdAxiomOkF, hfe]

theorem trustCompilerOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : trustCompilerOkF fe₁ cv = trustCompilerOkF fe₂ cv := by
  simp only [trustCompilerOkF, hfe]

theorem reduceStoredOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    reduceStoredOkF fe₁ c = reduceStoredOkF fe₂ c := by
  simp only [reduceStoredOkF, hfe]

theorem reduceElemOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    reduceElemOkF fe₁ c = reduceElemOkF fe₂ c := by
  simp only [reduceElemOkF, hfe]

theorem ofReduceAxOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : ofReduceAxOkF fe₁ cv = ofReduceAxOkF fe₂ cv := by
  simp only [ofReduceAxOkF, hfe, reduceElemOkF_congr hfe, reduceStoredOkF_congr hfe]

theorem reducePinGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    reducePinGuardF fe₁ c = reducePinGuardF fe₂ c := by
  simp only [reducePinGuardF, constsResolveF_congr hfe]

theorem divModEnvGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    divModEnvGuardF fe₁ c = divModEnvGuardF fe₂ c := by
  simp only [divModEnvGuardF, natOpGuardF_congr hfe, natOpStoredOkF_congr' hfe, hfe]

theorem divModCertGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name)
    (annVal : Expr) (hyps : List Expr) (eqE proof : Expr) :
    divModCertGuardF fe₁ c annVal hyps eqE proof = divModCertGuardF fe₂ c annVal hyps eqE proof := by
  simp only [divModCertGuardF, constsResolveF_congr hfe]

theorem divModPinGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (ps : NatOpPinSet) (c : Name) : divModPinGuardF ps fe₁ c = divModPinGuardF ps fe₂ c := by
  simp only [divModPinGuardF, constsResolveF_congr hfe]

theorem divModCertsGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (ps : NatOpPinSet) (c : Name) (annVal : Expr) :
    divModCertsGuardF ps fe₁ c annVal = divModCertsGuardF ps fe₂ c annVal := by
  simp only [divModCertsGuardF, divModCertGuardF_congr hfe]

/-! ## The declaration checker's mirrors over the index -/

section Mirrors

variable {ops : CheckerOps m}

theorem checkConstantValF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (cv : ConstantVal) :
    checkConstantValF ops fe₁ cv = checkConstantValF ops fe₂ cv := by
  unfold checkConstantValF
  simp only [h.annotate fe₁.env, h.annotate fe₂.env, h.inferType fe₁.env, h.inferType fe₂.env,
    h.ensureSort fe₁.env, h.ensureSort fe₂.env, hfe, constsResolveF_congr hfe]

omit [MonadExceptOf CheckError m] in
theorem checkDivModCertsF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : Name) (annVal : Expr) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      checkDivModCertsF ops fe₁ c annVal stmts proofs =
        checkDivModCertsF ops fe₂ c annVal stmts proofs
  | [], [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    have ih := checkDivModCertsF_congr h hfe c annVal srest prest
    unfold checkDivModCertsF
    simp only [h.annotate fe₁.env, h.annotate fe₂.env, h.inferType fe₁.env,
      h.inferType fe₂.env, h.isDefEq fe₁.env, h.isDefEq fe₂.env,
      divModCertGuardF_congr hfe]
    rw [ih]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

omit [MonadExceptOf CheckError m] in
theorem checkDivModPinAtF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : Name) (value' : Expr) (ps : NatOpPinSet) :
    checkDivModPinAtF ops fe₁ c value' ps = checkDivModPinAtF ops fe₂ c value' ps := by
  unfold checkDivModPinAtF
  simp only [h.annotate fe₁.env, h.annotate fe₂.env, h.isDefEq fe₁.env, h.isDefEq fe₂.env,
    checkDivModCertsF_congr h hfe]

theorem checkDivModPinLoopF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : Name) (value' : Expr) :
    ∀ (pins : List NatOpPinSet) (tried : List String),
      checkDivModPinLoopF ops fe₁ c value' pins tried =
        checkDivModPinLoopF ops fe₂ c value' pins tried
  | [], _ => rfl
  | ps :: rest, tried => by
    unfold checkDivModPinLoopF
    simp only [divModPinGuardF_congr hfe, divModCertsGuardF_congr hfe,
      checkDivModPinAtF_congr h hfe, checkDivModPinLoopF_congr h hfe c value' rest]

theorem checkDivModPinF_congr (h : EnvFree ops) {fe₁ fe₂ fe₁' fe₂' : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (hfe' : fe₁'.find? = fe₂'.find?)
    (pins : List NatOpPinSet) (c : Name) :
    checkDivModPinF ops pins fe₁ fe₁' c = checkDivModPinF ops pins fe₂ fe₂' c := by
  unfold checkDivModPinF
  simp only [divModEnvGuardF_congr hfe', hfe', checkDivModPinLoopF_congr h hfe]

theorem checkReducePinF_congr (h : EnvFree ops) {fe₁ fe₂ fe₁' fe₂' : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (hfe' : fe₁'.find? = fe₂'.find?) (c : Name) (value : Expr) :
    checkReducePinF ops fe₁ fe₁' c value = checkReducePinF ops fe₂ fe₂' c value := by
  unfold checkReducePinF
  simp only [reduceStoredOkF_congr hfe', reduceElemOkF_congr hfe, reducePinGuardF_congr hfe,
    h.annotate fe₁.env, h.annotate fe₂.env, h.isDefEq fe₁.env, h.isDefEq fe₂.env]

omit [MonadExceptOf CheckError m] in
theorem certifyNatEqs_envFree (h : EnvFree ops) (env : Env) :
    ∀ eqs : List (Expr × Expr), certifyNatEqs ops env eqs = certifyNatEqs ops Env.empty eqs
  | [] => rfl
  | eq :: rest => by
    unfold certifyNatEqs
    simp only [h.isDefEq env, certifyNatEqs_envFree h env rest]

end Mirrors

/-! ## Two runs, related

`RelRun R x₁ x₂`: from every state the two actions fail with the same
error, or both succeed into the same state with results related by `R`.
The walker below steps through two clauses that are the same but for
their `pure` leaves (after the reads of one have been rewritten into
the other's), which is what a stage looks like at two twin indices. -/

/-- The two runs fail alike or end in the same state with related
results. -/
def RelRun {α : Type} (R : α → α → Prop) (x₁ x₂ : CheckCM α) : Prop :=
  ∀ s, (∃ e, x₁ s = .error e ∧ x₂ s = .error e) ∨
    (∃ a₁ a₂ s', x₁ s = .ok (a₁, s') ∧ x₂ s = .ok (a₂, s') ∧ R a₁ a₂)

theorem RelRun.of_eq {α : Type} {x : CheckCM α} : RelRun Eq x x := by
  intro s
  cases h : x s with
  | error e => exact .inl ⟨e, rfl, rfl⟩
  | ok p => exact .inr ⟨p.1, p.1, p.2, rfl, rfl, rfl⟩

theorem RelRun.pure {α : Type} {R : α → α → Prop} {a₁ a₂ : α} (h : R a₁ a₂) :
    RelRun R (Pure.pure a₁) (Pure.pure a₂) :=
  fun s => .inr ⟨a₁, a₂, s, rfl, rfl, h⟩

theorem RelRun.ofThrow {α : Type} {R : α → α → Prop} {e : CheckError} :
    RelRun R (throw e : CheckCM α) (throw e) :=
  fun _ => .inl ⟨e, rfl, rfl⟩

/-- The bind rule: related bound actions, related continuations. -/
theorem RelRun.bind {α β : Type} {R : α → α → Prop} {R' : β → β → Prop}
    {x₁ x₂ : CheckCM α} {k₁ k₂ : α → CheckCM β} (hx : RelRun R x₁ x₂)
    (hk : ∀ a₁ a₂, R a₁ a₂ → RelRun R' (k₁ a₁) (k₂ a₂)) :
    RelRun R' (x₁ >>= k₁) (x₂ >>= k₂) := by
  intro s
  have h₁ : (x₁ >>= k₁) s = (x₁ s).bind (fun v => k₁ v.1 v.2) := rfl
  have h₂ : (x₂ >>= k₂) s = (x₂ s).bind (fun v => k₂ v.1 v.2) := rfl
  rw [h₁, h₂]
  rcases hx s with ⟨e, he₁, he₂⟩ | ⟨a₁, a₂, s', ha₁, ha₂, hR⟩
  · rw [he₁, he₂]; exact .inl ⟨e, rfl, rfl⟩
  · rw [ha₁, ha₂]; exact hk a₁ a₂ hR s'

/-- The bind rule at a shared bound action. -/
theorem RelRun.bind_same {α β : Type} {R' : β → β → Prop}
    {x : CheckCM α} {k₁ k₂ : α → CheckCM β} (hk : ∀ a, RelRun R' (k₁ a) (k₂ a)) :
    RelRun R' (x >>= k₁) (x >>= k₂) :=
  RelRun.bind RelRun.of_eq fun a₁ _a₂ h => h ▸ hk a₁

theorem RelRun.ofThrowBind {α β : Type} {R : β → β → Prop} {e : CheckError}
    {k₁ k₂ : α → CheckCM β} : RelRun R ((throw e : CheckCM α) >>= k₁) (throw e >>= k₂) :=
  fun _ => .inl ⟨e, rfl, rfl⟩

theorem RelRun.dite {α : Type} {R : α → α → Prop} {c : Prop} {d : Decidable c}
    {a₁ a₂ : ¬c → CheckCM α} {b₁ b₂ : c → CheckCM α}
    (ha : ∀ h, RelRun R (a₁ h) (a₂ h)) (hb : ∀ h, RelRun R (b₁ h) (b₂ h)) :
    RelRun R (@dite _ c d b₁ a₁) (@dite _ c d b₂ a₂) := by
  by_cases h : c
  · rw [dite_eq_left h, dite_eq_left h]; exact hb h
  · rw [dite_eq_right h, dite_eq_right h]; exact ha h

theorem RelRun.ite {α : Type} {R : α → α → Prop} {c : Prop} {d : Decidable c}
    {t₁ t₂ e₁ e₂ : CheckCM α}
    (ht : c → RelRun R t₁ t₂) (he : ¬c → RelRun R e₁ e₂) :
    RelRun R (@ite _ c d t₁ e₁) (@ite _ c d t₂ e₂) := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ht h
  · rw [ite_eq_right h, ite_eq_right h]; exact he h

/-- The clause walker over two runs that differ only in their leaves
(`with_reducible`, as `yields`). -/
syntax "relrun_step" : tactic
macro_rules
  | `(tactic| relrun_step) => `(tactic|
      first
        | with_reducible exact RelRun.ofThrowBind
        | ((with_reducible apply RelRun.bind_same); intro)
        | with_reducible exact RelRun.ofThrow
        | ((with_reducible apply RelRun.ite) <;> intro)
        | ((with_reducible apply RelRun.dite) <;> intro)
        | split)

syntax "relrun" : tactic
macro_rules
  | `(tactic| relrun) =>
      `(tactic| all_goals (first | (relrun_step; relrun) | skip))

/-- Two indices pushed the same constants onto twin bases. -/
def PushedFrom (fe₁ fe₂ : FEnv) (a₁ a₂ : FEnv) : Prop :=
  ∃ L, a₁ = FEnv.pushAll L fe₁ ∧ a₂ = FEnv.pushAll L fe₂

theorem PushedFrom.refl (fe₁ fe₂ : FEnv) : PushedFrom fe₁ fe₂ fe₁ fe₂ := ⟨[], rfl, rfl⟩

theorem PushedFrom.push (fe₁ fe₂ : FEnv) (ci : ConstantInfo) :
    PushedFrom fe₁ fe₂ (fe₁.push ci) (fe₂.push ci) := ⟨[ci], rfl, rfl⟩

theorem PushedFrom.trans {fe₁ fe₂ a₁ a₂ b₁ b₂ : FEnv} (h : PushedFrom fe₁ fe₂ a₁ a₂)
    (h' : PushedFrom a₁ a₂ b₁ b₂) : PushedFrom fe₁ fe₂ b₁ b₂ := by
  obtain ⟨L, rfl, rfl⟩ := h
  obtain ⟨L', rfl, rfl⟩ := h'
  exact ⟨L ++ L', FEnv.pushAll_append _ _ _, FEnv.pushAll_append _ _ _⟩

theorem PushedFrom.twin {fe₁ fe₂ a₁ a₂ : FEnv} (ht : Twin fe₁ fe₂)
    (h : PushedFrom fe₁ fe₂ a₁ a₂) : Twin a₁ a₂ := by
  obtain ⟨L, rfl, rfl⟩ := h
  exact ht.pushAll L

/-! ## The cached declaration stages -/

section Cached

variable {mode : CheckMode}

theorem opSIxC_congr' {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    opSIxC mode fe₁ = opSIxC mode fe₂ := opSIxC_congr hfe

theorem checkConstantValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : checkConstantValC mode fe₁ cv = checkConstantValC mode fe₂ cv := by
  unfold checkConstantValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe, opSIxC_congr hfe, hfe]

theorem checkDefnValC_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (cvA : ConstantVal)
    (jty value : Expr) (hint : ReducibilityHint) :
    RelRun (PushedFrom fe₁ fe₂) (checkDefnValC mode fe₁ cvA jty value hint)
      (checkDefnValC mode fe₂ cvA jty value hint) := by
  unfold checkDefnValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]
  relrun
  all_goals exact RelRun.pure (PushedFrom.push _ _ _)

theorem checkOpaqueValC_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (cvA : ConstantVal)
    (jty value : Expr) :
    RelRun (PushedFrom fe₁ fe₂) (checkOpaqueValC mode fe₁ cvA jty value)
      (checkOpaqueValC mode fe₂ cvA jty value) := by
  unfold checkOpaqueValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]
  relrun
  all_goals exact RelRun.pure (PushedFrom.push _ _ _)

theorem installBasisDeclF_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (ci : ConstantInfo) :
    RelRun (PushedFrom fe₁ fe₂) (installBasisDeclF fe₁ ci) (installBasisDeclF fe₂ ci) := by
  unfold installBasisDeclF
  simp only [hfe]
  relrun
  all_goals exact RelRun.pure (PushedFrom.push _ _ _)

end Cached

/-! ## Stages that only pass their environment to the operations

Normal forms: at `EnvFree` operations the `Env` argument is irrelevant,
so every such stage is stated equal to its run at `Env.empty`. -/

section EnvNormal

variable {ops : CheckerOps m}

theorem whnfTelescope_env (h : EnvFree ops) (env : Env) :
    ∀ i n e, whnfTelescope ops env i n e = whnfTelescope ops Env.empty i n e
  | i, 0, e => by unfold whnfTelescope; simp only [h.whnf env]
  | i, n + 1, e => by
    unfold whnfTelescope
    simp only [h.whnf env, whnfTelescope_env h env (i + 1) n]

theorem checkStructFieldSortsI_env (h : EnvFree ops) (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsI ops env isProp large s nP fvs idxArgs j =
      checkStructFieldSortsI ops Env.empty isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    have ih := checkStructFieldSortsI_env h env isProp large s nP fvs idxArgs j
    unfold checkStructFieldSortsI
    simp only [h.inferType env, h.ensureSort env]
    rw [ih]

theorem checkAbsCtorSorts_env (h : EnvFree ops) (env : Env) (ctx : NestCtx) :
    ∀ cs os, checkAbsCtorSorts ops env ctx cs os = checkAbsCtorSorts ops Env.empty ctx cs os
  | c :: cs, o :: os => by
    have ih := checkAbsCtorSorts_env h env ctx cs os
    unfold checkAbsCtorSorts
    simp only [checkStructFieldSortsI_env h env]
    rw [ih]
  | [], _ => by unfold checkAbsCtorSorts; rfl
  | _ :: _, [] => by unfold checkAbsCtorSorts; rfl

theorem checkAbsCtorSortsAll_env (h : EnvFree ops) (env : Env) (ctx : NestCtx) :
    ∀ css oss, checkAbsCtorSortsAll ops env ctx css oss =
      checkAbsCtorSortsAll ops Env.empty ctx css oss
  | cs :: css, os :: oss => by
    have ih := checkAbsCtorSortsAll_env h env ctx css oss
    unfold checkAbsCtorSortsAll
    simp only [checkAbsCtorSorts_env h env]
    rw [ih]
  | [], _ => by unfold checkAbsCtorSortsAll; rfl
  | _ :: _, [] => by unfold checkAbsCtorSortsAll; rfl

theorem nestCtors_env (h : EnvFree ops) (ctx : NestCtx) (env : Env)
    (rec : Expr → List NestHole → Nat → Nat → Expr → NestState →
      m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name)
    (holes : List Expr) :
    ∀ cs st, nestCtors ctx ops env rec prog hi us ds names holes cs st =
      nestCtors ctx ops Env.empty rec prog hi us ds names holes cs st
  | [], _ => rfl
  | (cv, nF) :: cs, st => by
    unfold nestCtors
    simp only [h.inferType env, h.ensureSort env, nestCtors_env h ctx env rec prog hi us ds names
      holes cs]

theorem nestFrame_env (h : EnvFree ops) (ctx : NestCtx) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) :
    nestFrame ctx ops env rec prog hi us ds nPc grp st =
      nestFrame ctx ops Env.empty rec prog hi us ds nPc grp st := by
  unfold nestFrame
  simp only [h.inferType env, nestCtors_env h ctx env]

theorem nestContNew_env (h : EnvFree ops) (ctx : NestCtx) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) :
    nestContNew ctx ops env rec prog kb n us ds nPc cty st =
      nestContNew ctx ops Env.empty rec prog kb n us ds nPc cty st := by
  unfold nestContNew
  simp only [nestFrame_env h ctx env]

theorem nestContKey_env (h : EnvFree ops) (ctx : NestCtx) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (cty : Expr) (st : NestState) :
    nestContKey ctx ops env rec prog kb n us ds nPc cty st =
      nestContKey ctx ops Env.empty rec prog kb n us ds nPc cty st := by
  unfold nestContKey
  simp only [nestContNew_env h ctx env]

theorem nestCont_env (h : EnvFree ops) (ctx : NestCtx) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    (st : NestState) :
    nestCont ctx ops env rec prog kb n us args st =
      nestCont ctx ops Env.empty rec prog kb n us args st := by
  unfold nestCont
  simp only [nestContKey_env h ctx env]

theorem nestPos_env (h : EnvFree ops) (env : Env) (ctx : NestCtx) :
    ∀ F, nestPos ops env ctx F = nestPos ops Env.empty ctx F
  | 0 => by funext prog dep kb e st; rfl
  | F + 1 => by
    have ih := nestPos_env h env ctx F
    funext prog dep kb e st
    unfold nestPos
    simp only [h.whnf env, nestCont_env h ctx env, ih]

theorem nestRoot_env (h : EnvFree ops) (env : Env) (ctx : NestCtx) (holes : List Expr) :
    ∀ css st, nestRoot ops env ctx holes css st = nestRoot ops Env.empty ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    have ih := nestRoot_env h env ctx holes css
    unfold nestRoot
    simp only [nestCtors_env h ctx env, nestPos_env h env ctx, ih]

theorem nestSeeds_env (h : EnvFree ops) (env : Env) (ctx : NestCtx) :
    ∀ ks st, nestSeeds ops env ctx ks st = nestSeeds ops Env.empty ctx ks st
  | [], _ => rfl
  | (key, nPc) :: ks, st => by
    have ih := nestSeeds_env h env ctx ks
    unfold nestSeeds
    simp only [nestContKey_env h ctx env, nestPos_env h env ctx, ih]

theorem checkBlockPositivity_env (h : EnvFree ops) (env : Env)
    (find? : Name → Option ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    checkBlockPositivity ops env find? p cvTas ctorsAs =
      checkBlockPositivity ops Env.empty find? p cvTas ctorsAs := by
  unfold checkBlockPositivity
  simp only [nestRoot_env h env, checkAbsCtorSortsAll_env h env]

end EnvNormal

/-! ## The recursor stage's reads -/

section RecStage

variable {ops : CheckerOps m}

omit [MonadExceptOf CheckError m] in
theorem targetParamsDefEq_env (h : EnvFree ops) (env : Env) (d : Nat) (absM : Expr → Expr)
    (pfvs : List Expr) :
    ∀ as bs, targetParamsDefEq ops env d absM pfvs as bs =
      targetParamsDefEq ops Env.empty d absM pfvs as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    have ih := targetParamsDefEq_env h env d absM pfvs as bs
    unfold targetParamsDefEq
    simp only [h.inferType env, h.isDefEq env, ih]
  | [], _ :: _ => by unfold targetParamsDefEq; rfl
  | _ :: _, [] => by unfold targetParamsDefEq; rfl

omit [MonadExceptOf CheckError m] in
theorem targetClassMatch_env (h : EnvFree ops) (env : Env) (p : BlockShape)
    (formerTys pfvs : List Expr) (us : List Level) (ds : List Expr) (lvls : List Level)
    (eds : List Expr) :
    targetClassMatch ops env p formerTys pfvs us ds lvls eds =
      targetClassMatch ops Env.empty p formerTys pfvs us ds lvls eds := by
  unfold targetClassMatch
  simp only [targetParamsDefEq_env h env]

omit [MonadExceptOf CheckError m] in
theorem targetMajorNfs_env (h : EnvFree ops) (env : Env) (p : BlockShape)
    (formerTys pfvs : List Expr) (us : List Level) (ds : List Expr)
    (ctors : List (ConstantVal × Nat)) :
    ∀ es, targetMajorNfs ops env p formerTys pfvs us ds ctors es =
      targetMajorNfs ops Env.empty p formerTys pfvs us ds ctors es
  | [] => rfl
  | e :: es => by
    have ih := targetMajorNfs_env h env p formerTys pfvs us ds ctors es
    unfold targetMajorNfs
    simp only [targetClassMatch_env h env, ih]

omit [MonadExceptOf CheckError m] in
theorem targetPinTys_env (h : EnvFree ops) (env : Env) (d : Nat) :
    ∀ xs, targetPinTys ops env d xs = targetPinTys ops Env.empty d xs
  | [] => rfl
  | x :: xs => by
    have ih := targetPinTys_env h env d xs
    unfold targetPinTys
    simp only [h.inferType env, ih]

omit [MonadExceptOf CheckError m] in
theorem targetMajorPins_env (h : EnvFree ops) (env : Env) (rP : Nat) (M : TargetMajor) :
    targetMajorPins ops env rP M = targetMajorPins ops Env.empty rP M := by
  unfold targetMajorPins
  simp only [targetPinTys_env h env, h.inferType env]

omit [MonadExceptOf CheckError m] in
theorem targetK53_env (h : EnvFree ops) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (majDom f : Expr) :
    targetK53 ops env p formerTys Mc tele majDom f =
      targetK53 ops Env.empty p formerTys Mc tele majDom f := by
  unfold targetK53
  simp only [targetClassMatch_env h env]

theorem classNodesAgree_env (h : EnvFree ops) (env : Env) (p : BlockShape)
    (formerTys : List Expr) (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (leaf : Expr)
    (fvs : List Expr) (i : Nat) (ctor : Name) :
    ∀ es, classNodesAgree ops env p formerTys Mc tele leaf fvs i ctor es =
      classNodesAgree ops Env.empty p formerTys Mc tele leaf fvs i ctor es
  | [] => rfl
  | e :: es => by
    have ih := classNodesAgree_env h env p formerTys Mc tele leaf fvs i ctor es
    unfold classNodesAgree
    simp only [targetK53_env h env, ih]

theorem classFieldsAgree_env (h : EnvFree ops) (env : Env) (p : BlockShape)
    (formerTys : List Expr) (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name)
    (E : List NestCtorNf) :
    ∀ i ks, classFieldsAgree ops env p formerTys Ms fvs ctor E i ks =
      classFieldsAgree ops Env.empty p formerTys Ms fvs ctor E i ks
  | _, [] => rfl
  | i, .ordinary :: ks => by
    unfold classFieldsAgree
    exact classFieldsAgree_env h env p formerTys Ms fvs ctor E (i + 1) ks
  | i, .recursive t tele :: ks => by
    have ih := classFieldsAgree_env h env p formerTys Ms fvs ctor E (i + 1) ks
    unfold classFieldsAgree
    simp only [classNodesAgree_env h env, ih]

theorem classCtorOf_env (h : EnvFree ops) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (cA : ConstantVal × Nat) :
    classCtorOf ops env p formerTys rd Ms c cA = classCtorOf ops Env.empty p formerTys rd Ms c cA := by
  unfold classCtorOf
  simp only [classFieldsAgree_env h env]

theorem classCtorsOf_env (h : EnvFree ops) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) :
    ∀ cs, classCtorsOf ops env p formerTys rd Ms c cs =
      classCtorsOf ops Env.empty p formerTys rd Ms c cs
  | [] => rfl
  | cA :: cs => by
    have ih := classCtorsOf_env h env p formerTys rd Ms c cs
    unfold classCtorsOf
    simp only [classCtorOf_env h env, ih]

theorem classesCtors_env (h : EnvFree ops) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) :
    ∀ c Ms', classesCtors ops env p formerTys rd Ms c Ms' =
      classesCtors ops Env.empty p formerTys rd Ms c Ms'
  | _, [] => rfl
  | c, M :: rest => by
    have ih := classesCtors_env h env p formerTys rd Ms (c + 1) rest
    unfold classesCtors
    simp only [classCtorsOf_env h env, ih]

omit [MonadExceptOf CheckError m] in
theorem classesNfs_env (h : EnvFree ops) (env : Env) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) :
    ∀ Ms, classesNfs ops env p formerTys tbl Ms = classesNfs ops Env.empty p formerTys tbl Ms
  | [] => rfl
  | M :: Ms => by
    have ih := classesNfs_env h env p formerTys tbl Ms
    unfold classesNfs
    simp only [targetMajorNfs_env h env, ih]

theorem classKeyOf_env (h : EnvFree ops) (env : Env) (nP : Nat) (params : List Expr)
    (k : ClassKey) : classKeyOf ops env nP params k = classKeyOf ops Env.empty nP params k := by
  unfold classKeyOf
  simp only [h.annotate env]

theorem classKeyOf_env' (h : EnvFree ops) (env : Env) (nP : Nat) (params : List Expr) :
    classKeyOf ops env nP params = classKeyOf ops Env.empty nP params :=
  funext (classKeyOf_env h env nP params)

theorem targetCtorsOf_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (I : Name) :
    targetCtorsOf fe₁ I = targetCtorsOf fe₂ I := by
  simp only [targetCtorsOf, hfe]

theorem targetOutsideInst_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (I : Name)
    (us : List Level) (ds : List Expr) :
    (targetOutsideInst fe₁ I us ds : m (Nat × Level)) = targetOutsideInst fe₂ I us ds := by
  simp only [targetOutsideInst, hfe]

theorem targetMajorOf_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) :
    (targetMajorOf fe₁ p ctorsAs pfvs fvs mty : m TargetMajor) =
      targetMajorOf fe₂ p ctorsAs pfvs fvs mty := by
  unfold targetMajorOf
  simp only [targetCtorsOf_congr hfe, targetOutsideInst_congr hfe]

theorem classMajors_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (p : BlockShape) (ctorsAs : List (List (ConstantVal × Nat))) (pfvs : List Expr) :
    ∀ keys, classMajors ops fe₁ p ctorsAs pfvs keys = classMajors ops fe₂ p ctorsAs pfvs keys
  | [] => rfl
  | key :: keys => by
    have ih := classMajors_congr h hfe p ctorsAs pfvs keys
    unfold classMajors
    simp only [targetMajorOf_congr hfe, targetMajorPins_env h fe₁.env,
      targetMajorPins_env h fe₂.env, ih]

theorem classNPcOf_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (p : BlockShape) :
    classNPcOf p fe₁ = classNPcOf p fe₂ := by
  funext I
  simp only [classNPcOf, hfe]

theorem checkBlockClasses_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (env₁ env₂ : Env) (p : BlockShape) (params : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    checkBlockClasses ops fe₁ env₁ p params ctorsAs =
      checkBlockClasses ops fe₂ env₂ p params ctorsAs := by
  unfold checkBlockClasses
  simp only [classNPcOf_congr hfe, classKeyOf_env' h env₁, classKeyOf_env' h env₂,
    classMajors_congr h hfe]

theorem classFormerTy_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cvTas : List ConstantVal) (M : TargetMajor) :
    (classFormerTy fe₁ cvTas M : m Expr) = classFormerTy fe₂ cvTas M := by
  simp only [classFormerTy, hfe]

theorem classFormerTy_congr' {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cvTas : List ConstantVal) :
    (classFormerTy fe₁ cvTas : TargetMajor → m Expr) = classFormerTy fe₂ cvTas :=
  funext (classFormerTy_congr hfe cvTas)

theorem classConstOk_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : classConstOk ops fe₁ cv = classConstOk ops fe₂ cv := by
  unfold classConstOk
  simp only [hfe, constsResolveF_congr hfe, h.inferType fe₁.env, h.inferType fe₂.env,
    h.ensureSort fe₁.env, h.ensureSort fe₂.env]

theorem classRecTyOk_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (g : ClassGen) (k : Nat) (rc : RecShape) (cvRi : ConstantVal) (c : Nat) :
    classRecTyOk ops fe₁ g k rc cvRi c = classRecTyOk ops fe₂ g k rc cvRi c := by
  unfold classRecTyOk
  simp only [classConstOk_congr h hfe, h.isDefEq fe₁.env, h.isDefEq fe₂.env]

theorem classRecTysOk_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (g : ClassGen) (k : Nat) :
    ∀ rcs cvs cs, classRecTysOk ops fe₁ g k rcs cvs cs = classRecTysOk ops fe₂ g k rcs cvs cs
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    have ih := classRecTysOk_congr h hfe g k rcs cvs cs
    unfold classRecTysOk
    simp only [classRecTyOk_congr h hfe, ih]
  | [], _, _ => by unfold classRecTysOk; rfl
  | _ :: _, [], _ => by unfold classRecTysOk; rfl
  | _ :: _, _ :: _, [] => by unfold classRecTysOk; rfl

theorem classStreamRecs_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    ∀ rcs, classStreamRecs ops fe₁ rcs = classStreamRecs ops fe₂ rcs
  | [] => rfl
  | rc :: rcs => by
    have ih := classStreamRecs_congr h hfe rcs
    unfold classStreamRecs
    simp only [checkConstantValF_congr h hfe, ih]

end RecStage

/-! ## The install stages over the index (the `F` mirrors) -/

section FStages

variable {ops : CheckerOps m}

theorem checkStructDomsAtF_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (off : Nat)
    (fvs doms : List Expr) :
    ∀ j, checkStructDomsAtF ops fe₁ off fvs doms j = checkStructDomsAtF ops fe₂ off fvs doms j
  | 0 => rfl
  | j + 1 => by
    have ih := checkStructDomsAtF_congr h fe₁ fe₂ off fvs doms j
    unfold checkStructDomsAtF
    simp only [h.isDefEq fe₁.env, h.isDefEq fe₂.env]
    rw [ih]

theorem checkStructDomsAtFA_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (off : Nat)
    (fvs doms : Array Expr) :
    ∀ j, checkStructDomsAtFA ops fe₁ off fvs doms j = checkStructDomsAtFA ops fe₂ off fvs doms j
  | 0 => rfl
  | j + 1 => by
    have ih := checkStructDomsAtFA_congr h fe₁ fe₂ off fvs doms j
    unfold checkStructDomsAtFA
    simp only [h.isDefEq fe₁.env, h.isDefEq fe₂.env]
    rw [ih]

theorem checkBlockDomsAtF_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (off : Nat)
    (fvs doms : List Expr) :
    ∀ j, checkBlockDomsAtF ops fe₁ off fvs doms j = checkBlockDomsAtF ops fe₂ off fvs doms j
  | 0 => rfl
  | j + 1 => by
    have ih := checkBlockDomsAtF_congr h fe₁ fe₂ off fvs doms j
    unfold checkBlockDomsAtF
    simp only [h.isDefEq fe₁.env, h.isDefEq fe₂.env]
    rw [ih]

theorem checkStructFieldSortsIF_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (isProp large : Bool)
    (sl : Level) (nP : Nat) (fvs idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsIF ops fe₁ isProp large sl nP fvs idxArgs j =
      checkStructFieldSortsIF ops fe₂ isProp large sl nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    have ih := checkStructFieldSortsIF_congr h fe₁ fe₂ isProp large sl nP fvs idxArgs j
    unfold checkStructFieldSortsIF
    simp only [h.inferType fe₁.env, h.inferType fe₂.env, h.ensureSort fe₁.env,
      h.ensureSort fe₂.env]
    rw [ih]

theorem checkStructFieldSortsIFA_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (isProp large : Bool)
    (sl : Level) (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) :
    ∀ j, checkStructFieldSortsIFA ops fe₁ isProp large sl nP fvs idxArgs j =
      checkStructFieldSortsIFA ops fe₂ isProp large sl nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    have ih := checkStructFieldSortsIFA_congr h fe₁ fe₂ isProp large sl nP fvs idxArgs j
    unfold checkStructFieldSortsIFA
    simp only [h.inferType fe₁.env, h.inferType fe₂.env, h.ensureSort fe₁.env,
      h.ensureSort fe₂.env]
    rw [ih]

theorem checkSumTeleF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkSumTeleF ops fe₁ cv n cvTa₀ = checkSumTeleF ops fe₂ cv n cvTa₀ := by
  unfold checkSumTeleF
  simp only [whnfTelescope_env h fe₁.env, whnfTelescope_env h fe₂.env,
    checkConstantValF_congr h hfe]

theorem checkBlockTeleF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (nP : Nat) (ms : MemberShape) :
    checkBlockTeleF ops fe₁ nP ms = checkBlockTeleF ops fe₂ nP ms := by
  unfold checkBlockTeleF
  simp only [checkConstantValF_congr h hfe, checkSumTeleF_congr h hfe]

theorem checkBlockTelesF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (nP : Nat) : ∀ ms, checkBlockTelesF ops fe₁ nP ms = checkBlockTelesF ops fe₂ nP ms
  | [] => rfl
  | ms :: rest => by
    have ih := checkBlockTelesF_congr h hfe nP rest
    unfold checkBlockTelesF
    simp only [checkBlockTeleF_congr h hfe, ih]

theorem checkBlockAgreeF_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (nP : Nat)
    (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs, checkBlockAgreeF ops fe₁ nP cvTa0 s0 cvs = checkBlockAgreeF ops fe₂ nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, sl) :: rest => by
    have ih := checkBlockAgreeF_congr h fe₁ fe₂ nP cvTa0 s0 rest
    unfold checkBlockAgreeF
    simp only [checkBlockDomsAtF_congr h fe₁ fe₂, ih]

theorem checkSumCtorF_congr (h : EnvFree ops) {fe₀₁ fe₀₂ fe₁ fe₂ : FEnv}
    (hfe₀ : fe₀₁.find? = fe₀₂.find?) (hfe : fe₁.find? = fe₂.find?) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    checkSumCtorF ops fe₀₁ fe₁ T lps nP nIdx resSort isProp large cvC nF cvTa =
      checkSumCtorF ops fe₀₂ fe₂ T lps nP nIdx resSort isProp large cvC nF cvTa := by
  unfold checkSumCtorF
  simp only [checkConstantValF_congr h hfe, checkStructDomsAtFA_congr h fe₁ fe₂,
    constsResolveF_congr hfe₀, checkStructFieldSortsIFA_congr h fe₁ fe₂]

theorem checkSumCtorsF_congr (h : EnvFree ops) {fe₀₁ fe₀₂ fe₁ fe₂ : FEnv}
    (hfe₀ : fe₀₁.find? = fe₀₂.find?) (hfe : fe₁.find? = fe₂.find?) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    ∀ cs, checkSumCtorsF ops fe₀₁ fe₁ T lps nP nIdx resSort isProp large cvTa cs =
      checkSumCtorsF ops fe₀₂ fe₂ T lps nP nIdx resSort isProp large cvTa cs
  | [] => rfl
  | c :: cs => by
    have ih := checkSumCtorsF_congr h hfe₀ hfe T lps nP nIdx resSort isProp large cvTa cs
    unfold checkSumCtorsF
    simp only [checkSumCtorF_congr h hfe₀ hfe, ih]

theorem checkBlockCtorsF_congr (h : EnvFree ops) {fe₀₁ fe₀₂ fe₁ fe₂ : FEnv}
    (hfe₀ : fe₀₁.find? = fe₀₂.find?) (hfe : fe₁.find? = fe₂.find?) (p : BlockShape) :
    ∀ xs, checkBlockCtorsF ops fe₀₁ fe₁ p xs = checkBlockCtorsF ops fe₀₂ fe₂ p xs
  | [] => rfl
  | (ms, cvTa) :: rest => by
    have ih := checkBlockCtorsF_congr h hfe₀ hfe p rest
    unfold checkBlockCtorsF
    simp only [checkSumCtorsF_congr h hfe₀ hfe, ih]

theorem checkBlockIdxSortsF_congr (h : EnvFree ops) (fe₁ fe₂ : FEnv) (p : BlockShape) :
    ∀ xs, checkBlockIdxSortsF ops fe₁ p xs = checkBlockIdxSortsF ops fe₂ p xs
  | [] => rfl
  | (ms, cvTa) :: rest => by
    have ih := checkBlockIdxSortsF_congr h fe₁ fe₂ p rest
    unfold checkBlockIdxSortsF
    simp only [checkStructFieldSortsIF_congr h fe₁ fe₂, ih]

end FStages

/-! ## The pushes, as lists -/

theorem consBlockIndsF_eq_pushAll (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvTas : List ConstantVal) (i : Nat) (fe : FEnv),
      ∃ L, consBlockIndsF p₁ isRec cvTas i fe = FEnv.pushAll L fe ∧
        ∀ fe', consBlockIndsF p₁ isRec cvTas i fe' = FEnv.pushAll L fe'
  | [], _, _ => ⟨[], rfl, fun _ => rfl⟩
  | cvTa :: rest, i, fe => by
    obtain ⟨L, -, hL⟩ := consBlockIndsF_eq_pushAll p₁ isRec rest (i + 1)
      (fe.push (.indInfo cvTa (blockCapsAt p₁ i isRec)))
    exact ⟨.indInfo cvTa (blockCapsAt p₁ i isRec) :: L, hL _, fun fe' => hL _⟩

theorem consSumCtorsF_eq_pushAll (nP : Nat) :
    ∀ (cs : List (ConstantVal × Nat)),
      ∃ L, ∀ fe, consSumCtorsF nP cs fe = FEnv.pushAll L fe
  | [] => ⟨[], fun _ => rfl⟩
  | c :: cs => by
    obtain ⟨L, hL⟩ := consSumCtorsF_eq_pushAll nP cs
    exact ⟨.ctorInfo c.1 nP c.2 :: L, fun fe => hL _⟩

theorem consBlockCtorsF_eq_pushAll (nP : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))),
      ∃ L, ∀ fe, consBlockCtorsF nP css fe = FEnv.pushAll L fe
  | [] => ⟨[], fun _ => rfl⟩
  | cs :: css => by
    obtain ⟨L₁, h₁⟩ := consSumCtorsF_eq_pushAll nP cs
    obtain ⟨L₂, h₂⟩ := consBlockCtorsF_eq_pushAll nP css
    exact ⟨L₁ ++ L₂, fun fe => by
      show consBlockCtorsF nP css (consSumCtorsF nP cs fe) = _
      rw [h₁, h₂, FEnv.pushAll_append]⟩

/-! ## The rule stage and the recursor stage -/

section Rules

variable {ops : CheckerOps m} {w : StructWalkers}

theorem classRuleOk_twin (h : EnvFree ops) {feT₁ feT₂ feR₁ feR₂ : FEnv}
    (hT : w.resolve feT₁ = w.resolve feT₂) (hR : w.resolve feR₁ = w.resolve feR₂)
    (cvR : ConstantVal) (pw : PropWhen) (n : Nat) (gen : Expr) :
    classRuleOk ops w feT₁ feR₁ cvR pw n gen = classRuleOk ops w feT₂ feR₂ cvR pw n gen := by
  unfold classRuleOk
  simp only [hT, hR, h.inferType feR₁.env, h.inferType feR₂.env]

theorem classRulesOk_twin (h : EnvFree ops) {feT₁ feT₂ feR₁ feR₂ : FEnv}
    (hT : w.resolve feT₁ = w.resolve feT₂) (hR : w.resolve feR₁ = w.resolve feR₂)
    (g : ClassGen) (recOf : Nat → Option Name) (cvR : ConstantVal) (pw : PropWhen) (c : Nat) :
    ∀ xs, classRulesOk ops w feT₁ feR₁ g recOf cvR pw c xs =
      classRulesOk ops w feT₂ feR₂ g recOf cvR pw c xs
  | [] => rfl
  | x :: xs => by
    have ih := classRulesOk_twin h hT hR g recOf cvR pw c xs
    unfold classRulesOk
    simp only [classRuleOk_twin h hT hR, ih]

theorem classRecsRulesOk_twin (h : EnvFree ops) {feT₁ feT₂ feR₁ feR₂ : FEnv}
    (hT : w.resolve feT₁ = w.resolve feT₂) (hR : w.resolve feR₁ = w.resolve feR₂)
    (g : ClassGen) (recOf : Nat → Option Name) (pw : PropWhen) :
    ∀ cvs cs, classRecsRulesOk ops w feT₁ feR₁ g recOf pw cvs cs =
      classRecsRulesOk ops w feT₂ feR₂ g recOf pw cvs cs
  | cvG :: cvs, c :: cs => by
    have ih := classRecsRulesOk_twin h hT hR g recOf pw cvs cs
    unfold classRecsRulesOk
    simp only [classRulesOk_twin h hT hR, ih]
  | [], _ => by unfold classRecsRulesOk; rfl
  | _ :: _, [] => by unfold classRecsRulesOk; rfl

end Rules

section RecStageC

variable {mode : CheckMode}

theorem classFeR_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    Twin (classFeR p Ms cvGs recCls fe₁) (classFeR p Ms cvGs recCls fe₂) := by
  unfold classFeR
  rw [consBlockRecsBareF_eq_pushAll, consBlockRecsBareF_eq_pushAll]
  exact ht.pushAll _

/-- **The recursor stage at twin indices is the same stage.** -/
theorem genRecCheck_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead)
    (Ms : List TargetMajor) (cvTas : List ConstantVal) (block : List ConstantInfo) :
    genRecCheck (shadowOpsC mode) fe₁ p nestedBit params tbl rd Ms cvTas block =
      genRecCheck (shadowOpsC mode) fe₂ p nestedBit params tbl rd Ms cvTas block := by
  have hfe := ht.find
  have key : ∀ (Ms' : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat)
      (g : ClassGen) (recOf : Nat → Option Name) (pw : PropWhen),
      classRecsRulesOk ((shadowOpsC mode).opsRuleR (classFeR p Ms' cvGs recCls fe₁))
          (shadowOpsC mode).walkers fe₁ (classFeR p Ms' cvGs recCls fe₁) g recOf pw cvGs recCls
        = classRecsRulesOk ((shadowOpsC mode).opsRuleR (classFeR p Ms' cvGs recCls fe₂))
          (shadowOpsC mode).walkers fe₂ (classFeR p Ms' cvGs recCls fe₂) g recOf pw
          cvGs recCls := by
    intro Ms' cvGs recCls g recOf pw
    have hR := (classFeR_twin ht p Ms' cvGs recCls).find
    show classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe₁ _ g recOf pw cvGs recCls
      = classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe₂ _ g recOf pw cvGs recCls
    rw [sharedOpsRuleR_congr mode hR]
    exact classRecsRulesOk_twin (sharedOpsRuleR_envFree mode _)
      (constsResolveFC_congr hfe) (constsResolveFC_congr hR) g recOf pw cvGs recCls
  have hops : (shadowOpsC mode).opsAt fe₁ = sharedOpsC mode fe₂ := sharedOpsC_congr hfe
  have hops₂ : (shadowOpsC mode).opsAt fe₂ = sharedOpsC mode fe₂ := rfl
  unfold genRecCheck
  simp only [key, hops, hops₂, classStreamRecs_congr (sharedOpsC_envFree mode fe₂) hfe,
    classesNfs_env (sharedOpsC_envFree mode fe₂) fe₁.env,
    classesNfs_env (sharedOpsC_envFree mode fe₂) fe₂.env,
    classesCtors_env (sharedOpsC_envFree mode fe₂) fe₁.env,
    classesCtors_env (sharedOpsC_envFree mode fe₂) fe₂.env,
    classFormerTy_congr' hfe, classRecTysOk_congr (sharedOpsC_envFree mode fe₂) hfe]

theorem blockRecInfosTF_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (p : BlockShape)
    (k : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) :
    blockRecInfosTF fe₁.find? (·.constsResolveF fe₁) p k out =
      blockRecInfosTF fe₂.find? (·.constsResolveF fe₂) p k out := by
  rw [hfe, constsResolveF_congr' hfe]

end RecStageC

/-! ## The block install, push for push -/

section Blocks

variable {mode : CheckMode}

theorem RelRun.mono {α : Type} {R R' : α → α → Prop} {x₁ x₂ : CheckCM α}
    (h : RelRun R x₁ x₂) (hR : ∀ a₁ a₂, R a₁ a₂ → R' a₁ a₂) : RelRun R' x₁ x₂ := by
  intro s
  rcases h s with ⟨e, h₁, h₂⟩ | ⟨a₁, a₂, s', h₁, h₂, hr⟩
  · exact .inl ⟨e, h₁, h₂⟩
  · exact .inr ⟨a₁, a₂, s', h₁, h₂, hR a₁ a₂ hr⟩

/-- Chaining FEnv-producing runs: the second at the first's results. -/
theorem RelRun.bind_push {β : Type} {R' : β → β → Prop} {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    {x₁ x₂ : CheckCM FEnv} {k₁ k₂ : FEnv → CheckCM β}
    (hx : RelRun (PushedFrom fe₁ fe₂) x₁ x₂)
    (hk : ∀ L, Twin (FEnv.pushAll L fe₁) (FEnv.pushAll L fe₂) →
      RelRun R' (k₁ (FEnv.pushAll L fe₁)) (k₂ (FEnv.pushAll L fe₂))) :
    RelRun R' (x₁ >>= k₁) (x₂ >>= k₂) :=
  RelRun.bind hx fun _ _ ⟨L, h₁, h₂⟩ => h₁ ▸ h₂ ▸ hk L (ht.pushAll L)

theorem checkStructProjTableF_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (T C : Name) (lps : List Name) (nP nF : Nat) (resSort : Level) (guards : List Level)
    (off : Nat) (cvCa : ConstantVal) :
    RelRun (PushedFrom fe₁ fe₂)
      (checkStructProjTableF (m := CheckCM) structWalkersC T C lps nP nF resSort guards off cvCa fe₁)
      (checkStructProjTableF (m := CheckCM) structWalkersC T C lps nP nF resSort guards off cvCa fe₂) := by
  unfold checkStructProjTableF
  have hres : structWalkersC.resolve fe₁ = structWalkersC.resolve fe₂ := constsResolveFC_congr hfe
  simp only [hres, hfe]
  relrun
  all_goals exact RelRun.pure (PushedFrom.push _ _ _)

theorem checkBlockTablesF_twin (p : BlockShape) :
    ∀ (xs : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {fe₁ fe₂ : FEnv},
      Twin fe₁ fe₂ →
      RelRun (PushedFrom fe₁ fe₂)
        (checkBlockTablesF (m := CheckCM) structWalkersC p xs fe₁)
        (checkBlockTablesF (m := CheckCM) structWalkersC p xs fe₂)
  | [], _, _, _ => RelRun.pure (PushedFrom.refl _ _)
  | (ms, ctorsA, sortss) :: rest, fe₁, fe₂, ht => by
    unfold checkBlockTablesF
    have hmid : RelRun (PushedFrom fe₁ fe₂)
        (match ctorsA, sortss with
         | [cA], [sorts] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) structWalkersC ms.cvT.name cA.1.name p.lps p.nP
               cA.2 p.resSort (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe₁
           else pure fe₁
         | _, _ => pure fe₁)
        (match ctorsA, sortss with
         | [cA], [sorts] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) structWalkersC ms.cvT.name cA.1.name p.lps p.nP
               cA.2 p.resSort (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe₂
           else pure fe₂
         | _, _ => pure fe₂) := by
      split
      · split
        · exact checkStructProjTableF_twin ht.find _ _ _ _ _ _ _ _ _
        · exact RelRun.pure (PushedFrom.refl _ _)
      · exact RelRun.pure (PushedFrom.refl _ _)
    refine RelRun.bind_push ht hmid fun L htL => ?_
    exact RelRun.mono (checkBlockTablesF_twin p rest htL) fun _ _ h =>
      PushedFrom.trans ⟨L, rfl, rfl⟩ h

/-- The relation of two block passes: the same pass but for its
environment, which is the same pushes onto the twins. -/
def PassRel (fe₁ fe₂ : FEnv) (q₁ q₂ : BlockPass FEnv) : Prop :=
  ∃ L : List ConstantInfo, q₁ = { q₂ with env₁ := FEnv.pushAll L fe₁ } ∧
    q₂.env₁ = FEnv.pushAll L fe₂

theorem consBlockIndsF_pushed (p₁ : BlockShape) (isRec : Bool) (cvTas : List ConstantVal)
    (i : Nat) (fe₁ fe₂ : FEnv) :
    PushedFrom fe₁ fe₂ (consBlockIndsF p₁ isRec cvTas i fe₁) (consBlockIndsF p₁ isRec cvTas i fe₂) := by
  obtain ⟨L, hL, hL'⟩ := consBlockIndsF_eq_pushAll p₁ isRec cvTas i fe₁
  exact ⟨L, hL, hL' fe₂⟩

theorem checkBlockIndsF_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (p : BlockParts)
    (isRec : Bool) :
    RelRun (fun a₁ a₂ => PushedFrom fe₁ fe₂ a₁.1 a₂.1 ∧ a₁.2 = a₂.2)
      (checkBlockIndsF (sharedOpsC mode fe₁) fe₁ p isRec)
      (checkBlockIndsF (sharedOpsC mode fe₂) fe₂ p isRec) := by
  unfold checkBlockIndsF
  have h := sharedOpsC_envFree mode fe₂
  simp only [sharedOpsC_congr hfe, checkBlockTeleF_congr h hfe, checkBlockTelesF_congr h hfe,
    checkBlockAgreeF_congr h fe₁ fe₂]
  relrun
  all_goals exact RelRun.pure ⟨consBlockIndsF_pushed _ _ _ _ _ _, rfl⟩

theorem checkBlockPassS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p₀ : BlockParts)
    (isRec : Bool) :
    RelRun (PassRel fe₁ fe₂) (checkBlockPassS mode fe₁ p₀ isRec)
      (checkBlockPassS mode fe₂ p₀ isRec) := by
  unfold checkBlockPassS
  refine RelRun.bind (checkBlockIndsF_twin ht.find p₀ isRec) ?_
  rintro ⟨a₁, cvTas, p₁⟩ ⟨a₂, cvTas', p₁'⟩ ⟨⟨L, rfl, rfl⟩, he⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have htL := ht.pushAll L
  have h := sharedOpsC_envFree mode (FEnv.pushAll L fe₂)
  simp only [sharedOpsC_congr htL.find, checkBlockCtorsF_congr h htL.find htL.find, htL.find,
    checkBlockClasses_congr h htL.find (FEnv.pushAll L fe₁).env (FEnv.pushAll L fe₂).env,
    checkBlockPositivity_env h (FEnv.pushAll L fe₁).env,
    checkBlockPositivity_env h (FEnv.pushAll L fe₂).env,
    nestSeeds_env h (FEnv.pushAll L fe₁).env, nestSeeds_env h (FEnv.pushAll L fe₂).env]
  relrun
  all_goals exact RelRun.pure ⟨L, rfl, rfl⟩

theorem checkBlockTailS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (block : List ConstantInfo)
    {q₁ q₂ : BlockPass FEnv} (hq : PassRel fe₁ fe₂ q₁ q₂) :
    RelRun (PushedFrom fe₁ fe₂) (checkBlockTailS mode block q₁)
      (checkBlockTailS mode block q₂) := by
  obtain ⟨L, rfl, hq₂⟩ := hq
  obtain ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, params, rd, cls, tbl⟩ := q₂
  simp only at hq₂
  subst hq₂
  rw [checkBlockTailS_eq_ref, checkBlockTailS_eq_ref]
  unfold checkBlockTailSRef
  have htL := ht.pushAll L
  have h := sharedOpsC_envFree mode (FEnv.pushAll L fe₂)
  obtain ⟨L₂, hL₂⟩ := consBlockCtorsF_eq_pushAll p.nP ctorsAs
  have ht₂ : Twin (consBlockCtorsF p.nP ctorsAs (FEnv.pushAll L fe₁))
      (consBlockCtorsF p.nP ctorsAs (FEnv.pushAll L fe₂)) := by
    rw [hL₂, hL₂]; exact htL.pushAll L₂
  simp only [sharedOpsC_congr htL.find, checkBlockIdxSortsF_congr h (FEnv.pushAll L fe₁)
      (FEnv.pushAll L fe₂), genRecCheck_twin ht₂, consBlockRecsTF_eq_fast, consBlockRecsTFFast,
    blockRecInfosTF_twin ht₂.find]
  relrun
  rw [hL₂, hL₂]
  rename_i out
  refine RelRun.mono (checkBlockTablesF_twin _ _ ((htL.pushAll L₂).pushAll _)) fun x₁ x₂ hr => ?_
  obtain ⟨L₃, rfl, rfl⟩ := hr
  exact (((PushedFrom.refl fe₁ fe₂).trans ⟨L, rfl, rfl⟩).trans ⟨L₂, rfl, rfl⟩).trans
    (⟨_, rfl, rfl⟩ : PushedFrom _ _ (FEnv.pushAll _ _) (FEnv.pushAll _ _)) |>.trans ⟨L₃, rfl, rfl⟩

theorem checkBlockKS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (block : List ConstantInfo)
    (p₀ : BlockParts) :
    RelRun (PushedFrom fe₁ fe₂) (checkBlockKS mode fe₁ block p₀)
      (checkBlockKS mode fe₂ block p₀) := by
  unfold checkBlockKS
  relrun
  all_goals
    exact RelRun.bind (checkBlockPassS_twin ht p₀ _) fun _ _ hq => checkBlockTailS_twin ht block hq

end Blocks

/-! ## Every declaration step, push for push -/

section Decls

variable {mode : CheckMode}

theorem RelRun.foldlM_push {α : Type} {f : FEnv → α → CheckCM FEnv}
    (hf : ∀ fe₁ fe₂, Twin fe₁ fe₂ → ∀ a, RelRun (PushedFrom fe₁ fe₂) (f fe₁ a) (f fe₂ a)) :
    ∀ (l : List α) {fe₁ fe₂ : FEnv}, Twin fe₁ fe₂ →
      RelRun (PushedFrom fe₁ fe₂) (l.foldlM f fe₁) (l.foldlM f fe₂)
  | [], _, _, _ => RelRun.pure (PushedFrom.refl _ _)
  | a :: l, fe₁, fe₂, ht => by
    simp only [List.foldlM_cons]
    refine RelRun.bind_push ht (hf fe₁ fe₂ ht a) fun L htL => ?_
    exact RelRun.mono (RelRun.foldlM_push hf l htL) fun _ _ h =>
      PushedFrom.trans ⟨L, rfl, rfl⟩ h

theorem checkBasisDeclC_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (kind : BasisKind) :
    RelRun (PushedFrom fe₁ fe₂) (checkBasisDeclC fe₁ kind) (checkBasisDeclC fe₂ kind) := by
  unfold checkBasisDeclC
  simp only [ht.find]
  relrun
  all_goals exact RelRun.foldlM_push (fun _ _ ht' ci => installBasisDeclF_twin ht'.find ci) _ ht

theorem checkShapelessS_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (block : List ConstantInfo) :
    RelRun (PushedFrom fe₁ fe₂) (checkShapelessS mode fe₁ block) (checkShapelessS mode fe₂ block) := by
  unfold checkShapelessS
  simp only [checkConstantValC_congr hfe]
  relrun

theorem checkThmValC_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (cvA : ConstantVal)
    (jty value : Expr) :
    RelRun (PushedFrom fe₁ fe₂) (checkThmValC mode fe₁ cvA jty value)
      (checkThmValC mode fe₂ cvA jty value) := by
  unfold checkThmValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe, opSIxC_congr hfe]
  relrun
  all_goals exact RelRun.pure (PushedFrom.push _ _ _)

/-- **Every declaration step at twin indices pushes the same constants
onto each, or fails alike.** -/
theorem checkDeclC_twin (pins : List NatOpPinSet) {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (pd : Declaration) :
    RelRun (PushedFrom fe₁ fe₂) (checkDeclC mode pins fe₁ pd) (checkDeclC mode pins fe₂ pd) := by
  have hfe := ht.find
  cases pd with
  | defnDecl cv value hint =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe]
    refine RelRun.bind_same fun r => ?_
    obtain ⟨cvA, jty⟩ := r
    simp only []
    split
    · refine RelRun.bind_push ht (checkDefnValC_twin hfe cvA jty value hint) fun L htL => ?_
      have h := sharedOpsC_envFree mode fe₂
      simp only [natOpGuardF_congr htL.find, natOpStoredOkF_congr' htL.find, htL.find,
        sharedOpsC_congr hfe, certifyNatEqs_envFree h fe₁.env, certifyNatEqs_envFree h fe₂.env,
        checkDivModPinF_congr h hfe htL.find]
      relrun
      all_goals exact RelRun.pure ⟨L, rfl, rfl⟩
    · exact checkDefnValC_twin hfe cvA jty value hint
  | thmDecl cv value =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe]
    refine RelRun.bind_same fun r => ?_
    exact checkThmValC_twin hfe r.1 r.2 value
  | opaqueDecl cv value =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe]
    refine RelRun.bind_same fun r => ?_
    obtain ⟨cvA, jty⟩ := r
    simp only []
    split
    · refine RelRun.bind_push ht (checkOpaqueValC_twin hfe cvA jty value) fun L htL => ?_
      have h := sharedOpsC_envFree mode fe₂
      simp only [sharedOpsC_congr hfe, checkReducePinF_congr h hfe htL.find]
      relrun
      all_goals exact RelRun.pure ⟨L, rfl, rfl⟩
    · exact checkOpaqueValC_twin hfe cvA jty value
  | axiomDecl cv =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe, stdAxiomOkF_congr hfe, trustCompilerOkF_congr hfe,
      ofReduceAxOkF_congr hfe]
    relrun
    all_goals first
      | exact RelRun.pure (PushedFrom.refl _ _)
      | exact RelRun.pure (PushedFrom.push _ _ _)
  | basisDecl kind =>
    unfold checkDeclC
    exact checkBasisDeclC_twin ht kind
  | indDecl block nP =>
    unfold checkDeclC
    dsimp only
    relrun
    all_goals first
      | exact checkBasisDeclC_twin ht _
      | exact checkBlockKS_twin ht block _
      | exact checkShapelessS_twin hfe block
  | quotDecl k cv =>
    unfold checkDeclC
    dsimp only
    relrun
    all_goals first
      | exact checkBasisDeclC_twin ht _
      | exact RelRun.pure (PushedFrom.refl _ _)

theorem checkDeclStepC_twin (pins : List NatOpPinSet) {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (pd : Declaration) :
    RelRun (PushedFrom fe₁ fe₂) (checkDeclStepC mode pins fe₁ pd)
      (checkDeclStepC mode pins fe₂ pd) := by
  unfold checkDeclStepC
  exact RelRun.bind_same fun _ => checkDeclC_twin pins ht pd

end Decls

/-! ## The commit of any record -/

section Commit

variable {mode : CheckMode}

/-- **A record's install at an index**: the constants it pushes, in push
order, with its pending check for a value record — or its error.  At a
worker view (no constants of its own) the pushed constants are its
environment, reversed. -/
def installStep (mode : CheckMode) (pins : List NatOpPinSet) (W : FEnv) (pd : Declaration) :
    Except CheckError (List ConstantInfo × Option ValueGroup) :=
  match valueStep mode W pd with
  | some (.ok (ci, vg)) => .ok ([ci], some vg)
  | some (.error e) => .error e
  | none =>
    match checkDeclStepC mode pins W pd {} with
    | .ok (W', _) => .ok (W'.env.consts.reverse, none)
    | .error e => .error e

theorem pushAll_env_consts :
    ∀ (L : List ConstantInfo) (fe : FEnv),
      (FEnv.pushAll L fe).env.consts = L.reverse ++ fe.env.consts
  | [], _ => rfl
  | ci :: L, fe => by
    show (FEnv.pushAll L (fe.push ci)).env.consts = _
    rw [pushAll_env_consts L (fe.push ci)]
    simp [FEnv.push]

theorem IdxBelow.ofWorkerView (B : BaseIdx) (S : Slots) (v : Nat) :
    IdxBelow (workerView B S v) :=
  ⟨rfl, fun n c ci h => by simp [ConLeche.Cached.workerView] at h⟩

theorem Twin.ofViewAgrees {B : BaseIdx} {S : Slots} {fe : FEnv} (hag : ViewAgrees B S fe)
    (hidx : IdxBelow fe) : Twin fe (workerView B S fe.visibleBelow) :=
  ⟨(funext hag).symm, rfl, hidx, IdxBelow.ofWorkerView B S _⟩

/-- Where `valueStep` has no verdict, phase A's step is the ordinary step. -/
theorem annotStepC_of_valueStep_none {pins : List NatOpPinSet} {i : Nat} {fe W : FEnv}
    {pend : Array PendingCheck} {pd : Declaration} (h : valueStep mode W pd = none) :
    annotStepC mode pins i fe pend pd = (checkDeclStepC mode pins fe pd >>= fun fe' =>
      pure (fe', pend)) := by
  cases pd with
  | defnDecl cv value hint =>
    by_cases hnat : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = true
    · unfold annotStepC
      dsimp only
      rw [ite_eq_left hnat]
    · unfold valueStep at h
      dsimp only at h
      rw [ite_eq_right hnat] at h
      exact nomatch h
  | thmDecl cv value => exact nomatch h
  | opaqueDecl cv value =>
    by_cases hred : reduceOpNames.contains cv.name = true
    · unfold annotStepC
      dsimp only
      rw [ite_eq_left hred]
    · unfold valueStep at h
      dsimp only at h
      rw [ite_eq_right hred] at h
      exact nomatch h
  | axiomDecl _ => rfl
  | basisDecl _ => rfl
  | quotDecl _ _ => rfl
  | indDecl _ _ => rfl

/-- The pending checks after a record: its check recorded, for a value
record. -/
def pushPending (pend : Array PendingCheck) (i v : Nat) : Option ValueGroup → Array PendingCheck
  | some vg => pend.push ⟨vg, i, v⟩
  | none => pend

/-- **The commit step of any record**: a record installed at the view
whose lookups are the serial index's is the serial fold's step — the
same constants pushed, the same pending check. -/
theorem installStep_commit {pins : List NatOpPinSet} {B : BaseIdx} {S : Slots} {i : Nat}
    {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {L : List ConstantInfo}
    {vg? : Option ValueGroup} (hag : ViewAgrees B S fe) (hidx : IdxBelow fe)
    (hand : andPinOk pd = true)
    (h : installStep mode pins (workerView B S fe.visibleBelow) pd = .ok (L, vg?)) :
    annotDeclStep mode pins (i, fe, pend) pd =
      .ok (i + 1, FEnv.pushAll L fe, pushPending pend i fe.visibleBelow vg?) := by
  unfold installStep at h
  split at h
  · rename_i ci vg hv
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact valueStep_commit hag hand hv
  · exact nomatch h
  · rename_i hv
    have hs := annotStepC_of_valueStep_none (pins := pins) (i := i) (fe := fe) (pend := pend) hv
    have ht := Twin.ofViewAgrees hag hidx
    split at h
    · rename_i W' s' hW
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases checkDeclStepC_twin pins ht pd {} with ⟨e, h₁, h₂⟩ | ⟨a₁, a₂, s'', h₁, h₂, L', ha₁, ha₂⟩
      · rw [h₂] at hW; exact nomatch hW
      · rw [h₂] at hW
        simp only [Except.ok.injEq, Prod.mk.injEq] at hW
        obtain ⟨rfl, rfl⟩ := hW
        have hL : (FEnv.pushAll L' (workerView B S fe.visibleBelow)).env.consts.reverse = L' := by
          rw [pushAll_env_consts]; simp [workerView]
        rw [ha₂, hL]
        unfold annotDeclStep
        simp only [hand, ↓reduceIte, hs]
        show (match (checkDeclStepC mode pins fe pd {}).bind
            (fun v => (pure (v.1, pend) : CheckCM _) v.2) with
          | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
          | .error e => .error (e, i)) = _
        rw [h₁, ha₁]
        rfl
    · exact nomatch h

/-- A failing install is the serial step's failure. -/
theorem installStep_commit_error {pins : List NatOpPinSet} {B : BaseIdx} {S : Slots} {i : Nat}
    {fe : FEnv} {pend : Array PendingCheck} {pd : Declaration} {e : CheckError}
    (hag : ViewAgrees B S fe) (hidx : IdxBelow fe) (hand : andPinOk pd = true)
    (h : installStep mode pins (workerView B S fe.visibleBelow) pd = .error e) :
    annotDeclStep mode pins (i, fe, pend) pd = .error (e, i) := by
  unfold installStep at h
  split at h
  · exact nomatch h
  · rename_i e' hv
    cases h
    exact valueStep_commit_error hag hand hv
  · rename_i hv
    have hs := annotStepC_of_valueStep_none (pins := pins) (i := i) (fe := fe) (pend := pend) hv
    have ht := Twin.ofViewAgrees hag hidx
    split at h
    · exact nomatch h
    · rename_i e' hW
      cases h
      rcases checkDeclStepC_twin pins ht pd {} with ⟨e'', h₁, h₂⟩ | ⟨a₁, a₂, s'', h₁, h₂, -⟩
      · rw [h₂] at hW
        cases hW
        unfold annotDeclStep
        simp only [hand, ↓reduceIte, hs]
        show (match (checkDeclStepC mode pins fe pd {}).bind
            (fun v => (pure (v.1, pend) : CheckCM _) v.2) with
          | .ok ((fe', pend'), _) => Except.ok (i + 1, fe', pend')
          | .error e => .error (e, i)) = _
        rw [h₁]
        rfl
      · rw [h₂] at hW; exact nomatch hW

end Commit

end ConLeche.Cached
