module

public import ConLeche.Verify.Cached.ParInstall
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.Cached.PinOverlay
import ConLeche.Verify.Cached.BlockOverlay

/-!
# Every install step reads its index only through `find?` (task #329)

The parallel install's workers install every record — blocks, axioms,
basis blocks and the pinned declarations too — at a WORKER VIEW
(`workerView`, `ConLeche/Verify/Cached/ParInstall.lean`): an index with no
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
and self-contained: it imports the cached checker, `KnotCongr` and
`BlockOverlay`, and nothing from the theory.  During task #329 this
file sat in the `Cached` tier, because the then-implementation driver
(`Main.lean`) could not import `Verify/*` (CLAUDE.md's exception for a
self-contained verification living with the implementation); the
maintainer's 2026-10-08 ruling lets the driver (`ConLeche/Driver/*`,
`Main.lean`) import `Verify/*`, so the file moved back to where a
proof about kernel functions that needs no model belongs.  `pushPending`
stays defined here too, next to the theorems it is about — the driver (now
`ConLeche/Driver/ParInstall.lean`) runs it, which the ruling makes as
straightforward as running anything else this file exports.
-/

public section

namespace ConLeche.Cached

open ConLeche

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-! ## Operations that ignore their environment -/

/-- The operations ignore the `Env` argument of every call. -/
structure EnvFree (ops : CheckerOps m) : Prop where
  inferType : ∀ e, ops.inferType e = ops.inferType Env.empty
  isDefEq : ∀ e, ops.isDefEq e = ops.isDefEq Env.empty
  ensureSort : ∀ e, ops.ensureSort e = ops.ensureSort Env.empty
  whnf : ∀ e, ops.whnf e = ops.whnf Env.empty

theorem sharedOpsC_envFree (mode : CheckMode) (fe : FEnv) : EnvFree (sharedOpsC mode fe) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem sharedOpsRuleR_envFree (mode : CheckMode) (fe : FEnv) :
    EnvFree (sharedOpsRuleR mode fe) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## Twin indices -/

/-- **Two indices that answer alike and grow alike**: the same
lookups — of constants, and of tables before the constant gate
(`FEnv.rawTable?`) — the same counter, every entry below it and no
overlay. -/
structure Twin (fe₁ fe₂ : FEnv) : Prop where
  find : fe₁.find? = fe₂.find?
  raw : fe₁.rawTable? = fe₂.rawTable?
  vis : fe₁.visibleBelow = fe₂.visibleBelow
  idx₁ : IdxBelow fe₁
  idx₂ : IdxBelow fe₂

/-- Twins answer every table lookup alike. -/
theorem Twin.findTable {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) :
    fe₁.findTable? = fe₂.findTable? := by
  funext T
  unfold FEnv.findTable?
  rw [h.find, h.raw]

theorem Twin.push {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) (ci : ConstantInfo) :
    Twin (fe₁.push ci) (fe₂.push ci) := by
  refine ⟨?_, h.raw, ?_, h.idx₁.push ci, h.idx₂.push ci⟩
  · funext n
    rw [h.idx₁.find?_push, h.idx₂.find?_push, h.find]
  · show fe₁.visibleBelow + 1 = fe₂.visibleBelow + 1
    rw [h.vis]

theorem Twin.pushTable {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) (t : ProjTable) :
    Twin (fe₁.pushTable t) (fe₂.pushTable t) := by
  refine ⟨h.find, ?_, h.vis, h.idx₁.pushTable t, h.idx₂.pushTable t⟩
  funext T
  rw [FEnv.rawTable?_pushTable, FEnv.rawTable?_pushTable, h.raw]

theorem Twin.pushTables :
    ∀ (Q : List ProjTable) {fe₁ fe₂ : FEnv}, Twin fe₁ fe₂ →
      Twin (FEnv.pushTables Q fe₁) (FEnv.pushTables Q fe₂)
  | [], _, _, h => h
  | t :: Q, _, _, h => Twin.pushTables Q (h.pushTable t)

theorem Twin.pushAll {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) :
    ∀ L : List ConstantInfo, Twin (FEnv.pushAll L fe₁) (FEnv.pushAll L fe₂)
  | [] => h
  | ci :: L => Twin.pushAll (h.push ci) L

theorem FEnv.pushAll_append :
    ∀ (L L' : List ConstantInfo) (fe : FEnv),
      FEnv.pushAll L' (FEnv.pushAll L fe) = FEnv.pushAll (L ++ L') fe
  | [], _, _ => rfl
  | ci :: L, L', fe => FEnv.pushAll_append L L' (fe.push ci)

theorem FEnv.pushTables_append :
    ∀ (Q Q' : List ProjTable) (fe : FEnv),
      FEnv.pushTables Q' (FEnv.pushTables Q fe) = FEnv.pushTables (Q ++ Q') fe
  | [], _, _ => rfl
  | t :: Q, Q', fe => FEnv.pushTables_append Q Q' (fe.pushTable t)

/-- A constant push and a table install commute: they touch different
components. -/
theorem FEnv.pushAll_pushTable :
    ∀ (L : List ConstantInfo) (fe : FEnv) (t : ProjTable),
      FEnv.pushAll L (fe.pushTable t) = (FEnv.pushAll L fe).pushTable t
  | [], _, _ => rfl
  | ci :: L, fe, t => FEnv.pushAll_pushTable L (fe.push ci) t

theorem FEnv.pushAll_pushTables (L : List ConstantInfo) :
    ∀ (Q : List ProjTable) (fe : FEnv),
      FEnv.pushAll L (FEnv.pushTables Q fe) = FEnv.pushTables Q (FEnv.pushAll L fe)
  | [], _ => rfl
  | t :: Q, fe => by
    show FEnv.pushAll L (FEnv.pushTables Q (fe.pushTable t)) = _
    rw [FEnv.pushAll_pushTables L Q, FEnv.pushAll_pushTable]
    rfl

theorem FEnv.pushDelta_append (L L' : List ConstantInfo) (Q Q' : List ProjTable) (fe : FEnv) :
    FEnv.pushDelta L' Q' (FEnv.pushDelta L Q fe) = FEnv.pushDelta (L ++ L') (Q ++ Q') fe := by
  unfold FEnv.pushDelta
  rw [FEnv.pushAll_pushTables, FEnv.pushAll_append, FEnv.pushTables_append]

theorem IdxBelow.pushDelta {fe : FEnv} (h : IdxBelow fe) (L : List ConstantInfo)
    (Q : List ProjTable) : IdxBelow (FEnv.pushDelta L Q fe) :=
  IdxBelow.pushTables Q (h.pushAll L)

theorem FEnv.visibleBelow_pushDelta (L : List ConstantInfo) (Q : List ProjTable) (fe : FEnv) :
    (FEnv.pushDelta L Q fe).visibleBelow = fe.visibleBelow + L.length := by
  unfold FEnv.pushDelta
  rw [FEnv.visibleBelow_pushTables, pushAll_visibleBelow]

theorem Twin.pushDelta {fe₁ fe₂ : FEnv} (h : Twin fe₁ fe₂) (L : List ConstantInfo)
    (Q : List ProjTable) : Twin (FEnv.pushDelta L Q fe₁) (FEnv.pushDelta L Q fe₂) :=
  Twin.pushTables Q (h.pushAll L)

/-! ## Read-only guards over the index -/

theorem stdAxiomOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (cv : ConstantVal) :
    stdAxiomOkF fe₁ cv = stdAxiomOkF fe₂ cv := by
  simp only [stdAxiomOkF, hfe]

theorem trustCompilerOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : trustCompilerOkF fe₁ cv = trustCompilerOkF fe₂ cv := by
  simp only [trustCompilerOkF, hfe]

theorem reduceElemOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    reduceElemOkF fe₁ c = reduceElemOkF fe₂ c := by
  simp only [reduceElemOkF, hfe]

theorem ofReduceAxOkF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (cv : ConstantVal) : ofReduceAxOkF fe₁ cv = ofReduceAxOkF fe₂ cv := by
  simp only [ofReduceAxOkF, hfe, reduceElemOkF_congr hfe, reduceStoredOkF_congr hfe]

theorem reducePinGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name) :
    reducePinGuardF fe₁ c = reducePinGuardF fe₂ c := by
  simp only [reducePinGuardF, constsResolveF_congr hfe]

theorem divModCertGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (c : Name)
    (annVal : Expr) (hyps : List Expr) (eqE proof : Expr) :
    divModCertGuardF fe₁ c annVal hyps eqE proof = divModCertGuardF fe₂ c annVal hyps eqE proof := by
  simp only [divModCertGuardF, constsResolveF_congr hfe]

theorem typePinStoredF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) (n : Name) :
    typePinStoredF fe₁ n = typePinStoredF fe₂ n := by
  simp only [typePinStoredF, hfe]

theorem divModPinGuardF_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (ps : NatOpPinSet) (c : Name) : divModPinGuardF ps fe₁ c = divModPinGuardF ps fe₂ c := by
  simp only [divModPinGuardF, constsResolveF_congr hfe, hfe, typePinStoredF_congr hfe]

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
  simp only [h.inferType fe₁.env, h.inferType fe₂.env,
    h.ensureSort fe₁.env, h.ensureSort fe₂.env, hfe, constsResolveF_congr hfe,
    strLitSupportedF_congr hfe]

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
    simp only [h.inferType fe₁.env,
      h.inferType fe₂.env, h.isDefEq fe₁.env, h.isDefEq fe₂.env,
      divModCertGuardF_congr hfe]
    rw [ih]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

omit [MonadExceptOf CheckError m] in
theorem checkTypePinsF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) :
    ∀ (tps : List (Name × Expr)), checkTypePinsF ops fe₁ tps = checkTypePinsF ops fe₂ tps
  | [] => rfl
  | p :: rest => by
    have ih := checkTypePinsF_congr h hfe rest
    unfold checkTypePinsF
    simp only [h.isDefEq fe₁.env, h.isDefEq fe₂.env, typePinStoredF_congr hfe]
    rw [ih]

omit [MonadExceptOf CheckError m] in
theorem checkDivModPinAtF_congr (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hfe : fe₁.find? = fe₂.find?) (c : Name) (value' : Expr) (ps : NatOpPinSet) :
    checkDivModPinAtF ops fe₁ c value' ps = checkDivModPinAtF ops fe₂ c value' ps := by
  unfold checkDivModPinAtF
  simp only [h.isDefEq fe₁.env, h.isDefEq fe₂.env, checkDivModCertsF_congr h hfe,
    checkTypePinsF_congr h hfe]

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
    h.isDefEq fe₁.env, h.isDefEq fe₂.env]

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
@[expose] def RelRun {α : Type} (R : α → α → Prop) (x₁ x₂ : CheckCM α) : Prop :=
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

/-- Two indices pushed the same constants and installed the same tables
onto twin bases. -/
@[expose] def PushedFrom (fe₁ fe₂ : FEnv) (a₁ a₂ : FEnv) : Prop :=
  ∃ L Q, a₁ = FEnv.pushDelta L Q fe₁ ∧ a₂ = FEnv.pushDelta L Q fe₂

theorem PushedFrom.refl (fe₁ fe₂ : FEnv) : PushedFrom fe₁ fe₂ fe₁ fe₂ := ⟨[], [], rfl, rfl⟩

theorem PushedFrom.push (fe₁ fe₂ : FEnv) (ci : ConstantInfo) :
    PushedFrom fe₁ fe₂ (fe₁.push ci) (fe₂.push ci) := ⟨[ci], [], rfl, rfl⟩

theorem PushedFrom.pushAll (fe₁ fe₂ : FEnv) (L : List ConstantInfo) :
    PushedFrom fe₁ fe₂ (FEnv.pushAll L fe₁) (FEnv.pushAll L fe₂) := ⟨L, [], rfl, rfl⟩

theorem PushedFrom.pushTable (fe₁ fe₂ : FEnv) (t : ProjTable) :
    PushedFrom fe₁ fe₂ (fe₁.pushTable t) (fe₂.pushTable t) := ⟨[], [t], rfl, rfl⟩

theorem PushedFrom.trans {fe₁ fe₂ a₁ a₂ b₁ b₂ : FEnv} (h : PushedFrom fe₁ fe₂ a₁ a₂)
    (h' : PushedFrom a₁ a₂ b₁ b₂) : PushedFrom fe₁ fe₂ b₁ b₂ := by
  obtain ⟨L, Q, rfl, rfl⟩ := h
  obtain ⟨L', Q', rfl, rfl⟩ := h'
  exact ⟨L ++ L', Q ++ Q', FEnv.pushDelta_append _ _ _ _ _, FEnv.pushDelta_append _ _ _ _ _⟩

/-! ## The cached declaration stages -/

section Cached

variable {mode : CheckMode}

theorem checkConstantValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?)
    (cv : ConstantVal) : checkConstantValC mode fe₁ cv = checkConstantValC mode fe₂ cv := by
  unfold checkConstantValC
  simp only [coreKnotI_congr hfe htb, constsResolveFC_congr hfe, opSIxC_congr hfe htb, hfe,
    strLitSupportedF_congr hfe]

/-- A definition's value check reads its index only through `find?`. -/
theorem checkDefnValCI_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) :
    checkDefnValCI mode fe₁ cv value hint = checkDefnValCI mode fe₂ cv value hint := by
  unfold checkDefnValCI
  simp only [coreKnotI_congr hfe htb, constsResolveFC_congr hfe, strLitSupportedF_congr hfe]

/-- An opaque's value check reads its index only through `find?`. -/
theorem checkOpaqueValCI_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (cv : ConstantVal)
    (value : Expr) :
    checkOpaqueValCI mode fe₁ cv value = checkOpaqueValCI mode fe₂ cv value := by
  unfold checkOpaqueValCI
  simp only [coreKnotI_congr hfe htb, constsResolveFC_congr hfe, strLitSupportedF_congr hfe]

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
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr) :
    targetK53 ops env p formerTys Mc tele majDom f =
      targetK53 ops Env.empty p formerTys Mc tele majDom f := by
  unfold targetK53
  simp only [targetClassMatch_env h env]

theorem classNodesAgree_env (h : EnvFree ops) (env : Env) (p : BlockShape)
    (formerTys : List Expr) (Mc : TargetMajor) (tele : List Expr) (leaf : Expr)
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
    (hfe : fe₁.find? = fe₂.find?) (p : BlockShape) (params : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    checkBlockClasses ops fe₁ p params ctorsAs =
      checkBlockClasses ops fe₂ p params ctorsAs := by
  unfold checkBlockClasses
  simp only [classNPcOf_congr hfe, classMajors_congr h hfe]

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
  unfold classRecTyOk classRecTyCheck
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
    (cvR : ConstantVal) (n : Nat) (gen : Expr) :
    classRuleOk ops w feT₁ feR₁ cvR n gen = classRuleOk ops w feT₂ feR₂ cvR n gen := by
  unfold classRuleOk classRuleCheck
  simp only [hT, hR, h.inferType feR₁.env, h.inferType feR₂.env]

theorem classRulesOk_twin (h : EnvFree ops) {feT₁ feT₂ feR₁ feR₂ : FEnv}
    (hT : w.resolve feT₁ = w.resolve feT₂) (hR : w.resolve feR₁ = w.resolve feR₂)
    (g : ClassGen) (recOf : Nat → Option Name) (cvR : ConstantVal) (c : Nat) :
    ∀ xs, classRulesOk ops w feT₁ feR₁ g recOf cvR c xs =
      classRulesOk ops w feT₂ feR₂ g recOf cvR c xs
  | [] => rfl
  | x :: xs => by
    have ih := classRulesOk_twin h hT hR g recOf cvR c xs
    unfold classRulesOk
    simp only [classRuleOk_twin h hT hR, ih]

theorem classRecsRulesOk_twin (h : EnvFree ops) {feT₁ feT₂ feR₁ feR₂ : FEnv}
    (hT : w.resolve feT₁ = w.resolve feT₂) (hR : w.resolve feR₁ = w.resolve feR₂)
    (g : ClassGen) (recOf : Nat → Option Name) :
    ∀ cvs cs, classRecsRulesOk ops w feT₁ feR₁ g recOf cvs cs =
      classRecsRulesOk ops w feT₂ feR₂ g recOf cvs cs
  | cvG :: cvs, c :: cs => by
    have ih := classRecsRulesOk_twin h hT hR g recOf cvs cs
    unfold classRecsRulesOk
    simp only [classRulesOk_twin h hT hR, ih]
  | [], _ => by unfold classRecsRulesOk; rfl
  | _ :: _, [] => by unfold classRecsRulesOk; rfl

theorem recDomsAt_envFree (h : EnvFree ops) (env₁ env₂ : Env) (rec : Name)
    (sfvs gfvs : List Expr) :
    ∀ j k, recDomsAt ops env₁ rec sfvs gfvs j k = recDomsAt ops env₂ rec sfvs gfvs j k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [recDomsAt, h.isDefEq env₁, h.isDefEq env₂,
      recDomsAt_envFree h env₁ env₂ rec sfvs gfvs (j + 1) k]

theorem recTyOpened_envFree (h : EnvFree ops) (env₁ env₂ : Env) (rec : Name) (n : Nat) :
    ∀ os og, recTyOpened ops env₁ rec n os og = recTyOpened ops env₂ rec n os og
  | some (_, _), some (_, _) => by
    simp only [recTyOpened, h.isDefEq env₁, h.isDefEq env₂, recDomsAt_envFree h env₁ env₂]
  | none, _ => rfl
  | some (_, _), none => rfl

/-- The stored recursors' check (task #431) reads its index through
`resolve` alone, and through operations that ignore their environment. -/
theorem storedRecsCheck_twin (h : EnvFree ops) {fe₁ fe₂ : FEnv}
    (hR : w.resolve fe₁ = w.resolve fe₂) :
    ∀ recs out, storedRecsCheck ops w fe₁ recs out = storedRecsCheck ops w fe₂ recs out
  | [], [] => rfl
  | rc :: rcs, g :: gs => by
    have ih := storedRecsCheck_twin h hR rcs gs
    have hrules : ∀ lps rec rs gs', storedRulesCheck ops w fe₁ rec lps rs gs'
        = storedRulesCheck ops w fe₂ rec lps rs gs' := by
      intro lps rec rs
      induction rs with
      | nil => intro gs'; cases gs' <;> rfl
      | cons r rs ihr =>
        intro gs'
        cases gs' with
        | nil => rfl
        | cons g' gs' =>
          simp only [storedRulesCheck, ruleAgree, hR, h.inferType fe₁.env, h.inferType fe₂.env,
            h.isDefEq fe₁.env, h.isDefEq fe₂.env, ihr]
    simp only [storedRecsCheck, storedRecCheck, storedRecCompare, recTyCheck, ih, hrules, hR,
      h.inferType fe₁.env, h.inferType fe₂.env, h.ensureSort fe₁.env, h.ensureSort fe₂.env,
      recTyOpened_envFree h fe₁.env fe₂.env]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

end Rules

section RecStageC

variable {mode : CheckMode}

theorem classFeR_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    Twin (classFeR p Ms cvGs recCls fe₁) (classFeR p Ms cvGs recCls fe₂) := by
  unfold classFeR
  rw [consBlockRecsBareF_eq_pushAll, consBlockRecsBareF_eq_pushAll]
  exact ht.pushAll _

/-- The rule-less recursors' overlays on twin indices answer alike. -/
theorem classFeROvl_find?_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    (classFeROvl p Ms cvGs recCls fe₁).find? = (classFeROvl p Ms cvGs recCls fe₂).find? := by
  rw [classFeROvl_find? ht.idx₁.1, classFeROvl_find? ht.idx₂.1]
  exact (classFeR_twin ht p Ms cvGs recCls).find

/-- The rule-less recursors' overlays on twin indices answer the table
lookups alike. -/
theorem classFeROvl_findTable?_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (Ms : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat) :
    (classFeROvl p Ms cvGs recCls fe₁).findTable? =
      (classFeROvl p Ms cvGs recCls fe₂).findTable? := by
  rw [classFeROvl_findTable? ht.idx₁.1, classFeROvl_findTable? ht.idx₂.1]
  exact (classFeR_twin ht p Ms cvGs recCls).findTable

/-- **The recursor stage at twin indices is the same stage.** -/
theorem genRecCheck_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (p : BlockShape)
    (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead)
    (Ms : List TargetMajor) (cvTas : List ConstantVal) (block : List ConstantInfo) :
    genRecCheck (shadowOpsC mode) fe₁ p nestedBit params tbl rd Ms cvTas block =
      genRecCheck (shadowOpsC mode) fe₂ p nestedBit params tbl rd Ms cvTas block := by
  have hfe := ht.find
  have key : ∀ (Ms' : List TargetMajor) (cvGs : List ConstantVal) (recCls : List Nat)
      (g : ClassGen) (recOf : Nat → Option Name) ,
      classRecsRulesOk
          ((shadowOpsC mode).opsRuleR (classFeROvl p Ms' cvGs recCls fe₁))
          (shadowOpsC mode).walkers fe₁ (classFeROvl p Ms' cvGs recCls fe₁) g recOf cvGs
          recCls
        = classRecsRulesOk
          ((shadowOpsC mode).opsRuleR (classFeROvl p Ms' cvGs recCls fe₂))
          (shadowOpsC mode).walkers fe₂ (classFeROvl p Ms' cvGs recCls fe₂) g recOf
          cvGs recCls := by
    intro Ms' cvGs recCls g recOf
    have hR := classFeROvl_find?_twin ht p Ms' cvGs recCls
    have hRt := classFeROvl_findTable?_twin ht p Ms' cvGs recCls
    show classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe₁ _ g recOf cvGs
        recCls
      = classRecsRulesOk (sharedOpsRuleR mode _) structWalkersC fe₂ _ g recOf cvGs
        recCls
    rw [sharedOpsRuleR_congr mode hR hRt]
    exact classRecsRulesOk_twin (sharedOpsRuleR_envFree mode _)
      (constsResolveFC_congr hfe) (constsResolveFC_congr hR) g recOf cvGs recCls
  have hops : (shadowOpsC mode).opsAt fe₁ = sharedOpsC mode fe₂ :=
    sharedOpsC_congr hfe ht.findTable
  have hops₂ : (shadowOpsC mode).opsAt fe₂ = sharedOpsC mode fe₂ := rfl
  have hre : (shadowOpsC mode).ruleEnv = classFeROvl := rfl
  unfold genRecCheck
  simp only [hre]
  simp only [key, hops, hops₂, classStreamRecs_congr (sharedOpsC_envFree mode fe₂) hfe,
    classesNfs_env (sharedOpsC_envFree mode fe₂) fe₁.env,
    classesNfs_env (sharedOpsC_envFree mode fe₂) fe₂.env,
    classesCtors_env (sharedOpsC_envFree mode fe₂) fe₁.env,
    classesCtors_env (sharedOpsC_envFree mode fe₂) fe₂.env,
    classFormerTy_congr' hfe, classRecTysOk_congr (sharedOpsC_envFree mode fe₂) hfe]

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
    (hk : ∀ L Q, Twin (FEnv.pushDelta L Q fe₁) (FEnv.pushDelta L Q fe₂) →
      RelRun R' (k₁ (FEnv.pushDelta L Q fe₁)) (k₂ (FEnv.pushDelta L Q fe₂))) :
    RelRun R' (x₁ >>= k₁) (x₂ >>= k₂) :=
  RelRun.bind hx fun _ _ ⟨L, Q, h₁, h₂⟩ => h₁ ▸ h₂ ▸ hk L Q (ht.pushDelta L Q)

theorem checkStructProjTableF_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (T C : Name) (lps : List Name) (nP nF : Nat)
    (cvCa : ConstantVal) :
    RelRun (PushedFrom fe₁ fe₂)
      (checkStructProjTableF (m := CheckCM) structWalkersC T C lps nP nF cvCa fe₁)
      (checkStructProjTableF (m := CheckCM) structWalkersC T C lps nP nF cvCa fe₂) := by
  unfold checkStructProjTableF
  have hres : structWalkersC.resolve fe₁ = structWalkersC.resolve fe₂ :=
    constsResolveFC_congr ht.find
  simp only [hres, ht.find, ht.findTable]
  relrun
  all_goals exact RelRun.pure (PushedFrom.pushTable _ _ _)

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
         | [cA], [_] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) structWalkersC ms.cvT.name cA.1.name p.lps p.nP
               cA.2 cA.1 fe₁
           else pure fe₁
         | _, _ => pure fe₁)
        (match ctorsA, sortss with
         | [cA], [_] =>
           if ms.nIdx == 0 then
             checkStructProjTableF (m := CheckCM) structWalkersC ms.cvT.name cA.1.name p.lps p.nP
               cA.2 cA.1 fe₂
           else pure fe₂
         | _, _ => pure fe₂) := by
      split
      · split
        · exact checkStructProjTableF_twin ht _ _ _ _ _ _
        · exact RelRun.pure (PushedFrom.refl _ _)
      · exact RelRun.pure (PushedFrom.refl _ _)
    refine RelRun.bind_push ht hmid fun L Q htL => ?_
    exact RelRun.mono (checkBlockTablesF_twin p rest htL) fun _ _ h =>
      PushedFrom.trans ⟨L, Q, rfl, rfl⟩ h

/-- The relation of two block passes: the same pass but for its
environment, which is the same pushes onto the twins. -/
def PassRel (fe₁ fe₂ : FEnv) (q₁ q₂ : BlockPass FEnv) : Prop :=
  ∃ (L : List ConstantInfo) (Q : List ProjTable),
    q₁ = { q₂ with env₁ := FEnv.pushDelta L Q fe₁ } ∧ q₂.env₁ = FEnv.pushDelta L Q fe₂

theorem consBlockIndsF_pushed (p₁ : BlockShape) (isRec : Bool) (cvTas : List ConstantVal)
    (i : Nat) (fe₁ fe₂ : FEnv) :
    PushedFrom fe₁ fe₂ (consBlockIndsF p₁ isRec cvTas i fe₁) (consBlockIndsF p₁ isRec cvTas i fe₂) := by
  obtain ⟨L, hL, hL'⟩ := consBlockIndsF_eq_pushAll p₁ isRec cvTas i fe₁
  exact ⟨L, [], hL, hL' fe₂⟩

theorem checkBlockIndsF_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (p : BlockParts)
    (isRec : Bool) :
    RelRun (fun a₁ a₂ => PushedFrom fe₁ fe₂ a₁.1 a₂.1 ∧ a₁.2 = a₂.2)
      (checkBlockIndsF (sharedOpsC mode fe₁) fe₁ p isRec)
      (checkBlockIndsF (sharedOpsC mode fe₂) fe₂ p isRec) := by
  unfold checkBlockIndsF
  have h := sharedOpsC_envFree mode fe₂
  simp only [sharedOpsC_congr hfe htb, checkBlockTeleF_congr h hfe, checkBlockTelesF_congr h hfe,
    checkBlockAgreeF_congr h fe₁ fe₂]
  relrun
  all_goals exact RelRun.pure ⟨consBlockIndsF_pushed _ _ _ _ _ _, rfl⟩

theorem checkBlockPassS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (p₀ : BlockParts) (isRec : Bool) :
    RelRun (PassRel fe₁ fe₂) (checkBlockPassS mode fe₁ p₀ isRec)
      (checkBlockPassS mode fe₂ p₀ isRec) := by
  unfold checkBlockPassS
  refine RelRun.bind (checkBlockIndsF_twin ht.find ht.findTable p₀ isRec) ?_
  rintro ⟨a₁, cvTas, p₁⟩ ⟨a₂, cvTas', p₁'⟩ ⟨⟨L, Q, rfl, rfl⟩, he⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have htL := ht.pushDelta L Q
  have h := sharedOpsC_envFree mode (FEnv.pushDelta L Q fe₂)
  simp only [sharedOpsC_congr htL.find htL.findTable, checkBlockCtorsF_congr h htL.find htL.find, htL.find,
    checkBlockClasses_congr h htL.find,
    checkBlockPositivity_env h (FEnv.pushDelta L Q fe₁).env,
    checkBlockPositivity_env h (FEnv.pushDelta L Q fe₂).env,
    nestSeeds_env h (FEnv.pushDelta L Q fe₁).env, nestSeeds_env h (FEnv.pushDelta L Q fe₂).env]
  relrun
  all_goals exact RelRun.pure ⟨L, Q, rfl, rfl⟩

theorem checkBlockTailS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (block : List ConstantInfo) {q₁ q₂ : BlockPass FEnv} (hq : PassRel fe₁ fe₂ q₁ q₂) :
    RelRun (PushedFrom fe₁ fe₂) (checkBlockTailS mode block q₁)
      (checkBlockTailS mode block q₂) := by
  obtain ⟨L, Q, rfl, hq₂⟩ := hq
  obtain ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, params, rd, cls, tbl⟩ := q₂
  simp only at hq₂
  subst hq₂
  unfold checkBlockTailS
  have htL := ht.pushDelta L Q
  have h := sharedOpsC_envFree mode (FEnv.pushDelta L Q fe₂)
  obtain ⟨L₂, hL₂⟩ := consBlockCtorsF_eq_pushAll p.nP ctorsAs
  have ht₂ : Twin (consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₁))
      (consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₂)) := by
    rw [hL₂, hL₂]; exact htL.pushAll L₂
  -- the stored recursors' check, at the generated recursors' overlays
  have hO : ∀ X : List ConstantInfo,
      storedRecsCheck
          (sharedOpsC mode ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₁)).overlay
            X.reverse)) structWalkersC
          ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₁)).overlay X.reverse)
        = storedRecsCheck
          (sharedOpsC mode ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₂)).overlay
            X.reverse)) structWalkersC
          ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₂)).overlay X.reverse) := by
    intro X
    have hf : ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₁)).overlay X.reverse).find?
        = ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₂)).overlay X.reverse).find? := by
      rw [find?_overlay_pushAll ht₂.idx₁.1, find?_overlay_pushAll ht₂.idx₂.1]
      exact (ht₂.pushAll X).find
    have htb : ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₁)).overlay
        X.reverse).findTable?
        = ((consBlockCtorsF p.nP ctorsAs (FEnv.pushDelta L Q fe₂)).overlay
          X.reverse).findTable? := by
      rw [findTable?_overlay_pushAll ht₂.idx₁.1, findTable?_overlay_pushAll ht₂.idx₂.1]
      exact (ht₂.pushAll X).findTable
    funext recs out
    rw [sharedOpsC_congr hf htb]
    exact storedRecsCheck_twin (sharedOpsC_envFree mode _)
      (constsResolveFC_congr hf) recs out
  simp only [sharedOpsC_congr htL.find htL.findTable, checkBlockIdxSortsF_congr h (FEnv.pushDelta L Q fe₁)
      (FEnv.pushDelta L Q fe₂), genRecCheck_twin ht₂, hO]
  relrun
  rw [hL₂, hL₂]
  rename_i out
  refine RelRun.mono (checkBlockTablesF_twin _ _ ((htL.pushAll L₂).pushAll _)) fun x₁ x₂ hr => ?_
  obtain ⟨L₃, Q₃, rfl, rfl⟩ := hr
  exact (((PushedFrom.refl fe₁ fe₂).trans ⟨L, Q, rfl, rfl⟩).trans
    (PushedFrom.pushAll _ _ L₂)).trans (PushedFrom.pushAll _ _ _) |>.trans ⟨L₃, Q₃, rfl, rfl⟩


theorem checkBlockKS_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (block : List ConstantInfo) (p₀ : BlockParts) :
    RelRun (PushedFrom fe₁ fe₂) (checkBlockKS mode fe₁ block p₀)
      (checkBlockKS mode fe₂ block p₀) := by
  unfold checkBlockKS
  relrun
  all_goals
    exact RelRun.bind (checkBlockPassS_twin ht p₀ _) fun _ _ hq =>
      checkBlockTailS_twin ht block hq

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
    refine RelRun.bind_push ht (hf fe₁ fe₂ ht a) fun L Q htL => ?_
    exact RelRun.mono (RelRun.foldlM_push hf l htL) fun _ _ h =>
      PushedFrom.trans ⟨L, Q, rfl, rfl⟩ h

theorem checkBasisBlockC_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (kind : BasisKind)
    (block : List ConstantInfo) :
    RelRun (PushedFrom fe₁ fe₂) (checkBasisBlockC fe₁ kind block)
      (checkBasisBlockC fe₂ kind block) := by
  unfold checkBasisBlockC
  relrun
  all_goals exact RelRun.foldlM_push (fun _ _ ht' ci => installBasisDeclF_twin ht'.find ci) _ ht

theorem checkQuotRecordC_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂) (k : QuotKind)
    (cv : ConstantVal) :
    RelRun (PushedFrom fe₁ fe₂) (checkQuotRecordC fe₁ k cv) (checkQuotRecordC fe₂ k cv) := by
  unfold checkQuotRecordC
  simp only [ht.find]
  relrun
  all_goals exact installBasisDeclF_twin ht.find _

theorem checkShapelessS_twin {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (block : List ConstantInfo) :
    RelRun (PushedFrom fe₁ fe₂) (checkShapelessS mode fe₁ block) (checkShapelessS mode fe₂ block) := by
  unfold checkShapelessS
  simp only [checkConstantValC_congr hfe htb]
  relrun

/-- The block install, push for push at twins. -/
theorem checkIndDeclC_twin {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (block : List ConstantInfo) (nP : Nat) :
    RelRun (PushedFrom fe₁ fe₂) (checkIndDeclC mode fe₁ block nP)
      (checkIndDeclC mode fe₂ block nP) := by
  unfold checkIndDeclC
  relrun
  all_goals first
    | exact checkBasisBlockC_twin ht _ block
    | exact checkBlockKS_twin ht block _
    | exact checkShapelessS_twin ht.find ht.findTable block

/-- **Every declaration step at twin indices pushes the same constants
onto each, or fails alike.** -/
theorem checkDeclC_twin (pins : List NatOpPinSet) {fe₁ fe₂ : FEnv} (ht : Twin fe₁ fe₂)
    (pd : Declaration) :
    RelRun (PushedFrom fe₁ fe₂) (checkDeclC mode pins fe₁ pd) (checkDeclC mode pins fe₂ pd) := by
  have hfe := ht.find
  have htb := ht.findTable
  cases pd with
  | defnDecl cv value hint =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe htb]
    refine RelRun.bind_same fun _ => ?_
    split
    · -- the pinned arm: the same record on both sides, certified against
      -- overlays that answer as the twin pushes do, pushed last
      rw [checkDefnValCI_congr hfe htb]
      refine RelRun.bind_same fun ci => ?_
      have hov : (fe₁.overlay [ci]).find? = (fe₂.overlay [ci]).find? := by
        rw [find?_overlay_push ht.idx₁.1, find?_overlay_push ht.idx₂.1]
        exact (ht.push ci).find
      have h := sharedOpsC_envFree mode fe₂
      simp only [natOpGuardF_congr hov, natOpStoredOkF_congr hov, hov,
        sharedOpsC_congr hfe htb, certifyNatEqs_envFree h fe₁.env, certifyNatEqs_envFree h fe₂.env,
        checkDivModPinF_congr h hfe hov]
      relrun
      all_goals exact RelRun.pure (PushedFrom.push _ _ _)
    · exact RelRun.ofThrow
  | thmDecl cv value =>
    unfold checkDeclC
    exact RelRun.ofThrow
  | opaqueDecl cv value =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe htb]
    refine RelRun.bind_same fun _ => ?_
    split
    · -- the pinned arm, as the definitions'
      rw [checkOpaqueValCI_congr hfe htb]
      refine RelRun.bind_same fun ci => ?_
      have hov : (fe₁.overlay [ci]).find? = (fe₂.overlay [ci]).find? := by
        rw [find?_overlay_push ht.idx₁.1, find?_overlay_push ht.idx₂.1]
        exact (ht.push ci).find
      have h := sharedOpsC_envFree mode fe₂
      simp only [sharedOpsC_congr hfe htb, checkReducePinF_congr h hfe hov]
      relrun
      all_goals exact RelRun.pure (PushedFrom.push _ _ _)
    · exact RelRun.ofThrow
  | axiomDecl cv =>
    unfold checkDeclC
    simp only [checkConstantValC_congr hfe htb, stdAxiomOkF_congr hfe, trustCompilerOkF_congr hfe,
      ofReduceAxOkF_congr hfe]
    relrun
    all_goals first
      | exact checkQuotRecordC_twin ht _ _
      | exact RelRun.pure (PushedFrom.refl _ _)
      | exact RelRun.pure (PushedFrom.push _ _ _)
  | indDecl block nP =>
    unfold checkDeclC
    exact checkIndDeclC_twin ht block nP
  | quotDecl k cv =>
    unfold checkDeclC
    exact checkQuotRecordC_twin ht k cv

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

theorem pushAll_env_consts :
    ∀ (L : List ConstantInfo) (fe : FEnv),
      (FEnv.pushAll L fe).env.consts = L.reverse ++ fe.env.consts
  | [], _ => rfl
  | ci :: L, fe => by
    show (FEnv.pushAll L (fe.push ci)).env.consts = _
    rw [pushAll_env_consts L (fe.push ci)]
    simp [FEnv.push]

theorem pushAll_env_tables :
    ∀ (L : List ConstantInfo) (fe : FEnv), (FEnv.pushAll L fe).env.tables = fe.env.tables
  | [], _ => rfl
  | ci :: L, fe => pushAll_env_tables L (fe.push ci)

theorem pushTables_env :
    ∀ (Q : List ProjTable) (fe : FEnv),
      (FEnv.pushTables Q fe).env = ⟨fe.env.consts, Q.reverse ++ fe.env.tables⟩
  | [], _ => rfl
  | t :: Q, fe => by
    show (FEnv.pushTables Q (fe.pushTable t)).env = _
    rw [pushTables_env Q (fe.pushTable t)]
    simp [FEnv.pushTable]

theorem pushDelta_env (L : List ConstantInfo) (Q : List ProjTable) (fe : FEnv) :
    (FEnv.pushDelta L Q fe).env = ⟨L.reverse ++ fe.env.consts, Q.reverse ++ fe.env.tables⟩ := by
  unfold FEnv.pushDelta
  rw [pushTables_env, pushAll_env_consts, pushAll_env_tables]

theorem IdxBelow.ofWorkerView (B : BaseIdx) (S : Slots) (v : Nat) :
    IdxBelow (workerView B S v) :=
  ⟨rfl, fun n c ci h => by simp [ConLeche.Cached.workerView] at h⟩

theorem Twin.ofViewAgrees {B : BaseIdx} {S : Slots} {fe : FEnv} (hag : ViewAgrees B S fe)
    (hidx : IdxBelow fe) : Twin fe (workerView B S fe.visibleBelow) :=
  ⟨(funext hag.find).symm, (funext hag.raw).symm, rfl, hidx, IdxBelow.ofWorkerView B S _⟩

/-- Where `valueStep` has no verdict, phase A's step is the ordinary step. -/
theorem installStepC_of_valueStep_none {pins : List NatOpPinSet} {i : Nat} {fe W : FEnv}
    {pend : Array PendingCheck} {pd : Declaration} (h : valueStep W pd = none) :
    installStepC mode pins i fe pend pd = (checkDeclStepC mode pins fe pd >>= fun fe' =>
      pure (fe', pend)) := by
  cases pd with
  | defnDecl cv value hint =>
    by_cases hnat : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = true
    · unfold installStepC
      dsimp only
      rw [ite_eq_left hnat]
    · unfold valueStep at h
      dsimp only at h
      rw [ite_eq_right hnat] at h
      exact nomatch h
  | thmDecl cv value => exact nomatch h
  | opaqueDecl cv value =>
    by_cases hred : reduceOpNames.contains cv.name = true
    · unfold installStepC
      dsimp only
      rw [ite_eq_left hred]
    · unfold valueStep at h
      dsimp only at h
      rw [ite_eq_right hred] at h
      exact nomatch h
  | axiomDecl _ => rfl
  | quotDecl _ _ => rfl
  | indDecl _ _ => rfl

/-- The pending checks after a record: its check recorded, for a value
record. -/
@[expose] def pushPending (pend : Array PendingCheck) (i v : Nat) : Option ValueGroup → Array PendingCheck
  | some vg => pend.push ⟨vg, i, v⟩
  | none => pend

end Commit

end ConLeche.Cached
