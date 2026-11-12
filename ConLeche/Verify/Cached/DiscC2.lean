module

public import ConLeche.Verify.Cached.DiscC1

public section

/-!
# Cached body walks, part 2: the stuck-term certificates (task #163)

Each walk is a `Std.WP` triple whose post names the cached value as the
fueled answer (`Runs`), proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`; the triple forms of the knot's
entry points and the vocabulary these walks add are in `DiscC1.lean`).
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

section Walks

variable {env : Env} {f : Nat}

/-- The hoisted `Prop`-branch test (task #168): the fast arms are the
same pure reads on both sides (`mkFEnv_find_fun`). -/
theorem propIrrelC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ propIrrelI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (propIrrel (fueledFns mode eager env) env d a b) v;
        ⊤⦄ := by
  sym only [conleche_grind, propIrrel, mkFEnv_find_fun, mkFEnv_findTable_fun] =>
    vcgen [propIrrelI.eq_def, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (eager :=
        eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

/-- The eq-true shortcut (the audit's E2) simulates its specification:
one `whnf`, then the store read of the head test. -/
theorem boolTrueShortcutC_spec (ih : SSimC mode eager env f) {d : Nat} {a : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d a) :
    ⦃fun s => s = s₀⦄ boolTrueShortcutI mode (mkFEnv env) eager f d a
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (boolTrueShortcut (fueledFns mode eager env) d a) v;
        ⊤⦄ := by
  sym only [conleche_grind, boolTrueShortcut] =>
    vcgen [boolTrueShortcutI.eq_def, ih.whnf_spec] <;> finish

/-- `proofIrrelI` simulates its fueled original. -/
theorem proofIrrelC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ proofIrrelI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (proofIrrel (fueledFns mode eager env) d a b) v; ⊤⦄
        := by
  sym only [conleche_grind, proofIrrel] =>
    vcgen [proofIrrelI.eq_def, ih.inferIO_spec, ih.whnf_spec, isEquivLM_spec (mode := mode) (eager :=
        eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the pure side is nine binds deep, one `Runs.bind_eq` generation each
      finish (gen := 12)

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- `etaCertI` simulates its fueled original. -/
theorem etaCertC_spec (ih : SSimC mode eager env f) {d : Nat} {ty₁ body₁ b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwty : Expr.WScoped d ty₁) (hwbody : Expr.WScoped d body₁)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ etaCertI mode (mkFEnv env) eager f d ty₁ body₁ b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (etaCert mode (fueledFns mode eager env) env d ty₁ body₁ b) v; ⊤⦄ := by
  sym only [conleche_grind, etaCert] =>
    vcgen [etaCertI.eq_def, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec, ih.infer_spec,
      inst1M_spec (mode := mode) (eager := eager) (env := env)] <;>
      -- the verified arm is seven binds deep, one `Runs.bind_eq` generation each
      finish (gen := 10)

/-- The cached projection-fire check is the spec's (`mkFEnv`). -/
theorem projCertAtF_mkFEnv (env : Env) (v : Bool) (c : Name) (args : List Expr) :
    projCertAtF (mkFEnv env) v c args = projCertAt env v c args := by
  unfold projCertAtF projCertAt projCertF projCert
  rw [mkFEnv_find?]
  split <;> rfl

/-- `isPropTypeI` simulates its fueled original. -/
theorem isPropTypeC_spec (ih : SSimC mode eager env f) {d : Nat} {T : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d T) :
    ⦃fun s => s = s₀⦄ isPropTypeI mode (mkFEnv env) eager f d T
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (isPropType (fueledFns mode eager env) d T) v; ⊤⦄ := by
  sym only [conleche_grind, isPropType] =>
    vcgen [isPropTypeI.eq_def, ih.inferIO_spec, ih.whnf_spec,
      isEquivLM_spec (mode := mode) (eager := eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- The field loop of the unit-like test simulates its fueled original,
given the field test's (the unit-like loop at its remaining fuel `ulf`)
simulation. -/
theorem unitLikeFieldsC_spec (ih : SSimC mode eager env f)
    {ulf : Nat} {ul' : Nat → Expr → FueledM Bool}
    (hul : ∀ {d : Nat} {e : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ unitLikeLoopI mode (mkFEnv env) eager f ulf d e
      ⦃fun v s' => CSOK mode eager env s' ∧ Runs (ul' d e) v; ⊤⦄) :
    ∀ {n d : Nat} {t : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d t →
      ⦃fun s => s = s₀⦄ unitLikeFieldsI mode (mkFEnv env) eager f ulf n d t
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeFields (fueledFns mode eager env) ul' n d t) v; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d t s₀ hs hw
    sym only [conleche_grind, unitLikeFields] =>
      vcgen [unitLikeFieldsI.eq_def] <;> finish
  | succ n ihn =>
    intro d t s₀ hs hw
    cases t with
    | forallE dom body =>
      sym only [conleche_grind, unitLikeFields] =>
        vcgen [unitLikeFieldsI.eq_def, isPropTypeC_spec ih, hul,
          inst1M_spec (mode := mode) (eager := eager) (env := env), ihn] <;> finish
    | _ =>
      rw [unitLikeFieldsI.eq_def]; simp only [unitLikeFields]
      sym only [conleche_grind] => vcgen <;> finish
/-- The cached shape read is the spec's (`mkFEnv`). -/
theorem unitLikeShapeF_mkFEnv (env : Env) (w : Expr) :
    unitLikeShapeF (mkFEnv env) w = unitLikeShape env w := by
  unfold unitLikeShapeF unitLikeShape unitFieldTele
  simp only [mkFEnv_find?, mkFEnv_findTable?, Expr.getAppArgsC_spec,
    Expr.instLevelParams_spec, Expr.instantiateListC_spec, Option.map_map]
  rfl

/-- The structure arm of the unit-like test simulates its fueled
original, given the field test's simulation. -/
theorem unitLikeStructC_spec (ih : SSimC mode eager env f) (henv : EnvWF env)
    {ulf : Nat} {ul' : Nat → Expr → FueledM Bool}
    (hul : ∀ {d : Nat} {e : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d e →
      ⦃fun s => s = s₀⦄ unitLikeLoopI mode (mkFEnv env) eager f ulf d e
      ⦃fun v s' => CSOK mode eager env s' ∧ Runs (ul' d e) v; ⊤⦄)
    {d : Nat} {w : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d w) :
    ⦃fun s => s = s₀⦄ unitLikeStructI mode (mkFEnv env) eager f ulf d w
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeStruct (fueledFns mode eager env) ul' env d w) v; ⊤⦄ := by
  rw [unitLikeStructI.eq_def]; unfold unitLikeStruct
  rw [unitLikeShapeF_mkFEnv]
  cases hsh : unitLikeShape env w with
  | none => sym only [conleche_grind] => vcgen <;> finish
  | some x =>
    obtain ⟨tele, n⟩ := x
    exact unitLikeFieldsC_spec ih hul hs (unitLikeShape_WScoped henv hw hsh)

/-- The unit-like test simulates its fueled original. -/
theorem unitLikeLoopC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) :
    ∀ {fuel d : Nat} {T : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d T →
      ⦃fun s => s = s₀⦄ unitLikeLoopI mode (mkFEnv env) eager f fuel d T
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (unitLikeLoop (fueledFns mode eager env) env fuel d T) v; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro d T s₀ hs hw
    sym only [conleche_grind, unitLikeLoop] =>
      vcgen [unitLikeLoopI.eq_def] <;> finish
  | succ fuel ihf =>
    intro d T s₀ hs hw
    sym only [conleche_grind, unitLikeLoop] =>
      vcgen [unitLikeLoopI.eq_def, ih.whnf_spec,
        inst1M_spec (mode := mode) (eager := eager) (env := env), ihf,
        unitLikeStructC_spec ih henv ihf] <;> finish
/-- `structUnitCertI` simulates its fueled original. -/
theorem structUnitCertC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structUnitCertI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structUnitCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structUnitCert] =>
    vcgen [structUnitCertI.eq_def, ih.inferIO_spec, ih.whnf_spec, ih.defeq_spec,
      unitLikeLoopC_spec ih henv] <;> finish
end Walks2

section Walks4

variable {env : Env} {f : Nat}

/-- The cached `.proj` spine (the tower spelling, task #175 W4c). -/
theorem projNodesC_spec (T : Name) (b : Expr) :
    ∀ (l : List Nat) {s₀ : CState}, CSOK mode eager env s₀ →
      ⦃fun s => s = s₀⦄ projNodesI T b l
      ⦃fun rs s' => CSOK mode eager env s' ∧ rs = projsOf T b l; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro _ _
    sym only [conleche_grind] =>
      vcgen [projNodesI] <;> finish
  | cons _ rest ih =>
    intro _ _
    sym only [conleche_grind] =>
      vcgen [projNodesI, ih] <;> finish

section PureSeta

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] {r : CoreFns m} {d : Nat}

/-- The pure structure-η certificate past its lookups (the constructor
head, its record, the arity, the type's head, its former and its
table). -/
@[expose] def setaBodyP (r : CoreFns m) (env : Env) (depth : Nat) (a b wtb : Expr) (c : Name)
    (us : List Level) (cvc : ConstantVal) (T : Name) (us' : List Level) (cvT : ConstantVal)
    (caps : IndCaps) (tbl : ProjTable) : m Bool := do
  if caps.eta = true ∧ tbl.ctor = c ∧
      wtb.getAppArgs.length = tbl.numParams ∧
      us'.length = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams then
    if ← liftFueled "level comparison" (Level.isEquivList us us') then
      if ← defEqList r env depth (a.getAppArgs.take tbl.numParams) wtb.getAppArgs then
        defEqList r env depth (a.getAppArgs.drop tbl.numParams) (etaProjs T b tbl.numFields)
      else pure false
    else pure false
  else pure false

/-! The pure certificate's arms, one equation each. -/

theorem seta_body {env : Env} {a b wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {cT : Name} {T : Name} {us' : List Level} {cvT : ConstantVal} {caps : IndCaps}
    {tbl : ProjTable} (h1 : a.getAppFn = .const c us)
    (h2 : env.find? c = some (.ctorInfo cvc cnP cnF cT)) (h3 : a.getAppArgs.length = cnP + cnF)
    (h4 : wtb.getAppFn = .const T us') (h5 : env.find? T = some (.indInfo cvT caps))
    (h6 : env.findTable? T = some tbl) :
    structEtaCertWith r env d a b wtb = setaBodyP r env d a b wtb c us cvc T us' cvT caps tbl := by
  rw [structEtaCertWith]; simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]; rfl
grind_pattern [conleche_grind] seta_body =>
    structEtaCertWith r env d a b wtb, Expr.const c us, ConstantInfo.ctorInfo cvc cnP cnF cT,
      Expr.const T us', ConstantInfo.indInfo cvT caps, Option.some tbl where
  guard a.getAppFn = .const c us
  guard env.find? c = some (.ctorInfo cvc cnP cnF cT)
  guard wtb.getAppFn = .const T us'
  guard env.find? T = some (.indInfo cvT caps)
  guard env.findTable? T = some tbl

theorem seta_notConst {env : Env} {a b wtb : Expr}
    (h1 : ∀ c us, a.getAppFn = .const c us → False) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; split
  · exact absurd ‹_› (h1 _ _)
  · rfl

theorem seta_notCtor {env : Env} {a b wtb : Expr} {c : Name} {us : List Level}
    (h1 : a.getAppFn = .const c us)
    (h2 : ∀ cvc cnP cnF cT, env.find? c = some (.ctorInfo cvc cnP cnF cT) → False) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; simp only [h1]
grind_pattern [conleche_grind] seta_notCtor => structEtaCertWith r env d a b wtb, Expr.const c us where
  guard a.getAppFn = .const c us

theorem seta_arity {env : Env} {a b wtb : Expr} {c : Name} {us : List Level} {cvc : ConstantVal}
    {cnP cnF : Nat} {cT : Name} (h1 : a.getAppFn = .const c us)
    (h2 : env.find? c = some (.ctorInfo cvc cnP cnF cT)) (h3 : ¬a.getAppArgs.length = cnP + cnF) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; simp only [h1, h2, h3, ↓reduceIte]
grind_pattern [conleche_grind] seta_arity =>
    structEtaCertWith r env d a b wtb, Expr.const c us, ConstantInfo.ctorInfo cvc cnP cnF cT where
  guard a.getAppFn = .const c us
  guard env.find? c = some (.ctorInfo cvc cnP cnF cT)

theorem seta_notConstT {env : Env} {a b wtb : Expr} {c : Name} {us : List Level}
    {cvc : ConstantVal} {cnP cnF : Nat} {cT : Name} (h1 : a.getAppFn = .const c us)
    (h2 : env.find? c = some (.ctorInfo cvc cnP cnF cT)) (h3 : a.getAppArgs.length = cnP + cnF)
    (h4 : ∀ T us', wtb.getAppFn = .const T us' → False) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; simp only [h1, h2, h3, ↓reduceIte]
grind_pattern [conleche_grind] seta_notConstT =>
    structEtaCertWith r env d a b wtb, Expr.const c us, ConstantInfo.ctorInfo cvc cnP cnF cT where
  guard a.getAppFn = .const c us
  guard env.find? c = some (.ctorInfo cvc cnP cnF cT)
  guard a.getAppArgs.length = cnP + cnF

theorem seta_notInd {env : Env} {a b wtb : Expr} {c : Name} {us : List Level}
    {cvc : ConstantVal} {cnP cnF : Nat} {cT : Name} {T : Name} {us' : List Level}
    (h1 : a.getAppFn = .const c us)
    (h2 : env.find? c = some (.ctorInfo cvc cnP cnF cT)) (h3 : a.getAppArgs.length = cnP + cnF)
    (h4 : wtb.getAppFn = .const T us')
    (h5 : ∀ cvT caps, env.find? T = some (.indInfo cvT caps) → False) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; simp only [h1, h2, h3, h4, ↓reduceIte]
grind_pattern [conleche_grind] seta_notInd =>
    structEtaCertWith r env d a b wtb, Expr.const c us, ConstantInfo.ctorInfo cvc cnP cnF cT,
      Expr.const T us' where
  guard a.getAppFn = .const c us
  guard env.find? c = some (.ctorInfo cvc cnP cnF cT)
  guard wtb.getAppFn = .const T us'

theorem seta_noTable {env : Env} {a b wtb : Expr} {c : Name} {us : List Level}
    {cvc : ConstantVal} {cnP cnF : Nat} {cT : Name} {T : Name} {us' : List Level} {cvT : ConstantVal}
    {caps : IndCaps} (h1 : a.getAppFn = .const c us)
    (h2 : env.find? c = some (.ctorInfo cvc cnP cnF cT)) (h3 : a.getAppArgs.length = cnP + cnF)
    (h4 : wtb.getAppFn = .const T us') (h5 : env.find? T = some (.indInfo cvT caps))
    (h6 : env.findTable? T = none) :
    structEtaCertWith r env d a b wtb = pure false := by
  rw [structEtaCertWith]; simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
grind_pattern [conleche_grind] seta_noTable =>
    structEtaCertWith r env d a b wtb, Expr.const c us, ConstantInfo.ctorInfo cvc cnP cnF cT,
      Expr.const T us', ConstantInfo.indInfo cvT caps where
  guard a.getAppFn = .const c us
  guard env.find? c = some (.ctorInfo cvc cnP cnF cT)
  guard wtb.getAppFn = .const T us'
  guard env.find? T = some (.indInfo cvT caps)
  guard env.findTable? T = none

end PureSeta

/-- `structEtaCertWithI` simulates its fueled original. -/
theorem structEtaCertWithC_spec (ih : SSimC mode eager env f) {d : Nat} {a b wtb : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (hwwtb : Expr.WScoped d wtb) :
    ⦃fun s => s = s₀⦄
      structEtaCertWithI mode (mkFEnv env) eager f d a b wtb
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaCertWith (fueledFns mode eager env) env d a b wtb) v; ⊤⦄ := by
  sym only [conleche_grind, seta_notConst, setaBodyP] =>
    vcgen [structEtaCertWithI.eq_def, isEquivListLM_spec (mode := mode) (eager := eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env), defEqListC_spec ih,
      projNodesC_spec (mode := mode) (eager := eager) (env := env)] <;> finish

/-- The partial-constructor gate reads the same store on both sides. -/
theorem etaCtorPartialC_eq (env : Env) (e : Expr) :
    etaCtorPartialC (mkFEnv env) e = etaCtorPartial env e := by
  unfold etaCtorPartialC etaCtorPartial
  simp only [mkFEnv_find?, mkFEnv_findTable?]
  cases e.getAppFn <;> rfl

/-- `structEtaFullI` simulates its fueled original. -/
theorem structEtaFullC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaFullI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaFull (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaFull] =>
    vcgen [structEtaFullI.eq_def, ih.inferIO_spec, ih.whnf_spec, structEtaCertWithC_spec ih] <;>
      finish

/-- The η-expansion simulates its fueled original. -/
theorem structEtaExpandC_spec (ih : SSimC mode eager env f) :
    ∀ {k d : Nat} {a b t : Expr} {s₀ : CState}, CSOK mode eager env s₀ →
      Expr.WScoped d a → Expr.WScoped d b → Expr.WScoped d t →
      ⦃fun s => s = s₀⦄ structEtaExpandI mode (mkFEnv env) eager f k d a b t
      ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaExpand (fueledFns mode eager env) env k d a b t) v; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro d a b t s₀ hs hwa hwb hwt
    sym only [conleche_grind, structEtaExpand] =>
      vcgen [structEtaExpandI.eq_def, structEtaFullC_spec ih] <;> finish
  | succ k ihk =>
    intro d a b t s₀ hs hwa hwb hwt
    cases t with
    | forallE dom body =>
      sym only [conleche_grind, structEtaExpand] =>
        vcgen [structEtaExpandI.eq_def, inst1M_spec (mode := mode) (eager := eager) (env := env),
          ihk] <;> finish
    | _ =>
      simp only [structEtaExpandI, structEtaExpand]
      sym only [conleche_grind] => vcgen <;> finish

/-- `structEtaCertI` simulates its fueled original. -/
theorem structEtaCertC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ structEtaCertI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (structEtaCert (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, structEtaCert, etaCtorPartialC_eq] =>
    vcgen [structEtaCertI.eq_def, structEtaFullC_spec ih, ih.inferIO_spec, ih.defeq_spec,
      structEtaExpandC_spec ih] <;> finish

/-- `stuckIrrelI` simulates its fueled original. -/
theorem stuckIrrelC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ stuckIrrelI mode (mkFEnv env) eager f d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
        Runs (stuckIrrel (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, stuckIrrel] =>
    vcgen [stuckIrrelI.eq_def, structEtaCertC_spec ih, structUnitCertC_spec ih henv,
      proofIrrelC_spec ih] <;> finish

end Walks4


end ConLeche.Cached
