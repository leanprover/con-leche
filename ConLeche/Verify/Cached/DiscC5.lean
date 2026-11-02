module

public import ConLeche.Verify.Cached.DiscC4

public section

/-!
# Cached body walks, part 5: definitional equality (task #163)

The simulation walks for the definitional-equality pieces
(`quickDefEqI`, `defeqOffsetI`, `tryUnfoldProjAppI`, `lazyDeltaStepI`,
the two lazy-delta loops, `defeqProjPairI`, `defeqStuckI`) and
`defeqBodyI` (`ConLeche/Cached/CoreC.lean`).

Every walk is a `Std.WP` triple proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`).  The two-sided dispatches
(`defeqStuck`, `quickDefEq`, `defeqProjPair`) reach `grind` as the pure
side's own per-arm equation lemmas, the fall-through one conditional:
`vcgen` splits the cached `match` and `grind` discharges the
fall-through premises from the arm's hypotheses.

The walks with continuations past a `match` (the λ telescope's step,
the lazy-delta loop, `defeqBody`) have them named on both sides
(`lamsStepI`/`lamsStepP`, `ldr…I`/`ldr…P`, `body…I`/`body…P`), each
block its own triple: a `fun` holding a `match` reaches `grind` as a
lambda it compares by splitting, and the do-notation's matchers are
shared between such lambdas.  The loops' induction hypotheses are named
predicates (`LamsSpec`, `LazySpec`, `LazyProjSpec`), atoms in `grind`'s
context rather than `∀`-facts it instantiates at every state in sight.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## The defeq family's vocabulary

The pairs its loops hand on as named scope predicates (`OptLamPairWS`,
`StepPairWS`, `LazyPairWS`), and the head readers' cached twins as
equations. -/

section Vocabulary

variable {env : Env}

/-- Both sides of a pair of λs, well scoped where present. -/
@[expose] def OptLamPairWS (d : Nat) : Option (Expr × Expr × Expr × Expr) → Prop
  | none => True
  | some q =>
    Expr.WScoped d q.1 ∧ Expr.WScoped d q.2.1 ∧ Expr.WScoped d q.2.2.1 ∧ Expr.WScoped d q.2.2.2

@[conleche_grind =] theorem OptLamPairWS.some_eq (d : Nat) (q : Expr × Expr × Expr × Expr) :
    OptLamPairWS d (some q) = (Expr.WScoped d q.1 ∧ Expr.WScoped d q.2.1 ∧
      Expr.WScoped d q.2.2.1 ∧ Expr.WScoped d q.2.2.2) := rfl

theorem wscoped_lamPair? {d : Nat} {b₁ b₂ : Expr} (h₁ : Expr.WScoped d b₁)
    (h₂ : Expr.WScoped d b₂) : OptLamPairWS d (Expr.lamPair? b₁ b₂) := by
  cases h : Expr.lamPair? b₁ b₂ with
  | none => trivial
  | some q =>
    obtain ⟨t₁, c₁, t₂, c₂⟩ := q
    obtain ⟨rfl, rfl⟩ := Expr.lamPair?_some h
    simp only [Expr.WScoped] at h₁ h₂
    exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩
grind_pattern [conleche_grind] wscoped_lamPair? =>
  Expr.WScoped d b₁, Expr.WScoped d b₂, Expr.lamPair? b₁ b₂

theorem wscoped_natPred? {d : Nat} {e : Expr} (h : Expr.WScoped d e) : OptWS d e.natPred? := by
  cases hp : e.natPred? with
  | none => trivial
  | some x => exact natPred?_WScoped hp h
grind_pattern [conleche_grind] wscoped_natPred? => Expr.WScoped d e, e.natPred?

/-- A lazy-delta step's handed-on pair is well scoped. -/
@[expose] def StepPairWS (d : Nat) : DeltaStep → Prop
  | .cont a b => Expr.WScoped d a ∧ Expr.WScoped d b
  | _ => True

@[conleche_grind =] theorem StepPairWS.cont_eq (d : Nat) (a b : Expr) :
    StepPairWS d (.cont a b) = (Expr.WScoped d a ∧ Expr.WScoped d b) := rfl
@[conleche_grind =] theorem StepPairWS.eq_eq (d : Nat) : StepPairWS d .eq = True := rfl
@[conleche_grind =] theorem StepPairWS.diff_eq (d : Nat) : StepPairWS d .diff = True := rfl
@[conleche_grind =] theorem StepPairWS.unknown_eq (d : Nat) : StepPairWS d .unknown = True := rfl

/-- The lazy-delta loop's stuck pair is well scoped. -/
@[expose] def LazyPairWS (d : Nat) : LazyRes → Prop
  | .unknown a b => Expr.WScoped d a ∧ Expr.WScoped d b
  | .verdict _ => True

@[conleche_grind =] theorem LazyPairWS.unknown_eq (d : Nat) (a b : Expr) :
    LazyPairWS d (.unknown a b) = (Expr.WScoped d a ∧ Expr.WScoped d b) := rfl
@[conleche_grind =] theorem LazyPairWS.verdict_eq (d : Nat) (v : Bool) :
    LazyPairWS d (.verdict v) = True := rfl

@[conleche_grind =] theorem unfoldableHeadC_eq (env : Env) (e : Expr) :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env e := unfoldableHeadC_spec

@[conleche_grind =] theorem headHintC_eq (env : Env) (e : Expr) :
    headHintC (mkFEnv env) e = headHint env e := headHintC_spec

@[conleche_grind =] theorem sameConstHeadsC_eq (a b : Expr) :
    sameConstHeadsC a b = sameConstHeads a b := sameConstHeadsC_spec

end Vocabulary

section Walks

variable {env : Env} {f : Nat}

/-- The innermost level of the λ-telescope comparison: the opened
bodies, then (at the verified mode) their full-grade types. -/
theorem defeqLamsInnerC_spec (ih : SSimC mode env f) {d : Nat} {b₁ b₂ : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (h1 : Expr.WScoped (d + 1) b₁) (h2 : Expr.WScoped (d + 1) b₂) :
    ⦃fun s => s = s₀⦄ defeqLamsInnerI mode (coreKnotI mode (mkFEnv env) f) d b₁ b₂
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqLamsInner mode (fueledFns mode env) d b₁ b₂) v; ⊤⦄ := by
  sym only [conleche_grind, defeqLamsInner] =>
    vcgen [defeqLamsInnerI, ih.defeq_spec, ih.infer_spec] <;> finish

/-- The cached λ-telescope comparison past the opened bodies. -/
@[expose] def lamsStepI (mode : CheckMode) (r : CoreFnsI) (n d : Nat) (b₁ b₂ : Expr) :
    CheckCM Bool :=
  match Expr.lamPair? b₁ b₂ with
  | some q =>
    if b₁ == b₂ then pure true
    else defeqLamsI mode r n (d + 1) q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => defeqLamsInnerI mode r d b₁ b₂

theorem defeqLamsI_zero (r : CoreFnsI) (d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqLamsI mode r 0 d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      let fv ← pure (Expr.fvar d ty₂)
      let b₁ ← inst1M body₁ fv
      let b₂ ← inst1M body₂ fv
      defeqLamsInnerI mode r d b₁ b₂ : CheckCM Bool) := rfl

set_option smartUnfolding false in
/-- `defeqLamsI`'s step (its structural recursion sits under the binds,
where the equation compiler generates no equation; smart unfolding
would not unfold it past the stuck `lamPair?` match). -/
theorem defeqLamsI_succ (r : CoreFnsI) (n d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqLamsI mode r (n + 1) d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      let fv ← pure (Expr.fvar d ty₂)
      let b₁ ← inst1M body₁ fv
      let b₂ ← inst1M body₂ fv
      lamsStepI mode r n d b₁ b₂ : CheckCM Bool) := by
  refine congrArg (r.defeq d ty₁ ty₂ >>= ·) (funext fun x => ?_)
  cases x
  · rfl
  · refine congrArg (pure (Expr.fvar d ty₂) >>= ·) (funext fun fv => ?_)
    refine congrArg (inst1M body₁ fv >>= ·) (funext fun b₁ => ?_)
    refine congrArg (inst1M body₂ fv >>= ·) (funext fun b₂ => ?_)
    unfold lamsStepI
    cases Expr.lamPair? b₁ b₂ with
    | none => rfl
    | some q => rfl

section PureLams
variable {m : Type → Type} [Monad m] (r : CoreFns m)

theorem defeqLams_zero (d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqLams mode r 0 d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      defeqLamsInner mode r d (body₁.instantiate1 (.fvar d ty₂))
        (body₂.instantiate1 (.fvar d ty₂)) : m Bool) := by
  rw [defeqLams.eq_1]

/-- The pure λ-telescope comparison past the opened bodies. -/
@[expose] def lamsStepP (mode : CheckMode) (n d : Nat) (b₁ b₂ : Expr) : m Bool :=
  match Expr.lamPair? b₁ b₂ with
  | some q =>
    if b₁ == b₂ then pure true
    else defeqLams mode r n (d + 1) q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => defeqLamsInner mode r d b₁ b₂

theorem defeqLams_succ (n d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqLams mode r (n + 1) d ty₁ body₁ ty₂ body₂ = (do
      unless ← r.defeq d ty₁ ty₂ do return false
      lamsStepP r mode n d (body₁.instantiate1 (.fvar d ty₂))
        (body₂.instantiate1 (.fvar d ty₂)) : m Bool) := by
  rw [defeqLams.eq_1]
  refine congrArg (r.defeq d ty₁ ty₂ >>= ·) (funext fun x => ?_)
  cases x
  · rfl
  · dsimp only
    unfold lamsStepP
    cases Expr.lamPair? (body₁.instantiate1 (.fvar d ty₂)) (body₂.instantiate1 (.fvar d ty₂)) with
    | none => rfl
    | some q => rfl

end PureLams

/-- The λ-telescope comparison at fuel `n` simulates its fueled
original (a named predicate, so that the induction hypothesis is an
atom in `grind`'s context). -/
@[expose] def LamsSpec (mode : CheckMode) (env : Env) (f n : Nat) : Prop :=
  ∀ {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState}, CSOK mode env s₀ →
    Expr.WScoped d ty₁ → Expr.WScoped d body₁ → Expr.WScoped d ty₂ → Expr.WScoped d body₂ →
    ⦃fun s => s = s₀⦄
      defeqLamsI mode (coreKnotI mode (mkFEnv env) f) n d ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqLams mode (fueledFns mode env) n d ty₁ body₁ ty₂ body₂) v; ⊤⦄

theorem LamsSpec.triple {n : Nat} (h : LamsSpec mode env f n) {d : Nat}
    {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (h1 : Expr.WScoped d ty₁) (h2 : Expr.WScoped d body₁) (h3 : Expr.WScoped d ty₂)
    (h4 : Expr.WScoped d body₂) :
    ⦃fun s => s = s₀⦄
      defeqLamsI mode (coreKnotI mode (mkFEnv env) f) n d ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqLams mode (fueledFns mode env) n d ty₁ body₁ ty₂ body₂) v; ⊤⦄ :=
  h hs h1 h2 h3 h4

theorem lamsStepC_spec (ih : SSimC mode env f) {n : Nat} (hn : LamsSpec mode env f n)
    {d : Nat} {b₁ b₂ : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (h1 : Expr.WScoped (d + 1) b₁) (h2 : Expr.WScoped (d + 1) b₂) :
    ⦃fun s => s = s₀⦄ lamsStepI mode (coreKnotI mode (mkFEnv env) f) n d b₁ b₂
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lamsStepP (fueledFns mode env) mode n d b₁ b₂) v; ⊤⦄ := by
  sym only [conleche_grind, lamsStepP] =>
    vcgen [lamsStepI, defeqLamsInnerC_spec ih, hn.triple] <;> finish

/-- By induction on the descent budget. -/
theorem lamsSpec_all (ih : SSimC mode env f) (fuel : Nat) : LamsSpec mode env f fuel := by
  induction fuel with
  | zero =>
    intro d ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _
    sym only [conleche_grind, defeqLams_zero] =>
      vcgen [defeqLamsI_zero, ih.defeq_spec, inst1M_spec (mode := mode) (env := env),
        defeqLamsInnerC_spec ih] <;> finish
  | succ n ihn =>
    intro d ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _
    sym only [conleche_grind, defeqLams_succ] =>
      vcgen [defeqLamsI_succ, ih.defeq_spec, inst1M_spec (mode := mode) (env := env),
        lamsStepC_spec ih ihn] <;> finish

/-- The λ-telescope comparison simulates its fueled original. -/
theorem defeqLamsC_spec (ih : SSimC mode env f) (fuel : Nat) {d : Nat}
    {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (h1 : Expr.WScoped d ty₁) (h2 : Expr.WScoped d body₁) (h3 : Expr.WScoped d ty₂)
    (h4 : Expr.WScoped d body₂) :
    ⦃fun s => s = s₀⦄
      defeqLamsI mode (coreKnotI mode (mkFEnv env) f) fuel d ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqLams mode (fueledFns mode env) fuel d ty₁ body₁ ty₂ body₂) v; ⊤⦄ :=
  LamsSpec.triple (lamsSpec_all ih fuel) hs h1 h2 h3 h4

/-- The syntactic fast path of `quickDefEq` (the arms' equations carry
it inside their `if`). -/
theorem quickDefEq_self {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) {d : Nat} {a b : Expr} (h : a = b) :
    quickDefEq mode r d a b = pure (some true) := by
  subst h; simp [quickDefEq]
grind_pattern [conleche_grind] quickDefEq_self => quickDefEq mode r d a b

/-- The easy cases simulate their specification. -/
theorem quickDefEqC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ quickDefEqI mode (coreKnotI mode (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (quickDefEq mode (fueledFns mode env) d a b) v; ⊤⦄ := by
  sym only [conleche_grind, quickDefEq] =>
    vcgen [quickDefEqI, ih.defeq_spec, inst1M_spec (mode := mode) (env := env),
      isEquivLM_spec (mode := mode) (env := env), liftFueled_spec (mode := mode) (env := env),
      defeqLamsC_spec ih lamsFuel] <;> finish

/-- Offsets simulate their specification. -/
theorem defeqOffsetC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqOffsetI (coreKnotI mode (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (defeqOffset (fueledFns mode env) d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqOffset] =>
    vcgen [defeqOffsetI, ih.defeq_spec] <;> finish

/-- `try_unfold_proj_app` simulates its specification. -/
theorem tryUnfoldProjAppC_spec (ih : SSimC mode env f) {d : Nat} {e : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ tryUnfoldProjAppI (coreKnotI mode (mkFEnv env) f) d e
    ⦃fun o s' => CSOK mode env s' ∧ Runs (tryUnfoldProjApp (fueledFns mode env) d e) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, tryUnfoldProjApp] =>
    vcgen [tryUnfoldProjAppI, ih.whnfCore_spec] <;> finish

/-- The end of a step simulates its specification. -/
theorem deltaQuickC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ deltaQuickI mode (coreKnotI mode (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (deltaQuick mode (fueledFns mode env) d a b) v ∧
      StepPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, deltaQuick] =>
    vcgen [deltaQuickI, quickDefEqC_spec ih] <;> finish

/-- One lazy-delta step simulates its specification. -/
theorem lazyDeltaStepC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ lazyDeltaStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (lazyDeltaStep mode (fueledFns mode env) env d a b) v ∧
      StepPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, lazyDeltaStep, unfoldDefinition_WScoped henv] =>
    vcgen [lazyDeltaStepI, tryUnfoldProjAppC_spec ih, deltaQuickC_spec ih, ih.whnfCore_spec,
      unfoldDefinitionC_spec (mode := mode) (env := env), defeqSpineC_spec ih] <;> finish

section PureLazy

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
  (r : CoreFns m) (env : Env) (depth : Nat)

/-! The pure lazy-delta loop's continuations, named (the loop's `match`es
on the literal accelerations share one matcher, so as lambdas `grind`
would compare them). -/

/-- Past the step. -/
@[expose] def ldrStepP (mode : CheckMode) (n : Nat) (a b : Expr) : DeltaStep → m LazyRes
  | .cont a' b' => lazyDeltaReduction mode r env depth n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration. -/
@[expose] def ldrNatBP (mode : CheckMode) (n : Nat) (a b : Expr) : Option Expr → m LazyRes
  | some b₂ => r.defeq depth a b₂ >>= fun v => pure (.verdict v)
  | none => lazyDeltaStep mode r env depth a b >>= ldrStepP r env depth mode n a b

/-- Past the left literal acceleration. -/
@[expose] def ldrNatAP (mode : CheckMode) (n : Nat) (a b : Expr) : Option Expr → m LazyRes
  | some a₂ => r.defeq depth a₂ b >>= fun v => pure (.verdict v)
  | none =>
    (if mode.eager || (!a.hasFvar && !b.hasFvar) then reduceNat r env depth b
      else pure none) >>= ldrNatBP r env depth mode n a b

/-- Past the offset check. -/
@[expose] def ldrOffP (mode : CheckMode) (n : Nat) (a b : Expr) : Option Bool → m LazyRes
  | some v => pure (.verdict v)
  | none =>
    (if mode.eager || (!a.hasFvar && !b.hasFvar) then reduceNat r env depth a
      else pure none) >>= ldrNatAP r env depth mode n a b

/-- The pure loop's step with its continuations named. -/
theorem lazyDeltaReduction_succ (mode : CheckMode) (n : Nat) (a b : Expr) :
    lazyDeltaReduction mode r env depth (n + 1) a b =
      defeqOffset r depth a b >>= ldrOffP r env depth mode n a b := by
  rw [lazyDeltaReduction.eq_2]; rfl

end PureLazy

/-- The lazy-delta loop at budget `n` simulates its specification (a
named predicate, so that the induction hypothesis is an atom in
`grind`'s context). -/
@[expose] def LazySpec (mode : CheckMode) (env : Env) (f d n : Nat) : Prop :=
  ∀ {a b : Expr} {s₀ : CState}, CSOK mode env s₀ → Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaReduction mode (fueledFns mode env) env d n a b) v ∧ LazyPairWS d v; ⊤⦄

theorem LazySpec.triple {d n : Nat} (h : LazySpec mode env f d n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaReduction mode (fueledFns mode env) env d n a b) v ∧ LazyPairWS d v; ⊤⦄ :=
  h hs hwa hwb

/-! The cached loop's continuations, named as the pure ones are, each
block its own triple (one short bind chain each). -/

/-- Past the step (cached). -/
@[expose] def ldrStepI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : DeltaStep → CheckCM LazyRes
  | .cont a' b' => lazyDeltaReductionI mode r fe depth n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration (cached). -/
@[expose] def ldrNatBI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : Option Expr → CheckCM LazyRes
  | some b₂ => do
    let v ← r.defeq depth a b₂
    pure (.verdict v)
  | none => lazyDeltaStepI mode r fe depth a b >>= ldrStepI mode r fe depth n a b

/-- Past the left literal acceleration (cached). -/
@[expose] def ldrNatAI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) (fold : Bool) : Option Expr → CheckCM LazyRes
  | some a₂ => do
    let v ← r.defeq depth a₂ b
    pure (.verdict v)
  | none =>
    (if fold then reduceNatI r fe depth b else pure none) >>= ldrNatBI mode r fe depth n a b

/-- Past the offset check (cached). -/
@[expose] def ldrOffI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : Option Bool → CheckCM LazyRes
  | some v => pure (.verdict v)
  | none => do
    let fold ← pure (mode.eager || (!Expr.hasFvar a && !Expr.hasFvar b))
    (if fold then reduceNatI r fe depth a else pure none) >>= ldrNatAI mode r fe depth n a b fold

/-- The cached loop's step with its continuations named. -/
theorem lazyDeltaReductionI_succ (r : CoreFnsI) (fe : FEnv) (depth n : Nat) (a b : Expr) :
    lazyDeltaReductionI mode r fe depth (n + 1) a b =
      defeqOffsetI r depth a b >>= ldrOffI mode r fe depth n a b := by
  rw [lazyDeltaReductionI.eq_2]; rfl

theorem ldrStepC_spec {d n : Nat} (hn : LazySpec mode env f d n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (st : DeltaStep)
    (hst : StepPairWS d st) :
    ⦃fun s => s = s₀⦄ ldrStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b st
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (ldrStepP (fueledFns mode env) env d mode n a b st) v ∧ LazyPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, ldrStepP] =>
    vcgen [ldrStepI, hn.triple] <;> finish

theorem ldrNatBC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Expr) (ho : OptWS d o) :
    ⦃fun s => s = s₀⦄ ldrNatBI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b o
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (ldrNatBP (fueledFns mode env) env d mode n a b o) v ∧ LazyPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, ldrNatBP] =>
    vcgen [ldrNatBI, ih.defeq_spec, lazyDeltaStepC_spec ih henv, ldrStepC_spec hn] <;> finish

theorem ldrNatAC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Expr) (ho : OptWS d o) :
    ⦃fun s => s = s₀⦄ ldrNatAI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b
      (mode.eager || (!Expr.hasFvar a && !Expr.hasFvar b)) o
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (ldrNatAP (fueledFns mode env) env d mode n a b o) v ∧ LazyPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, ldrNatAP] =>
    vcgen [ldrNatAI, ih.defeq_spec, reduceNatC_spec ih, ldrNatBC_spec ih henv hn] <;> finish

theorem ldrOffC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ ldrOffI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b o
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (ldrOffP (fueledFns mode env) env d mode n a b o) v ∧ LazyPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, ldrOffP] =>
    vcgen [ldrOffI, reduceNatC_spec ih, ldrNatAC_spec ih henv hn] <;> finish

/-- By induction on the step budget. -/
theorem lazySpec_all (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} (n : Nat) :
    LazySpec mode env f d n := by
  induction n with
  | zero =>
    intro a b s₀ hs _ _
    sym only [conleche_grind] => vcgen [lazyDeltaReductionI] <;> finish
  | succ n ihn =>
    intro a b s₀ hs _ _
    sym only [conleche_grind, lazyDeltaReduction_succ] =>
      vcgen [lazyDeltaReductionI_succ, defeqOffsetC_spec ih, ldrOffC_spec ih henv ihn] <;> finish

/-- The lazy-delta loop simulates its specification, by induction on
its step budget. -/
theorem lazyDeltaReductionC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    (n : Nat) {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaReduction mode (fueledFns mode env) env d n a b) v ∧ LazyPairWS d v; ⊤⦄ :=
  LazySpec.triple (lazySpec_all ih henv n) hs hwa hwb

/-- `lazy_delta_proj_reduction` at budget `n` simulates its
specification (the induction hypothesis as an atom). -/
@[expose] def LazyProjSpec (mode : CheckMode) (env : Env) (f d : Nat) (sn : Name) (ip n : Nat) :
    Prop :=
  ∀ {a b : Expr} {s₀ : CState}, CSOK mode env s₀ → Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode env) env d sn ip n a b) v; ⊤⦄

theorem LazyProjSpec.triple {d : Nat} {sn : Name} {ip n : Nat}
    (h : LazyProjSpec mode env f d sn ip n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode env) env d sn ip n a b) v; ⊤⦄ :=
  h hs hwa hwb

/-- By induction on the step budget. -/
theorem lazyProjSpec_all (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {sn : Name}
    {ip : Nat} (n : Nat) : LazyProjSpec mode env f d sn ip n := by
  induction n with
  | zero =>
    intro a b s₀ hs _ _
    sym only [conleche_grind] => vcgen [lazyDeltaProjReductionI] <;> finish
  | succ n ihn =>
    intro a b s₀ hs _ _
    sym only [conleche_grind, lazyDeltaProjReduction] =>
      vcgen [lazyDeltaProjReductionI, lazyDeltaStepC_spec ih henv, reduceProjCoreC_spec ih,
        ih.defeq_spec, ihn.triple] <;> finish

/-- `lazy_delta_proj_reduction` simulates its specification. -/
theorem lazyDeltaProjReductionC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat}
    {sn : Name} {ip : Nat} (n : Nat) {a b : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode env) env d sn ip n a b) v; ⊤⦄ :=
  LazyProjSpec.triple (lazyProjSpec_all ih henv n) hs hwa hwb

/-- The proj/proj check simulates its specification. -/
theorem defeqProjPairC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      defeqProjPairI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqProjPair mode (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqProjPair] =>
    vcgen [defeqProjPairI, lazyDeltaProjReductionC_spec ih henv] <;> finish

/-- The stuck comparison simulates its specification. -/
theorem defeqStuckC_spec (ih : SSimC mode env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqStuckI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (defeqStuck mode (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqStuck, strLitSupportedF_eq, strLitToConstructor_WScoped] =>
    vcgen [defeqStuckI, ih.defeq_spec, stuckIrrelC_spec ih, etaCertC_spec ih, defEqListC_spec ih,
      isEquivListLM_spec (mode := mode) (env := env),
      liftFueled_spec (mode := mode) (env := env)] <;> finish

section PureBody

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
  (r : CoreFns m) (env : Env) (depth : Nat)

/-! The pure body's continuations, named (a `fun` holding a `match`
would reach `grind` as a lambda it compares by splitting). -/

/-- Past the lazy-delta loop's stuck pair: the proj/proj check, the full
`whnfCore` restart and the stuck comparison. -/
@[expose] def bodyTailP (mode : CheckMode) (a₁ b₁ : Expr) : m Bool := do
  if ← defeqProjPair mode r env depth a₁ b₁ then pure true else
  if !a₁.headIsProj && !b₁.headIsProj then defeqStuck mode r env depth a₁ b₁ else
  let a₂ ← r.whnfCore false depth a₁
  let b₂ ← r.whnfCore false depth b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuck mode r env depth a₁ b₁
  else r.defeq depth a₂ b₂

/-- The lazy-delta loop's outcome. -/
@[expose] def bodyLazyP (mode : CheckMode) : LazyRes → m Bool
  | .verdict v => pure v
  | .unknown a₁ b₁ => bodyTailP r env depth mode a₁ b₁

/-- Past `quickDefEq` on the cheaply normalized pair. -/
@[expose] def bodyQ2P (mode : CheckMode) (a' b' : Expr) : Option Bool → m Bool
  | some v => pure v
  | none => lazyDeltaReduction mode r env depth defeqLoopFuel a' b' >>= bodyLazyP r env depth mode

/-- Past proof irrelevance: the cheap normalization and `quickDefEq`. -/
@[expose] def bodyPIP (mode : CheckMode) (a b : Expr) : m Bool := do
  if ← propIrrel r env depth a b then pure true else
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  quickDefEq mode r depth a' b' >>= bodyQ2P r env depth mode a' b'

/-- Past `quickDefEq` on the unreduced pair. -/
@[expose] def bodyQ1P (mode : CheckMode) (a b : Expr) : Option Bool → m Bool
  | some v => pure v
  | none => bodyPIP r env depth mode a b

/-- `defeqBody` with its continuations named. -/
theorem defeqBody_eq (mode : CheckMode) (a b : Expr) :
    defeqBody mode r env depth a b =
      (if a == b then pure true else do
        if ← (if b.isBoolTrue && (mode.eager || !a.hasFvar) then
            boolTrueShortcut r depth a else pure false) then pure true else
        quickDefEq mode r depth a b >>= bodyQ1P r env depth mode a b : m Bool) := by
  rw [defeqBody.eq_1]; rfl

end PureBody

/-! The cached body's continuations, named as the pure ones are, each
block its own triple. -/

/-- Past the lazy-delta loop's stuck pair (cached). -/
@[expose] def bodyTailI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a₁ b₁ : Expr) : CheckCM Bool := do
  if ← defeqProjPairI mode r fe depth a₁ b₁ then pure true else
  if !(Expr.headIsProj a₁) && !(Expr.headIsProj b₁) then
    defeqStuckI mode r fe depth a₁ b₁ else
  let a₂ ← r.whnfCore false depth a₁
  let b₂ ← r.whnfCore false depth b₁
  if a₂ == a₁ && b₂ == b₁ then defeqStuckI mode r fe depth a₁ b₁
  else r.defeq depth a₂ b₂

/-- The lazy-delta loop's outcome (cached). -/
@[expose] def bodyLazyI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    LazyRes → CheckCM Bool
  | .verdict v => pure v
  | .unknown a₁ b₁ => bodyTailI mode r fe depth a₁ b₁

/-- Past `quickDefEq` on the cheaply normalized pair (cached). -/
@[expose] def bodyQ2I (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a' b' : Expr) : Option Bool → CheckCM Bool
  | some v => pure v
  | none =>
    lazyDeltaReductionI mode r fe depth defeqLoopFuel a' b' >>= bodyLazyI mode r fe depth

/-- Past proof irrelevance (cached). -/
@[expose] def bodyPII (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b : Expr) : CheckCM Bool := do
  if ← propIrrelI r fe depth a b then pure true else
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  quickDefEqI mode r depth a' b' >>= bodyQ2I mode r fe depth a' b'

/-- Past `quickDefEq` on the unreduced pair (cached). -/
@[expose] def bodyQ1I (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b : Expr) : Option Bool → CheckCM Bool
  | some v => pure v
  | none => bodyPII mode r fe depth a b

/-- `defeqBodyI` with its continuations named. -/
theorem defeqBodyI_eq (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    defeqBodyI mode r fe depth a b =
      (if a == b then pure true else do
        let bt ← pure (Expr.isBoolTrue b)
        let af ← pure (Expr.hasFvar a)
        if ← (if bt && (mode.eager || !af) then boolTrueShortcutI r depth a
            else pure false) then pure true else
        quickDefEqI mode r depth a b >>= bodyQ1I mode r fe depth a b : CheckCM Bool) := rfl

theorem bodyTailC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ bodyTailI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (bodyTailP (fueledFns mode env) env d mode a b) v; ⊤⦄ := by
  sym only [conleche_grind, bodyTailP] =>
    vcgen [bodyTailI, defeqProjPairC_spec ih henv, defeqStuckC_spec ih, ih.whnfCore_spec,
      ih.defeq_spec] <;> finish

theorem bodyLazyC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {s₀ : CState}
    (hs : CSOK mode env s₀) (lr : LazyRes) (hlr : LazyPairWS d lr) :
    ⦃fun s => s = s₀⦄ bodyLazyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d lr
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (bodyLazyP (fueledFns mode env) env d mode lr) v; ⊤⦄ := by
  sym only [conleche_grind, bodyLazyP] =>
    vcgen [bodyLazyI, bodyTailC_spec ih henv] <;> finish

theorem bodyQ2C_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ2I mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b o
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (bodyQ2P (fueledFns mode env) env d mode a b o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ2P] =>
    vcgen [bodyQ2I, lazyDeltaReductionC_spec ih henv, bodyLazyC_spec ih henv] <;> finish

theorem bodyPIC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ bodyPII mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (bodyPIP (fueledFns mode env) env d mode a b) v; ⊤⦄ := by
  sym only [conleche_grind, bodyPIP] =>
    vcgen [bodyPII, propIrrelC_spec ih, ih.whnfCore_spec, quickDefEqC_spec ih,
      bodyQ2C_spec ih henv] <;> finish

theorem bodyQ1C_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ1I mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b o
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (bodyQ1P (fueledFns mode env) env d mode a b o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ1P] =>
    vcgen [bodyQ1I, bodyPIC_spec ih henv] <;> finish

/-- The definitional-equality body simulates its specification. -/
theorem defeqBodyC_spec (ih : SSimC mode env f) (henv : EnvWF env) {s₀ : CState} {d : Nat}
    {a b : Expr} (hs : CSOK mode env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode env s' ∧ Runs (defeqBody mode (fueledFns mode env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqBody_eq] =>
    vcgen [defeqBodyI_eq, boolTrueShortcutC_spec ih, quickDefEqC_spec ih,
      bodyQ1C_spec ih henv] <;> finish

end Walks

end ConLeche.Cached
