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

The walks with continuations past a `match` (the binder telescope's step,
the lazy-delta loop, `defeqBody`) have them named on both sides
(`bindersStepI`/`bindersStepP`, `ldr…I`/`ldr…P`, `body…I`/`body…P`), each
block its own triple: a `fun` holding a `match` reaches `grind` as a
lambda it compares by splitting, and the do-notation's matchers are
shared between such lambdas.  The loops' induction hypotheses are named
predicates (`BindersSpec`, `LazySpec`, `LazyProjSpec`), atoms in `grind`'s
context rather than `∀`-facts it instantiates at every state in sight.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool}

/-! ## The defeq family's vocabulary

The pairs its loops hand on as named scope predicates (`OptLamPairWS`,
`StepPairWS`, `LazyPairWS`), and the head readers' cached twins as
equations. -/

section Vocabulary

variable {env : Env}

/-- Both sides of a pair of binders, opened over the accumulator `vs`
(the domains at the cursor, the bodies one deeper), well scoped where
present. -/
@[expose] def OptBinderPairWS (d : Nat) (vs : List Expr) :
    Option (Expr × Expr × Expr × Expr) → Prop
  | none => True
  | some q =>
    Expr.WScoped d (q.1.instantiateList vs) ∧ Expr.WScoped d (q.2.1.instantiateList vs 1) ∧
      Expr.WScoped d (q.2.2.1.instantiateList vs) ∧ Expr.WScoped d (q.2.2.2.instantiateList vs 1)

@[conleche_grind =] theorem OptBinderPairWS.some_eq (d : Nat) (vs : List Expr)
    (q : Expr × Expr × Expr × Expr) :
    OptBinderPairWS d vs (some q) = (Expr.WScoped d (q.1.instantiateList vs) ∧
      Expr.WScoped d (q.2.1.instantiateList vs 1) ∧ Expr.WScoped d (q.2.2.1.instantiateList vs) ∧
      Expr.WScoped d (q.2.2.2.instantiateList vs 1)) := rfl

theorem wscoped_binderPair? {d : Nat} {lam : Bool} {b₁ b₂ : Expr} {vs : List Expr}
    (h₁ : Expr.WScoped d (b₁.instantiateList vs)) (h₂ : Expr.WScoped d (b₂.instantiateList vs)) :
    OptBinderPairWS d vs (Expr.binderPair? lam b₁ b₂) := by
  cases h : Expr.binderPair? lam b₁ b₂ with
  | none => trivial
  | some q =>
    obtain ⟨t₁, c₁, t₂, c₂⟩ := q
    obtain ⟨rfl, rfl⟩ := Expr.binderPair?_some h
    cases lam <;>
      simp only [Expr.binderOf, instList_lam_eq, instList_forallE_eq, Expr.WScoped] at h₁ h₂ <;>
      exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩
grind_pattern [conleche_grind] wscoped_binderPair? =>
  Expr.WScoped d (b₁.instantiateList vs), Expr.WScoped d (b₂.instantiateList vs),
    Expr.binderPair? lam b₁ b₂

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

/-- The innermost level of the binder-telescope comparison: the
opened bodies, then (for λs at the verified mode) their full-grade
types. -/
theorem defeqBindersInnerC_spec (ih : SSimC mode eager env f) {lam : Bool} {d : Nat}
    {b₁ b₂ : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (h1 : Expr.WScoped (d + 1) b₁) (h2 : Expr.WScoped (d + 1) b₂) :
    ⦃fun s => s = s₀⦄ defeqBindersInnerI mode (coreKnotI mode eager (mkFEnv env) f) lam d b₁ b₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqBindersInner mode (fueledFns mode eager env) lam d b₁ b₂) v; ⊤⦄ := by
  sym only [conleche_grind, defeqBindersInner] =>
    vcgen [defeqBindersInnerI, ih.defeq_spec, ih.infer_spec] <;> finish

/-- One level's domain comparison. -/
theorem defeqDomainC_spec (ih : SSimC mode eager env f) {d : Nat} {fvs : Array Expr}
    {ty₁ ty₂ dom₂ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (h1 : Expr.WScoped d (ty₁.instantiateList fvs.toList.reverse)) (h2 : Expr.WScoped d dom₂) :
    ⦃fun s => s = s₀⦄ defeqDomainI (coreKnotI mode eager (mkFEnv env) f) d fvs ty₁ ty₂ dom₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqDomain (fueledFns mode eager env) d fvs.toList.reverse ty₁ ty₂ dom₂) v; ⊤⦄ := by
  sym only [conleche_grind, defeqDomain] =>
    vcgen [defeqDomainI, instListRevM_spec (mode := mode) (eager := eager) (env := env), ih.defeq_spec] <;> finish

/-- The cached innermost level on the bulk-opened bodies (the leaf of
`defeqBindersI`). -/
@[expose] def bindersLeafI (mode : CheckMode) (r : CoreFnsI) (lam : Bool) (d : Nat)
    (fvs : Array Expr) (b₁ b₂ : Expr) : CheckCM Bool := do
  let o₁ ← instListRevM b₁ fvs
  let o₂ ← instListRevM b₂ fvs
  defeqBindersInnerI mode r lam d o₁ o₂

/-- The cached binder-telescope comparison past the domains. -/
@[expose] def bindersStepI (mode : CheckMode) (r : CoreFnsI) (lam : Bool) (n d : Nat)
    (fvs : Array Expr) (b₁ b₂ : Expr) : CheckCM Bool :=
  match Expr.binderPair? lam b₁ b₂ with
  | some q => defeqBindersI mode r lam n (d + 1) fvs q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => bindersLeafI mode r lam d fvs b₁ b₂

theorem defeqBindersI_zero (r : CoreFnsI) (lam : Bool) (d : Nat) (fvs : Array Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqBindersI mode r lam 0 d fvs ty₁ body₁ ty₂ body₂ = (do
      let dom₂ ← instListRevM ty₂ fvs
      unless ← defeqDomainI r d fvs ty₁ ty₂ dom₂ do return false
      let fvs' ← pure (fvs.push (Expr.fvar d dom₂))
      bindersLeafI mode r lam d fvs' body₁ body₂ : CheckCM Bool) := rfl

set_option smartUnfolding false in
/-- `defeqBindersI`'s step (its structural recursion sits under the
binds, where the equation compiler generates no equation; smart
unfolding would not unfold it past the stuck `binderPair?` match). -/
theorem defeqBindersI_succ (r : CoreFnsI) (lam : Bool) (n d : Nat) (fvs : Array Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqBindersI mode r lam (n + 1) d fvs ty₁ body₁ ty₂ body₂ = (do
      let dom₂ ← instListRevM ty₂ fvs
      unless ← defeqDomainI r d fvs ty₁ ty₂ dom₂ do return false
      let fvs' ← pure (fvs.push (Expr.fvar d dom₂))
      bindersStepI mode r lam n d fvs' body₁ body₂ : CheckCM Bool) := by
  refine congrArg (instListRevM ty₂ fvs >>= ·) (funext fun dom₂ => ?_)
  refine congrArg (defeqDomainI r d fvs ty₁ ty₂ dom₂ >>= ·) (funext fun x => ?_)
  cases x
  · rfl
  · refine congrArg (pure (fvs.push (Expr.fvar d dom₂)) >>= ·) (funext fun fvs' => ?_)
    unfold bindersStepI
    cases Expr.binderPair? lam body₁ body₂ with
    | none => rfl
    | some q => rfl

section PureBinders
variable {m : Type → Type} [Monad m] (r : CoreFns m)

/-- The pure innermost level on the bulk-opened bodies. -/
@[expose] def bindersLeafP (mode : CheckMode) (lam : Bool) (d : Nat) (fvs : List Expr)
    (b₁ b₂ : Expr) : m Bool :=
  defeqBindersInner mode r lam d (b₁.instantiateList fvs) (b₂.instantiateList fvs)

/-- The pure binder-telescope comparison past the domains. -/
@[expose] def bindersStepP (mode : CheckMode) (lam : Bool) (n d : Nat) (fvs : List Expr)
    (b₁ b₂ : Expr) : m Bool :=
  match Expr.binderPair? lam b₁ b₂ with
  | some q => defeqBinders mode r lam n (d + 1) fvs q.1 q.2.1 q.2.2.1 q.2.2.2
  | none => bindersLeafP r mode lam d fvs b₁ b₂

theorem defeqBinders_zero (lam : Bool) (d : Nat) (fvs : List Expr) (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqBinders mode r lam 0 d fvs ty₁ body₁ ty₂ body₂ = (do
      unless ← defeqDomain r d fvs ty₁ ty₂ (ty₂.instantiateList fvs) do return false
      bindersLeafP r mode lam d (.fvar d (ty₂.instantiateList fvs) :: fvs) body₁ body₂ : m Bool) := by
  rw [defeqBinders.eq_1]
  rfl

theorem defeqBinders_succ (lam : Bool) (n d : Nat) (fvs : List Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    defeqBinders mode r lam (n + 1) d fvs ty₁ body₁ ty₂ body₂ = (do
      unless ← defeqDomain r d fvs ty₁ ty₂ (ty₂.instantiateList fvs) do return false
      bindersStepP r mode lam n d (.fvar d (ty₂.instantiateList fvs) :: fvs) body₁ body₂ : m Bool) := by
  rw [defeqBinders.eq_1]
  refine congrArg (defeqDomain r d fvs ty₁ ty₂ (ty₂.instantiateList fvs) >>= ·)
    (funext fun x => ?_)
  cases x
  · rfl
  · dsimp only
    unfold bindersStepP
    cases Expr.binderPair? lam body₁ body₂ with
    | none => rfl
    | some q => rfl

end PureBinders

/-- The binder-telescope comparison at fuel `n` simulates its fueled
original (a named predicate, so that the induction hypothesis is an
atom in `grind`'s context).  The scope facts are the level's parts
opened over the accumulator. -/
@[expose] def BindersSpec (mode : CheckMode) (eager : Bool) (env : Env) (f n : Nat) : Prop :=
  ∀ {lam : Bool} {d : Nat} {fvs : Array Expr} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState},
    CSOK mode eager env s₀ →
    Expr.WScoped d (ty₁.instantiateList fvs.toList.reverse) →
    Expr.WScoped d (body₁.instantiateList fvs.toList.reverse 1) →
    Expr.WScoped d (ty₂.instantiateList fvs.toList.reverse) →
    Expr.WScoped d (body₂.instantiateList fvs.toList.reverse 1) →
    ⦃fun s => s = s₀⦄
      defeqBindersI mode (coreKnotI mode eager (mkFEnv env) f) lam n d fvs ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqBinders mode (fueledFns mode eager env) lam n d fvs.toList.reverse
        ty₁ body₁ ty₂ body₂) v; ⊤⦄

theorem BindersSpec.triple {n : Nat} (h : BindersSpec mode eager env f n) {lam : Bool} {d : Nat}
    {fvs : Array Expr} {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (h1 : Expr.WScoped d (ty₁.instantiateList fvs.toList.reverse))
    (h2 : Expr.WScoped d (body₁.instantiateList fvs.toList.reverse 1))
    (h3 : Expr.WScoped d (ty₂.instantiateList fvs.toList.reverse))
    (h4 : Expr.WScoped d (body₂.instantiateList fvs.toList.reverse 1)) :
    ⦃fun s => s = s₀⦄
      defeqBindersI mode (coreKnotI mode eager (mkFEnv env) f) lam n d fvs ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqBinders mode (fueledFns mode eager env) lam n d fvs.toList.reverse
        ty₁ body₁ ty₂ body₂) v; ⊤⦄ :=
  h hs h1 h2 h3 h4

theorem bindersLeafC_spec (ih : SSimC mode eager env f) {lam : Bool} {d : Nat} {fvs : Array Expr}
    {b₁ b₂ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (h1 : Expr.WScoped (d + 1) (b₁.instantiateList fvs.toList.reverse))
    (h2 : Expr.WScoped (d + 1) (b₂.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ bindersLeafI mode (coreKnotI mode eager (mkFEnv env) f) lam d fvs b₁ b₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bindersLeafP (fueledFns mode eager env) mode lam d fvs.toList.reverse b₁ b₂) v; ⊤⦄ := by
  sym only [conleche_grind, bindersLeafP] =>
    vcgen [bindersLeafI, instListRevM_spec (mode := mode) (eager := eager) (env := env), defeqBindersInnerC_spec ih] <;> finish

theorem bindersStepC_spec (ih : SSimC mode eager env f) {n : Nat}
    (hn : BindersSpec mode eager env f n) {lam : Bool} {d : Nat} {fvs : Array Expr}
    {b₁ b₂ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (h1 : Expr.WScoped (d + 1) (b₁.instantiateList fvs.toList.reverse))
    (h2 : Expr.WScoped (d + 1) (b₂.instantiateList fvs.toList.reverse)) :
    ⦃fun s => s = s₀⦄ bindersStepI mode (coreKnotI mode eager (mkFEnv env) f) lam n d fvs b₁ b₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bindersStepP (fueledFns mode eager env) mode lam n d fvs.toList.reverse b₁ b₂) v;
      ⊤⦄ := by
  sym only [conleche_grind, bindersStepP] =>
    vcgen [bindersStepI, bindersLeafC_spec ih, hn.triple] <;> finish

/-- By induction on the descent budget. -/
theorem bindersSpec_all (ih : SSimC mode eager env f) (fuel : Nat) :
    BindersSpec mode eager env f fuel := by
  induction fuel with
  | zero =>
    intro lam d fvs ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _
    sym only [conleche_grind, defeqBinders_zero] =>
      vcgen [defeqBindersI_zero, instListRevM_spec (mode := mode) (eager := eager) (env := env), defeqDomainC_spec ih,
        bindersLeafC_spec ih] <;> finish
  | succ n ihn =>
    intro lam d fvs ty₁ body₁ ty₂ body₂ s₀ hs _ _ _ _
    sym only [conleche_grind, defeqBinders_succ] =>
      vcgen [defeqBindersI_succ, instListRevM_spec (mode := mode) (eager := eager) (env := env), defeqDomainC_spec ih,
        bindersStepC_spec ih ihn] <;> finish

/-- The binder-telescope comparison simulates its fueled original. -/
theorem defeqBindersC_spec (ih : SSimC mode eager env f) (fuel : Nat) {lam : Bool} {d : Nat}
    {ty₁ body₁ ty₂ body₂ : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (h1 : Expr.WScoped d ty₁) (h2 : Expr.WScoped d body₁) (h3 : Expr.WScoped d ty₂)
    (h4 : Expr.WScoped d body₂) :
    ⦃fun s => s = s₀⦄
      defeqBindersI mode (coreKnotI mode eager (mkFEnv env) f) lam fuel d #[] ty₁ body₁ ty₂ body₂
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqBinders mode (fueledFns mode eager env) lam fuel d [] ty₁ body₁ ty₂ body₂) v;
      ⊤⦄ := by
  have h := BindersSpec.triple (bindersSpec_all ih fuel) (lam := lam) (fvs := #[]) hs
    (by rw [toListRev_empty, Expr.instantiateList_nil]; exact h1)
    (by rw [toListRev_empty, Expr.instantiateList_nil]; exact h2)
    (by rw [toListRev_empty, Expr.instantiateList_nil]; exact h3)
    (by rw [toListRev_empty, Expr.instantiateList_nil]; exact h4)
  rwa [toListRev_empty] at h

/-- The syntactic fast path of `quickDefEq` (the arms' equations carry
it inside their `if`). -/
theorem quickDefEq_self {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) {d : Nat} {a b : Expr} (h : a = b) :
    quickDefEq mode r d a b = pure (some true) := by
  subst h; simp [quickDefEq]
grind_pattern [conleche_grind] quickDefEq_self => quickDefEq mode r d a b

/-- The easy cases simulate their specification. -/
theorem quickDefEqC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ quickDefEqI mode (coreKnotI mode eager (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (quickDefEq mode (fueledFns mode eager env) d a b)
        v; ⊤⦄ := by
  sym only [conleche_grind, quickDefEq] =>
    vcgen [quickDefEqI,
      isEquivLM_spec (mode := mode) (eager := eager) (env := env), liftFueled_spec (mode := mode)
          (eager := eager) (env := env),
      defeqBindersC_spec ih bindersFuel] <;> finish

/-- Offsets simulate their specification. -/
theorem defeqOffsetC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqOffsetI (coreKnotI mode eager (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (defeqOffset (fueledFns mode eager env) d a b) v; ⊤⦄
        := by
  sym only [conleche_grind, defeqOffset] =>
    vcgen [defeqOffsetI, ih.defeq_spec] <;> finish

/-- `try_unfold_proj_app` simulates its specification. -/
theorem tryUnfoldProjAppC_spec (ih : SSimC mode eager env f) {d : Nat} {e : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ tryUnfoldProjAppI (coreKnotI mode eager (mkFEnv env) f) d e
    ⦃fun o s' => CSOK mode eager env s' ∧ Runs (tryUnfoldProjApp (fueledFns mode eager env) d e) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, tryUnfoldProjApp] =>
    vcgen [tryUnfoldProjAppI, ih.whnfCore_spec] <;> finish

/-- The end of a step simulates its specification. -/
theorem deltaQuickC_spec (ih : SSimC mode eager env f) {d : Nat} {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ deltaQuickI mode (coreKnotI mode eager (mkFEnv env) f) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (deltaQuick mode (fueledFns mode eager env) d a b) v
        ∧
      StepPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, deltaQuick] =>
    vcgen [deltaQuickI, quickDefEqC_spec ih] <;> finish

/-- One lazy-delta step simulates its specification. -/
theorem lazyDeltaStepC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ lazyDeltaStepI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (lazyDeltaStep mode (fueledFns mode eager env) env d
        a b) v ∧
      StepPairWS d v; ⊤⦄ := by
  sym only [conleche_grind, lazyDeltaStep, unfoldDefinition_WScoped henv] =>
    vcgen [lazyDeltaStepI, tryUnfoldProjAppC_spec ih, deltaQuickC_spec ih, ih.whnfCore_spec,
      unfoldDefinitionC_spec (mode := mode) (eager := eager) (env := env), defeqSpineC_spec ih] <;>
          finish

section PureLazy

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
  (r : CoreFns m) (env : Env) (depth : Nat)

/-! The pure lazy-delta loop's continuations, named (the loop's `match`es
on the literal accelerations share one matcher, so as lambdas `grind`
would compare them). -/

/-- Past the step. -/
@[expose] def ldrStepP (mode : CheckMode) (eager : Bool) (n : Nat) (a b : Expr) : DeltaStep → m
    LazyRes
  | .cont a' b' => lazyDeltaReduction mode eager r env depth n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration. -/
@[expose] def ldrNatBP (mode : CheckMode) (eager : Bool) (n : Nat) (a b : Expr) : Option Expr → m
    LazyRes
  | some b₂ => r.defeq depth a b₂ >>= fun v => pure (.verdict v)
  | none => lazyDeltaStep mode r env depth a b >>= ldrStepP r env depth mode eager n a b

/-- Past the left literal acceleration. -/
@[expose] def ldrNatAP (mode : CheckMode) (eager : Bool) (n : Nat) (a b : Expr) : Option Expr → m
    LazyRes
  | some a₂ => r.defeq depth a₂ b >>= fun v => pure (.verdict v)
  | none =>
    (if eager || (!a.hasFvar && !b.hasFvar) then reduceNat r env depth b
      else pure none) >>= ldrNatBP r env depth mode eager n a b

/-- Past the offset check. -/
@[expose] def ldrOffP (mode : CheckMode) (eager : Bool) (n : Nat) (a b : Expr) : Option Bool → m
    LazyRes
  | some v => pure (.verdict v)
  | none =>
    (if eager || (!a.hasFvar && !b.hasFvar) then reduceNat r env depth a
      else pure none) >>= ldrNatAP r env depth mode eager n a b

/-- The pure loop's step with its continuations named. -/
theorem lazyDeltaReduction_succ (mode : CheckMode) (n : Nat) (a b : Expr) :
    lazyDeltaReduction mode eager r env depth (n + 1) a b =
      defeqOffset r depth a b >>= ldrOffP r env depth mode eager n a b := by
  rw [lazyDeltaReduction.eq_2]; rfl

end PureLazy

/-- The lazy-delta loop at budget `n` simulates its specification (a
named predicate, so that the induction hypothesis is an atom in
`grind`'s context). -/
@[expose] def LazySpec (mode : CheckMode) (eager : Bool) (env : Env) (f d n : Nat) : Prop :=
  ∀ {a b : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaReduction mode eager (fueledFns mode eager env) env d n a b) v ∧ LazyPairWS d
          v; ⊤⦄

theorem LazySpec.triple {d n : Nat} (h : LazySpec mode eager env f d n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaReduction mode eager (fueledFns mode eager env) env d n a b) v ∧ LazyPairWS d
          v; ⊤⦄ :=
  h hs hwa hwb

/-! The cached loop's continuations, named as the pure ones are, each
block its own triple (one short bind chain each). -/

/-- Past the step (cached). -/
@[expose] def ldrStepI (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : DeltaStep → CheckCM LazyRes
  | .cont a' b' => lazyDeltaReductionI mode eager r fe depth n a' b'
  | .eq => pure (.verdict true)
  | .diff => pure (.verdict false)
  | .unknown => pure (.unknown a b)

/-- Past the right literal acceleration (cached). -/
@[expose] def ldrNatBI (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : Option Expr → CheckCM LazyRes
  | some b₂ => do
    let v ← r.defeq depth a b₂
    pure (.verdict v)
  | none => lazyDeltaStepI mode r fe depth a b >>= ldrStepI mode eager r fe depth n a b

/-- Past the left literal acceleration (cached). -/
@[expose] def ldrNatAI (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) (fold : Bool) : Option Expr → CheckCM LazyRes
  | some a₂ => do
    let v ← r.defeq depth a₂ b
    pure (.verdict v)
  | none =>
    (if fold then reduceNatI r fe depth b else pure none) >>= ldrNatBI mode eager r fe depth n a b

/-- Past the offset check (cached). -/
@[expose] def ldrOffI (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth n : Nat)
    (a b : Expr) : Option Bool → CheckCM LazyRes
  | some v => pure (.verdict v)
  | none => do
    let fold ← pure (eager || (!Expr.hasFvar a && !Expr.hasFvar b))
    (if fold then reduceNatI r fe depth a else pure none) >>= ldrNatAI mode eager r fe depth n a b
        fold

/-- The cached loop's step with its continuations named. -/
theorem lazyDeltaReductionI_succ (r : CoreFnsI) (fe : FEnv) (depth n : Nat) (a b : Expr) :
    lazyDeltaReductionI mode eager r fe depth (n + 1) a b =
      defeqOffsetI r depth a b >>= ldrOffI mode eager r fe depth n a b := by
  rw [lazyDeltaReductionI.eq_2]; rfl

theorem ldrStepC_spec {d n : Nat} (hn : LazySpec mode eager env f d n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (st : DeltaStep)
    (hst : StepPairWS d st) :
    ⦃fun s => s = s₀⦄ ldrStepI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a
        b st
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ldrStepP (fueledFns mode eager env) env d mode eager n a b st) v ∧ LazyPairWS d v; ⊤⦄
          := by
  sym only [conleche_grind, ldrStepP] =>
    vcgen [ldrStepI, hn.triple] <;> finish

theorem ldrNatBC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode eager env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Expr) (ho : OptWS d o) :
    ⦃fun s => s = s₀⦄ ldrNatBI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a
        b o
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ldrNatBP (fueledFns mode eager env) env d mode eager n a b o) v ∧ LazyPairWS d v; ⊤⦄ :=
          by
  sym only [conleche_grind, ldrNatBP] =>
    vcgen [ldrNatBI, ih.defeq_spec, lazyDeltaStepC_spec ih henv, ldrStepC_spec hn] <;> finish

theorem ldrNatAC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode eager env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Expr) (ho : OptWS d o) :
    ⦃fun s => s = s₀⦄ ldrNatAI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a b
      (eager || (!Expr.hasFvar a && !Expr.hasFvar b)) o
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ldrNatAP (fueledFns mode eager env) env d mode eager n a b o) v ∧ LazyPairWS d v; ⊤⦄ :=
          by
  sym only [conleche_grind, ldrNatAP] =>
    vcgen [ldrNatAI, ih.defeq_spec, reduceNatC_spec ih, ldrNatBC_spec ih henv hn] <;> finish

theorem ldrOffC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d n : Nat}
    (hn : LazySpec mode eager env f d n) {a b : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) (o : Option Bool) :
    ⦃fun s => s = s₀⦄ ldrOffI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a b
        o
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (ldrOffP (fueledFns mode eager env) env d mode eager n a b o) v ∧ LazyPairWS d v; ⊤⦄ :=
          by
  sym only [conleche_grind, ldrOffP] =>
    vcgen [ldrOffI, reduceNatC_spec ih, ldrNatAC_spec ih henv hn] <;> finish

/-- By induction on the step budget. -/
theorem lazySpec_all (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} (n : Nat) :
    LazySpec mode eager env f d n := by
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
theorem lazyDeltaReductionC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    (n : Nat) {a b : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaReductionI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaReduction mode eager (fueledFns mode eager env) env d n a b) v ∧ LazyPairWS d
          v; ⊤⦄ :=
  LazySpec.triple (lazySpec_all ih henv n) hs hwa hwb

/-- `lazy_delta_proj_reduction` at budget `n` simulates its
specification (the induction hypothesis as an atom). -/
@[expose] def LazyProjSpec (mode : CheckMode) (eager : Bool) (env : Env) (f d : Nat) (sn : Name)
    (ip n : Nat) :
    Prop :=
  ∀ {a b : Expr} {s₀ : CState}, CSOK mode eager env s₀ → Expr.WScoped d a → Expr.WScoped d b →
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode eager env) env d sn ip n a b) v; ⊤⦄

theorem LazyProjSpec.triple {d : Nat} {sn : Name} {ip n : Nat}
    (h : LazyProjSpec mode eager env f d sn ip n) {a b : Expr} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode eager env) env d sn ip n a b) v; ⊤⦄ :=
  h hs hwa hwb

/-- By induction on the step budget. -/
theorem lazyProjSpec_all (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {sn : Name}
    {ip : Nat} (n : Nat) : LazyProjSpec mode eager env f d sn ip n := by
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
theorem lazyDeltaProjReductionC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat}
    {sn : Name} {ip : Nat} (n : Nat) {a b : Expr} {s₀ : CState} (hs : CSOK mode eager env s₀)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      lazyDeltaProjReductionI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d sn ip n a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (lazyDeltaProjReduction mode (fueledFns mode eager env) env d sn ip n a b) v; ⊤⦄ :=
  LazyProjSpec.triple (lazyProjSpec_all ih henv n) hs hwa hwb

/-- The proj/proj check simulates its specification. -/
theorem defeqProjPairC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄
      defeqProjPairI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqProjPair mode (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqProjPair] =>
    vcgen [defeqProjPairI, lazyDeltaProjReductionC_spec ih henv] <;> finish

/-- The stuck comparison simulates its specification. -/
theorem defeqStuckC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState}
    (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqStuckI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (defeqStuck mode (fueledFns mode eager env) env d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqStuck, strLitStoredF_eq, strLitToConstructor_WScoped] =>
    vcgen [defeqStuckI, ih.defeq_spec, stuckIrrelC_spec ih henv, etaCertC_spec ih, defEqListC_spec ih,
      isEquivListLM_spec (mode := mode) (eager := eager) (env := env),
      liftFueled_spec (mode := mode) (eager := eager) (env := env)] <;> finish

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
@[expose] def bodyQ2P (mode : CheckMode) (eager : Bool) (a' b' : Expr) : Option Bool → m Bool
  | some v => pure v
  | none => lazyDeltaReduction mode eager r env depth defeqLoopFuel a' b' >>= bodyLazyP r env depth
      mode

/-- Past proof irrelevance: the cheap normalization and `quickDefEq`. -/
@[expose] def bodyPIP (mode : CheckMode) (eager : Bool) (a b : Expr) : m Bool := do
  if ← propIrrel r env depth a b then pure true else
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  quickDefEq mode r depth a' b' >>= bodyQ2P r env depth mode eager a' b'

/-- Past `quickDefEq` on the unreduced pair. -/
@[expose] def bodyQ1P (mode : CheckMode) (eager : Bool) (a b : Expr) : Option Bool → m Bool
  | some v => pure v
  | none => bodyPIP r env depth mode eager a b

/-- `defeqBody` with its continuations named. -/
theorem defeqBody_eq (mode : CheckMode) (a b : Expr) :
    defeqBody mode eager r env depth a b =
      (if a == b then pure true else do
        if ← (if b.isBoolTrue && (eager || !a.hasFvar) then
            boolTrueShortcut r depth a else pure false) then pure true else
        quickDefEq mode r depth a b >>= bodyQ1P r env depth mode eager a b : m Bool) := by
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
@[expose] def bodyQ2I (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a' b' : Expr) : Option Bool → CheckCM Bool
  | some v => pure v
  | none =>
    lazyDeltaReductionI mode eager r fe depth defeqLoopFuel a' b' >>= bodyLazyI mode r fe depth

/-- Past proof irrelevance (cached). -/
@[expose] def bodyPII (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b : Expr) : CheckCM Bool := do
  if ← propIrrelI r fe depth a b then pure true else
  let a' ← r.whnfCore true depth a
  let b' ← r.whnfCore true depth b
  quickDefEqI mode r depth a' b' >>= bodyQ2I mode eager r fe depth a' b'

/-- Past `quickDefEq` on the unreduced pair (cached). -/
@[expose] def bodyQ1I (mode : CheckMode) (eager : Bool) (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b : Expr) : Option Bool → CheckCM Bool
  | some v => pure v
  | none => bodyPII mode eager r fe depth a b

/-- `defeqBodyI` with its continuations named. -/
theorem defeqBodyI_eq (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    defeqBodyI mode eager r fe depth a b =
      (if a == b then pure true else do
        let bt ← pure (Expr.isBoolTrue b)
        let af ← pure (Expr.hasFvar a)
        if ← (if bt && (eager || !af) then boolTrueShortcutI r depth a
            else pure false) then pure true else
        quickDefEqI mode r depth a b >>= bodyQ1I mode eager r fe depth a b : CheckCM Bool) := rfl

theorem bodyTailC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ bodyTailI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bodyTailP (fueledFns mode eager env) env d mode a b) v; ⊤⦄ := by
  sym only [conleche_grind, bodyTailP] =>
    vcgen [bodyTailI, defeqProjPairC_spec ih henv, defeqStuckC_spec ih henv, ih.whnfCore_spec,
      ih.defeq_spec] <;> finish

theorem bodyLazyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {s₀ : CState}
    (hs : CSOK mode eager env s₀) (lr : LazyRes) (hlr : LazyPairWS d lr) :
    ⦃fun s => s = s₀⦄ bodyLazyI mode (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d lr
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bodyLazyP (fueledFns mode eager env) env d mode lr) v; ⊤⦄ := by
  sym only [conleche_grind, bodyLazyP] =>
    vcgen [bodyLazyI, bodyTailC_spec ih henv] <;> finish

theorem bodyQ2C_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ2I mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b o
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bodyQ2P (fueledFns mode eager env) env d mode eager a b o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ2P] =>
    vcgen [bodyQ2I, lazyDeltaReductionC_spec ih henv, bodyLazyC_spec ih henv] <;> finish

theorem bodyPIC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ bodyPII mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bodyPIP (fueledFns mode eager env) env d mode eager a b) v; ⊤⦄ := by
  sym only [conleche_grind, bodyPIP] =>
    vcgen [bodyPII, propIrrelC_spec ih, ih.whnfCore_spec, quickDefEqC_spec ih,
      bodyQ2C_spec ih henv] <;> finish

theorem bodyQ1C_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b)
    (o : Option Bool) :
    ⦃fun s => s = s₀⦄ bodyQ1I mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b o
    ⦃fun v s' => CSOK mode eager env s' ∧
      Runs (bodyQ1P (fueledFns mode eager env) env d mode eager a b o) v; ⊤⦄ := by
  sym only [conleche_grind, bodyQ1P] =>
    vcgen [bodyQ1I, bodyPIC_spec ih henv] <;> finish

/-- The definitional-equality body simulates its specification. -/
theorem defeqBodyC_spec (ih : SSimC mode eager env f) (henv : EnvWF env) {s₀ : CState} {d : Nat}
    {a b : Expr} (hs : CSOK mode eager env s₀) (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ defeqBodyI mode eager (coreKnotI mode eager (mkFEnv env) f) (mkFEnv env) d a b
    ⦃fun v s' => CSOK mode eager env s' ∧ Runs (defeqBody mode eager (fueledFns mode eager env) env
        d a b) v; ⊤⦄ := by
  sym only [conleche_grind, defeqBody_eq] =>
    vcgen [defeqBodyI_eq, boolTrueShortcutC_spec ih, quickDefEqC_spec ih,
      bodyQ1C_spec ih henv] <;> finish

end Walks

end ConLeche.Cached
