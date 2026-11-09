module

public import ConLeche.Verify.Knot

public section

/-!
# A generic relational pair monad over the checker core

The core bodies are monad-polymorphic, so relational proofs about two
instantiations (fuel monotonicity, the cache-refinement bridge) need
not walk the bodies: instantiate them **once** at a monad of pairs
carrying the relation (`PairM`), whose `bind`/`pure`/`throw` preserve
it — the instantiated body's subtype proof *is* the per-body lemma.
The projection equations relating the pair instantiation's components
back to the plain instantiations are `rfl` up to a small tactic
cascade; the three structurally recursive list helpers get hand-rolled
commute lemmas.
-/

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

/-- A binary relation between two checker monads, closed under the
monadic operations the bodies use. -/
structure MonadRel (M₁ M₂ : Type → Type)
    [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂] where
  R : ∀ {α : Type}, M₁ α → M₂ α → Prop
  pure_rel : ∀ {α : Type} (a : α), R (pure a) (pure a)
  bind_rel : ∀ {α β : Type} {x₁ : M₁ α} {x₂ : M₂ α}
    {f₁ : α → M₁ β} {f₂ : α → M₂ β},
    R x₁ x₂ → (∀ a, R (f₁ a) (f₂ a)) → R (x₁ >>= f₁) (x₂ >>= f₂)
  throw_rel : ∀ {α : Type} (e : CheckError),
    R (throw e : M₁ α) (throw e : M₂ α)

variable {M₁ M₂ : Type → Type}
  [Monad M₁] [Monad M₂]
  [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]

/-- Pairs of computations related by `rel`. -/
@[expose] def PairM (rel : MonadRel M₁ M₂) (α : Type) : Type :=
  {pq : M₁ α × M₂ α // rel.R pq.1 pq.2}

namespace PairM

variable {rel : MonadRel M₁ M₂}

instance : Monad (PairM rel) where
  pure a := ⟨(pure a, pure a), rel.pure_rel a⟩
  bind x f :=
    ⟨(x.val.1 >>= fun a => (f a).val.1, x.val.2 >>= fun a => (f a).val.2),
      rel.bind_rel x.property (fun a => (f a).property)⟩

instance : MonadExceptOf CheckError (PairM rel) where
  throw e := ⟨(throw e, throw e), rel.throw_rel e⟩
  -- the bodies never catch; a related stub keeps the instance total
  tryCatch _ _ :=
    ⟨(throw (.internal "tryCatch unsupported"),
      throw (.internal "tryCatch unsupported")),
      rel.throw_rel _⟩

@[simp] theorem fst_bind {α β : Type} (x : PairM rel α)
    (f : α → PairM rel β) :
    (x >>= f).val.1 = x.val.1 >>= fun a => (f a).val.1 := rfl

@[simp] theorem snd_bind {α β : Type} (x : PairM rel α)
    (f : α → PairM rel β) :
    (x >>= f).val.2 = x.val.2 >>= fun a => (f a).val.2 := rfl

@[simp] theorem fst_pure {α : Type} (a : α) :
    (pure a : PairM rel α).val.1 = pure a := rfl

@[simp] theorem snd_pure {α : Type} (a : α) :
    (pure a : PairM rel α).val.2 = pure a := rfl

@[simp] theorem fst_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.1 = if c then x.val.1 else y.val.1 := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem snd_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.2 = if c then x.val.2 else y.val.2 := by
  by_cases hc : c <;> simp [hc]

end PairM

/-- Componentwise relatedness of two core records.  (Task #172 B4: the
io slot joins as the sixth component.) -/
@[expose] def FnsRel (rel : MonadRel M₁ M₂) (r₁ : CoreFns M₁) (r₂ : CoreFns M₂) :
    Prop :=
  (∀ c d e, rel.R (r₁.whnfCore c d e) (r₂.whnfCore c d e)) ∧
  (∀ d e, rel.R (r₁.whnf d e) (r₂.whnf d e)) ∧
  (∀ d e, rel.R (r₁.infer d e) (r₂.infer d e)) ∧
  (∀ d a b, rel.R (r₁.defeq d a b) (r₂.defeq d a b)) ∧
  (∀ d a b, rel.R (r₁.defeqE d a b) (r₂.defeqE d a b)) ∧
  (∀ d e, rel.R (r₁.inferIO d e) (r₂.inferIO d e))

/-- Relatedness transports along the io-grade view: the view only
permutes fields. -/
theorem FnsRel.ioView {rel : MonadRel M₁ M₂} {r₁ : CoreFns M₁}
    {r₂ : CoreFns M₂} (h : FnsRel rel r₁ r₂) :
    FnsRel rel r₁.ioView r₂.ioView :=
  ⟨h.1, h.2.1, h.2.2.2.2.2, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The paired record. -/
def pairFns {rel : MonadRel M₁ M₂} (r₁ : CoreFns M₁) (r₂ : CoreFns M₂)
    (h : FnsRel rel r₁ r₂) : CoreFns (PairM rel) where
  whnfCore c d e := ⟨(r₁.whnfCore c d e, r₂.whnfCore c d e), h.1 c d e⟩
  whnf d e := ⟨(r₁.whnf d e, r₂.whnf d e), h.2.1 d e⟩
  infer d e := ⟨(r₁.infer d e, r₂.infer d e), h.2.2.1 d e⟩
  defeq d a b := ⟨(r₁.defeq d a b, r₂.defeq d a b), h.2.2.2.1 d a b⟩
  defeqE d a b := ⟨(r₁.defeqE d a b, r₂.defeqE d a b), h.2.2.2.2.1 d a b⟩
  inferIO d e := ⟨(r₁.inferIO d e, r₂.inferIO d e), h.2.2.2.2.2 d e⟩

section Commute

variable {rel : MonadRel M₁ M₂} {r₁ : CoreFns M₁} {r₂ : CoreFns M₂}
  {h : FnsRel rel r₁ r₂} {env : Env}

theorem iotaCertsFull_fst (d : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCertsFull (pairFns r₁ r₂ h) env d ty args).val.1 =
        iotaCertsFull r₁ env d ty args
  | _, [] => rfl
  | .forallE ty body, arg :: rest => by
    show ((do
        let ta ← (pairFns r₁ r₂ h).infer d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCertsFull (pairFns r₁ r₂ h) env d (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.1 = (do
        let ta ← r₁.infer d arg
        if ← r₁.defeq d ta ty then
          iotaCertsFull r₁ env d (body.instantiate1 arg) rest
        else pure false)
    rw [PairM.fst_bind]
    congr 1
    funext ta
    rw [PairM.fst_bind]
    congr 1
    funext b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact iotaCertsFull_fst d (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem iotaCertsFull_snd (d : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCertsFull (pairFns r₁ r₂ h) env d ty args).val.2 =
        iotaCertsFull r₂ env d ty args
  | _, [] => rfl
  | .forallE ty body, arg :: rest => by
    show ((do
        let ta ← (pairFns r₁ r₂ h).infer d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCertsFull (pairFns r₁ r₂ h) env d (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.2 = (do
        let ta ← r₂.infer d arg
        if ← r₂.defeq d ta ty then
          iotaCertsFull r₂ env d (body.instantiate1 arg) rest
        else pure false)
    rw [PairM.snd_bind]
    congr 1
    funext ta
    rw [PairM.snd_bind]
    congr 1
    funext b
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact iotaCertsFull_snd d (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _, _ :: _
  | .letE _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem defEqList_fst (d : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (pairFns r₁ r₂ h) env d as bs).val.1 =
        defEqList r₁ env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (pairFns r₁ r₂ h).defeq d a b then
          defEqList (pairFns r₁ r₂ h) env d as bs
        else pure false : PairM rel Bool)).val.1 = (do
        if ← r₁.defeq d a b then
          defEqList r₁ env d as bs
        else pure false)
    rw [PairM.fst_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_fst d as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem defEqList_snd (d : Nat) :
    ∀ (as bs : List Expr),
      (defEqList (pairFns r₁ r₂ h) env d as bs).val.2 =
        defEqList r₂ env d as bs
  | [], [] => rfl
  | a :: as, b :: bs => by
    show ((do
        if ← (pairFns r₁ r₂ h).defeq d a b then
          defEqList (pairFns r₁ r₂ h) env d as bs
        else pure false : PairM rel Bool)).val.2 = (do
        if ← r₂.defeq d a b then
          defEqList r₂ env d as bs
        else pure false)
    rw [PairM.snd_bind]
    congr 1
    funext r
    cases r with
    | true =>
      simp only [↓reduceIte]
      exact defEqList_snd d as bs
    | false => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

theorem defeqBindersInner_fst (lam : Bool) (d : Nat) (b₁ b₂ : Expr) :
    (defeqBindersInner mode (pairFns r₁ r₂ h) lam d b₁ b₂).val.1 =
      defeqBindersInner mode r₁ lam d b₁ b₂ := by
  unfold defeqBindersInner
  repeat (first
    | rfl
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem defeqDomain_fst (d : Nat) (fvs : List Expr) (ty₁ ty₂ dom₂ : Expr) :
    (defeqDomain (pairFns r₁ r₂ h) d fvs ty₁ ty₂ dom₂).val.1 =
      defeqDomain r₁ d fvs ty₁ ty₂ dom₂ := by
  unfold defeqDomain
  split <;> rfl

theorem defeqBinders_fst (lam : Bool) :
    ∀ (fuel d : Nat) (fvs : List Expr) (ty₁ body₁ ty₂ body₂ : Expr),
      (defeqBinders mode (pairFns r₁ r₂ h) lam fuel d fvs ty₁ body₁ ty₂ body₂).val.1 =
        defeqBinders mode r₁ lam fuel d fvs ty₁ body₁ ty₂ body₂
  | fuel, d, fvs, ty₁, body₁, ty₂, body₂ => by
    rw [defeqBinders.eq_def, defeqBinders.eq_def]
    rw [PairM.fst_bind, defeqDomain_fst]
    congr 1
    funext ok
    cases ok with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      split
      · exact defeqBinders_fst lam _ (d + 1) _ _ _ _ _
      · exact defeqBindersInner_fst lam d _ _

theorem defeqBindersInner_snd (lam : Bool) (d : Nat) (b₁ b₂ : Expr) :
    (defeqBindersInner mode (pairFns r₁ r₂ h) lam d b₁ b₂).val.2 =
      defeqBindersInner mode r₂ lam d b₁ b₂ := by
  unfold defeqBindersInner
  repeat (first
    | rfl
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem defeqDomain_snd (d : Nat) (fvs : List Expr) (ty₁ ty₂ dom₂ : Expr) :
    (defeqDomain (pairFns r₁ r₂ h) d fvs ty₁ ty₂ dom₂).val.2 =
      defeqDomain r₂ d fvs ty₁ ty₂ dom₂ := by
  unfold defeqDomain
  split <;> rfl

theorem defeqBinders_snd (lam : Bool) :
    ∀ (fuel d : Nat) (fvs : List Expr) (ty₁ body₁ ty₂ body₂ : Expr),
      (defeqBinders mode (pairFns r₁ r₂ h) lam fuel d fvs ty₁ body₁ ty₂ body₂).val.2 =
        defeqBinders mode r₂ lam fuel d fvs ty₁ body₁ ty₂ body₂
  | fuel, d, fvs, ty₁, body₁, ty₂, body₂ => by
    rw [defeqBinders.eq_def, defeqBinders.eq_def]
    rw [PairM.snd_bind, defeqDomain_snd]
    congr 1
    funext ok
    cases ok with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      split
      · exact defeqBinders_snd lam _ (d + 1) _ _ _ _ _
      · exact defeqBindersInner_snd lam d _ _

theorem iotaIndexOk_fst (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : List Expr) :
    (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs idx).val.1 =
      iotaIndexOk r₁ env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, ite_eq_left hmr]; rfl
  · simp only [iotaIndexOk, ite_eq_right hmr]
    cases piResidual tyCtor margs with
    | none => rfl
    | some residual => exact defEqList_fst d _ _

theorem iotaIndexOk_snd (d : Nat) (mI rP cnP : Nat) (tyCtor : Expr)
    (margs idx : List Expr) :
    (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs idx).val.2 =
      iotaIndexOk r₂ env d mI rP cnP tyCtor margs idx := by
  by_cases hmr : mI = rP
  · simp only [iotaIndexOk, ite_eq_left hmr]; rfl
  · simp only [iotaIndexOk, ite_eq_right hmr]
    cases piResidual tyCtor margs with
    | none => rfl
    | some residual => exact defEqList_snd d _ _

theorem defeqArg_fst (d : Nat) (a ta ty : Expr) :
    (defeqArg (pairFns r₁ r₂ h) d a ta ty).val.1 = defeqArg r₁ d a ta ty := by
  unfold defeqArg; split <;> rfl

theorem defeqArg_snd (d : Nat) (a ta ty : Expr) :
    (defeqArg (pairFns r₁ r₂ h) d a ta ty).val.2 = defeqArg r₂ d a ta ty := by
  unfold defeqArg; split <;> rfl

theorem defeqSpine_fst (d : Nat) (a b : Expr) :
    (defeqSpine (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqSpine r₁ env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_fst])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem defeqSpine_snd (d : Nat) (a b : Expr) :
    (defeqSpine (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqSpine r₂ env d a b := by
  unfold defeqSpine
  repeat (first
    | rfl
    | (rw [defEqList_snd])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem liftFueled_fst_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.1 = liftFueled what o := by
  cases o <;> rfl

theorem liftFueled_snd_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.2 = liftFueled what o := by
  cases o <;> rfl

theorem formerSortLoop_fst {wh : Nat → Expr → PairM rel Expr} {wh' : Nat → Expr → M₁ Expr}
    (hw : ∀ d e, (wh d e).val.1 = wh' d e) :
    ∀ (d n : Nat) (e : Expr),
      (formerSortLoop wh d n e).val.1 = formerSortLoop wh' d n e
  | d, 0, e => by
    unfold formerSortLoop
    rw [PairM.fst_bind, hw]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> rfl
  | d, n + 1, e => by
    unfold formerSortLoop
    rw [PairM.fst_bind, hw]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    exact formerSortLoop_fst hw (d + 1) n _

theorem formerNeverZeroAt_fst_proj (cvT : ConstantVal) (caps : IndCaps) (us : List Level) :
    (formerNeverZeroAt (pairFns r₁ r₂ h).whnf cvT caps us).val.1 =
      formerNeverZeroAt r₁.whnf cvT caps us := by
  unfold formerNeverZeroAt
  split
  · rfl
  · rw [PairM.fst_bind, formerSortLoop_fst (fun _ _ => rfl)]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem iotaCase3At_fst_proj (find? : Name → Option ConstantInfo) (isK : Bool) (cvj : ConstantVal)
    (us : List Level) :
    (iotaCase3At (pairFns r₁ r₂ h).whnf find? isK cvj us).val.1 =
      iotaCase3At r₁.whnf find? isK cvj us := by
  unfold iotaCase3At
  split
  · rfl
  · split
    · split
      · rw [PairM.fst_bind, formerNeverZeroAt_fst_proj]
        rfl
      · rfl
    · rfl

theorem formerSortLoop_snd {wh : Nat → Expr → PairM rel Expr} {wh' : Nat → Expr → M₂ Expr}
    (hw : ∀ d e, (wh d e).val.2 = wh' d e) :
    ∀ (d n : Nat) (e : Expr),
      (formerSortLoop wh d n e).val.2 = formerSortLoop wh' d n e
  | d, 0, e => by
    unfold formerSortLoop
    rw [PairM.snd_bind, hw]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> rfl
  | d, n + 1, e => by
    unfold formerSortLoop
    rw [PairM.snd_bind, hw]
    refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    exact formerSortLoop_snd hw (d + 1) n _

theorem formerNeverZeroAt_snd_proj (cvT : ConstantVal) (caps : IndCaps) (us : List Level) :
    (formerNeverZeroAt (pairFns r₁ r₂ h).whnf cvT caps us).val.2 =
      formerNeverZeroAt r₂.whnf cvT caps us := by
  unfold formerNeverZeroAt
  split
  · rfl
  · rw [PairM.snd_bind, formerSortLoop_snd (fun _ _ => rfl)]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem iotaCase3At_snd_proj (find? : Name → Option ConstantInfo) (isK : Bool) (cvj : ConstantVal)
    (us : List Level) :
    (iotaCase3At (pairFns r₁ r₂ h).whnf find? isK cvj us).val.2 =
      iotaCase3At r₂.whnf find? isK cvj us := by
  unfold iotaCase3At
  split
  · rfl
  · split
    · split
      · rw [PairM.snd_bind, formerNeverZeroAt_snd_proj]
        rfl
      · rfl
    · rfl

macro "fst_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCase3At_fst_proj])
    | (rw [formerNeverZeroAt_fst_proj])
    | (rw [iotaCertsFull_fst])
    | (rw [defeqBinders_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac" : tactic =>
  `(tactic| fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step <;> fst_step <;>
    fst_step <;> fst_step <;> fst_step)

macro "snd_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCase3At_snd_proj])
    | (rw [formerNeverZeroAt_snd_proj])
    | (rw [iotaCertsFull_snd])
    | (rw [defeqBinders_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac" : tactic =>
  `(tactic| snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step <;> snd_step <;>
    snd_step <;> snd_step <;> snd_step)

theorem reduceNat_fst_proj (d : Nat) (e : Expr) :
    (reduceNat (pairFns r₁ r₂ h) env d e).val.1 =
      reduceNat r₁ env d e := by
  unfold reduceNat
  fst_tac

theorem reduceNat_snd_proj (d : Nat) (e : Expr) :
    (reduceNat (pairFns r₁ r₂ h) env d e).val.2 =
      reduceNat r₂ env d e := by
  unfold reduceNat
  snd_tac

theorem ensureSort_fst_proj (d : Nat) (e : Expr) :
    (ensureSort (pairFns r₁ r₂ h) env d e).val.1 =
      ensureSort r₁ env d e := by
  unfold ensureSort
  fst_tac

theorem ensureSort_snd_proj (d : Nat) (e : Expr) :
    (ensureSort (pairFns r₁ r₂ h) env d e).val.2 =
      ensureSort r₂ env d e := by
  unfold ensureSort
  snd_tac

theorem checkGuardRows_fst (guardSort : Level) {inf wh : Nat → Expr → PairM rel Expr} {inf₁ wh₁ : Nat → Expr → M₁ Expr}
    (hi : ∀ d e, (inf d e).val.1 = inf₁ d e) (hw : ∀ d e, (wh d e).val.1 = wh₁ d e) :
    ∀ rows, (checkGuardRows inf wh guardSort rows).val.1 = checkGuardRows inf₁ wh₁ guardSort rows
  | [] => rfl
  | (d, dom) :: rest => by
    unfold checkGuardRows
    rw [PairM.fst_bind]
    rw [hi d dom]; refine congrArg _ (funext fun t => ?_)
    rw [PairM.fst_bind]
    rw [hw d t]; refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    dsimp only []
    have hk := checkGuardRows_fst guardSort hi hw rest
    split
    · exact hk
    · rw [PairM.fst_bind, hk]; rfl

theorem checkGuardRows_snd (guardSort : Level) {inf wh : Nat → Expr → PairM rel Expr} {inf₂ wh₂ : Nat → Expr → M₂ Expr}
    (hi : ∀ d e, (inf d e).val.2 = inf₂ d e) (hw : ∀ d e, (wh d e).val.2 = wh₂ d e) :
    ∀ rows, (checkGuardRows inf wh guardSort rows).val.2 = checkGuardRows inf₂ wh₂ guardSort rows
  | [] => rfl
  | (d, dom) :: rest => by
    unfold checkGuardRows
    rw [PairM.snd_bind]
    rw [hi d dom]; refine congrArg _ (funext fun t => ?_)
    rw [PairM.snd_bind]
    rw [hw d t]; refine congrArg _ (funext fun w => ?_)
    cases w <;> try rfl
    dsimp only []
    have hk := checkGuardRows_snd guardSort hi hw rest
    split
    · exact hk
    · rw [PairM.snd_bind, hk]; rfl

theorem projGuardSort_fst_proj (cvT : ConstantVal) (caps : IndCaps) (us : List Level) :
    (projGuardSort (pairFns r₁ r₂ h).whnf cvT caps us).val.1 =
      projGuardSort r₁.whnf cvT caps us := by
  unfold projGuardSort
  split
  · rfl
  · rw [PairM.fst_bind, formerSortLoop_fst (fun _ _ => rfl)]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem checkProjGuard_fst_proj (entry : ProjEntry) (us : List Level) :
    (checkProjGuard (pairFns r₁ r₂ h).inferIO (pairFns r₁ r₂ h).whnf env entry us).val.1 =
      checkProjGuard r₁.inferIO r₁.whnf env entry us := by
  unfold checkProjGuard
  split
  · rw [PairM.fst_bind, projGuardSort_fst_proj]
    refine congrArg _ (funext fun o => ?_)
    cases o with
    | none => rfl
    | some guardSort =>
      dsimp only
      split
      · exact checkGuardRows_fst guardSort (fun _ _ => rfl) (fun _ _ => rfl) _
      · rfl
  · rfl

theorem projGuardSort_snd_proj (cvT : ConstantVal) (caps : IndCaps) (us : List Level) :
    (projGuardSort (pairFns r₁ r₂ h).whnf cvT caps us).val.2 =
      projGuardSort r₂.whnf cvT caps us := by
  unfold projGuardSort
  split
  · rfl
  · rw [PairM.snd_bind, formerSortLoop_snd (fun _ _ => rfl)]
    refine congrArg _ (funext fun o => ?_)
    cases o <;> rfl

theorem checkProjGuard_snd_proj (entry : ProjEntry) (us : List Level) :
    (checkProjGuard (pairFns r₁ r₂ h).inferIO (pairFns r₁ r₂ h).whnf env entry us).val.2 =
      checkProjGuard r₂.inferIO r₂.whnf env entry us := by
  unfold checkProjGuard
  split
  · rw [PairM.snd_bind, projGuardSort_snd_proj]
    refine congrArg _ (funext fun o => ?_)
    cases o with
    | none => rfl
    | some guardSort =>
      dsimp only
      split
      · exact checkGuardRows_snd guardSort (fun _ _ => rfl) (fun _ _ => rfl) _
      · rfl
  · rfl

theorem checkProjGuardI_fst_proj (entry : ProjEntry) (us : List Level) :
    (checkProjGuard (pairFns r₁ r₂ h).infer (pairFns r₁ r₂ h).whnf env entry us).val.1 =
      checkProjGuard r₁.infer r₁.whnf env entry us := by
  unfold checkProjGuard
  split
  · rw [PairM.fst_bind, projGuardSort_fst_proj]
    refine congrArg _ (funext fun o => ?_)
    cases o with
    | none => rfl
    | some guardSort =>
      dsimp only
      split
      · exact checkGuardRows_fst guardSort (fun _ _ => rfl) (fun _ _ => rfl) _
      · rfl
  · rfl

theorem checkProjGuardI_snd_proj (entry : ProjEntry) (us : List Level) :
    (checkProjGuard (pairFns r₁ r₂ h).infer (pairFns r₁ r₂ h).whnf env entry us).val.2 =
      checkProjGuard r₂.infer r₂.whnf env entry us := by
  unfold checkProjGuard
  split
  · rw [PairM.snd_bind, projGuardSort_snd_proj]
    refine congrArg _ (funext fun o => ?_)
    cases o with
    | none => rfl
    | some guardSort =>
      dsimp only
      split
      · exact checkGuardRows_snd guardSort (fun _ _ => rfl) (fun _ _ => rfl) _
      · rfl
  · rfl

theorem proofIrrel_fst_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) d a b).val.1 =
      proofIrrel r₁ d a b := by
  unfold proofIrrel
  fst_tac

theorem proofIrrel_snd_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) d a b).val.2 =
      proofIrrel r₂ d a b := by
  unfold proofIrrel
  snd_tac

theorem propIrrel_fst_proj (d : Nat) (a b : Expr) :
    (propIrrel (pairFns r₁ r₂ h) env d a b).val.1 =
      propIrrel r₁ env d a b := by
  unfold propIrrel
  fst_tac

theorem propIrrel_snd_proj (d : Nat) (a b : Expr) :
    (propIrrel (pairFns r₁ r₂ h) env d a b).val.2 =
      propIrrel r₂ env d a b := by
  unfold propIrrel
  snd_tac

theorem structEtaCertWith_fst_proj (d : Nat) (a b wtb : Expr) :
    (structEtaCertWith (pairFns r₁ r₂ h) env d a b wtb).val.1 =
      structEtaCertWith r₁ env d a b wtb := by
  unfold structEtaCertWith
  fst_tac

theorem structEtaCertWith_snd_proj (d : Nat) (a b wtb : Expr) :
    (structEtaCertWith (pairFns r₁ r₂ h) env d a b wtb).val.2 =
      structEtaCertWith r₂ env d a b wtb := by
  unfold structEtaCertWith
  snd_tac

theorem structUnitCert_fst_proj (d : Nat) (a b : Expr) :
    (structUnitCert (pairFns r₁ r₂ h) env d a b).val.1 =
      structUnitCert r₁ env d a b := by
  unfold structUnitCert
  fst_tac

theorem structUnitCert_snd_proj (d : Nat) (a b : Expr) :
    (structUnitCert (pairFns r₁ r₂ h) env d a b).val.2 =
      structUnitCert r₂ env d a b := by
  unfold structUnitCert
  snd_tac

theorem etaCert_fst_proj (d : Nat) (ty body : Expr) (b : Expr) :
    (etaCert mode (pairFns r₁ r₂ h) env d ty body b).val.1 =
      etaCert mode r₁ env d ty body b := by
  unfold etaCert
  fst_tac

theorem etaCert_snd_proj (d : Nat) (ty body : Expr) (b : Expr) :
    (etaCert mode (pairFns r₁ r₂ h) env d ty body b).val.2 =
      etaCert mode r₂ env d ty body b := by
  unfold etaCert
  snd_tac

macro "fst_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCase3At_fst_proj])
    | (rw [formerNeverZeroAt_fst_proj])
    | (rw [iotaCertsFull_fst])
    | (rw [defeqBinders_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [propIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac2" : tactic =>
  `(tactic| fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2 <;> fst_step2 <;>
    fst_step2 <;> fst_step2 <;> fst_step2)

macro "snd_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCase3At_snd_proj])
    | (rw [formerNeverZeroAt_snd_proj])
    | (rw [iotaCertsFull_snd])
    | (rw [defeqBinders_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [propIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac2" : tactic =>
  `(tactic| snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2 <;> snd_step2 <;>
    snd_step2 <;> snd_step2 <;> snd_step2)

theorem structEtaCert_fst_proj (d : Nat) (a b : Expr) :
    (structEtaCert (pairFns r₁ r₂ h) env d a b).val.1 =
      structEtaCert r₁ env d a b := by
  unfold structEtaCert
  fst_tac2

theorem structEtaCert_snd_proj (d : Nat) (a b : Expr) :
    (structEtaCert (pairFns r₁ r₂ h) env d a b).val.2 =
      structEtaCert r₂ env d a b := by
  unfold structEtaCert
  snd_tac2

-- The `majorToCtor` body outgrew the split-driven macros (the
-- splitter's internal simp hits its step ceiling on the full match
-- tower), so the outer casing is peeled by hand and the macro closes
-- each rescue branch separately.
set_option maxHeartbeats 800000 in
theorem majorToCtor_fst_proj (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr) :
    (majorToCtor mode (pairFns r₁ r₂ h) env d c isK rules e).val.1 =
      majorToCtor mode r₁ env d c isK rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [ite_eq_left hca, ite_eq_left hca]; rfl
  rw [ite_eq_right hca, ite_eq_right hca]
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
    by_cases hK : isK = true
    · rw [ite_eq_left hK, ite_eq_left hK]
      fst_tac2
    rw [ite_eq_right hK, ite_eq_right hK]
    by_cases hE : etaRescueOk rl.ctor cvj cvT caps = true
    · rw [ite_eq_left hE, ite_eq_left hE]
      fst_tac2
    rw [ite_eq_right hE, ite_eq_right hE]
    by_cases hA : T = andName
    · rw [ite_eq_left hA, ite_eq_left hA]
      fst_tac2
    rw [ite_eq_right hA, ite_eq_right hA]
    rfl

set_option maxHeartbeats 800000 in
theorem majorToCtor_snd_proj (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr) :
    (majorToCtor mode (pairFns r₁ r₂ h) env d c isK rules e).val.2 =
      majorToCtor mode r₂ env d c isK rules e := by
  unfold majorToCtor
  by_cases hca : isCtorApp env e = true
  · rw [ite_eq_left hca, ite_eq_left hca]; rfl
  rw [ite_eq_right hca, ite_eq_right hca]
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
    by_cases hK : isK = true
    · rw [ite_eq_left hK, ite_eq_left hK]
      snd_tac2
    rw [ite_eq_right hK, ite_eq_right hK]
    by_cases hE : etaRescueOk rl.ctor cvj cvT caps = true
    · rw [ite_eq_left hE, ite_eq_left hE]
      snd_tac2
    rw [ite_eq_right hE, ite_eq_right hE]
    by_cases hA : T = andName
    · rw [ite_eq_left hA, ite_eq_left hA]
      snd_tac2
    rw [ite_eq_right hA, ite_eq_right hA]
    rfl

theorem litMajorToCtor_fst_proj (d : Nat) (e : Expr) :
    (litMajorToCtor (pairFns r₁ r₂ h) env d e).val.1 =
      litMajorToCtor r₁ env d e := by
  unfold litMajorToCtor
  fst_tac2

theorem litMajorToCtor_snd_proj (d : Nat) (e : Expr) :
    (litMajorToCtor (pairFns r₁ r₂ h) env d e).val.2 =
      litMajorToCtor r₂ env d e := by
  unfold litMajorToCtor
  snd_tac2

theorem prepareMajor_fst_proj (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr) :
    (prepareMajor mode (pairFns r₁ r₂ h) env d c isK rules e).val.1 =
      prepareMajor mode r₁ env d c isK rules e := by
  unfold prepareMajor
  split
  · repeat (first
      | rfl
      | (rw [majorToCtor_fst_proj])
      | (rw [litMajorToCtor_fst_proj])
      | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (split <;> (first | rfl | rw [litMajorToCtor_fst_proj]))
      | (dsimp only []))
  · simp only [PairM.fst_ite, PairM.fst_bind, PairM.fst_pure,
      majorToCtor_fst_proj, litMajorToCtor_fst_proj]
    rfl

theorem prepareMajor_snd_proj (d : Nat) (c : Name) (isK : Bool) (rules : List RecRule) (e : Expr) :
    (prepareMajor mode (pairFns r₁ r₂ h) env d c isK rules e).val.2 =
      prepareMajor mode r₂ env d c isK rules e := by
  unfold prepareMajor
  split
  · repeat (first
      | rfl
      | (rw [majorToCtor_snd_proj])
      | (rw [litMajorToCtor_snd_proj])
      | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (split <;> (first | rfl | rw [litMajorToCtor_snd_proj]))
      | (dsimp only []))
  · simp only [PairM.snd_ite, PairM.snd_bind, PairM.snd_pure,
      majorToCtor_snd_proj, litMajorToCtor_snd_proj]
    rfl

theorem projLitToCtor_fst_proj (d : Nat) (e : Expr) :
    (projLitToCtor (pairFns r₁ r₂ h) env d e).val.1 =
      projLitToCtor r₁ env d e := by
  unfold projLitToCtor
  fst_tac2

theorem projLitToCtor_snd_proj (d : Nat) (e : Expr) :
    (projLitToCtor (pairFns r₁ r₂ h) env d e).val.2 =
      projLitToCtor r₂ env d e := by
  unfold projLitToCtor
  snd_tac2

macro "fst_core3" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCase3At_fst_proj])
    | (rw [formerNeverZeroAt_fst_proj])
    | (rw [iotaCertsFull_fst])
    | (rw [defeqBinders_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [litMajorToCtor_fst_proj])
    | (rw [prepareMajor_fst_proj])
    | (rw [projLitToCtor_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_step3" : tactic => `(tactic| fst_core3 (fail))

macro "fst_tac3" : tactic =>
  `(tactic| fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3)

macro "snd_core3" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCase3At_snd_proj])
    | (rw [formerNeverZeroAt_snd_proj])
    | (rw [iotaCertsFull_snd])
    | (rw [defeqBinders_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [litMajorToCtor_snd_proj])
    | (rw [prepareMajor_snd_proj])
    | (rw [projLitToCtor_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_step3" : tactic => `(tactic| snd_core3 (fail))

macro "snd_tac3" : tactic =>
  `(tactic| snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3 <;> snd_step3 <;>
    snd_step3 <;> snd_step3 <;> snd_step3)

theorem stuckIrrel_fst_proj (d : Nat) (a b : Expr) :
    (stuckIrrel (pairFns r₁ r₂ h) env d a b).val.1 =
      stuckIrrel r₁ env d a b := by
  unfold stuckIrrel
  fst_tac3

theorem stuckIrrel_snd_proj (d : Nat) (a b : Expr) :
    (stuckIrrel (pairFns r₁ r₂ h) env d a b).val.2 =
      stuckIrrel r₂ env d a b := by
  unfold stuckIrrel
  snd_tac3

theorem iotaRec_fst_proj (d : Nat) (e : Expr) :
    (iotaRec mode (pairFns r₁ r₂ h) env d e).val.1 =
      iotaRec mode r₁ env d e := by
  unfold iotaRec
  fst_tac3

theorem iotaRec_snd_proj (d : Nat) (e : Expr) :
    (iotaRec mode (pairFns r₁ r₂ h) env d e).val.2 =
      iotaRec mode r₂ env d e := by
  unfold iotaRec
  snd_tac3

theorem reduceProjCore_fst_proj (d : Nat) (sn : Name) (i : Nat) (e : Expr) :
    (reduceProjCore mode (pairFns r₁ r₂ h) env d sn i e).val.1 =
      reduceProjCore mode r₁ env d sn i e := by
  unfold reduceProjCore
  fst_tac3

theorem reduceProjCore_snd_proj (d : Nat) (sn : Name) (i : Nat) (e : Expr) :
    (reduceProjCore mode (pairFns r₁ r₂ h) env d sn i e).val.2 =
      reduceProjCore mode r₂ env d sn i e := by
  unfold reduceProjCore
  snd_tac3

theorem quickDefEq_fst_proj (d : Nat) (a b : Expr) :
    (quickDefEq mode (pairFns r₁ r₂ h) d a b).val.1 = quickDefEq mode r₁ d a b := by
  unfold quickDefEq
  fst_tac3

theorem quickDefEq_snd_proj (d : Nat) (a b : Expr) :
    (quickDefEq mode (pairFns r₁ r₂ h) d a b).val.2 = quickDefEq mode r₂ d a b := by
  unfold quickDefEq
  snd_tac3

theorem defeqOffset_fst_proj (d : Nat) (a b : Expr) :
    (defeqOffset (pairFns r₁ r₂ h) d a b).val.1 = defeqOffset r₁ d a b := by
  unfold defeqOffset
  fst_tac3

theorem defeqOffset_snd_proj (d : Nat) (a b : Expr) :
    (defeqOffset (pairFns r₁ r₂ h) d a b).val.2 = defeqOffset r₂ d a b := by
  unfold defeqOffset
  snd_tac3

theorem tryUnfoldProjApp_fst_proj (d : Nat) (e : Expr) :
    (tryUnfoldProjApp (pairFns r₁ r₂ h) d e).val.1 = tryUnfoldProjApp r₁ d e := by
  unfold tryUnfoldProjApp
  fst_tac3

theorem tryUnfoldProjApp_snd_proj (d : Nat) (e : Expr) :
    (tryUnfoldProjApp (pairFns r₁ r₂ h) d e).val.2 = tryUnfoldProjApp r₂ d e := by
  unfold tryUnfoldProjApp
  snd_tac3

theorem deltaQuick_fst_proj (d : Nat) (a b : Expr) :
    (deltaQuick mode (pairFns r₁ r₂ h) d a b).val.1 = deltaQuick mode r₁ d a b := by
  unfold deltaQuick
  fst_core3 (rw [quickDefEq_fst_proj])

theorem deltaQuick_snd_proj (d : Nat) (a b : Expr) :
    (deltaQuick mode (pairFns r₁ r₂ h) d a b).val.2 = deltaQuick mode r₂ d a b := by
  unfold deltaQuick
  snd_core3 (rw [quickDefEq_snd_proj])

theorem lazyDeltaStep_fst_proj (d : Nat) (a b : Expr) :
    (lazyDeltaStep mode (pairFns r₁ r₂ h) env d a b).val.1 =
      lazyDeltaStep mode r₁ env d a b := by
  unfold lazyDeltaStep
  fst_core3 (first | rw [deltaQuick_fst_proj] | rw [tryUnfoldProjApp_fst_proj] | rw [defeqSpine_fst])

theorem lazyDeltaStep_snd_proj (d : Nat) (a b : Expr) :
    (lazyDeltaStep mode (pairFns r₁ r₂ h) env d a b).val.2 =
      lazyDeltaStep mode r₂ env d a b := by
  unfold lazyDeltaStep
  snd_core3 (first | rw [deltaQuick_snd_proj] | rw [tryUnfoldProjApp_snd_proj] | rw [defeqSpine_snd])

theorem lazyDeltaReduction_fst_proj (d : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaReduction mode eager (pairFns r₁ r₂ h) env d n a b).val.1 =
        lazyDeltaReduction mode eager r₁ env d n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaReduction
    fst_core3 (first | rw [lazyDeltaStep_fst_proj] | rw [defeqOffset_fst_proj] | rw [lazyDeltaReduction_fst_proj d n])

theorem lazyDeltaReduction_snd_proj (d : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaReduction mode eager (pairFns r₁ r₂ h) env d n a b).val.2 =
        lazyDeltaReduction mode eager r₂ env d n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaReduction
    snd_core3 (first | rw [lazyDeltaStep_snd_proj] | rw [defeqOffset_snd_proj] | rw [lazyDeltaReduction_snd_proj d n])

theorem lazyDeltaProjReduction_fst_proj (d : Nat) (sn : Name) (i : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaProjReduction mode (pairFns r₁ r₂ h) env d sn i n a b).val.1 =
        lazyDeltaProjReduction mode r₁ env d sn i n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaProjReduction
    fst_core3 (first | rw [lazyDeltaStep_fst_proj] | rw [reduceProjCore_fst_proj] | rw [lazyDeltaProjReduction_fst_proj d sn i n])

theorem lazyDeltaProjReduction_snd_proj (d : Nat) (sn : Name) (i : Nat) :
    ∀ (n : Nat) (a b : Expr),
      (lazyDeltaProjReduction mode (pairFns r₁ r₂ h) env d sn i n a b).val.2 =
        lazyDeltaProjReduction mode r₂ env d sn i n a b
  | 0, _, _ => rfl
  | n + 1, a, b => by
    unfold lazyDeltaProjReduction
    snd_core3 (first | rw [lazyDeltaStep_snd_proj] | rw [reduceProjCore_snd_proj] | rw [lazyDeltaProjReduction_snd_proj d sn i n])

theorem defeqProjPair_fst_proj (d : Nat) (a b : Expr) :
    (defeqProjPair mode (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqProjPair mode r₁ env d a b := by
  unfold defeqProjPair
  fst_core3 (rw [lazyDeltaProjReduction_fst_proj])

theorem defeqProjPair_snd_proj (d : Nat) (a b : Expr) :
    (defeqProjPair mode (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqProjPair mode r₂ env d a b := by
  unfold defeqProjPair
  snd_core3 (rw [lazyDeltaProjReduction_snd_proj])

theorem defeqStuck_fst_proj (d : Nat) (a b : Expr) :
    (defeqStuck mode (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqStuck mode r₁ env d a b := by
  unfold defeqStuck
  fst_core3 (rw [stuckIrrel_fst_proj])

theorem defeqStuck_snd_proj (d : Nat) (a b : Expr) :
    (defeqStuck mode (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqStuck mode r₂ env d a b := by
  unfold defeqStuck
  snd_core3 (rw [stuckIrrel_snd_proj])

/-- The level-4 cascade, parameterized over one extra alternative so
that loop-body lemmas can feed in their continuation hypothesis
(`fst_step4k`) without duplicating the rewrite list. -/
macro "fst_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [checkProjGuard_fst_proj])
    | (rw [checkProjGuardI_fst_proj])
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCase3At_fst_proj])
    | (rw [formerNeverZeroAt_fst_proj])
    | (rw [iotaCertsFull_fst])
    | (rw [defeqBinders_fst])
    | (rw [iotaIndexOk_fst])
    | (rw [defEqList_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [propIrrel_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [stuckIrrel_fst_proj])
    | (rw [iotaRec_fst_proj])
    | (rw [projLitToCtor_fst_proj])
    | (rw [defeqSpine_fst])
    | (rw [defeqArg_fst])
    | (rw [reduceProjCore_fst_proj])
    | (rw [quickDefEq_fst_proj])
    | (rw [lazyDeltaReduction_fst_proj])
    | (rw [defeqProjPair_fst_proj])
    | (rw [defeqStuck_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- an `if` in the cascade: unfolding the `ite` primitive hands
    -- both arms back to the cascade's own `split`
    | ((rw [PairM.fst_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "fst_step4" : tactic => `(tactic| fst_core4 (fail))

macro "fst_step4k" hk:ident : tactic =>
  `(tactic| fst_core4 (rw [$hk:ident]))

macro "fst_tac4k" hk:ident : tactic =>
  `(tactic| fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk <;>
    fst_step4k $hk <;> fst_step4k $hk <;> fst_step4k $hk)

macro "fst_tac4" : tactic =>
  `(tactic| fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4)

/-- The level-4 cascade, parameterized over one extra alternative so
that loop-body lemmas can feed in their continuation hypothesis
(`snd_step4k`) without duplicating the rewrite list. -/
macro "snd_core4" x:tactic : tactic =>
  `(tactic| repeat (first
    | rfl
    | $x:tactic
    | (rw [checkProjGuard_snd_proj])
    | (rw [checkProjGuardI_snd_proj])
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCase3At_snd_proj])
    | (rw [formerNeverZeroAt_snd_proj])
    | (rw [iotaCertsFull_snd])
    | (rw [defeqBinders_snd])
    | (rw [iotaIndexOk_snd])
    | (rw [defEqList_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [propIrrel_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [stuckIrrel_snd_proj])
    | (rw [iotaRec_snd_proj])
    | (rw [projLitToCtor_snd_proj])
    | (rw [defeqSpine_snd])
    | (rw [defeqArg_snd])
    | (rw [reduceProjCore_snd_proj])
    | (rw [quickDefEq_snd_proj])
    | (rw [lazyDeltaReduction_snd_proj])
    | (rw [defeqProjPair_snd_proj])
    | (rw [defeqStuck_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    -- an `if` in the cascade: unfolding the `ite` primitive hands
    -- both arms back to the cascade's own `split`
    | ((rw [PairM.snd_ite]; congr 1) <;> try rfl)
    | (dsimp only [])
    | split))

macro "snd_step4" : tactic => `(tactic| snd_core4 (fail))

macro "snd_step4k" hk:ident : tactic =>
  `(tactic| snd_core4 (rw [$hk:ident]))

macro "snd_tac4k" hk:ident : tactic =>
  `(tactic| snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk <;>
    snd_step4k $hk <;> snd_step4k $hk <;> snd_step4k $hk)

macro "snd_tac4" : tactic =>
  `(tactic| snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4)

theorem whnfCoreBody_fst_proj (c : Bool) (d : Nat) (e : Expr) :
    (whnfCoreBody mode (pairFns r₁ r₂ h) env c d e).val.1 =
      whnfCoreBody mode r₁ env c d e := by
  unfold whnfCoreBody
  fst_tac4

theorem whnfCoreBody_snd_proj (c : Bool) (d : Nat) (e : Expr) :
    (whnfCoreBody mode (pairFns r₁ r₂ h) env c d e).val.2 =
      whnfCoreBody mode r₂ env c d e := by
  unfold whnfCoreBody
  snd_tac4

/-! The reduction-loop and lazy-delta-loop bodies (task #106) are
parameterized over their continuation exactly as over the record, so
each gets one projection lemma with a continuation hypothesis and the
loop lemma is a plain induction on the step budget. -/

theorem whnfStep_fst_proj (d : Nat) (k : Expr → PairM rel Expr)
    (k₁ : Expr → M₁ Expr) (hk : ∀ e, (k e).val.1 = k₁ e) (e : Expr) :
    (whnfStep (pairFns r₁ r₂ h) env d k e).val.1 =
      whnfStep r₁ env d k₁ e := by
  unfold whnfStep
  fst_tac4k hk

theorem whnfStep_snd_proj (d : Nat) (k : Expr → PairM rel Expr)
    (k₂ : Expr → M₂ Expr) (hk : ∀ e, (k e).val.2 = k₂ e) (e : Expr) :
    (whnfStep (pairFns r₁ r₂ h) env d k e).val.2 =
      whnfStep r₂ env d k₂ e := by
  unfold whnfStep
  snd_tac4k hk

theorem whnfLoop_fst_proj (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (pairFns r₁ r₂ h) env d n e).val.1 = whnfLoop r₁ env d n e
  | 0, _ => rfl
  | n + 1, e =>
    whnfStep_fst_proj d _ _ (fun e' => whnfLoop_fst_proj d n e') e

theorem whnfLoop_snd_proj (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      (whnfLoop (pairFns r₁ r₂ h) env d n e).val.2 = whnfLoop r₂ env d n e
  | 0, _ => rfl
  | n + 1, e =>
    whnfStep_snd_proj d _ _ (fun e' => whnfLoop_snd_proj d n e') e

theorem whnfBody_fst_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.1 =
      whnfBody r₁ env d e :=
  whnfLoop_fst_proj d whnfLoopFuel e

theorem whnfBody_snd_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.2 =
      whnfBody r₂ env d e :=
  whnfLoop_snd_proj d whnfLoopFuel e

theorem inferBody_fst_proj (d : Nat) (e : Expr) :
    (inferBody (pairFns r₁ r₂ h) env d e).val.1 =
      inferBody r₁ env d e := by
  unfold inferBody
  fst_tac4

theorem inferBody_snd_proj (d : Nat) (e : Expr) :
    (inferBody (pairFns r₁ r₂ h) env d e).val.2 =
      inferBody r₂ env d e := by
  unfold inferBody
  snd_tac4

/-! The io inference body (task #172 B4): the same walk with the io
clauses.  The pairing of the io-grade views is definitionally the io-grade
view of the pairing on the fields the body reads, so the walks go
through the plain `pairFns` of the viewed records. -/

theorem inferBodyIO_fst_proj (d : Nat) (e : Expr) :
    (inferBodyIO (pairFns r₁ r₂ h) env d e).val.1 =
      inferBodyIO r₁ env d e := by
  unfold inferBodyIO
  fst_tac4

theorem inferBodyIO_snd_proj (d : Nat) (e : Expr) :
    (inferBodyIO (pairFns r₁ r₂ h) env d e).val.2 =
      inferBodyIO r₂ env d e := by
  unfold inferBodyIO
  snd_tac4

theorem defeqBody_fst_proj (d : Nat) (a b : Expr) :
    (defeqBody mode eager (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqBody mode eager r₁ env d a b := by
  unfold defeqBody
  fst_tac4

theorem defeqBody_snd_proj (d : Nat) (a b : Expr) :
    (defeqBody mode eager (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqBody mode eager r₂ env d a b := by
  unfold defeqBody
  snd_tac4

end Commute

end ConLeche
