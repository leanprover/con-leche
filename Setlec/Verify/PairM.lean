import Setlec.Verify.Knot

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

namespace Setlec

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
def PairM (rel : MonadRel M₁ M₂) (α : Type) : Type :=
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

@[simp] theorem fst_throw {α : Type} (e : CheckError) :
    (throw e : PairM rel α).val.1 = throw e := rfl

@[simp] theorem snd_throw {α : Type} (e : CheckError) :
    (throw e : PairM rel α).val.2 = throw e := rfl

@[simp] theorem fst_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.1 = if c then x.val.1 else y.val.1 := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem snd_ite {α : Type} {c : Prop} [Decidable c]
    (x y : PairM rel α) :
    (if c then x else y).val.2 = if c then x.val.2 else y.val.2 := by
  by_cases hc : c <;> simp [hc]

end PairM

/-- Componentwise relatedness of two core records. -/
def FnsRel (rel : MonadRel M₁ M₂) (r₁ : CoreFns M₁) (r₂ : CoreFns M₂) :
    Prop :=
  (∀ d e, rel.R (r₁.whnfCore d e) (r₂.whnfCore d e)) ∧
  (∀ d e, rel.R (r₁.whnf d e) (r₂.whnf d e)) ∧
  (∀ d e, rel.R (r₁.infer d e) (r₂.infer d e)) ∧
  (∀ d a b, rel.R (r₁.defeq d a b) (r₂.defeq d a b)) ∧
  (∀ d e, rel.R (r₁.annotate d e) (r₂.annotate d e))

/-- The paired record. -/
def pairFns {rel : MonadRel M₁ M₂} (r₁ : CoreFns M₁) (r₂ : CoreFns M₂)
    (h : FnsRel rel r₁ r₂) : CoreFns (PairM rel) where
  whnfCore d e := ⟨(r₁.whnfCore d e, r₂.whnfCore d e), h.1 d e⟩
  whnf d e := ⟨(r₁.whnf d e, r₂.whnf d e), h.2.1 d e⟩
  infer d e := ⟨(r₁.infer d e, r₂.infer d e), h.2.2.1 d e⟩
  defeq d a b := ⟨(r₁.defeq d a b, r₂.defeq d a b), h.2.2.2.1 d a b⟩
  annotate d e := ⟨(r₁.annotate d e, r₂.annotate d e), h.2.2.2.2 d e⟩

section Commute

variable {rel : MonadRel M₁ M₂} {r₁ : CoreFns M₁} {r₂ : CoreFns M₂}
  {h : FnsRel rel r₁ r₂} {env : Env}

theorem iotaCerts_fst (d : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (pairFns r₁ r₂ h) env d ty args).val.1 =
        iotaCerts r₁ env d ty args
  | _, [] => rfl
  | .forallE n ty body mb, arg :: rest => by
    show ((do
        let ta ← (pairFns r₁ r₂ h).infer d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCerts (pairFns r₁ r₂ h) env d (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.1 = (do
        let ta ← r₁.infer d arg
        if ← r₁.defeq d ta ty then
          iotaCerts r₁ env d (body.instantiate1 arg) rest
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
      exact iotaCerts_fst d (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

theorem iotaCerts_snd (d : Nat) :
    ∀ (ty : Expr) (args : List Expr),
      (iotaCerts (pairFns r₁ r₂ h) env d ty args).val.2 =
        iotaCerts r₂ env d ty args
  | _, [] => rfl
  | .forallE n ty body mb, arg :: rest => by
    show ((do
        let ta ← (pairFns r₁ r₂ h).infer d arg
        if ← (pairFns r₁ r₂ h).defeq d ta ty then
          iotaCerts (pairFns r₁ r₂ h) env d (body.instantiate1 arg) rest
        else pure false : PairM rel Bool)).val.2 = (do
        let ta ← r₂.infer d arg
        if ← r₂.defeq d ta ty then
          iotaCerts r₂ env d (body.instantiate1 arg) rest
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
      exact iotaCerts_snd d (body.instantiate1 arg) rest
    | false => rfl
  | .bvar _, _ :: _ | .fvar _ _ _, _ :: _ | .sort _, _ :: _
  | .const _ _, _ :: _ | .app _ _, _ :: _ | .lam _ _ _ _, _ :: _
  | .letE _ _ _ _, _ :: _ | .lit _, _ :: _ | .proj _ _ _, _ :: _ => rfl

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

theorem structEtaProjCerts_fst (d : Nat) (T : Name) (us' : List Level)
    (targs : List Expr) (b : Expr) (lpsT : List Name) :
    ∀ (idxs : List Nat),
      (structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b lpsT
        idxs).val.1 =
      structEtaProjCerts r₁ env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pairFns r₁ r₂ h) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : PairM rel Bool)).val.1 = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts r₁ env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts r₁ env d T us' targs b lpsT rest
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
        · rw [PairM.fst_bind, iotaCerts_fst]
          congr 1
          funext r
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCerts_fst d T us' targs b lpsT rest
          | false => rfl
        · rfl
      | axiomInfo cv => rfl
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

theorem structEtaProjCerts_snd (d : Nat) (T : Name) (us' : List Level)
    (targs : List Expr) (b : Expr) (lpsT : List Name) :
    ∀ (idxs : List Nat),
      (structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b lpsT
        idxs).val.2 =
      structEtaProjCerts r₂ env d T us' targs b lpsT idxs
  | [] => rfl
  | i :: rest => by
    show ((do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts (pairFns r₁ r₂ h) env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b
                lpsT rest
            else pure false
          else pure false
        | _ => pure false : PairM rel Bool)).val.2 = (do
        match env.find? (projFnName T i) with
        | some (.recInfo cvp _ _ _ _ _) =>
          if cvp.levelParams = lpsT ∧
              (cvp.type.stripPis (targs.length + 1)).isSome = true then
            if ← iotaCerts r₂ env d
                (cvp.type.instantiateLevelParams cvp.levelParams us')
                (targs ++ [b]) then
              structEtaProjCerts r₂ env d T us' targs b lpsT rest
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
        · rw [PairM.snd_bind, iotaCerts_snd]
          congr 1
          funext r
          cases r with
          | true =>
            simp only [↓reduceIte]
            exact structEtaProjCerts_snd d T us' targs b lpsT rest
          | false => rfl
        · rfl
      | axiomInfo cv => rfl
      | defnInfo cv value => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv nP nF => rfl

theorem liftFueled_fst_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.1 = liftFueled what o := by
  cases o <;> rfl

theorem liftFueled_snd_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : PairM rel α).val.2 = liftFueled what o := by
  cases o <;> rfl

macro "fst_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
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
    | (rw [iotaCerts_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
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

theorem proofIrrel_fst_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) env d a b).val.1 =
      proofIrrel r₁ env d a b := by
  unfold proofIrrel
  fst_tac

theorem proofIrrel_snd_proj (d : Nat) (a b : Expr) :
    (proofIrrel (pairFns r₁ r₂ h) env d a b).val.2 =
      proofIrrel r₂ env d a b := by
  unfold proofIrrel
  snd_tac

theorem pairEtaCert_fst_proj (d : Nat) (a b : Expr) :
    (pairEtaCert (pairFns r₁ r₂ h) env d a b).val.1 =
      pairEtaCert r₁ env d a b := by
  unfold pairEtaCert
  fst_tac

theorem pairEtaCert_snd_proj (d : Nat) (a b : Expr) :
    (pairEtaCert (pairFns r₁ r₂ h) env d a b).val.2 =
      pairEtaCert r₂ env d a b := by
  unfold pairEtaCert
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

theorem etaCert_fst_proj (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) (b : Expr) :
    (etaCert (pairFns r₁ r₂ h) env d n ty body mb b).val.1 =
      etaCert r₁ env d n ty body mb b := by
  unfold etaCert
  fst_tac

theorem etaCert_snd_proj (d : Nat) (n : Name) (ty body : Expr) (mb : BinderMeta) (b : Expr) :
    (etaCert (pairFns r₁ r₂ h) env d n ty body mb b).val.2 =
      etaCert r₂ env d n ty body mb b := by
  unfold etaCert
  snd_tac

theorem projCert_fst_proj (d : Nat) (e₂ : Expr) (i : Nat) (us : List Level) (nP : Nat) :
    (projCert (pairFns r₁ r₂ h) env d e₂ i us nP).val.1 =
      projCert r₁ env d e₂ i us nP := by
  unfold projCert
  fst_tac

theorem projCert_snd_proj (d : Nat) (e₂ : Expr) (i : Nat) (us : List Level) (nP : Nat) :
    (projCert (pairFns r₁ r₂ h) env d e₂ i us nP).val.2 =
      projCert r₂ env d e₂ i us nP := by
  unfold projCert
  snd_tac

macro "fst_step2" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [pairEtaCert_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCert_fst_proj])
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
    | (rw [iotaCerts_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [pairEtaCert_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCert_snd_proj])
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

theorem majorToCtor_fst_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (majorToCtor (pairFns r₁ r₂ h) env d c rules e).val.1 =
      majorToCtor r₁ env d c rules e := by
  unfold majorToCtor
  fst_tac2

theorem majorToCtor_snd_proj (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    (majorToCtor (pairFns r₁ r₂ h) env d c rules e).val.2 =
      majorToCtor r₂ env d c rules e := by
  unfold majorToCtor
  snd_tac2

theorem isPropType_fst_proj (d : Nat) (ty : Expr) :
    (isPropType (pairFns r₁ r₂ h) env d ty).val.1 =
      isPropType r₁ env d ty := by
  unfold isPropType
  fst_tac2

theorem isPropType_snd_proj (d : Nat) (ty : Expr) :
    (isPropType (pairFns r₁ r₂ h) env d ty).val.2 =
      isPropType r₂ env d ty := by
  unfold isPropType
  snd_tac2

theorem projFieldDom_fst_proj (structProp : Bool) (sn : Name) (e₂ : Expr) :
    ∀ (k j d : Nat) (tel : Expr),
      (projFieldDom (pairFns r₁ r₂ h) env d structProp sn e₂ j k tel).val.1 =
        projFieldDom r₁ env d structProp sn e₂ j k tel := by
  intro k
  induction k with
  | zero =>
    intro j d tel
    cases tel <;> dsimp only [projFieldDom] <;> rfl
  | succ k ih =>
    intro j d tel
    cases tel <;> dsimp only [projFieldDom] <;> try rfl
    repeat (first
      | rfl
      | (rw [ih])
      | (rw [isPropType_fst_proj])
      | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (dsimp only [])
      | split)

theorem projFieldDom_snd_proj (structProp : Bool) (sn : Name) (e₂ : Expr) :
    ∀ (k j d : Nat) (tel : Expr),
      (projFieldDom (pairFns r₁ r₂ h) env d structProp sn e₂ j k tel).val.2 =
        projFieldDom r₂ env d structProp sn e₂ j k tel := by
  intro k
  induction k with
  | zero =>
    intro j d tel
    cases tel <;> dsimp only [projFieldDom] <;> rfl
  | succ k ih =>
    intro j d tel
    cases tel <;> dsimp only [projFieldDom] <;> try rfl
    repeat (first
      | rfl
      | (rw [ih])
      | (rw [isPropType_snd_proj])
      | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
      | (dsimp only [])
      | split)

theorem annotateProjRec_fst_proj (d : Nat) (sn : Name) (i : Nat)
    (te e₂ : Expr) (us : List Level) :
    (annotateProjRec (pairFns r₁ r₂ h) env d sn i te e₂ us).val.1 =
      annotateProjRec r₁ env d sn i te e₂ us := by
  unfold annotateProjRec
  repeat (first
    | rfl
    | (rw [isPropType_fst_proj])
    | (rw [projFieldDom_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [liftFueled_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem annotateProjRec_snd_proj (d : Nat) (sn : Name) (i : Nat)
    (te e₂ : Expr) (us : List Level) :
    (annotateProjRec (pairFns r₁ r₂ h) env d sn i te e₂ us).val.2 =
      annotateProjRec r₂ env d sn i te e₂ us := by
  unfold annotateProjRec
  repeat (first
    | rfl
    | (rw [isPropType_snd_proj])
    | (rw [projFieldDom_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [liftFueled_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem annotateProjElim_fst_proj (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) :
    (annotateProjElim (pairFns r₁ r₂ h) env d sn i te e₂).val.1 =
      annotateProjElim r₁ env d sn i te e₂ := by
  unfold annotateProjElim
  repeat (first
    | rfl
    | (rw [annotateProjRec_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

theorem annotateProjElim_snd_proj (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) :
    (annotateProjElim (pairFns r₁ r₂ h) env d sn i te e₂).val.2 =
      annotateProjElim r₂ env d sn i te e₂ := by
  unfold annotateProjElim
  repeat (first
    | rfl
    | (rw [annotateProjRec_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split)

macro "fst_step3" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [pairEtaCert_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [annotateProjElim_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac3" : tactic =>
  `(tactic| fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3 <;> fst_step3 <;>
    fst_step3 <;> fst_step3 <;> fst_step3)

macro "snd_step3" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [pairEtaCert_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [annotateProjElim_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

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
    (iotaRec (pairFns r₁ r₂ h) env d e).val.1 =
      iotaRec r₁ env d e := by
  unfold iotaRec
  fst_tac3

theorem iotaRec_snd_proj (d : Nat) (e : Expr) :
    (iotaRec (pairFns r₁ r₂ h) env d e).val.2 =
      iotaRec r₂ env d e := by
  unfold iotaRec
  snd_tac3

macro "fst_step4" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | (rw [reduceNat_fst_proj])
    | (rw [ensureSort_fst_proj])
    | (rw [proofIrrel_fst_proj])
    | (rw [pairEtaCert_fst_proj])
    | (rw [structEtaCertWith_fst_proj])
    | (rw [structUnitCert_fst_proj])
    | (rw [etaCert_fst_proj])
    | (rw [projCert_fst_proj])
    | (rw [structEtaCert_fst_proj])
    | (rw [majorToCtor_fst_proj])
    | (rw [annotateProjElim_fst_proj])
    | (rw [stuckIrrel_fst_proj])
    | (rw [iotaRec_fst_proj])
    | ((rw [PairM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "fst_tac4" : tactic =>
  `(tactic| fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4 <;> fst_step4 <;>
    fst_step4 <;> fst_step4 <;> fst_step4)

macro "snd_step4" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_snd_proj])
    | (rw [iotaCerts_snd])
    | (rw [defEqList_snd])
    | (rw [structEtaProjCerts_snd])
    | (rw [reduceNat_snd_proj])
    | (rw [ensureSort_snd_proj])
    | (rw [proofIrrel_snd_proj])
    | (rw [pairEtaCert_snd_proj])
    | (rw [structEtaCertWith_snd_proj])
    | (rw [structUnitCert_snd_proj])
    | (rw [etaCert_snd_proj])
    | (rw [projCert_snd_proj])
    | (rw [structEtaCert_snd_proj])
    | (rw [majorToCtor_snd_proj])
    | (rw [annotateProjElim_snd_proj])
    | (rw [stuckIrrel_snd_proj])
    | (rw [iotaRec_snd_proj])
    | ((rw [PairM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
    | (dsimp only [])
    | split))

macro "snd_tac4" : tactic =>
  `(tactic| snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4 <;> snd_step4 <;>
    snd_step4 <;> snd_step4 <;> snd_step4)

theorem whnfCoreBody_fst_proj (d : Nat) (e : Expr) :
    (whnfCoreBody (pairFns r₁ r₂ h) env d e).val.1 =
      whnfCoreBody r₁ env d e := by
  unfold whnfCoreBody
  fst_tac4

theorem whnfCoreBody_snd_proj (d : Nat) (e : Expr) :
    (whnfCoreBody (pairFns r₁ r₂ h) env d e).val.2 =
      whnfCoreBody r₂ env d e := by
  unfold whnfCoreBody
  snd_tac4

theorem whnfBody_fst_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.1 =
      whnfBody r₁ env d e := by
  unfold whnfBody
  fst_tac4

theorem whnfBody_snd_proj (d : Nat) (e : Expr) :
    (whnfBody (pairFns r₁ r₂ h) env d e).val.2 =
      whnfBody r₂ env d e := by
  unfold whnfBody
  snd_tac4

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

theorem defeqBody_fst_proj (d : Nat) (a b : Expr) :
    (defeqBody (pairFns r₁ r₂ h) env d a b).val.1 =
      defeqBody r₁ env d a b := by
  unfold defeqBody
  fst_tac4

theorem defeqBody_snd_proj (d : Nat) (a b : Expr) :
    (defeqBody (pairFns r₁ r₂ h) env d a b).val.2 =
      defeqBody r₂ env d a b := by
  unfold defeqBody
  snd_tac4

theorem annotateBody_fst_proj (d : Nat) (e : Expr) :
    (annotateBody (pairFns r₁ r₂ h) env d e).val.1 =
      annotateBody r₁ env d e := by
  unfold annotateBody
  fst_tac4

theorem annotateBody_snd_proj (d : Nat) (e : Expr) :
    (annotateBody (pairFns r₁ r₂ h) env d e).val.2 =
      annotateBody r₂ env d e := by
  unfold annotateBody
  snd_tac4


end Commute

end Setlec
