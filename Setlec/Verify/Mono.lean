import Setlec.Verify.Knot

/-!
# Fuel monotonicity via a relational pair monad

The core bodies are monad-polymorphic, so instead of walking each
body's monadic structure by hand we instantiate the bodies **once** at
a monad of *pairs of `CheckM` computations carrying a
success-refinement proof* (`RelM`): the bind/pure/throw of `RelM`
preserve the refinement, so the instantiated body's subtype proof *is*
the per-body monotonicity lemma.  Projection equations relate the
instantiated body's components back to the plain instantiations (plain
`rfl` except across the structurally recursive list helpers, which get
their own commute lemmas).  One induction at the knot then yields fuel
monotonicity for every fueled entry point.
-/

namespace Setlec

/-- `q` succeeds wherever `p` succeeds, with the same value. -/
def MRefines {α : Type} (p q : CheckM α) : Prop :=
  ∀ v, p = .ok v → q = .ok v

theorem MRefines.rfl {α : Type} {p : CheckM α} : MRefines p p := fun _ h => h

/-- Pairs of `CheckM` computations, the second refining the first. -/
def RelM (α : Type) : Type := {pq : CheckM α × CheckM α // MRefines pq.1 pq.2}

namespace RelM

def mk {α : Type} (p q : CheckM α) (h : MRefines p q) : RelM α := ⟨(p, q), h⟩

instance : Monad RelM where
  pure a := ⟨(pure a, pure a), MRefines.rfl⟩
  bind x f :=
    ⟨(x.val.1 >>= fun a => (f a).val.1, x.val.2 >>= fun a => (f a).val.2),
      by
        intro v h
        cases hx : x.val.1 with
        | error e =>
          rw [hx] at h
          exact nomatch h
        | ok a =>
          rw [hx] at h
          rw [x.property a hx]
          exact (f a).property v h⟩

instance : MonadExceptOf CheckError RelM where
  throw e := ⟨(throw e, throw e), fun _ h => nomatch h⟩
  -- the bodies never catch; a vacuously related stub keeps the
  -- instance total
  tryCatch _ _ :=
    ⟨(throw (.internal "tryCatch unsupported"),
      throw (.internal "tryCatch unsupported")), fun _ h => nomatch h⟩

@[simp] theorem fst_bind {α β : Type} (x : RelM α) (f : α → RelM β) :
    (x >>= f).val.1 = x.val.1 >>= fun a => (f a).val.1 := rfl

@[simp] theorem snd_bind {α β : Type} (x : RelM α) (f : α → RelM β) :
    (x >>= f).val.2 = x.val.2 >>= fun a => (f a).val.2 := rfl

@[simp] theorem fst_pure {α : Type} (a : α) :
    (pure a : RelM α).val.1 = pure a := rfl

@[simp] theorem snd_pure {α : Type} (a : α) :
    (pure a : RelM α).val.2 = pure a := rfl

@[simp] theorem fst_throw {α : Type} (e : CheckError) :
    (throw e : RelM α).val.1 = throw e := rfl

@[simp] theorem snd_throw {α : Type} (e : CheckError) :
    (throw e : RelM α).val.2 = throw e := rfl

end RelM

/-- Componentwise success-refinement between two records. -/
def FnsRefines (r₁ r₂ : CoreFns CheckM) : Prop :=
  (∀ d e, MRefines (r₁.whnfCore d e) (r₂.whnfCore d e)) ∧
  (∀ d e, MRefines (r₁.whnf d e) (r₂.whnf d e)) ∧
  (∀ d e, MRefines (r₁.infer d e) (r₂.infer d e)) ∧
  (∀ d a b, MRefines (r₁.defeq d a b) (r₂.defeq d a b)) ∧
  (∀ d e, MRefines (r₁.annotate d e) (r₂.annotate d e))

/-- The paired record. -/
def pairFns (r₁ r₂ : CoreFns CheckM) (h : FnsRefines r₁ r₂) :
    CoreFns RelM where
  whnfCore d e := ⟨(r₁.whnfCore d e, r₂.whnfCore d e), h.1 d e⟩
  whnf d e := ⟨(r₁.whnf d e, r₂.whnf d e), h.2.1 d e⟩
  infer d e := ⟨(r₁.infer d e, r₂.infer d e), h.2.2.1 d e⟩
  defeq d a b := ⟨(r₁.defeq d a b, r₂.defeq d a b), h.2.2.2.1 d a b⟩
  annotate d e := ⟨(r₁.annotate d e, r₂.annotate d e), h.2.2.2.2 d e⟩

section Commute

variable {r₁ r₂ : CoreFns CheckM} {h : FnsRefines r₁ r₂} {env : Env}

/-! Projection commute lemmas for the structurally recursive list
helpers; everything else projects definitionally. -/

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
        else pure false : RelM Bool)).val.1 = (do
        let ta ← r₁.infer d arg
        if ← r₁.defeq d ta ty then
          iotaCerts r₁ env d (body.instantiate1 arg) rest
        else pure false)
    rw [RelM.fst_bind]
    congr 1
    funext ta
    rw [RelM.fst_bind]
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
        else pure false : RelM Bool)).val.2 = (do
        let ta ← r₂.infer d arg
        if ← r₂.defeq d ta ty then
          iotaCerts r₂ env d (body.instantiate1 arg) rest
        else pure false)
    rw [RelM.snd_bind]
    congr 1
    funext ta
    rw [RelM.snd_bind]
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
        else pure false : RelM Bool)).val.1 = (do
        if ← r₁.defeq d a b then
          defEqList r₁ env d as bs
        else pure false)
    rw [RelM.fst_bind]
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
        else pure false : RelM Bool)).val.2 = (do
        if ← r₂.defeq d a b then
          defEqList r₂ env d as bs
        else pure false)
    rw [RelM.snd_bind]
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
        | _ => pure false : RelM Bool)).val.1 = (do
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
        · rw [RelM.fst_bind, iotaCerts_fst]
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
        | _ => pure false : RelM Bool)).val.2 = (do
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
        · rw [RelM.snd_bind, iotaCerts_snd]
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
    (liftFueled what o : RelM α).val.1 = liftFueled what o := by
  cases o <;> rfl

theorem liftFueled_snd_proj {α : Type} (what : String) (o : Option α) :
    (liftFueled what o : RelM α).val.2 = liftFueled what o := by
  cases o <;> rfl

macro "fst_step" : tactic =>
  `(tactic| repeat (first
    | rfl
    | (rw [liftFueled_fst_proj])
    | (rw [iotaCerts_fst])
    | (rw [defEqList_fst])
    | (rw [structEtaProjCerts_fst])
    | ((rw [RelM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
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

theorem annotateProjElim_fst_proj (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) :
    (annotateProjElim (pairFns r₁ r₂ h) env d sn i te e₂).val.1 =
      annotateProjElim r₁ env d sn i te e₂ := by
  unfold annotateProjElim
  fst_tac2

theorem annotateProjElim_snd_proj (d : Nat) (sn : Name) (i : Nat) (te e₂ : Expr) :
    (annotateProjElim (pairFns r₁ r₂ h) env d sn i te e₂).val.2 =
      annotateProjElim r₂ env d sn i te e₂ := by
  unfold annotateProjElim
  snd_tac2

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
    | ((rw [RelM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.fst_bind]; congr 1 <;> try rfl) <;> try funext _)
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
    | ((rw [RelM.snd_bind]; congr 1 <;> try rfl) <;> try funext _)
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


/-! ## Per-body monotonicity, extracted from the pair instantiation -/

theorem whnfCoreBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (whnfCoreBody r₁ env d e) (whnfCoreBody r₂ env d e) := by
  have := (whnfCoreBody (pairFns r₁ r₂ h) env d e).property
  rwa [whnfCoreBody_fst_proj, whnfCoreBody_snd_proj] at this

theorem whnfBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (whnfBody r₁ env d e) (whnfBody r₂ env d e) := by
  have := (whnfBody (pairFns r₁ r₂ h) env d e).property
  rwa [whnfBody_fst_proj, whnfBody_snd_proj] at this

theorem inferBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (inferBody r₁ env d e) (inferBody r₂ env d e) := by
  have := (inferBody (pairFns r₁ r₂ h) env d e).property
  rwa [inferBody_fst_proj, inferBody_snd_proj] at this

theorem defeqBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (defeqBody r₁ env d a b) (defeqBody r₂ env d a b) := by
  have := (defeqBody (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqBody_fst_proj, defeqBody_snd_proj] at this

theorem annotateBody_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (annotateBody r₁ env d e) (annotateBody r₂ env d e) := by
  have := (annotateBody (pairFns r₁ r₂ h) env d e).property
  rwa [annotateBody_fst_proj, annotateBody_snd_proj] at this

theorem ensureSort_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (ensureSort r₁ env d e) (ensureSort r₂ env d e) := by
  have := (ensureSort (pairFns r₁ r₂ h) env d e).property
  rwa [ensureSort_fst_proj, ensureSort_snd_proj] at this

end Commute

/-! ## Fuel monotonicity at the knot -/

theorem pureFns_mono (env : Env) : ∀ {f f' : Nat}, f ≤ f' →
    FnsRefines (pureFns env f) (pureFns env f')
  | 0, f', _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e v hv
      rw [show (pureFns env 0).whnfCore d e = whnfCore env 0 d e from rfl,
        whnfCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns env 0).whnf d e = whnf env 0 d e from rfl,
        whnf_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns env 0).infer d e = inferTypeCore env 0 d e from rfl,
        inferTypeCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d a b v hv
      rw [show (pureFns env 0).defeq d a b = isDefEqCore env 0 d a b from rfl,
        isDefEqCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
    · intro d e v hv
      rw [show (pureFns env 0).annotate d e = annotateCore env 0 d e from rfl,
        annotateCore_zero] at hv
      simp [throw, throwThe, MonadExceptOf.throw] at hv
  | f + 1, f' + 1, hle => by
    have ih := pureFns_mono env (Nat.le_of_succ_le_succ hle)
    exact ⟨fun d e => whnfCoreBody_mono ih d e,
      fun d e => whnfBody_mono ih d e,
      fun d e => inferBody_mono ih d e,
      fun d a b => defeqBody_mono ih d a b,
      fun d e => annotateBody_mono ih d e⟩

/-! ## Fueled corollaries -/

theorem whnfCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : whnfCore env f d e = .ok r) :
    whnfCore env f' d e = .ok r :=
  (pureFns_mono env hle).1 d e r h

theorem whnf_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : whnf env f d e = .ok r) :
    whnf env f' d e = .ok r :=
  (pureFns_mono env hle).2.1 d e r h

theorem inferTypeCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : inferTypeCore env f d e = .ok r) :
    inferTypeCore env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.1 d e r h

theorem isDefEqCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {a b : Expr} {r : Bool} (h : isDefEqCore env f d a b = .ok r) :
    isDefEqCore env f' d a b = .ok r :=
  (pureFns_mono env hle).2.2.2.1 d a b r h

theorem annotateCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr} (h : annotateCore env f d e = .ok r) :
    annotateCore env f' d e = .ok r :=
  (pureFns_mono env hle).2.2.2.2 d e r h

theorem ensureSortCore_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e : Expr} {u : Level}
    (h : ensureSortCore env f d e = .ok u) :
    ensureSortCore env f' d e = .ok u := by
  cases f with
  | zero =>
    rw [show ensureSortCore env 0 d e =
      ensureSort (pureFns env 0) env d e from rfl] at h
    revert h
    unfold ensureSort
    rw [show (pureFns env 0).whnf d e = whnf env 0 d e from rfl, whnf_zero]
    intro h
    simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | succ f =>
    cases f' with
    | zero => exact absurd hle (by omega)
    | succ f' =>
      exact ensureSort_mono (pureFns_mono env hle) d e u h

end Setlec
