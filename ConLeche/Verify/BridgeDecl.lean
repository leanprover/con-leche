module

public import ConLeche.Verify.Fueled
public import ConLeche.Kernel.CheckDecl

public section

/-!
# The cache-refinement bridge, part C: the declaration checker

The declaration checker is monad-polymorphic over a `CheckerOps`
record, so the same pair-monad game applies: `bridgeRel` relates
monotone fueled families to plain executable computations
("success on the executable side is reproduced at some fuel"), the
fueled/cached operation records are related by part B's entry-point
bridges, and the `atF` battery reads every declaration-checker
function at a fuel.  The punchline: a successful
`checkDeclsPure mode (wfOpsM mode)` run is reproduced by `checkDeclsPure mode (fueledOps mode F)`
for some fuel `F`.

This module holds the operation records (`bridgeRel`, `OpsRel`, `pairOps`,
`fueledOpsM`, `wfOpsM` and the `wfOpsM_*` equations) and the `atF` battery
— for every `check*` function, `(… (fueledOpsM …) …).val F = … (fueledOps …
F) …`, which is what `Verify/BridgeWfImp` and the cached lane's
`Verify/Cached/Bridge*` rewrite by (#184).
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-- Success on the executable side is reproduced at some fuel. -/
def bridgeRel : MonadRel FueledM CheckM where
  R p c := ∀ v, c = .ok v → ∃ F, p.val F = .ok v
  pure_rel a := fun v h => ⟨0, by cases h; rfl⟩
  bind_rel {α β x₁ x₂ f₁ f₂} hx hf := by
    intro v h
    simp only [Bind.bind] at h
    cases hx2 : x₂ with
    | error e => rw [hx2] at h; exact nomatch h
    | ok a =>
      rw [hx2] at h
      dsimp only [Except.bind] at h
      obtain ⟨F₁, h1⟩ := hx a hx2
      obtain ⟨F₂, h2⟩ := hf a v h
      refine ⟨max F₁ F₂, ?_⟩
      rw [FueledM.atF_bind]
      simp only [Bind.bind]
      rw [x₁.property (Nat.le_max_left F₁ F₂) h1]
      dsimp only [Except.bind]
      exact (f₁ a).property (Nat.le_max_right F₁ F₂) h2
  throw_rel e := fun v h => nomatch h

/-- Componentwise relatedness of two operation records. -/
def OpsRel {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    (rel : MonadRel M₁ M₂) (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂) :
    Prop :=
  (∀ env d e, rel.R (o₁.annotate env d e) (o₂.annotate env d e)) ∧
  (∀ env d e, rel.R (o₁.inferType env d e) (o₂.inferType env d e)) ∧
  (∀ env d a b, rel.R (o₁.isDefEq env d a b) (o₂.isDefEq env d a b)) ∧
  (∀ env d e, rel.R (o₁.ensureSort env d e) (o₂.ensureSort env d e)) ∧
  (∀ env d e, rel.R (o₁.whnf env d e) (o₂.whnf env d e)) ∧
  (∀ (x₁ : M₁ Bool) (x₂ : M₂ Bool) (k₁ : Option CheckError → M₁ Unit)
      (k₂ : Option CheckError → M₂ Unit),
    rel.R x₁ x₂ → (∀ r, rel.R (k₁ r) (k₂ r)) →
    rel.R (o₁.orElse x₁ k₁) (o₂.orElse x₂ k₂))

/-- The paired operation record. -/
def pairOps {M₁ M₂ : Type → Type} [Monad M₁] [Monad M₂]
    [MonadExceptOf CheckError M₁] [MonadExceptOf CheckError M₂]
    {rel : MonadRel M₁ M₂} (o₁ : CheckerOps M₁) (o₂ : CheckerOps M₂)
    (h : OpsRel rel o₁ o₂) : CheckerOps (PairM rel) where
  annotate env d e := ⟨(o₁.annotate env d e, o₂.annotate env d e), h.1 env d e⟩
  inferType env d e :=
    ⟨(o₁.inferType env d e, o₂.inferType env d e), h.2.1 env d e⟩
  isDefEq env d a b :=
    ⟨(o₁.isDefEq env d a b, o₂.isDefEq env d a b), h.2.2.1 env d a b⟩
  ensureSort env d e :=
    ⟨(o₁.ensureSort env d e, o₂.ensureSort env d e), h.2.2.2.1 env d e⟩
  whnf env d e := ⟨(o₁.whnf env d e, o₂.whnf env d e), h.2.2.2.2.1 env d e⟩
  orElse x k :=
    ⟨(o₁.orElse x.val.1 (fun r => (k r).val.1),
      o₂.orElse x.val.2 (fun r => (k r).val.2)),
      h.2.2.2.2.2 _ _ _ _ x.property (fun r => (k r).property)⟩

/-- The fueled operations as monotone families. -/
@[expose] def fueledOpsM (mode : CheckMode) : CheckerOps FueledM where
  annotate env d e :=
    ⟨fun F => annotateCore mode env F d e, fun hle h => annotateCore_mono hle h⟩
  inferType env d e :=
    ⟨fun F => inferTypeCore mode env F d e, fun hle h => inferTypeCore_mono hle h⟩
  isDefEq env d a b :=
    ⟨fun F => isDefEqCore mode env F d a b, fun hle h => isDefEqCore_mono hle h⟩
  ensureSort env d e :=
    ⟨fun F => ensureSortCore mode env F d e, fun hle h => ensureSortCore_mono hle h⟩
  whnf env d e :=
    ⟨fun F => whnf mode env F d e, fun hle h => whnf_mono hle h⟩
  -- the variant-fallback combinator (task #273): monotone because the
  -- result is `Unit` — an attempt that errs at one fuel and matches at
  -- a larger one changes the branch, not the success; the continuation
  -- is handed `none` (see `CheckerOps.orElse`)
  orElse x k :=
    ⟨fun F => match x.val F with
      | .ok true => pure ()
      | _ => (k none).val F, by
      intro F F' v hle h
      dsimp only at h ⊢
      cases hx : x.val F with
      | ok b =>
        rw [hx] at h
        rw [x.property hle hx]
        cases b with
        | true => exact h
        | false => exact (k none).property hle h
      | error e =>
        rw [hx] at h
        cases hx' : x.val F' with
        | ok b =>
          cases b with
          | true => cases v; rfl
          | false => exact (k none).property hle h
        | error e' => exact (k none).property hle h⟩

/-- `fueledOpsM`'s combinator at a fuel, by definition. -/
@[simp] theorem fueledOpsM_orElse_atF (x : FueledM Bool)
    (k : Option CheckError → FueledM Unit) (F : Nat) :
    ((fueledOpsM mode).orElse x k).val F =
      match x.val F with
      | .ok true => pure ()
      | _ => (k none).val F := rfl

/-- `fueledOps`' combinator, by definition (restated here for the
`atF` battery; `ConLeche/Verify/Extend/Inversions.lean` has the same
statement for its consumers). -/
theorem fueledOps_orElse' (F : Nat) (x : CheckM Bool)
    (k : Option CheckError → CheckM Unit) :
    (fueledOps mode F).orElse x k =
      match x with | .ok true => pure () | _ => k none := rfl

/-! ## The WF-conditional fueled comparand

Part B's entry-point bridges hold only over well-formed environments
(`EnvWF` — the depth-free memo cache is justified by depth invariance,
which needs it), and there is **no runtime check** for `EnvWF`: the
executable always runs the memoized knot.  To keep the pair-monad
battery unconditional, the fueled comparand is chosen per environment:
over a well-formed environment it is the pure fueled family, otherwise
the constant family that merely repeats the cached run (trivially
related).  The battery then yields, for *every* environment: a
successful cached `checkDecl` run is reproduced by its `wfOpsM mode`
instantiation at some fuel.
`ConLeche/Verify/BridgeWfImp.lean` turns `wfOpsM mode` runs into pure
`fueledOps` runs by threading `EnvWF` through the declaration checker's
intermediate environments, using the `wfOpsM_*` equalities below. -/

open Classical in
/-- The fueled families over well-formed environments *and* well-scoped
arguments (both are hypotheses of part B's entry-point bridges — the
executable's memo operations carry no runtime check for either); the
constant `.internal` error (a trivially monotone family) otherwise: every
use of `wfOpsM` goes through the `if_pos` equations below, so the other
branch has no consumer (#172). -/
noncomputable def wfOpsM (mode : CheckMode) : CheckerOps FueledM where
  annotate env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => annotateCore mode env F d e, fun hle h => annotateCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  inferType env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => inferTypeCore mode env F d e,
        fun hle h => inferTypeCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  isDefEq env d a b :=
    if EnvWF env ∧ a.wscopedB d = true ∧ b.wscopedB d = true then
      ⟨fun F => isDefEqCore mode env F d a b, fun hle h => isDefEqCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  ensureSort env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => ensureSortCore mode env F d e,
        fun hle h => ensureSortCore_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  whnf env d e :=
    if EnvWF env ∧ e.wscopedB d = true then
      ⟨fun F => whnf mode env F d e, fun hle h => whnf_mono hle h⟩
    else ⟨fun _ => throw (.internal "wfOpsM: precondition failed"),
      fun _ h => h⟩
  -- no precondition: the combinator runs no core body of its own
  orElse x k := (fueledOpsM mode).orElse x k

theorem wfOpsM_whnf {env : Env} (henv : EnvWF env) {d : Nat} {e : Expr}
    (hg : e.wscopedB d = true) :
    (wfOpsM mode).whnf env d e = (fueledOpsM mode).whnf env d e := by
  dsimp only [wfOpsM, fueledOpsM]
  exact if_pos ⟨henv, hg⟩

/-! ## The `atF` battery: fueled-family runs are fueled-ops runs -/

theorem foldlM_atF {α β : Type} (g : β → α → FueledM β) (F : Nat) :
    ∀ (l : List α) (init : β),
      (l.foldlM g init).val F =
        l.foldlM (fun b a => (g b a).val F) init
  | [], init => rfl
  | a :: l, init => by
    show ((g init a >>= fun b => l.foldlM g b : FueledM β)).val F = _
    rw [FueledM.atF_bind]
    show _ = (g init a).val F >>= fun b =>
      l.foldlM (fun b a => (g b a).val F) b
    congr 1
    funext b
    exact foldlM_atF g F l b

macro "datF_step_alt" : tactic =>
  `(tactic| first
    | (rw [liftFueled_atF])
    | (rw [foldlM_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only []))

macro "datF_tac" : tactic =>
  `(tactic| repeat' datF_step_alt)

theorem checkConstantVal_datF (env : Env) (cv : ConstantVal) (F : Nat) :
    (checkConstantVal (fueledOpsM mode) env cv).val F =
      checkConstantVal (fueledOps mode F) env cv := by
  unfold checkConstantVal
  datF_tac

theorem fueledOpsM_isDefEq_atF (env : Env) (d : Nat) (a b : Expr)
    (F : Nat) :
    ((fueledOpsM mode).isDefEq env d a b).val F =
      (fueledOps mode F).isDefEq env d a b := by rfl

theorem unwrapOr_atF {α : Type} (o : Option α) (e : CheckError)
    (F : Nat) :
    (unwrapOr o e : FueledM α).val F = (unwrapOr o e : CheckM α) := by
  cases o <;> rfl

theorem fueledOpsM_inferType_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).inferType env d a).val F =
      (fueledOps mode F).inferType env d a := by rfl

theorem installBasisDecl_datF (env : Env) (ci : ConstantInfo) (F : Nat) :
    (installBasisDecl env ci : FueledM _).val F =
      (installBasisDecl env ci : CheckM _) := by
  unfold installBasisDecl
  datF_tac

/-! ### The per-member stages, at fuel `F` -/

theorem fueledOpsM_annotate_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).annotate env d a).val F =
      (fueledOps mode F).annotate env d a := by rfl

theorem fueledOpsM_ensureSort_atF (env : Env) (d : Nat) (a : Expr)
    (F : Nat) :
    ((fueledOpsM mode).ensureSort env d a).val F =
      (fueledOps mode F).ensureSort env d a := by rfl

theorem checkStructDomsAt_datF (env : Env) (off : Nat)
    (fvs doms : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructDomsAt (fueledOpsM mode) env off fvs doms j).val F =
        checkStructDomsAt (fueledOps mode F) env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, unwrapOr_atF,
      checkStructDomsAt_datF env off fvs doms F j]

theorem checkStructProjTable_datF (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) (F : Nat) :
    (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM _).val F =
      (checkStructProjTable T C lps nP nF rs guards off cvCa env : CheckM _) := by
  unfold checkStructProjTable
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF]

/-! ### The constructor-list stages (#175) -/

theorem fueledOpsM_whnf_atF (env : Env) (d : Nat) (a : Expr) (F : Nat) :
    ((fueledOpsM mode).whnf env d a).val F = (fueledOps mode F).whnf env d a := by rfl

/-- Official's telescope loop (task #195) at fuel `F`. -/
theorem whnfTelescope_datF (env : Env) (F : Nat) :
    ∀ (i n : Nat) (e : Expr),
      (whnfTelescope (fueledOpsM mode) env i n e).val F =
        whnfTelescope (fueledOps mode F) env i n e
  | i, 0, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split <;> simp only [FueledM.atF_pure, FueledM.atF_throw]
  | i, n + 1, e => by
    unfold whnfTelescope
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext e'
    split
    · next nm dom body bm =>
      simp only [FueledM.atF_bind, FueledM.atF_pure,
        whnfTelescope_datF env F (i + 1) n (body.instantiate1 (.fvar i dom))]
    · simp only [FueledM.atF_throw]

/-- The former's telescope stage (task #195) at fuel `F`. -/
theorem checkSumTele_datF (env : Env) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) (F : Nat) :
    (checkSumTele (fueledOpsM mode) env cv n cvTa₀).val F =
      checkSumTele (fueledOps mode F) env cv n cvTa₀ := by
  unfold checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none =>
    simp only [FueledM.atF_bind, FueledM.atF_pure, whnfTelescope_datF, checkConstantVal_datF]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [FueledM.atF_bind, FueledM.atF_pure, whnfTelescope_datF,
      checkConstantVal_datF]

/-- `checkStructFieldSortsI` (task #175 indexed) at fuel `F`. -/
theorem checkStructFieldSortsI_datF (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkStructFieldSortsI (fueledOpsM mode) env isProp large s nP fvs idxArgs
          j).val F =
        checkStructFieldSortsI (fueledOps mode F) env isProp large s nP fvs idxArgs j
  | 0 => rfl
  | j + 1 => by
    unfold checkStructFieldSortsI
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      liftFueled_atF, unwrapOr_atF,
      checkStructFieldSortsI_datF env isProp large s nP fvs idxArgs F j]

/-! ### The positivity function (`nestPos`) at fuel `F` -/

section NestPos

open ConLeche (NestCtx NestKey NestHole NestState NestFieldKind nestInstType nestGrowGroup
  nestGroupCtors nestFields nestCtors nestFrame nestCont nestPos nestMemberCtor
  nestMemberCtors nestBlockCtors nestedBlockPositivity nestContainerC)

theorem nestInstType_datF (ctx : NestCtx) (hi : Nat) (key : NestKey) (F : Nat) :
    (nestInstType (m := FueledM) ctx hi key).val F = nestInstType (m := CheckM) ctx hi key := by
  unfold nestInstType
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite, unwrapOr_atF,
    liftFueled_atF]

theorem nestGrowGroup_datF (ctx : NestCtx) (hi : Nat) (us : List Level) (ds : List Expr)
    (F : Nat) :
    ∀ (cs : List Name) (grp : List (Name × Expr)),
      (nestGrowGroup (m := FueledM) ctx hi us ds cs grp).val F
        = nestGrowGroup (m := CheckM) ctx hi us ds cs grp
  | [], _ => rfl
  | c :: cs, grp => by
    unfold nestGrowGroup
    simp only [FueledM.atF_bind, nestInstType_datF]
    congr 1
    funext q
    exact nestGrowGroup_datF ctx hi us ds F cs _

theorem nestGroupCtors_datF (ctx : NestCtx) (nPc : Nat) (F : Nat) :
    ∀ (cs : List Name) (st : NestState),
      (nestGroupCtors (m := FueledM) ctx nPc cs st).val F = nestGroupCtors (m := CheckM) ctx nPc cs st
  | [], _ => rfl
  | c :: cs, st => by
    unfold nestGroupCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, nestGroupCtors_datF ctx nPc F cs]

variable {rec : List NestHole → Nat → Nat → Expr → NestState →
    FueledM (NestFieldKind × Expr × NestState)}
  {rec' : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}

theorem nestFields_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState),
      (nestFields rec prog base err nF j cur st).val F
        = nestFields rec' prog base err nF j cur st
  | 0, _, _, _ => rfl
  | nF + 1, j, cur, st => by
    unfold nestFields
    split
    · simp only [FueledM.atF_bind, hrec]
      congr 1
      funext q
      simp only [FueledM.atF_pure, FueledM.atF_bind,
        nestFields_datF hrec prog base err nF (j + 1)]
    · rfl

theorem nestCtors_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (sub : Name → List Level → Option Expr) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState),
      (nestCtors ctx (fueledOpsM mode) env rec prog hi us ds nPc sub cs st).val F
        = nestCtors ctx (fueledOps mode F) env rec' prog hi us ds nPc sub cs st
  | [], _ => rfl
  | (cv, nF) :: cs, st => by
    unfold nestCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      nestFields_datF hrec, nestCtors_datF hrec ctx env prog hi us ds nPc sub cs]

theorem nestFrame_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (grp : List (Name × Expr)) (st : NestState) :
    (nestFrame ctx (fueledOpsM mode) env rec prog hi us ds nPc grp st).val F
      = nestFrame ctx (fueledOps mode F) env rec' prog hi us ds nPc grp st := by
  unfold nestFrame
  simp only [FueledM.atF_bind, fueledOpsM_inferType_atF, nestGroupCtors_datF]
  congr 1
  funext _
  congr 1
  funext q
  simp only [nestCtors_datF hrec]

theorem nestContNew_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) (cty : Expr) (st : NestState) :
    (ConLeche.nestContNew ctx (fueledOpsM mode) env rec prog kb n us ds nPc cty st).val F
      = ConLeche.nestContNew ctx (fueledOps mode F) env rec' prog kb n us ds nPc cty st := by
  unfold ConLeche.nestContNew
  simp only [FueledM.atF_bind, FueledM.atF_pure, nestGrowGroup_datF, nestFrame_datF hrec]

theorem nestContKey_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (ds : List Expr) (nPc : Nat) (cty : Expr) (st : NestState) :
    (ConLeche.nestContKey ctx (fueledOpsM mode) env rec prog kb n us ds nPc cty st).val F
      = ConLeche.nestContKey ctx (fueledOps mode F) env rec' prog kb n us ds nPc cty st := by
  unfold ConLeche.nestContKey
  split
  · simp only [FueledM.atF_throw]
  · split
    · rfl
    · exact nestContNew_datF hrec ctx env prog kb n us ds nPc cty st

theorem nestCont_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level)
    (args : List Expr) (st : NestState) :
    (nestCont ctx (fueledOpsM mode) env rec prog kb n us args st).val F
      = nestCont ctx (fueledOps mode F) env rec' prog kb n us args st := by
  unfold nestCont
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, nestContKey_datF hrec, nestInstType_datF]

end NestPos

theorem nestPos_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (fuel : Nat) (prog : List ConLeche.NestHole) (dep kb : Nat) (e : Expr)
      (st : ConLeche.NestState),
      (ConLeche.nestPos (fueledOpsM mode) env ctx fuel prog dep kb e st).val F
        = ConLeche.nestPos (fueledOps mode F) env ctx fuel prog dep kb e st := by
  intro fuel
  induction fuel with
  | zero => exact fun _ _ _ _ _ => rfl
  | succ fuel ih =>
    intro prog dep kb e st
    unfold ConLeche.nestPos
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext w
    simp only [FueledM.atF_ite, FueledM.atF_pure]
    split
    · rfl
    · split
      · simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_bind, FueledM.atF_pure, ih]
      · repeat' split
        all_goals (try simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_bind,
          FueledM.atF_pure, nestCont_datF (rec := ConLeche.nestPos (fueledOpsM mode) env ctx fuel)
            (rec' := ConLeche.nestPos (fueledOps mode F) env ctx fuel) ih])
        all_goals (try rfl)

theorem nestMemberCtor_datF (env : Env) (ctx : ConLeche.NestCtx) (nF : Nat) (crest : Expr)
    (st : ConLeche.NestState) (F : Nat) :
    (ConLeche.nestMemberCtor (fueledOpsM mode) env ctx nF crest st).val F
      = ConLeche.nestMemberCtor (fueledOps mode F) env ctx nF crest st := by
  unfold ConLeche.nestMemberCtor
  simp only [FueledM.atF_bind, nestFields_datF (nestPos_datF env ctx F (ConLeche.whnfWalkFuel crest))]
  congr 1
  funext q
  simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_pure, FueledM.atF_bind]

theorem nestNoMemberConst_datF (ctx : ConLeche.NestCtx) (e : Expr) (F : Nat) :
    (ConLeche.nestNoMemberConst (m := FueledM) ctx e).val F
      = ConLeche.nestNoMemberConst (m := CheckM) ctx e := by
  unfold ConLeche.nestNoMemberConst
  simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_pure]

theorem nestMemberCtors_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr)
    (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (st : ConLeche.NestState),
      (ConLeche.nestMemberCtors (fueledOpsM mode) env ctx holes cs st).val F
        = ConLeche.nestMemberCtors (fueledOps mode F) env ctx holes cs st
  | [], _ => rfl
  | c :: cs, st => by
    unfold ConLeche.nestMemberCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, FueledM.atF_throw,
      nestNoMemberConst_datF, unwrapOr_atF, nestMemberCtor_datF,
      nestMemberCtors_datF env ctx holes F cs]

theorem checkSumCtor_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat)
    (cvTa : ConstantVal) (F : Nat) :
    (checkSumCtor (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
      cvC nF cvTa).val F =
      checkSumCtor (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
        cvC nF cvTa := by
  unfold checkSumCtor
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, unwrapOr_atF, checkConstantVal_datF,
    checkStructFieldSortsI_datF, checkStructDomsAt_datF]

theorem checkSumCtors_datF (env₀ env : Env) (T : Name) (lps : List Name)
    (nP nIdx : Nat) (rs : Level) (isProp large : Bool) (cvTa : ConstantVal) (F : Nat) :
    ∀ cs : List (ConstantVal × Nat),
      (checkSumCtors (fueledOpsM mode) env₀ env T lps nP nIdx rs isProp large
        cvTa cs).val F =
        checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx rs isProp large
          cvTa cs
  | [] => rfl
  | c :: cs => by
    unfold checkSumCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumCtor_datF,
      checkSumCtors_datF env₀ env T lps nP nIdx rs isProp large cvTa F cs]

/-! ### The recursor conformance check's generator (#188) -/

theorem checkNativeRules_datF (envR : Env) (rlps : List Name) (T : Name)
    (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level)
    (F : Nat) :
    ∀ k j : Nat,
      (checkNativeRules (m := FueledM) envR rlps T lps elim large nP nIdx tty ctors
        recC rlvls k j).val F =
        checkNativeRules (m := CheckM) envR rlps T lps elim large nP nIdx tty ctors
          recC rlvls k j
  | 0, _ => rfl
  | k + 1, j => by
    unfold checkNativeRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF,
      checkNativeRules_datF envR rlps T lps elim large nP nIdx tty ctors recC rlvls F k
        (j + 1)]

theorem checkNativeRec_datF (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) (F : Nat) :
    (checkNativeRec (fueledOpsM mode) env p cvTa ctorsA).val F =
      checkNativeRec (fueledOps mode F) env p cvTa ctorsA := by
  unfold checkNativeRec
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
    FueledM.atF_ite, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
    fueledOpsM_ensureSort_atF, unwrapOr_atF, checkConstantVal_datF,
    checkNativeRules_datF]

/-! ### The uniform install at k members

Every stage of `checkBlock` at fuel `F`, read off the same program at
the two monads, at EVERY `k`. -/

theorem checkBlockTele_datF (env : Env) (nP : Nat) (ms : MemberShape) (F : Nat) :
    (checkBlockTele (fueledOpsM mode) env nP ms).val F =
      checkBlockTele (fueledOps mode F) env nP ms := by
  unfold checkBlockTele
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkConstantVal_datF, checkSumTele_datF]

theorem checkBlockTeles_datF (env : Env) (nP F : Nat) :
    ∀ mss : List MemberShape,
      (checkBlockTeles (fueledOpsM mode) env nP mss).val F =
        checkBlockTeles (fueledOps mode F) env nP mss
  | [] => rfl
  | ms :: rest => by
    unfold checkBlockTeles
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockTele_datF,
      checkBlockTeles_datF env nP F rest]

theorem checkBlockDomsAt_datF (env : Env) (off : Nat) (fvs doms : List Expr) (F : Nat) :
    ∀ j : Nat,
      (checkBlockDomsAt (fueledOpsM mode) env off fvs doms j).val F =
        checkBlockDomsAt (fueledOps mode F) env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    unfold checkBlockDomsAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, fueledOpsM_isDefEq_atF, unwrapOr_atF,
      checkBlockDomsAt_datF env off fvs doms F j]

theorem checkBlockAgree_datF (env : Env) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level)
    (F : Nat) :
    ∀ cvs : List (ConstantVal × Level),
      (checkBlockAgree (fueledOpsM mode) env nP cvTa0 s0 cvs).val F =
        checkBlockAgree (fueledOps mode F) env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    unfold checkBlockAgree
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      FueledM.atF_ite, unwrapOr_atF, checkBlockDomsAt_datF, liftFueled_atF,
      checkBlockAgree_datF env nP cvTa0 s0 F rest]

theorem checkBlockInds_datF (env : Env) (p : BlockParts) (isRec : Bool) (F : Nat) :
    (checkBlockInds (fueledOpsM mode) env p isRec).val F =
      checkBlockInds (fueledOps mode F) env p isRec := by
  unfold checkBlockInds
  split
  · rfl
  · simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockTele_datF,
      checkBlockTeles_datF, checkBlockAgree_datF]

theorem checkBlockCtors_datF (env₀ env : Env) (p : BlockShape)
    (F : Nat) :
    ∀ l : List (MemberShape × ConstantVal),
      (checkBlockCtors (fueledOpsM mode) env₀ env p l).val F =
        checkBlockCtors (fueledOps mode F) env₀ env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    unfold checkBlockCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkSumCtors_datF,
      checkBlockCtors_datF env₀ env p F rest]

theorem checkBlockIdxSorts_datF (env₁ : Env) (p : BlockShape) (F : Nat) :
    ∀ l : List (MemberShape × ConstantVal),
      (checkBlockIdxSorts (fueledOpsM mode) env₁ p l).val F =
        checkBlockIdxSorts (fueledOps mode F) env₁ p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    unfold checkBlockIdxSorts
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF,
      checkStructFieldSortsI_datF, checkBlockIdxSorts_datF env₁ p F rest]

theorem checkBlockDefEqList_datF (env : Env) (depth : Nat) (what : String) (F : Nat) :
    ∀ (as bs : List Expr),
      (checkBlockDefEqList (fueledOpsM mode) env depth what as bs).val F =
        checkBlockDefEqList (fueledOps mode F) env depth what as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold checkBlockDefEqList
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      fueledOpsM_isDefEq_atF, checkBlockDefEqList_datF env depth what F as bs]

theorem checkBlockRecPrefixAt_datF (env : Env) (p : BlockShape) (rP0 : Nat)
    (doms0 : List Expr) (F : Nat) :
    ∀ (l : List ConstantVal) (ri : Nat),
      (checkBlockRecPrefixAt (fueledOpsM mode) env p rP0 doms0 l ri).val F =
        checkBlockRecPrefixAt (fueledOps mode F) env p rP0 doms0 l ri
  | [], _ => rfl
  | cv :: rest, ri => by
    unfold checkBlockRecPrefixAt
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, checkBlockDefEqList_datF,
      checkBlockRecPrefixAt_datF env p rP0 doms0 F rest (ri + 1)]

theorem checkBlockRecPrefixAgree_datF (env : Env) (p : BlockShape) (cvRs : List ConstantVal)
    (F : Nat) :
    (checkBlockRecPrefixAgree (fueledOpsM mode) env p cvRs).val F =
      checkBlockRecPrefixAgree (fueledOps mode F) env p cvRs := by
  unfold checkBlockRecPrefixAgree
  split
  · rfl
  · simp only [FueledM.atF_bind, unwrapOr_atF, checkBlockRecPrefixAt_datF]

theorem checkBlockRecSmallElim_datF (p : BlockShape) (nested : Bool) (us : List Level)
    (F : Nat) :
    (checkBlockRecSmallElim (m := FueledM) p nested us).val F =
      checkBlockRecSmallElim (m := CheckM) p nested us := by
  unfold checkBlockRecSmallElim
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite]

theorem checkBlockRecElimPin_datF (p : BlockShape) (us : List Level) (F : Nat) :
    (checkBlockRecElimPin (m := FueledM) p us).val F =
      checkBlockRecElimPin (m := CheckM) p us := by
  unfold checkBlockRecElimPin
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    liftFueled_atF]

theorem FueledM.atF_mapConst {α : Type} (x : FueledM α) (F : Nat) :
    (Functor.mapConst PUnit.unit x : FueledM PUnit).val F
      = (Functor.mapConst PUnit.unit (x.val F) : CheckM PUnit) := by
  show (x >>= fun _ => pure PUnit.unit : FueledM PUnit).val F = _
  rw [FueledM.atF_bind]
  cases x.val F <;> rfl

theorem confKinds_datF (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (F : Nat) :
    (confKinds (m := FueledM) T lps nP nIdx ctorsA).val F =
      confKinds (m := CheckM) T lps nP nIdx ctorsA := by
  unfold confKinds
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF]

/-- The reject-only conformance check at fuel `F`. -/
theorem checkBlockRecConform_datF (env : Env) (p : BlockParts) (block : List ConstantInfo)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (nfs : List (List Expr)) (F : Nat) :
    (checkBlockRecConform (fueledOpsM mode) env p block cvTas ctorsAs nfs).val F =
      checkBlockRecConform (fueledOps mode F) env p block cvTas ctorsAs nfs := by
  unfold checkBlockRecConform
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      discard, Functor.discard, FueledM.atF_mapConst, checkNativeRec_datF, confKinds_datF]
  · rfl

/-! ### The target recursor check at fuel `F` -/

macro "tdatF_tac" : tactic =>
  `(tactic| repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
        fueledOpsM_ensureSort_atF, fueledOpsM_whnf_atF, fueledOpsM_annotate_atF,
        liftFueled_atF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)))


theorem checkConstantValF_datF (fe : FEnv) (cv : ConstantVal) (F : Nat) :
    (checkConstantValF (fueledOpsM mode) fe cv).val F =
      checkConstantValF (fueledOps mode F) fe cv := by
  unfold checkConstantValF
  datF_tac

theorem targetOutsideInst_datF (fe : FEnv) (I : Name) (us : List Level) (ds : List Expr)
    (F : Nat) :
    (targetOutsideInst (m := FueledM) fe I us ds).val F =
      targetOutsideInst (m := CheckM) fe I us ds := by
  unfold targetOutsideInst
  datF_tac

theorem targetParamsDefEq_datF (env : Env) (d : Nat) (absM : Expr → Expr) (pfvs : List Expr)
    (F : Nat) :
    ∀ (as bs : List Expr),
      (targetParamsDefEq (fueledOpsM mode) env d absM pfvs as bs).val F =
        targetParamsDefEq (fueledOps mode F) env d absM pfvs as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold targetParamsDefEq
    simp only [FueledM.atF_bind, FueledM.atF_pure, fueledOpsM_inferType_atF,
      fueledOpsM_isDefEq_atF, FueledM.atF_ite, targetParamsDefEq_datF env d absM pfvs F as bs]
    repeat' split <;> try rfl

theorem targetClassMatch_datF (env : Env) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr) (F : Nat) :
    (targetClassMatch (fueledOpsM mode) env p formerTys pfvs us ds lvls eds).val F =
      targetClassMatch (fueledOps mode F) env p formerTys pfvs us ds lvls eds := by
  unfold targetClassMatch
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, targetParamsDefEq_datF]

theorem targetMajorNfs_datF (env : Env) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat)) (F : Nat) :
    ∀ (es : List NestCtorNf),
      (targetMajorNfs (fueledOpsM mode) env p formerTys pfvs us ds ctors es).val F =
        targetMajorNfs (fueledOps mode F) env p formerTys pfvs us ds ctors es
  | [] => rfl
  | e :: es => by
    unfold targetMajorNfs
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, targetClassMatch_datF,
      targetMajorNfs_datF env p formerTys pfvs us ds ctors F es]

theorem targetNodeTie_datF (env : Env) (p : BlockShape) (formerTys pfvs : List Expr) (I : Name)
    (us : List Level) (ds : List Expr) (F : Nat) :
    ∀ (ks : List NestKey),
      (targetNodeTie (fueledOpsM mode) env p formerTys pfvs I us ds ks).val F =
        targetNodeTie (fueledOps mode F) env p formerTys pfvs I us ds ks
  | [] => rfl
  | k :: ks => by
    unfold targetNodeTie
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_ite, targetClassMatch_datF,
      targetNodeTie_datF env p formerTys pfvs I us ds F ks]

theorem targetMajorOf_datF (fe : FEnv) (p : BlockShape) (aux : NestNodes) (formerTys : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) (F : Nat) :
    (targetMajorOf (fueledOpsM mode) fe p aux formerTys ctorsAs pfvs fvs mty).val F =
      targetMajorOf (fueledOps mode F) fe p aux formerTys ctorsAs pfvs fvs mty := by
  unfold targetMajorOf
  repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, liftFueled_atF, targetOutsideInst_datF, targetMajorNfs_datF,
        targetNodeTie_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _))

theorem targetIdxDoms_datF (fe : FEnv) (p : BlockShape) (cvTas : List ConstantVal) (rP : Nat)
    (M : TargetMajor) (F : Nat) :
    (targetIdxDoms (m := FueledM) fe p cvTas rP M).val F =
      targetIdxDoms (m := CheckM) fe p cvTas rP M := by
  unfold targetIdxDoms
  tdatF_tac

theorem targetPinTys_datF (env : Env) (d : Nat) (F : Nat) :
    ∀ (xs : List Expr),
      (targetPinTys (fueledOpsM mode) env d xs).val F = targetPinTys (fueledOps mode F) env d xs
  | [] => rfl
  | x :: xs => by
    unfold targetPinTys
    simp only [FueledM.atF_bind, fueledOpsM_inferType_atF, targetPinTys_datF env d F xs]

theorem targetMajorPins_datF (env : Env) (rP : Nat) (M : TargetMajor) (F : Nat) :
    (targetMajorPins (fueledOpsM mode) env rP M).val F
      = targetMajorPins (fueledOps mode F) env rP M := by
  unfold targetMajorPins
  split
  · simp only [FueledM.atF_bind, FueledM.atF_pure, fueledOpsM_inferType_atF,
      targetPinTys_datF env rP F M.ds]
  · rfl

theorem targetRecTy_datF (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : NestNodes)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) (rc : RecShape)
    (F : Nat) :
    (targetRecTy (fueledOpsM mode) fe p nested aux cvTas ctorsAs rc).val F =
      targetRecTy (fueledOps mode F) fe p nested aux cvTas ctorsAs rc := by
  unfold targetRecTy
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkConstantValF_datF, targetMajorOf_datF, targetIdxDoms_datF,
    checkBlockDefEqList_datF, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF,
    fueledOpsM_ensureSort_atF, targetMajorPins_datF]

theorem targetRecTys_datF (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : NestNodes)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    ∀ (l : List RecShape),
      (targetRecTys (fueledOpsM mode) fe p nested aux cvTas ctorsAs l).val F =
        targetRecTys (fueledOps mode F) fe p nested aux cvTas ctorsAs l
  | [] => rfl
  | rc :: rest => by
    unfold targetRecTys
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetRecTy_datF,
      targetRecTys_datF fe p nested aux cvTas ctorsAs F rest]

theorem targetRecPins_datF (p : BlockShape) (block : List ConstantInfo) (F : Nat) :
    (targetRecPins (m := FueledM) p block).val F = targetRecPins (m := CheckM) p block := by
  unfold targetRecPins
  datF_tac

theorem targetRulePins_datF (rc : ConstantVal) (M : TargetMajor) (rules : List RecRule)
    (F : Nat) :
    (targetRulePins (m := FueledM) rc M rules).val F = targetRulePins (m := CheckM) rc M rules := by
  unfold targetRulePins
  datF_tac

theorem targetRulePinsAll_datF (F : Nat) :
    ∀ (tys : List (ConstantVal × TargetMajor × Level)) (rss : List (List RecRule)),
      (targetRulePinsAll (m := FueledM) tys rss).val F = targetRulePinsAll (m := CheckM) tys rss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, rs :: rss => by
    unfold targetRulePinsAll
    simp only [FueledM.atF_bind, targetRulePins_datF, targetRulePinsAll_datF F ts rss]

theorem targetWhnfPis_datF (env : Env) (F : Nat) :
    ∀ (d fuel : Nat) (e : Expr),
      (targetWhnfPis (fueledOpsM mode) env d fuel e).val F =
        targetWhnfPis (fueledOps mode F) env d fuel e
  | _, 0, _ => rfl
  | d, fuel + 1, e => by
    unfold targetWhnfPis
    simp only [FueledM.atF_bind, fueledOpsM_whnf_atF]
    congr 1
    funext w
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, targetWhnfPis_datF env F]
    · rfl

theorem targetFieldNorms_datF (env : Env) (depth : Nat) (absM : Expr → Expr) (F : Nat) :
    ∀ (l : List Expr),
      (targetFieldNorms (fueledOpsM mode) env depth absM l).val F =
        targetFieldNorms (fueledOps mode F) env depth absM l
  | [] => rfl
  | f :: fs => by
    unfold targetFieldNorms
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetWhnfPis_datF,
      targetFieldNorms_datF env depth absM F fs]

theorem targetAbsFieldsOk_datF (env : Env) (F : Nat) :
    ∀ (d : Nat) (l : List Expr),
      (targetAbsFieldsOk (fueledOpsM mode) env d l).val F =
        targetAbsFieldsOk (fueledOps mode F) env d l
  | _, [] => rfl
  | d, f :: fs => by
    unfold targetAbsFieldsOk
    simp only [FueledM.atF_bind, fueledOpsM_inferType_atF, targetAbsFieldsOk_datF env F (d + 1) fs]

theorem targetK53_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (Mc : TargetMajor)
    (tele : List (Expr × BinderMeta)) (majDom f : Expr) (F : Nat) :
    (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f).val F =
      targetK53 (fueledOps mode F) env p formerTys Mc tele majDom f := by
  unfold targetK53
  repeat' split
  all_goals first | rfl | exact targetClassMatch_datF _ _ _ _ _ _ _ _ _

theorem targetK53All_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (Mc : TargetMajor)
    (tele : List (Expr × BinderMeta)) (majDom : Expr) (i F : Nat) :
    ∀ (fwss : List (List Expr)),
      (targetK53All (fueledOpsM mode) env p formerTys Mc tele majDom i fwss).val F =
        targetK53All (fueledOps mode F) env p formerTys Mc tele majDom i fwss
  | [] => rfl
  | fws :: fwss => by
    unfold targetK53All
    split
    · rfl
    · simp only [FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_pure, targetK53_datF,
        targetK53All_datF env p formerTys Mc tele majDom i F fwss]

theorem targetCallOk_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (cn : Name)
    (fam : TargetFamily)
    (fvsPref fvsF : List Expr) (teles : List (List (Expr × BinderMeta)))
    (absM mvF : Expr → Expr) (base k dA : Nat) (pw : PropWhen) (fwss : List (List Expr))
    (ih : TargetIh) (F : Nat) :
    (targetCallOk (fueledOpsM mode) env p formerTys cn fam fvsPref fvsF teles absM mvF base k
        dA pw fwss ih).val F =
      targetCallOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles absM mvF base k
        dA pw fwss ih := by
  unfold targetCallOk
  repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, fueledOpsM_isDefEq_atF, fueledOpsM_inferType_atF, targetK53All_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _))

theorem targetCallsOk_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (cn : Name)
    (fam : TargetFamily)
    (fvsPref fvsF : List Expr) (teles : List (List (Expr × BinderMeta)))
    (absM mvF : Expr → Expr) (base k dA : Nat) (pw : PropWhen) (fwss : List (List Expr))
    (F : Nat) :
    ∀ (ihs : List TargetIh),
      (targetCallsOk (fueledOpsM mode) env p formerTys cn fam fvsPref fvsF teles absM mvF base
          k dA pw fwss ihs).val F =
        targetCallsOk (fueledOps mode F) env p formerTys cn fam fvsPref fvsF teles absM mvF base
          k dA pw fwss ihs
  | [] => rfl
  | ih :: ihs => by
    unfold targetCallsOk
    simp only [FueledM.atF_bind, targetCallOk_datF,
      targetCallsOk_datF env p formerTys cn fam fvsPref fvsF teles absM mvF base k dA pw fwss F
        ihs]

theorem targetRule_datF (feR : FEnv) (feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (cvR : ConstantVal) (rP : Nat) (recTy : Expr) (M : TargetMajor)
    (c : ConstantVal × Nat) (rhs : Expr) (F : Nat) :
    (targetRule (fueledOpsM mode) .plain feR (fueledOpsM mode) feT p formerTys fam cvR rP recTy M
        c rhs).val F =
      targetRule (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvR rP
        recTy M c rhs := by
  unfold targetRule
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, checkBlockDefEqList_datF, fueledOpsM_isDefEq_atF,
    fueledOpsM_inferType_atF, fueledOpsM_annotate_atF, targetFieldNorms_datF,
    targetAbsFieldsOk_datF, targetCallsOk_datF]

theorem targetRules_datF (feR feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (cvRi : ConstantVal) (rP : Nat) (M : TargetMajor) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (rhss : List Expr),
      (targetRules (fueledOpsM mode) .plain feR (fueledOpsM mode) feT p formerTys fam cvRi rP M
          cs rhss).val F =
        targetRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam cvRi rP
          M cs rhss
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | cA :: cs, rhs :: rhss => by
    unfold targetRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetRule_datF,
      targetRules_datF feR feT p formerTys fam cvRi rP M F cs rhss]

theorem targetRecsRules_datF (feR feT : FEnv) (p : BlockShape) (formerTys : List Expr)
    (fam : TargetFamily) (F : Nat) :
    ∀ (recs : List RecShape) (tys : List (ConstantVal × TargetMajor × Level)),
      (targetRecsRules (fueledOpsM mode) .plain feR (fueledOpsM mode) feT p formerTys fam recs
          tys).val F =
        targetRecsRules (fueledOps mode F) .plain feR (fueledOps mode F) feT p formerTys fam
          recs tys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | rc :: rcs, (cvRi, M, u) :: ts => by
    unfold targetRecsRules
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      targetRules_datF, targetRecsRules_datF feR feT p formerTys fam F rcs ts]

/-- **The target recursor check at fuel `F`**: the pure install's run
(`ShadowOps.ofOps` at the fueled family) is the model's fueled run. -/
theorem targetRecCheck_datF (fe : FEnv) (p : BlockShape) (nested : Bool)
    (aux : NestNodes)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (targetRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe p nested aux block cvTas
        ctorsAs).val F =
      targetRecCheck (ShadowOps.fueled mode F) fe p nested aux block cvTas ctorsAs := by
  unfold targetRecCheck
  simp only [ShadowOps.ofOps, ShadowOps.fueled, FueledM.atF_bind, FueledM.atF_pure,
    targetRecPins_datF, targetRecTys_datF, checkBlockRecSmallElim_datF,
    checkBlockRecElimPin_datF, checkBlockRecPrefixAgree_datF, targetRulePinsAll_datF,
    targetRecsRules_datF]

theorem checkBlockRecT_datF (env : Env) (p : BlockParts) (nested : Bool) (aux : NestNodes)
    (block : List ConstantInfo)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (checkBlockRecT (fueledOpsM mode) env p nested aux block cvTas ctorsAs).val F =
      checkBlockRecT (fueledOps mode F) env p nested aux block cvTas ctorsAs := by
  unfold checkBlockRecT
  simp only [targetRecCheck_datF]
  rfl

theorem checkBlockRec_datF (env : Env) (p : BlockParts) (nested conf : Bool)
    (aux : NestNodes)
    (block : List ConstantInfo)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (nfs : List (List Expr)) (F : Nat) :
    (checkBlockRec (fueledOpsM mode) env p nested conf aux block cvTas ctorsAs nfs).val F =
      checkBlockRec (fueledOps mode F) env p nested conf aux block cvTas ctorsAs nfs := by
  unfold checkBlockRec thenConform
  cases conf <;>
  simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockRecT_datF,
    checkBlockRecConform_datF, Bool.false_eq_true, ↓reduceIte]

theorem checkBlockTables_datF (p : BlockShape) (F : Nat) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env),
      (checkBlockTables (m := FueledM) p l env).val F =
        checkBlockTables (m := CheckM) p l env
  | [], _ => rfl
  | (ms, ctorsA, sortss) :: rest, env => by
    unfold checkBlockTables
    rw [FueledM.atF_bind]
    split
    · split
      · rw [checkStructProjTable_datF]
        congr 1
        funext env'
        exact checkBlockTables_datF p F rest env'
      · exact checkBlockTables_datF p F rest env
    · exact checkBlockTables_datF p F rest env

theorem nestBlockCtors_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr)
    (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : ConLeche.NestState),
      (ConLeche.nestBlockCtors (fueledOpsM mode) env ctx holes css st).val F
        = ConLeche.nestBlockCtors (fueledOps mode F) env ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    unfold ConLeche.nestBlockCtors
    simp only [FueledM.atF_bind, nestMemberCtors_datF]
    congr 1
    funext q
    simp only [FueledM.atF_bind, FueledM.atF_pure, nestBlockCtors_datF env ctx holes F css]

theorem nestedBlockPositivity_datF (env : Env) (ctx : ConLeche.NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) (F : Nat) :
    (ConLeche.nestedBlockPositivity (fueledOpsM mode) env ctx ctorss).val F
      = ConLeche.nestedBlockPositivity (fueledOps mode F) env ctx ctorss := by
  unfold ConLeche.nestedBlockPositivity
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, nestBlockCtors_datF]

theorem checkAbsCtorTys_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (ns : List Expr),
      (checkAbsCtorTys (fueledOpsM mode) env ctx holes cs ns).val F
        = checkAbsCtorTys (fueledOps mode F) env ctx holes cs ns
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, n :: ns => by
    unfold checkAbsCtorTys
    simp only [FueledM.atF_bind, unwrapOr_atF, fueledOpsM_inferType_atF, FueledM.atF_ite,
      FueledM.atF_throw, FueledM.atF_pure, fueledOpsM_ensureSort_atF, checkStructFieldSortsI_datF,
      checkAbsCtorTys_datF env ctx holes F cs ns]

theorem checkAbsCtorTysAll_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (nss : List (List Expr)),
      (checkAbsCtorTysAll (fueledOpsM mode) env ctx holes css nss).val F
        = checkAbsCtorTysAll (fueledOps mode F) env ctx holes css nss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | cs :: css, ns :: nss => by
    unfold checkAbsCtorTysAll
    simp only [FueledM.atF_bind, checkAbsCtorTys_datF, checkAbsCtorTysAll_datF env ctx holes F css nss]

theorem nestAnnotAll_datF (env : Env) (d F : Nat) :
    ∀ (xs : List Expr),
      (ConLeche.nestAnnotAll (fueledOpsM mode) env d xs).val F
        = ConLeche.nestAnnotAll (fueledOps mode F) env d xs
  | [] => rfl
  | x :: xs => by
    unfold ConLeche.nestAnnotAll
    simp only [FueledM.atF_bind, FueledM.atF_pure, fueledOpsM_annotate_atF,
      nestAnnotAll_datF env d F xs]

theorem nestSeedKeys_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (rs : List (Nat × Expr)),
      (ConLeche.nestSeedKeys (fueledOpsM mode) env ctx holes rs).val F
        = ConLeche.nestSeedKeys (fueledOps mode F) env ctx holes rs
  | [] => rfl
  | (nB, ty) :: rs => by
    unfold ConLeche.nestSeedKeys
    simp only [FueledM.atF_bind, nestSeedKeys_datF env ctx holes F rs]
    congr 1
    funext rest
    split
    · rfl
    · simp only [FueledM.atF_bind, FueledM.atF_pure, nestAnnotAll_datF]

theorem nestSeeds_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (ks : List (ConLeche.NestKey × Nat)) (st : ConLeche.NestState),
      (ConLeche.nestSeeds (fueledOpsM mode) env ctx ks st).val F
        = ConLeche.nestSeeds (fueledOps mode F) env ctx ks st
  | [], _ => rfl
  | (key, nPc) :: ks, st => by
    unfold ConLeche.nestSeeds
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      ConLeche.nestInstType_datF,
      nestContKey_datF (rec := ConLeche.nestPos (fueledOpsM mode) env ctx _)
        (rec' := ConLeche.nestPos (fueledOps mode F) env ctx _) (nestPos_datF env ctx F _),
      nestSeeds_datF env ctx F ks]

theorem checkBlockPositivity_datF (env₁ : Env) (find? : Name → Option ConstantInfo)
    (consts : List ConstantInfo) (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (checkBlockPositivity (fueledOpsM mode) env₁ find? consts p cvTas ctorsAs).val F
      = checkBlockPositivity (fueledOps mode F) env₁ find? consts p cvTas ctorsAs := by
  unfold checkBlockPositivity
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, nestBlockCtors_datF, checkAbsCtorTysAll_datF, nestSeedKeys_datF,
    nestSeeds_datF]

theorem checkBlockPass_datF (env : Env) (p : BlockParts) (isRec : Bool) (F : Nat) :
    (checkBlockPass (fueledOpsM mode) env p isRec).val F =
      checkBlockPass (fueledOps mode F) env p isRec := by
  unfold checkBlockPass
  simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockInds_datF, checkBlockCtors_datF,
    checkBlockPositivity_datF, unwrapOr_atF]

theorem checkBlockTail_datF (block : List ConstantInfo) (q : BlockPass Env)
    (F : Nat) :
    (checkBlockTail (fueledOpsM mode) block q).val F =
      checkBlockTail (fueledOps mode F) block q := by
  unfold checkBlockTail
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    checkBlockIdxSorts_datF, checkBlockRec_datF, checkBlockTables_datF]

/-- **The uniform install at fuel `F`, at k members**: the same program
at the two monads, stage by stage. -/
theorem checkBlock_datF (env : Env) (block : List ConstantInfo) (p : BlockParts)
    (F : Nat) :
    (checkBlock (fueledOpsM mode) env block p).val F =
      checkBlock (fueledOps mode F) env block p := by
  unfold checkBlock
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    checkBlockPass_datF, checkBlockTail_datF]

theorem checkShapeless_datF (env : Env) (block : List ConstantInfo) (F : Nat) :
    (checkShapeless (fueledOpsM mode) env block).val F =
      checkShapeless (fueledOps mode F) env block := by
  unfold checkShapeless
  rw [FueledM.atF_bind, foldlM_atF]
  congr 1
  · congr 1
    funext _ ci
    cases ci with
    | indInfo cv _ =>
      simp only [discard, Functor.discard, FueledM.atF_mapConst, checkConstantVal_datF]
    | _ => rfl

theorem checkDefnVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (hint : ReducibilityHint) (F : Nat) :
    (checkDefnVal (fueledOpsM mode) env cv value hint).val F =
      checkDefnVal (fueledOps mode F) env cv value hint := by
  unfold checkDefnVal
  datF_tac

theorem checkThmVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkThmVal (fueledOpsM mode) env cv value).val F =
      checkThmVal (fueledOps mode F) env cv value := by
  unfold checkThmVal
  datF_tac

theorem checkOpaqueVal_datF (env : Env) (cv : ConstantVal) (value : Expr)
    (F : Nat) :
    (checkOpaqueVal (fueledOpsM mode) env cv value).val F =
      checkOpaqueVal (fueledOps mode F) env cv value := by
  unfold checkOpaqueVal
  datF_tac

theorem certifyNatEqs_datF (env : Env) (F : Nat) :
    ∀ eqs : List (Expr × Expr),
      (certifyNatEqs (fueledOpsM mode) env eqs).val F =
        certifyNatEqs (fueledOps mode F) env eqs
  | [] => rfl
  | eq :: rest => by
    show ((do
        if ← CheckerOps.isDefEq (fueledOpsM mode) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOpsM mode) env rest
        else pure false : FueledM _)).val F = _
    rw [FueledM.atF_bind]
    show _ = (do
        if ← CheckerOps.isDefEq (fueledOps mode F) env 2 eq.1 eq.2 then
          certifyNatEqs (fueledOps mode F) env rest
        else pure false : CheckM _)
    congr 1
    funext b
    cases b with
    | true => exact certifyNatEqs_datF env F rest
    | false => rfl

theorem checkDivModCerts_datF (env : Env) (c : Name) (annVal : Expr)
    (F : Nat) :
    ∀ (stmts : List (List Expr × Expr)) (proofs : List Expr),
      (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs).val F =
        checkDivModCerts (fueledOps mode F) env c annVal stmts proofs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (hyps, eqE) :: srest, proof :: prest => by
    simp only [checkDivModCerts]
    split
    · rw [FueledM.atF_bind]
      congr 1
      funext appliedA
      rw [FueledM.atF_bind]
      congr 1
      funext tp
      rw [FueledM.atF_bind]
      congr 1
      funext b
      cases b with
      | true => exact checkDivModCerts_datF env c annVal F srest prest
      | false => rfl
    · rfl

theorem checkDivModPinAt_datF (env : Env) (c : Name) (value' : Expr)
    (ps : NatOpPinSet) (F : Nat) :
    (checkDivModPinAt (fueledOpsM mode) env c value' ps).val F =
      checkDivModPinAt (fueledOps mode F) env c value' ps := by
  unfold checkDivModPinAt
  repeat (first
    | (rw [checkDivModCerts_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkDivModPinLoop_datF (env : Env) (c : Name) (value' : Expr)
    (F : Nat) :
    ∀ (pss : List NatOpPinSet) (tried : List String),
      (checkDivModPinLoop (fueledOpsM mode) env c value' pss tried).val F =
        checkDivModPinLoop (fueledOps mode F) env c value' pss tried
  | [], _ => rfl
  | ps :: rest, tried => by
    unfold checkDivModPinLoop
    split
    · rw [fueledOpsM_orElse_atF, fueledOps_orElse', checkDivModPinAt_datF]
      cases checkDivModPinAt (fueledOps mode F) env c value' ps with
      | ok b =>
        cases b with
        | true => rfl
        | false => exact checkDivModPinLoop_datF env c value' F rest _
      | error e => exact checkDivModPinLoop_datF env c value' F rest _
    · exact checkDivModPinLoop_datF env c value' F rest _

theorem checkDivModPin_datF (env env2 : Env) (c : Name) (F : Nat) :
    (checkDivModPin (fueledOpsM mode) pins env env2 c).val F =
      checkDivModPin (fueledOps mode F) pins env env2 c := by
  unfold checkDivModPin
  repeat (first
    | (rw [checkDivModPinLoop_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

theorem checkReducePin_datF (env env2 : Env) (c : Name) (value : Expr)
    (F : Nat) :
    (checkReducePin (fueledOpsM mode) env env2 c value).val F =
      checkReducePin (fueledOps mode F) env env2 c value := by
  unfold checkReducePin
  repeat (first
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
    | rfl
    | (simp only [FueledM.atF_pure, FueledM.atF_throw]))

/-- The pinned-block install at a fuel datum.  Three of `checkDecl`'s
arms share this body since task #293. -/
theorem checkBasisDecl_datF (env : Env) (kind : BasisKind) (F : Nat) :
    (checkBasisDecl (m := FueledM) env kind).val F =
      checkBasisDecl (m := CheckM) env kind := by
  unfold checkBasisDecl
  dsimp only
  by_cases hq : kind = .quotK
  · rw [if_pos hq, if_pos hq]
    by_cases he : env.find? eqName = some eqA
    · rw [if_pos he, if_pos he, foldlM_atF]
      simp only [installBasisDecl_datF]
    · rw [if_neg he, if_neg he, FueledM.atF_bind]
      simp only [FueledM.atF_throw]
      congr 1
      funext x
      rw [foldlM_atF]
      simp only [installBasisDecl_datF]
  · rw [if_neg hq, if_neg hq, foldlM_atF]
    simp only [installBasisDecl_datF]

theorem checkDecl_datF (env : Env) (d : Declaration) (F : Nat) :
    (checkDecl mode (fueledOpsM mode) pins env d).val F =
      checkDecl mode (fueledOps mode F) pins env d := by
  unfold checkDecl
  cases d with
  | defnDecl cv value hint =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkDefnVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [certifyNatEqs_datF])
      | (rw [checkDivModPin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | thmDecl cv value =>
    show ((checkConstantVal (fueledOpsM mode) env cv >>= fun cv =>
      checkThmVal (fueledOpsM mode) env cv value : FueledM _)).val F = _
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [checkThmVal_datF]
  | opaqueDecl cv value =>
    dsimp only
    rw [FueledM.atF_bind, checkConstantVal_datF]
    congr 1
    funext cv'
    rw [FueledM.atF_bind, checkOpaqueVal_datF]
    congr 1
    funext env2
    repeat (first
      | (rw [checkReducePin_datF])
      | split
      | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _)
      | rfl
      | (simp only [FueledM.atF_pure, FueledM.atF_throw]))
  | axiomDecl cv =>
    dsimp only
    -- the `Quot.sound` comparison (task #293) is a pure guard
    by_cases hqs : cv.name = quotSoundName
    · rw [if_pos hqs, if_pos hqs]
      simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
    · rw [if_neg hqs, if_neg hqs]
      rw [FueledM.atF_bind, checkConstantVal_datF]
      congr 1
      funext cvA
      simp only [FueledM.atF_ite, FueledM.atF_pure, FueledM.atF_throw]
  | basisDecl kind => exact checkBasisDecl_datF env kind F
  | quotDecl k cv =>
    dsimp only
    -- the pin comparison (task #293) is a pure guard
    by_cases hp : quotPinHit k cv = true
    · rw [if_pos hp, if_pos hp]
      cases k
      · exact checkBasisDecl_datF env .quotK F
      all_goals simp only [FueledM.atF_pure]
    · rw [if_neg hp, if_neg hp]
      simp only [FueledM.atF_throw]
  | indDecl block nP =>
    dsimp only
    -- the pinned-block recognition (task #293) and the declared
    -- parameter count (task #228) are pure guards: the two sides take
    -- the same branch, and the guards' `throw` is fuel-free
    split
    · exact checkBasisDecl_datF env _ F
    · split
      · split
        · exact checkBlock_datF env block _ F
        · exact checkShapeless_datF env block F
      · rfl

theorem checkDeclsPure_datF (ds : List Declaration) (F : Nat) :
    (checkDeclsPure mode (fueledOpsM mode) pins ds).val F =
      checkDeclsPure mode (fueledOps mode F) pins ds := by
  unfold checkDeclsPure
  rw [foldlM_atF]
  simp only [checkDecl_datF]

end ConLeche
