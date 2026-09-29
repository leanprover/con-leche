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
  nestGroupCtors nestFields nestCtors nestFrame nestCont nestPos nestRoot nestRootLines
  nestRootLinesAll nestedBlockPositivity nestContainer)

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
    ∀ (cs : List Name),
      (nestGroupCtors (m := FueledM) ctx nPc cs).val F = nestGroupCtors (m := CheckM) ctx nPc cs
  | [] => rfl
  | c :: cs => by
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

theorem nestCtors_datF {F : Nat}
    {recC : Expr → List NestHole → Nat → Nat → Expr → NestState →
      FueledM (NestFieldKind × Expr × NestState)}
    {recC' : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckM (NestFieldKind × Expr × NestState)}
    (hrec : ∀ x a b c d e, (recC x a b c d e).val F = recC' x a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (sub : Name → List Level → Option Expr) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState),
      (nestCtors ctx (fueledOpsM mode) env recC prog hi us ds nPc sub cs st).val F
        = nestCtors ctx (fueledOps mode F) env recC' prog hi us ds nPc sub cs st
  | [], _ => rfl
  | (cv, nF) :: cs, st => by
    unfold nestCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, fueledOpsM_inferType_atF, fueledOpsM_ensureSort_atF,
      nestFields_datF (hrec _), nestCtors_datF hrec ctx env prog hi us ds nPc sub cs]

theorem nestFrame_datF {F : Nat} (hrec : ∀ a b c d e, (rec a b c d e).val F = rec' a b c d e)
    (ctx : NestCtx) (env : Env) (prog : List NestHole) (hi : Nat) (us : List Level)
    (ds : List Expr) (nPc : Nat) (grp : List (Name × Expr)) (st : NestState) :
    (nestFrame ctx (fueledOpsM mode) env rec prog hi us ds nPc grp st).val F
      = nestFrame ctx (fueledOps mode F) env rec' prog hi us ds nPc grp st := by
  unfold nestFrame
  simp only [FueledM.atF_bind, FueledM.atF_pure, fueledOpsM_inferType_atF, nestGroupCtors_datF]
  congr 1
  funext _
  congr 1
  funext q
  simp only [FueledM.atF_bind, FueledM.atF_pure, nestCtors_datF (fun _ => hrec)]

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

theorem nestNoMemberConst_datF (ctx : ConLeche.NestCtx) (e : Expr) (F : Nat) :
    (ConLeche.nestNoMemberConst (m := FueledM) ctx e).val F
      = ConLeche.nestNoMemberConst (m := CheckM) ctx e := by
  unfold ConLeche.nestNoMemberConst
  simp only [FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_pure]

theorem nestRoot_datF (env : Env) (ctx : ConLeche.NestCtx) (holes : List Expr)
    (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : ConLeche.NestState),
      (nestRoot (fueledOpsM mode) env ctx holes css st).val F
        = nestRoot (fueledOps mode F) env ctx holes css st
  | [], _ => rfl
  | cs :: css, st => by
    unfold nestRoot
    simp only [FueledM.atF_bind, FueledM.atF_pure,
      nestCtors_datF (fun x => nestPos_datF env ctx F (ConLeche.whnfWalkFuel x)),
      nestRoot_datF env ctx holes F css]

theorem nestRootLines_datF (ctx : ConLeche.NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)),
      (nestRootLines (m := FueledM) ctx holes cs os).val F
        = nestRootLines (m := CheckM) ctx holes cs os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, o :: os => by
    unfold nestRootLines
    simp only [FueledM.atF_bind, FueledM.atF_ite, FueledM.atF_throw, FueledM.atF_pure,
      nestNoMemberConst_datF, nestRootLines_datF ctx holes F cs os]

theorem nestRootLinesAll_datF (ctx : ConLeche.NestCtx) (holes : List Expr) (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (oss : List (List (List NestFieldKind × Expr))),
      (nestRootLinesAll (m := FueledM) ctx holes css oss).val F
        = nestRootLinesAll (m := CheckM) ctx holes css oss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | cs :: css, os :: oss => by
    unfold nestRootLinesAll
    simp only [FueledM.atF_bind, nestRootLines_datF, nestRootLinesAll_datF ctx holes F css oss]

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

theorem FueledM.atF_mapConst {α : Type} (x : FueledM α) (F : Nat) :
    (Functor.mapConst PUnit.unit x : FueledM PUnit).val F
      = (Functor.mapConst PUnit.unit (x.val F) : CheckM PUnit) := by
  show (x >>= fun _ => pure PUnit.unit : FueledM PUnit).val F = _
  rw [FueledM.atF_bind]
  cases x.val F <;> rfl

/-! ### The recursor stage's class kit at fuel `F` -/

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

theorem targetMajorOf_datF (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) (F : Nat) :
    (targetMajorOf (m := FueledM) fe p ctorsAs pfvs fvs mty).val F =
      targetMajorOf (m := CheckM) fe p ctorsAs pfvs fvs mty := by
  unfold targetMajorOf
  repeat' (first
    | rfl
    | (simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        unwrapOr_atF, liftFueled_atF, targetOutsideInst_datF])
    | split
    | ((rw [FueledM.atF_bind]; congr 1 <;> try rfl) <;> try funext _))

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

theorem targetRecPins_datF (p : BlockShape) (block : List ConstantInfo) (F : Nat) :
    (targetRecPins (m := FueledM) p block).val F = targetRecPins (m := CheckM) p block := by
  unfold targetRecPins
  datF_tac

theorem targetK53_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (Mc : TargetMajor)
    (tele : List (Expr × BinderMeta)) (majDom f : Expr) (F : Nat) :
    (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f).val F =
      targetK53 (fueledOps mode F) env p formerTys Mc tele majDom f := by
  unfold targetK53
  repeat' split
  all_goals first | rfl | exact targetClassMatch_datF _ _ _ _ _ _ _ _ _

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

theorem nestedBlockPositivity_datF (env : Env) (ctx : ConLeche.NestCtx)
    (ctorss : List (List (ConstantVal × Nat))) (F : Nat) :
    (ConLeche.nestedBlockPositivity (fueledOpsM mode) env ctx ctorss).val F
      = ConLeche.nestedBlockPositivity (fueledOps mode F) env ctx ctorss := by
  unfold ConLeche.nestedBlockPositivity
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, nestRoot_datF,
    nestRootLinesAll_datF]

theorem checkAbsCtorSorts_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)),
      (checkAbsCtorSorts (fueledOpsM mode) env ctx cs os).val F
        = checkAbsCtorSorts (fueledOps mode F) env ctx cs os
  | [], _ => rfl
  | _ :: _, [] => rfl
  | c :: cs, o :: os => by
    unfold checkAbsCtorSorts
    simp only [FueledM.atF_bind, unwrapOr_atF, FueledM.atF_ite,
      FueledM.atF_throw, FueledM.atF_pure, checkStructFieldSortsI_datF,
      checkAbsCtorSorts_datF env ctx F cs os]

theorem checkAbsCtorSortsAll_datF (env : Env) (ctx : ConLeche.NestCtx) (F : Nat) :
    ∀ (css : List (List (ConstantVal × Nat))) (oss : List (List (List NestFieldKind × Expr))),
      (checkAbsCtorSortsAll (fueledOpsM mode) env ctx css oss).val F
        = checkAbsCtorSortsAll (fueledOps mode F) env ctx css oss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | cs :: css, os :: oss => by
    unfold checkAbsCtorSortsAll
    simp only [FueledM.atF_bind, checkAbsCtorSorts_datF, checkAbsCtorSortsAll_datF env ctx F css oss]

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

theorem blockNestCtx_datF (p : BlockShape) (cvTas : List ConstantVal)
    (find? : Name → Option ConstantInfo) (F : Nat) :
    (blockNestCtx (m := FueledM) p cvTas find?).val F =
      blockNestCtx (m := CheckM) p cvTas find? := by
  unfold blockNestCtx
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF]

/-! ### The generated recursor stage at fuel `F` -/

theorem classMinorSlot_datF (rd : ClassRead) (c : Nat) (C : Name) (F : Nat) :
    (classMinorSlot (m := FueledM) rd c C).val F = classMinorSlot (m := CheckM) rd c C := by
  unfold classMinorSlot
  dsimp only
  split <;> rfl

theorem classFieldsOf_datF (p : BlockShape) (ctor : Name) (ihs : List (Nat × Nat)) (F : Nat) :
    ∀ (i : Nat) (fs : List Expr),
      (classFieldsOf (m := FueledM) p ctor ihs i fs).val F =
        classFieldsOf (m := CheckM) p ctor ihs i fs
  | _, [] => rfl
  | i, f :: fs => by
    unfold classFieldsOf
    dsimp only
    split <;>
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw,
      classFieldsOf_datF p ctor ihs F (i + 1) fs] <;> rfl

theorem classNodesAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List (Expr × BinderMeta)) (leaf : Expr) (fvs : List Expr)
    (i : Nat) (ctor : Name) (F : Nat) :
    ∀ (es : List NestCtorNf),
      (classNodesAgree (fueledOpsM mode) env p formerTys Mc tele leaf fvs i ctor es).val F =
        classNodesAgree (fueledOps mode F) env p formerTys Mc tele leaf fvs i ctor es
  | [] => rfl
  | e :: es => by
    unfold classNodesAgree
    split
    · simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
        targetK53_datF, classNodesAgree_datF env p formerTys Mc tele leaf fvs i ctor F es]
    · rfl

theorem classFieldsAgree_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf) (F : Nat) :
    ∀ (i : Nat) (ks : List ClassField),
      (classFieldsAgree (fueledOpsM mode) env p formerTys Ms fvs ctor E i ks).val F =
        classFieldsAgree (fueledOps mode F) env p formerTys Ms fvs ctor E i ks
  | _, [] => rfl
  | i, .ordinary :: ks => by
    unfold classFieldsAgree
    exact classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks
  | i, .recursive t tele :: ks => by
    unfold classFieldsAgree
    simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
      unwrapOr_atF, classNodesAgree_datF,
      classFieldsAgree_datF env p formerTys Ms fvs ctor E F (i + 1) ks]

theorem classCtorOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (cA : ConstantVal × Nat) (F : Nat) :
    (classCtorOf (fueledOpsM mode) env p formerTys rd Ms c cA).val F =
      classCtorOf (fueledOps mode F) env p formerTys rd Ms c cA := by
  unfold classCtorOf
  simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classMinorSlot_datF,
    classFieldsOf_datF, classFieldsAgree_datF]

theorem classCtorsOf_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (c : Nat) (F : Nat) :
    ∀ (cs : List (ConstantVal × Nat)),
      (classCtorsOf (fueledOpsM mode) env p formerTys rd Ms c cs).val F =
        classCtorsOf (fueledOps mode F) env p formerTys rd Ms c cs
  | [] => rfl
  | cA :: cs => by
    unfold classCtorsOf
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorOf_datF,
      classCtorsOf_datF env p formerTys rd Ms c F cs]

theorem classesCtors_datF (env : Env) (p : BlockShape) (formerTys : List Expr) (rd : ClassRead)
    (Ms : List TargetMajor) (F : Nat) :
    ∀ (c : Nat) (l : List TargetMajor),
      (classesCtors (fueledOpsM mode) env p formerTys rd Ms c l).val F =
        classesCtors (fueledOps mode F) env p formerTys rd Ms c l
  | _, [] => rfl
  | c, M :: rest => by
    unfold classesCtors
    simp only [FueledM.atF_bind, FueledM.atF_pure, classCtorsOf_datF,
      classesCtors_datF env p formerTys rd Ms F (c + 1) rest]

theorem classMajors_datF (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs : List Expr) (F : Nat) :
    ∀ (keys : List ClassKey),
      (classMajors (fueledOpsM mode) fe p ctorsAs pfvs keys).val F =
        classMajors (fueledOps mode F) fe p ctorsAs pfvs keys
  | [] => rfl
  | key :: keys => by
    unfold classMajors
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorOf_datF, targetMajorPins_datF,
      classMajors_datF fe p ctorsAs pfvs F keys]

theorem classesNfs_datF (env : Env) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) (F : Nat) :
    ∀ (Ms : List TargetMajor),
      (classesNfs (fueledOpsM mode) env p formerTys tbl Ms).val F =
        classesNfs (fueledOps mode F) env p formerTys tbl Ms
  | [] => rfl
  | M :: Ms => by
    unfold classesNfs
    simp only [FueledM.atF_bind, FueledM.atF_pure, targetMajorNfs_datF,
      classesNfs_datF env p formerTys tbl F Ms]

theorem classFormerTy_datF (fe : FEnv) (cvTas : List ConstantVal) (M : TargetMajor) (F : Nat) :
    (classFormerTy (m := FueledM) fe cvTas M).val F = classFormerTy (m := CheckM) fe cvTas M := by
  unfold classFormerTy
  repeat' split
  all_goals rfl

theorem mapMLoop_atF {α β : Type} (f : α → FueledM β) (F : Nat) :
    ∀ (l : List α) (bs : List β),
      (List.mapM.loop f l bs).val F = List.mapM.loop (fun a => (f a).val F) l bs
  | [], _ => rfl
  | a :: l, bs => by
    simp only [List.mapM.loop, FueledM.atF_bind, mapMLoop_atF f F l]

theorem mapM_atF {α β : Type} (f : α → FueledM β) (F : Nat) (l : List α) :
    (l.mapM f).val F = l.mapM (fun a => (f a).val F) :=
  mapMLoop_atF f F l []

theorem classFormerTys_datF (fe : FEnv) (cvTas : List ConstantVal) (F : Nat)
    (Ms : List TargetMajor) :
    (Ms.mapM (classFormerTy (m := FueledM) fe cvTas)).val F =
      Ms.mapM (classFormerTy (m := CheckM) fe cvTas) := by
  rw [mapM_atF]
  simp only [classFormerTy_datF]

theorem fueledOpsM_annotate_atF (env : Env) (d : Nat) (a : Expr) (F : Nat) :
    ((fueledOpsM mode).annotate env d a).val F = (fueledOps mode F).annotate env d a := by rfl

theorem classKeyOf_datF (env : Env) (nP : Nat) (params : List Expr) (k : ClassKey)
    (F : Nat) :
    (classKeyOf (fueledOpsM mode) env nP params k).val F =
      classKeyOf (fueledOps mode F) env nP params k := by
  unfold classKeyOf
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite, mapM_atF,
    fueledOpsM_annotate_atF]

theorem checkBlockClasses_datF (fe₁ : FEnv) (env₁ : Env) (p : BlockShape) (params : List Expr)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (checkBlockClasses (fueledOpsM mode) fe₁ env₁ p params ctorsAs).val F =
      checkBlockClasses (fueledOps mode F) fe₁ env₁ p params ctorsAs := by
  unfold checkBlockClasses
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, mapM_atF, classKeyOf_datF, classMajors_datF]

theorem classConstOk_datF (fe : FEnv) (cv : ConstantVal) (F : Nat) :
    (classConstOk (fueledOpsM mode) fe cv).val F = classConstOk (fueledOps mode F) fe cv := by
  unfold classConstOk
  datF_tac

theorem classRecTyOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) (F : Nat) :
    (classRecTyOk (fueledOpsM mode) fe g k rc cvRi c).val F =
      classRecTyOk (fueledOps mode F) fe g k rc cvRi c := by
  unfold classRecTyOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, classConstOk_datF, fueledOpsM_isDefEq_atF]

theorem classRecTysOk_datF (fe : FEnv) (g : ClassGen) (k : Nat) (F : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cls : List Nat),
      (classRecTysOk (fueledOpsM mode) fe g k recs cvs cls).val F =
        classRecTysOk (fueledOps mode F) fe g k recs cvs cls
  | rc :: rcs, cvRi :: cvs, c :: cs => by
    unfold classRecTysOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRecTyOk_datF,
      classRecTysOk_datF fe g k F rcs cvs cs]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl

theorem classRuleOk_datF (feT feR : FEnv) (cvR : ConstantVal) (pw : PropWhen) (n : Nat)
    (gen : Expr) (F : Nat) :
    (classRuleOk (fueledOpsM mode) .plain feT feR cvR pw n gen).val F =
      classRuleOk (fueledOps mode F) .plain feT feR cvR pw n gen := by
  unfold classRuleOk
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    unwrapOr_atF, fueledOpsM_inferType_atF]

theorem classRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (pw : PropWhen) (c : Nat) (F : Nat) :
    ∀ (xs : List ClassCtor),
      (classRulesOk (fueledOpsM mode) .plain feT feR g recOf cvR pw c xs).val F =
        classRulesOk (fueledOps mode F) .plain feT feR g recOf cvR pw c xs
  | [] => rfl
  | x :: xs => by
    unfold classRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, unwrapOr_atF, classRuleOk_datF,
      classRulesOk_datF feT feR g recOf cvR pw c F xs]

theorem classRecsRulesOk_datF (feT feR : FEnv) (g : ClassGen) (recOf : Nat → Option Name)
    (pw : PropWhen) (F : Nat) :
    ∀ (cvs : List ConstantVal) (cs : List Nat),
      (classRecsRulesOk (fueledOpsM mode) .plain feT feR g recOf pw cvs cs).val F =
        classRecsRulesOk (fueledOps mode F) .plain feT feR g recOf pw cvs cs
  | cvG :: cvs, c :: cs => by
    unfold classRecsRulesOk
    simp only [FueledM.atF_bind, FueledM.atF_pure, classRulesOk_datF,
      classRecsRulesOk_datF feT feR g recOf pw F cvs cs]
  | [], _ => rfl
  | _ :: _, [] => rfl

theorem classStreamRecs_datF (fe : FEnv) (F : Nat) :
    ∀ (recs : List RecShape),
      (classStreamRecs (fueledOpsM mode) fe recs).val F = classStreamRecs (fueledOps mode F) fe recs
  | [] => rfl
  | rc :: rcs => by
    unfold classStreamRecs
    simp only [FueledM.atF_bind, FueledM.atF_pure, checkConstantValF_datF,
      classStreamRecs_datF fe F rcs]

/-- **The generated recursor stage at fuel `F`**: the pure install's run
(`ShadowOps.ofOps` at the fueled family) is the model's fueled run. -/
theorem genRecCheck_datF (fe : FEnv) (p : BlockShape) (nestedBit : Bool) (params : List Expr)
    (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor) (cvTas : List ConstantVal)
    (block : List ConstantInfo) (F : Nat) :
    (genRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe p nestedBit params tbl rd Ms cvTas
        block).val F =
      genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms cvTas block := by
  unfold genRecCheck
  simp only [ShadowOps.ofOps, ShadowOps.fueled, FueledM.atF_bind, FueledM.atF_pure,
    FueledM.atF_throw, FueledM.atF_ite, unwrapOr_atF, targetRecPins_datF, classStreamRecs_datF,
    classesNfs_datF, classesCtors_datF, classFormerTys_datF, classRecTysOk_datF,
    classRecsRulesOk_datF]

theorem checkBlockRec_datF (env : Env) (p : BlockParts) (nested : Bool) (params : List Expr)
    (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor) (block : List ConstantInfo)
    (cvTas : List ConstantVal) (F : Nat) :
    (checkBlockRec (fueledOpsM mode) env p nested params tbl rd Ms block cvTas).val F =
      checkBlockRec (fueledOps mode F) env p nested params tbl rd Ms block cvTas := by
  unfold checkBlockRec
  exact genRecCheck_datF _ _ _ _ _ _ _ _ _ F

theorem checkBlockPositivity_datF (env₁ : Env) (find? : Name → Option ConstantInfo)
    (p : BlockParts) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (F : Nat) :
    (checkBlockPositivity (fueledOpsM mode) env₁ find? p cvTas ctorsAs).val F
      = checkBlockPositivity (fueledOps mode F) env₁ find? p cvTas ctorsAs := by
  unfold checkBlockPositivity
  simp only [FueledM.atF_bind, FueledM.atF_pure, FueledM.atF_throw, FueledM.atF_ite,
    blockNestCtx_datF, nestRoot_datF, nestRootLinesAll_datF, checkAbsCtorSortsAll_datF]

theorem checkBlockPass_datF (env : Env) (p : BlockParts) (isRec : Bool) (F : Nat) :
    (checkBlockPass (fueledOpsM mode) env p isRec).val F =
      checkBlockPass (fueledOps mode F) env p isRec := by
  unfold checkBlockPass
  simp only [FueledM.atF_bind, FueledM.atF_pure, checkBlockInds_datF, checkBlockCtors_datF,
    blockNestCtx_datF, checkBlockClasses_datF, checkBlockPositivity_datF, nestSeeds_datF,
    unwrapOr_atF]

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
