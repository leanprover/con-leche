module

import ConLeche.Verify.Inductives.NestCallSyn
public import ConLeche.Cached.CheckerC
public import ConLeche.Verify.BridgeDecl
public import ConLeche.Verify.Cached.Grind
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.SimCS
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.NestContInv
public import ConLeche.Verify.Inductives.NestScope
public section

/-!
# The positivity function at the cached driver

`nestPos` (`Kernel/Inductives/Positivity.lean`) and the check's
positivity stage (`checkBlockPositivity`, `BlockInstall.lean`) are
written once, over `CheckerOps`; the cached driver runs them at the
shared operations (`sharedOpsC`), the model at the fueled ones.  This
file is the simulation: a successful cached run is reproduced by the
fueled one, with the same result.  Every walk is a `Std.WP` triple whose
post names the cached value as the fueled answer (`Runs`,
`Verify/Cached/Grind.lean`), proved by `vcgen` and `grind` — one
`sym … => vcgen […] <;> finish` per arm: the cached and the fueled side
are the same generic function, so its own equation lemmas unfold the
fueled side, and the callees' triples go into `vcgen`'s list.  The walk's
recursive call is the named predicate `RecSpec`; the scope side
conditions are named predicates (`ListAll` of an element predicate,
`TeleWS`, `InstWS`, `HolesOk`, `FvsWS`), each with its equations.

The only operations the function calls are `whnf` (every step), and at
the install stage `inferType`/`ensureSort` (U2); their simulations need
the input WELL SCOPED at its depth, which the walk keeps: a member
constructor's type is closed, its members abstracted to holes below the
walk's depth; opening a field instantiates at a fresh variable; a
container frame instantiates a closed stored constructor type at the
frame's holes and at parameters without local variables.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## Container lookups read closed constructor types -/

/-- A stored constructor's type is closed. -/
@[expose] def CtorClosed (c : ConstantVal × Nat) : Prop := c.1.type.hasFvar = false

@[conleche_grind =] theorem CtorClosed.eq (cv : ConstantVal) (n : Nat) :
    CtorClosed (cv, n) = (cv.type.hasFvar = false) := rfl

theorem nestContainer_closed {ctx : NestCtx} (hc : NestCtxOk ctx) {C : Name} {n : Nat}
    {L : List (ConstantVal × Nat)} (h : nestContainer ctx C = some (n, L)) :
    ListAll CtorClosed L := by
  intro x hx
  obtain ⟨n, nPc, hf⟩ := nestContainer_mem h x hx
  exact hc.1 _ _ hf

/-- A term scoped wherever the list `ds` is (an instantiated container
type: closed, instantiated at `ds`). -/
@[expose] def InstWS (ds : List Expr) (e : Expr) : Prop := ∀ d, AllWS d ds → WScoped d e

/-- A group entry's hole type is scoped wherever `ds` is. -/
@[expose] def GrpWS (ds : List Expr) (x : Name × Expr) : Prop := InstWS ds x.2

@[conleche_grind =] theorem GrpWS.eq (ds : List Expr) (n : Name) (t : Expr) :
    GrpWS ds (n, t) = InstWS ds t := rfl

theorem nestCtx_find_closed {ctx : NestCtx} (hc : NestCtxOk ctx) {n : Name} {cv : ConstantVal}
    {caps : IndCaps} (h : ctx.find? n = some (.indInfo cv caps)) : cv.type.hasFvar = false :=
  hc.1 _ _ h

theorem instWS_instPisWith {ds : List Expr} {ty : Expr} {ks : List Name} {us : List Level}
    {r : Expr} (hcl : ty.hasFvar = false)
    (h : instPisWith ds (ty.instantiateLevelParams ks us) = some r) : InstWS ds r :=
  fun _ hds => wscoped_instPisWith hds
    (WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl)) h

/-! ## The environment-reading steps (no operation) -/

section Pure

variable {env : Env}

/-- Official's telescope loop (task #195) at the shared operations:
every `whnf` is the shared one, on a well-scoped input at its depth
(the opened body is well-scoped one deeper). -/
theorem whnfTelescopeS_spec (henv : EnvWF env) :
    ∀ {i n : Nat} {e : Expr} {s₀ : CState}, CSOK .verified false env s₀ → WScoped i e →
      ⦃fun s => s = s₀⦄ whnfTelescope (sharedOpsC .verified (mkFEnv env)) env i n e
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (whnfTelescope (fueledOpsM .verified) env i n e) v; ⊤⦄ := by
  intro i n
  induction n generalizing i with
  | zero =>
    intro _ _ _ _
    sym only [conleche_grind, whnfTelescope.eq_1] =>
      vcgen [whnfTelescope, whnfS_spec henv] <;> finish
  | succ n ih =>
    intro _ _ _ _
    sym only [conleche_grind, whnfTelescope.eq_2] =>
      vcgen [whnfTelescope, whnfS_spec henv, ih] <;>
        finish

/-- The reduct a run reads has no free variable where the stored type has none. -/
theorem Runs.reducedFormer_hasFvar (henv : EnvWF env) {cv cvR : ConstantVal} {n : Nat}
    (hc : cv.type.hasFvar = false) (h : Runs (reducedFormer (fueledOpsM .verified) env cv n) cvR) :
    cvR.type.hasFvar = false := by
  obtain ⟨F, hF⟩ := h
  rw [reducedFormer_datF] at hF
  exact ConLeche.reducedFormer_hasFvar (fun _ _ _ hw he => whnf_WScoped henv F hw he) hF hc

/-- The reduced former at the cached operations simulates its fueled original. -/
theorem reducedFormerRunS_spec (henv : EnvWF env) {cv : ConstantVal} {n : Nat} {s₀ : CState}
    (hw : WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ reducedFormer (sharedOpsC .verified (mkFEnv env)) env cv n
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (reducedFormer (fueledOpsM .verified) env cv n) v; ⊤⦄ := by
  sym only [conleche_grind, reducedFormer] =>
    vcgen [reducedFormer, whnfTelescopeS_spec henv] <;> finish

/-- The reduced former of a closed type at the cached operations simulates its fueled
original, and is closed. -/
theorem reducedFormerS_spec (henv : EnvWF env) {cv : ConstantVal} {n : Nat} {s₀ : CState}
    (hw : WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ reducedFormer (sharedOpsC .verified (mkFEnv env)) env cv n
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (reducedFormer (fueledOpsM .verified) env cv n) v ∧ v.type.hasFvar = false; ⊤⦄ :=
  triple_iff_run.mpr fun v s' hr => by
    obtain ⟨h₁, h₂⟩ := triple_iff_run.mp (reducedFormerRunS_spec henv (n := n) (cv := cv) hw hs) v s' hr
    exact ⟨h₁, h₂, Runs.reducedFormer_hasFvar henv
      (not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow hw)) h₂⟩

/-- A family's telescope at the cached operations simulates its fueled original, and is closed
where its stored type is. -/
theorem familyTelescopeS_spec (henv : EnvWF env) {cv : ConstantVal} {caps : IndCaps} {s₀ : CState}
    (hcl : cv.type.hasFvar = false) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ familyTelescope (sharedOpsC .verified (mkFEnv env)) env cv caps
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (familyTelescope (fueledOpsM .verified) env cv caps) v ∧ v.hasFvar = false; ⊤⦄ := by
  have hw : WScoped 0 cv.type := WScoped.of_not_hasFvar hcl
  sym only [conleche_grind, familyTelescope, reducedFormer] =>
    vcgen [familyTelescope, reducedFormerS_spec henv hw] <;> finish

/-- The arguments against a telescope at the cached operations simulate their fueled original. -/
theorem checkSpineAtS_spec (henv : EnvWF env) {d : Nat} :
    ∀ (ds : List Expr) (T : Expr) {s₀ : CState}, CSOK .verified false env s₀ → AllWS d ds →
      WScoped d T →
      ⦃fun s => s = s₀⦄ checkSpineAt (sharedOpsC .verified (mkFEnv env)) env d T ds
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkSpineAt (fueledOpsM .verified) env d T ds) v; ⊤⦄ := by
  intro ds
  induction ds with
  | nil =>
    intro T _ hs _ _
    sym only [conleche_grind, checkSpineAt.eq_1] =>
      vcgen [checkSpineAt.eq_def] <;> finish
  | cons a as ih =>
    intro T s₀ hs hds hT
    sym only [conleche_grind, checkSpineAt.eq_2] =>
      vcgen [checkSpineAt.eq_def, inferS_spec henv, defeqS_spec henv, ih] <;> finish

/-- A family at a key, at the cached operations. -/
theorem familyKeyCheckS_spec (henv : EnvWF env) {find? : Name → Option ConstantInfo}
    (hfind : ∀ n ci, find? n = some ci → ci.toConstantVal.type.hasFvar = false) {d : Nat} {c : Name}
    {us : List Level} {ds : List Expr} {s₀ : CState} (hs : CSOK .verified false env s₀)
    (hds : AllWS d ds) :
    ⦃fun s => s = s₀⦄ familyKeyCheck (sharedOpsC .verified (mkFEnv env)) env find? d c us ds
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (familyKeyCheck (fueledOpsM .verified) env find? d c us ds) v; ⊤⦄ := by
  have hty : ∀ cv caps, find? c = some (.indInfo cv caps) → cv.type.hasFvar = false :=
    fun cv caps h => hfind c _ h
  sym only [conleche_grind, familyKeyCheck.eq_1] =>
    vcgen [familyKeyCheck, familyTelescopeS_spec henv, checkSpineAtS_spec henv] <;> finish

theorem nestInstTypeS_spec (henv : EnvWF env) {ctx : NestCtx} (hc : NestCtxOk ctx) {s₀ : CState}
    (hs : CSOK .verified false env s₀) (hi : Nat) (key : NestKey) :
    ⦃fun s => s = s₀⦄ nestInstType ctx (sharedOpsC .verified (mkFEnv env)) env hi key
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (nestInstType ctx (fueledOpsM .verified) env hi key) v ∧
      InstWS key.ds v.2; ⊤⦄ := by
  -- `gen`: E-matching evaluates the pure side bind by bind (`Runs.pure_bind_eq`), one
  -- generation per bind, through six binds and two guards
  sym only [conleche_grind, nestInstType.eq_1, unwrapOr.eq_1, liftFueled.eq_1,
      → nestCtx_find_closed hc, → instWS_instPisWith] =>
    vcgen [nestInstType, unwrapOr, liftFueled, familyTelescopeS_spec henv] <;> finish (gen := 12)

theorem nestGrowGroupS_spec (henv : EnvWF env) {ctx : NestCtx} (hc : NestCtxOk ctx) (hi : Nat)
    (us : List Level) (ds : List Expr) :
    ∀ (cs : List Name) (grp : List (Name × Expr)) {s₀ : CState}, CSOK .verified false env s₀ →
      ListAll (GrpWS ds) grp →
      ⦃fun s => s = s₀⦄ nestGrowGroup ctx (sharedOpsC .verified (mkFEnv env)) env hi us ds cs grp
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (nestGrowGroup ctx (fueledOpsM .verified) env hi us ds cs grp) v ∧
        ListAll (GrpWS ds) v; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro grp _ hs hg
    sym only [conleche_grind, nestGrowGroup.eq_1] =>
      vcgen [nestGrowGroup] <;> finish
  | cons c cs ih =>
    intro grp _ hs hg
    sym only [conleche_grind, nestGrowGroup.eq_2] =>
      vcgen [nestGrowGroup, nestInstTypeS_spec henv hc, ih] <;> finish

theorem nestGroupCtorsS_spec {ctx : NestCtx} (hc : NestCtxOk ctx) (nPc : Nat) :
    ∀ (cs : List Name) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄ nestGroupCtors (m := CheckCM) ctx nPc cs
      ⦃fun v s' => CSOK mode false env s' ∧ Runs (nestGroupCtors (m := FueledM) ctx nPc cs) v ∧
        ListAll CtorClosed v; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro _ hs
    sym only [conleche_grind, nestGroupCtors.eq_1] =>
      vcgen [nestGroupCtors] <;> finish
  | cons c cs ih =>
    intro _ hs
    sym only [conleche_grind, nestGroupCtors.eq_2, unwrapOr.eq_1, nestContainer_closed hc] =>
      vcgen [nestGroupCtors, unwrapOr, ih] <;> finish

end Pure

/-! ## The walk -/

section Walk

variable {env : Env}

/-- **The triple a walk's recursive call provides**: at a well-scoped
input. -/
@[expose] def RecSpec (mode : CheckMode) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (rec' : List NestHole → Nat → Nat → Expr → NestState →
      FueledM (NestFieldKind × Expr × NestState)) : Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) {s₀ : CState},
    CSOK mode false env s₀ → WScoped dep e →
    ⦃fun s => s = s₀⦄ rec prog dep kb e st
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (rec' prog dep kb e st) v ∧ WScoped dep v.2.1; ⊤⦄

variable {rec : List NestHole → Nat → Nat → Expr → NestState →
    CheckCM (NestFieldKind × Expr × NestState)}
  {rec' : List NestHole → Nat → Nat → Expr → NestState →
    FueledM (NestFieldKind × Expr × NestState)}

theorem RecSpec.triple (h : RecSpec mode env rec rec') (prog : List NestHole) (dep kb : Nat)
    (e : Expr) (st : NestState) {s₀ : CState} (hs : CSOK mode false env s₀) (hw : WScoped dep e) :
    ⦃fun s => s = s₀⦄ rec prog dep kb e st
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (rec' prog dep kb e st) v ∧ WScoped dep v.2.1; ⊤⦄ :=
  h prog dep kb e st hs hw

/-- A field telescope opened from depth `i`: its `k`-th domain scoped
at `i + k`. -/
@[expose] def TeleWS (i : Nat) (nds : List Expr) : Prop :=
  ∀ (k : Nat) (nd : Expr), nds[k]? = some nd → WScoped (i + k) nd

@[conleche_grind =] theorem TeleWS.nil_eq (i : Nat) : TeleWS i [] = True := by
  simp [TeleWS]

@[conleche_grind =] theorem TeleWS.cons_eq (i : Nat) (x : Expr) (xs : List Expr) :
    TeleWS i (x :: xs) = (WScoped i x ∧ TeleWS (i + 1) xs) := by
  apply propext; constructor
  · intro h
    refine ⟨by simpa using h 0 x rfl, fun k nd hk => ?_⟩
    have := h (k + 1) nd (by simpa using hk)
    rwa [show i + (k + 1) = i + 1 + k by omega] at this
  · rintro ⟨hx, h⟩ k nd hk
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk; simpa
    | succ k =>
      have := h k nd (by simpa using hk)
      rwa [show i + 1 + k = i + (k + 1) by omega] at this

theorem nestFieldsS_spec (hrec : RecSpec mode env rec rec')
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) {s₀ : CState}, CSOK mode false env s₀ →
      WScoped (base + j) cur →
      ⦃fun s => s = s₀⦄ nestFields rec prog base err nF j cur st
      ⦃fun v s' => CSOK mode false env s' ∧
        Runs (nestFields rec' prog base err nF j cur st) v ∧
        TeleWS (base + j) v.2.1 ∧ WScoped (base + j + v.2.1.length) v.2.2.1; ⊤⦄ := by
  intro nF
  induction nF with
  | zero =>
    intro j cur st _ hs hw
    sym only [conleche_grind, nestFields.eq_1, List.length_nil] =>
      vcgen [nestFields] <;> finish
  | succ nF ih =>
    intro j cur st _ hs hw
    sym only [conleche_grind, nestFields.eq_2, nestFields.eq_3, List.length_cons] =>
      vcgen [nestFields.eq_def, hrec.triple,
        ih (j + 1)] <;> finish

theorem closeTelescope_wscopedA {nds : List Expr} {i : Nat} {body : Expr}
    (h : TeleWS i nds) (hb : WScoped (i + nds.length) body) :
    WScoped i (closeTelescope nds i body) :=
  closeTelescope_wscoped nds i body h hb
grind_pattern [conleche_grind] closeTelescope_wscopedA =>
  TeleWS i nds, closeTelescope nds i body

/-- A frame output's normal form is scoped at `hi`. -/
@[expose] def OutWS (hi : Nat) (o : List NestFieldKind × Expr) : Prop := WScoped hi o.2

@[conleche_grind =] theorem OutWS.eq (hi : Nat) (ks : List NestFieldKind) (e : Expr) :
    OutWS hi (ks, e) = WScoped hi e := rfl

/-- A crest of a closed constructor type is scoped where the key and the
holes are. -/
theorem wscoped_nestCrest {names : List Name} {us : List Level} {ds holes : List Expr}
    {d : Nat} {cv : ConstantVal} {ks : List Name} {crest : Expr} (hcl : cv.type.hasFvar = false)
    (hlen : names.length ≤ holes.length) (hds : AllWS d ds) (hholes : AllWS d holes)
    (h : nestCrest names us ds holes (cv.type.instantiateLevelParams ks us) = some crest) :
    WScoped d crest :=
  WScoped_nestCrest (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl) hlen
    (fun x hx => (List.mem_append.mp hx).elim (hds x) (hholes x)) h

theorem nestCtorsS_spec (henv : EnvWF env)
    {recC : Expr → List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState)}
    {recC' : Expr → List NestHole → Nat → Nat → Expr → NestState →
      FueledM (NestFieldKind × Expr × NestState)}
    (hrec : ∀ x, RecSpec .verified env (recC x) (recC' x)) (ctx : NestCtx)
    (prog : List NestHole)
    (hi : Nat) (us : List Level) (ds : List Expr) (names : List Name) (holes : List Expr)
    (hds : AllWS hi ds) (hholes : AllWS hi holes)
    (hlen : names.length ≤ holes.length) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) {s₀ : CState}, CSOK .verified false env s₀ →
      ListAll CtorClosed cs →
      ⦃fun s => s = s₀⦄
        nestCtors ctx (sharedOpsC .verified (mkFEnv env)) env recC prog hi us ds names holes cs st
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (nestCtors ctx (fueledOpsM .verified) env recC' prog hi us ds names holes cs st) v ∧
        ListAll (OutWS hi) v.1; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro st _ hs _
    sym only [conleche_grind, nestCtors.eq_1] =>
      vcgen [nestCtors] <;> finish
  | cons x cs ih =>
    obtain ⟨cv, nF⟩ := x
    intro st _ hs₀ hcs
    sym only [conleche_grind, nestCtors.eq_2, unwrapOr.eq_1,
        → wscoped_nestCrest (hlen := hlen) (hds := hds) (hholes := hholes)] =>
      vcgen [nestCtors, unwrapOr, inferS_spec henv, sortS_spec henv,
        nestFieldsS_spec (hrec _), ih] <;> finish

/-- A frame's holes: its group's entries at `hi, hi + 1, …`. -/
@[expose] def frameHoles (hi : Nat) (grp : List (Name × Expr)) : List Expr :=
  grp.mapIdx fun i (_, ty) => Expr.fvar (hi + i) ty

/-- A frame's holes are well scoped above the frame. -/
theorem frameHoles_wscoped {grp : List (Name × Expr)} {hi : Nat}
    (hg : ∀ x ∈ grp, WScoped hi x.2) : AllWS (hi + grp.length) (frameHoles hi grp) := by
  intro e hm
  obtain ⟨i, hi', heq⟩ := List.mem_mapIdx.mp hm
  subst heq
  simp only [WScoped]
  exact ⟨by omega, WScoped.mono (by omega) (hg _ (List.getElem_mem hi'))⟩

/-- `nestFrame` with its holes named (`frameHoles`). -/
theorem nestFrame_eq {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] (ctx : NestCtx)
    (ops : CheckerOps m) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState → m (NestFieldKind × Expr × NestState))
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (grp : List (Name × Expr)) (st : NestState) :
    nestFrame ctx ops env rec prog hi us ds nPc grp st = (do
      familyKeyCheck ops env ctx.find? hi (grp.headD default).1 us ds
      let prog' := (grp.mapIdx fun _ (c, ty) =>
        ({ key := ⟨c, us, ds⟩, base := hi, nIdx := ty.piBinders.1.length } : NestHole)).reverse ++ prog
      let ctors ← nestGroupCtors ctx nPc (grp.map (·.1))
      let (_, st) ← nestCtors ctx ops env (fun _ => rec) prog' (hi + grp.length) us ds
        (grp.map (·.1)) (frameHoles hi grp) ctors st
      pure st) := rfl

theorem nestFrameS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSpec .verified env rec rec')
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : AllWS hi ds) (grp : List (Name × Expr)) (st : NestState) {s₀ : CState}
    (hs : CSOK .verified false env s₀) (hg : ListAll (GrpWS ds) grp) :
    ⦃fun s => s = s₀⦄ nestFrame ctx (sharedOpsC .verified (mkFEnv env)) env rec prog hi us ds nPc grp st
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (nestFrame ctx (fueledOpsM .verified) env rec' prog hi us ds nPc grp st) v; ⊤⦄ := by
  sym only [conleche_grind, nestFrame_eq] =>
    vcgen [nestFrame_eq, familyKeyCheckS_spec henv hc.1,
      nestGroupCtorsS_spec (mode := .verified) (env := env) hc nPc,
      nestCtorsS_spec henv (fun _ => hrec) ctx _ (hi + grp.length) us ds (grp.map Prod.fst)
        (frameHoles hi grp) (AllWS.mono (Nat.le_add_right _ _) hds)
        (frameHoles_wscoped fun x hx => hg x hx hi hds) (by simp [frameHoles])] <;> finish

/-- The walk stack's depth bounds an instantiation's parameters that are
scoped at the enclosing one. -/
theorem allWS_nestWalkStack {ctx : NestCtx} {prog : List NestHole} {ds : List Expr}
    (hds : AllWS (ctx.hiAt prog.length) ds) :
    AllWS (ctx.hiAt (nestWalkStack ctx prog ds).length) ds := by
  unfold nestWalkStack; split
  · rename_i hfree
    intro x hx
    exact WScoped.of_fvarsBelow (hds x hx)
      (fvarB_le (by simpa using List.all_eq_true.mp hfree x hx))
  · exact hds

theorem nestContNewS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSpec .verified env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : AllWS (ctx.hiAt prog.length) ds) (cty : Expr) (hni : InstWS ds cty)
    (st : NestState) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄
      nestContNew ctx (sharedOpsC .verified (mkFEnv env)) env rec prog kb n us ds nPc cty st
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (nestContNew ctx (fueledOpsM .verified) env rec' prog kb n us ds nPc cty st) v; ⊤⦄ := by
  sym only [conleche_grind, nestContNew.eq_1, allWS_nestWalkStack hds] =>
    vcgen [nestContNew, nestGrowGroupS_spec henv hc, nestFrameS_spec henv hc hrec _ _ us ds nPc
      (allWS_nestWalkStack hds)] <;> finish

theorem nestContKeyS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSpec .verified env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : AllWS (ctx.hiAt prog.length) ds) (cty : Expr) (hni : InstWS ds cty)
    (st : NestState) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄
      nestContKey ctx (sharedOpsC .verified (mkFEnv env)) env rec prog kb n us ds nPc cty st
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (nestContKey ctx (fueledOpsM .verified) env rec' prog kb n us ds nPc cty st) v; ⊤⦄ := by
  sym only [conleche_grind, nestContKey.eq_1] =>
    vcgen [nestContKey, nestContNewS_spec henv hc hrec prog kb n us ds nPc hds cty hni st hs]
      <;> finish

/-- An instantiation's parameters that pass the container case's guard
are scoped at the walk's depth. -/
theorem allWS_take_guard {dep D n : Nat} {args : List Expr} (hargs : AllWS dep args)
    (hck : (List.take n args).all
      (fun x => x.bvarB == 0 && decide (x.fvarB ≤ D)) = true) :
    AllWS D (List.take n args) := by
  intro d hd
  have h1 := List.all_eq_true.mp hck d hd
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  exact WScoped.of_fvarsBelow (hargs d (List.mem_of_mem_take hd)) (fvarB_le h1.2)

theorem nestContS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSpec .verified env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    {dep : Nat} (hargs : AllWS dep args) (st : NestState) {s₀ : CState}
    (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ nestCont ctx (sharedOpsC .verified (mkFEnv env)) env rec prog kb n us args st
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (nestCont ctx (fueledOpsM .verified) env rec' prog kb n us args st) v; ⊤⦄ := by
  sym only [conleche_grind, nestCont.eq_1, unwrapOr.eq_1, allWS_take_guard hargs] =>
    vcgen [nestCont, unwrapOr, nestInstTypeS_spec henv hc,
      nestContKeyS_spec henv hc hrec prog kb n us] <;> finish

end Walk

/-! ## The function itself, and the install stage -/

section Top

variable {env : Env}

/-- **`nestPos` at the shared operations**: every successful cached run
is a fueled one, with the same result. -/
theorem nestPosS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) :
    ∀ fuel, RecSpec .verified env (nestPos (sharedOpsC .verified (mkFEnv env)) env ctx fuel)
      (nestPos (fueledOpsM .verified) env ctx fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog dep kb e st s₀ hs hw
    sym only [conleche_grind, nestPos.eq_1] =>
      vcgen [nestPos] <;> finish
  | succ fuel ih =>
    intro prog dep kb e st s₀ hs hw
    sym only [conleche_grind, nestPos.eq_2] =>
      vcgen [nestPos, whnfS_spec henv, ih.triple,
        nestContS_spec henv hc ih (dep := dep)] <;> finish

/-- The member holes: scoped at the walk's depth, each a variable. -/
@[expose] def HolesOk (d : Nat) (holes : List Expr) : Prop :=
  ∀ x ∈ holes, WScoped d x ∧ ∃ i ty, x = .fvar i ty

theorem HolesOk.allWS {d : Nat} {holes : List Expr} (h : HolesOk d holes) : AllWS d holes :=
  fun x hx => (h x hx).1

/-- **The root frame at the shared operations.** -/
theorem nestRootS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) {holes : List Expr} (hholes : HolesOk (ctx.hiAt 0) holes)
    (hlen : ctx.names.length ≤ holes.length) (hpar : AllWS (ctx.hiAt 0) ctx.params) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState) {s₀ : CState},
      CSOK .verified false env s₀ → ListAll (ListAll CtorClosed) css →
      ⦃fun s => s = s₀⦄ nestRoot (sharedOpsC .verified (mkFEnv env)) env ctx holes css st
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (nestRoot (fueledOpsM .verified) env ctx holes css st) v ∧
        ListAll (ListAll (OutWS (ctx.hiAt 0))) v.1; ⊤⦄ := by
  intro css
  induction css with
  | nil =>
    intro st _ hs _
    sym only [conleche_grind, nestRoot.eq_1] =>
      vcgen [nestRoot] <;> finish
  | cons cs css ih =>
    intro st _ hs hcs
    sym only [conleche_grind, nestRoot.eq_2] =>
      vcgen [nestRoot, nestCtorsS_spec henv (fun x => nestPosS_spec henv hc (whnfWalkFuel x))
        ctx [] (ctx.hiAt 0) _ _ _ _ hpar hholes.allWS hlen,
        ih] <;> finish

/-- Official's uniform-occurrence check at the shared operations (no
operation: the same verdict). -/
theorem nestUniformS_spec {ctx : NestCtx}
    (ctorss : List (List (ConstantVal × Nat))) {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ nestUniform (m := CheckCM) ctx ctorss
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (nestUniform (m := FueledM) ctx ctorss) v; ⊤⦄ := by
  sym only [conleche_grind, nestUniform.eq_1] =>
    vcgen [nestUniform] <;> finish

/-- An opened field telescope: its `i`-th variable's type scoped at
`nP + i`. -/
@[expose] def FvsWS (nP : Nat) (fvs : List Expr) : Prop :=
  ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (nP + i) (Expr.fvarTypeD x)

theorem FvsWS.get {nP : Nat} {fvs : List Expr} (h : FvsWS nP fvs) {j : Nat} {x : Expr}
    (hx : fvs[j]? = some x) : WScoped (nP + j) (Expr.fvarTypeD x) :=
  h j x hx

/-- The per-field sort walk at the shared operations
(#175: the large-eliminator escape admits a field that is
one of the residual's index expressions). -/
theorem checkStructFieldSortsIS_spec (henv : EnvWF env)
    {isProp large : Bool} {s : Level} {nP : Nat} {fvs idxArgs : List Expr}
    (hfvs : FvsWS nP fvs) :
    ∀ {j : Nat} {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄
        checkStructFieldSortsI (sharedOpsC .verified (mkFEnv env)) env isProp large s nP fvs idxArgs j
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkStructFieldSortsI (fueledOpsM .verified) env isProp large s nP fvs idxArgs j) v;
        ⊤⦄ := by
  intro j
  induction j with
  | zero =>
    intro _ hs
    sym only [conleche_grind, checkStructFieldSortsI.eq_1] =>
      vcgen [checkStructFieldSortsI] <;> finish
  | succ j ih =>
    intro _ hs
    sym only [conleche_grind, checkStructFieldSortsI.eq_2, unwrapOr.eq_1, liftFueled.eq_1,
        → hfvs.get] =>
      vcgen [checkStructFieldSortsI, unwrapOr, liftFueled, inferS_spec henv,
        sortS_spec henv, ih] <;>
        finish

/-- An abstracted constructor's fields, opened at the holes' depth. -/
theorem fvsWS_openPis {n d : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e d = some (fvs, body)) (hw : WScoped d e) : FvsWS d fvs := by
  intro i x hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ h i x hx
  have hw' := (openPisAtFvars_WScoped _ _ _ h hw).1 _ (List.mem_of_getElem? hx)
  simp only [WScoped] at hw'
  exact hw'.2

/-- The fields' universes at the holes, at the shared operations. -/
theorem checkAbsCtorSortsS_spec (henv : EnvWF env)
    {ctx : NestCtx} :
    ∀ (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)) {s₀ : CState},
      CSOK .verified false env s₀ → ListAll (OutWS (ctx.hiAt 0)) os →
      ⦃fun s => s = s₀⦄ checkAbsCtorSorts (sharedOpsC .verified (mkFEnv env)) env ctx cs os
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkAbsCtorSorts (fueledOpsM .verified) env ctx cs os) v; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro os _ hs _
    sym only [conleche_grind, checkAbsCtorSorts] =>
      vcgen [checkAbsCtorSorts.eq_def] <;> finish
  | cons c cs ih =>
    intro os
    cases os with
    | nil =>
      intro _ hs _
      sym only [conleche_grind, checkAbsCtorSorts] =>
        vcgen [checkAbsCtorSorts.eq_def] <;> finish
    | cons o os =>
      intro _ hs hos
      sym only [conleche_grind, checkAbsCtorSorts.eq_1, unwrapOr.eq_1, → fvsWS_openPis] =>
        vcgen [checkAbsCtorSorts, unwrapOr, checkStructFieldSortsIS_spec henv,
          ih os] <;> finish

theorem checkAbsCtorSortsAllS_spec (henv : EnvWF env)
    {ctx : NestCtx} :
    ∀ (css : List (List (ConstantVal × Nat))) (oss : List (List (List NestFieldKind × Expr)))
      {s₀ : CState}, CSOK .verified false env s₀ → ListAll (ListAll (OutWS (ctx.hiAt 0))) oss →
      ⦃fun s => s = s₀⦄ checkAbsCtorSortsAll (sharedOpsC .verified (mkFEnv env)) env ctx css oss
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkAbsCtorSortsAll (fueledOpsM .verified) env ctx css oss) v; ⊤⦄ := by
  intro css
  induction css with
  | nil =>
    intro oss _ hs _
    sym only [conleche_grind, checkAbsCtorSortsAll] =>
      vcgen [checkAbsCtorSortsAll.eq_def] <;> finish
  | cons cs css ih =>
    intro oss
    cases oss with
    | nil =>
      intro _ hs _
      sym only [conleche_grind, checkAbsCtorSortsAll] =>
        vcgen [checkAbsCtorSortsAll.eq_def] <;> finish
    | cons os oss =>
      intro _ hs hos
      sym only [conleche_grind, checkAbsCtorSortsAll.eq_1] =>
        vcgen [checkAbsCtorSortsAll, checkAbsCtorSortsS_spec henv cs os,
          ih oss] <;> finish

/-- A seed's parameters are scoped at `d`. -/
@[expose] def SeedWS (d : Nat) (k : NestKey × Nat) : Prop := AllWS d k.1.ds

@[conleche_grind =] theorem SeedWS.eq (d : Nat) (key : NestKey) (n : Nat) :
    SeedWS d (key, n) = AllWS d key.ds := rfl

theorem nestSeedsS_spec (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) :
    ∀ (ks : List (NestKey × Nat)) (st : NestState) {s₀ : CState}, CSOK .verified false env s₀ →
      ListAll (SeedWS (ctx.hiAt 0)) ks →
      ⦃fun s => s = s₀⦄ nestSeeds (sharedOpsC .verified (mkFEnv env)) env ctx ks st
      ⦃fun v s' => CSOK .verified false env s' ∧ Runs (nestSeeds (fueledOpsM .verified) env ctx ks st) v; ⊤⦄
          := by
  intro ks
  induction ks with
  | nil =>
    intro st _ hs _
    sym only [conleche_grind, nestSeeds.eq_1] =>
      vcgen [nestSeeds] <;> finish
  | cons x ks ih =>
    obtain ⟨key, nPc⟩ := x
    intro st _ hs hw
    sym only [conleche_grind, nestSeeds.eq_2, List.length_nil] =>
      vcgen [nestSeeds, nestInstTypeS_spec henv hc,
        nestContKeyS_spec henv hc (nestPosS_spec henv hc _) [] 0 key.cname key.lvls key.ds,
        ih] <;> finish

/-- The pieces of the walk's context `blockNestCtx` builds. -/
theorem blockNestCtx_ok {env₁ : Env} (henv₁ : EnvWF env₁) {p : BlockShape}
    (hM : ∀ ms ∈ p.members, ms.cvT.type.hasFvar = false)
    {formers : List ConstantVal} (hT : ∀ cv ∈ formers, WScoped 0 cv.type) {cv0 : ConstantVal}
    (h0 : formers.head? = some cv0) {fvs : List Expr} {body : Expr}
    (hpq : openPisAtFvars p.nP cv0.type 0 = some (fvs, body)) :
    NestCtxOk (p.nestCtx fvs env₁.find?) ∧ AllWS p.nP fvs ∧ fvs.length = p.nP := by
  have hw0 : WScoped 0 cv0.type := hT _ (List.mem_of_mem_head? h0)
  refine ⟨⟨fun n ci hf => (henv₁.consts ci (List.mem_of_find?_eq_some hf)).1, fun cv hcv => ?_⟩,
    fun x hx => ?_, ConLeche.Verify.openPisAtFvars_length _ hpq⟩
  · obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcv
    exact hM ms hms
  have := (openPisAtFvars_WScoped p.nP cv0.type 0 hpq hw0).1 x hx
  rwa [Nat.zero_add] at this

theorem holesOk_nestHoles {ctx : NestCtx} {holes : List Expr} (hh : nestHoles ctx = some holes)
    (hc : NestCtxOk ctx) (hpar : AllWS ctx.nP ctx.params) : HolesOk (ctx.hiAt 0) holes :=
  nestHoles_ok hc hpar hh

@[conleche_grind =] theorem nestCtx_params_eq (p : BlockShape) (fvs : List Expr)
    (find? : Name → Option ConstantInfo) : (p.nestCtx fvs find?).params = fvs := rfl

@[conleche_grind =] theorem nestCtx_nP_eq (p : BlockShape) (fvs : List Expr)
    (find? : Name → Option ConstantInfo) : (p.nestCtx fvs find?).nP = p.nP := rfl

theorem allWS_hiAt {ctx : NestCtx} {xs : List Expr} (h : AllWS ctx.nP xs) :
    AllWS (ctx.hiAt 0) xs :=
  AllWS.mono (by simp [NestCtx.hiAt]) h

/-- **The walk's context at the shared operations** (`blockNestCtx`, no
operation run): the same value, a context whose stored constants are
closed, its holes and canonical variables well scoped at its depth, one
canonical variable per parameter. -/
theorem blockNestCtxS_spec (henv : EnvWF env) (p : BlockShape)
    (hM : ∀ ms ∈ p.members, ms.cvT.type.hasFvar = false)
    (hT : ∀ cv ∈ p.formers, WScoped 0 cv.type) {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ blockNestCtx (m := CheckCM) p env.find?
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (blockNestCtx (m := FueledM) p env.find?) v ∧
      NestCtxOk v.1 ∧ HolesOk (v.1.hiAt 0) v.2 ∧ AllWS (v.1.hiAt 0) v.1.params ∧
      v.1.params.length = v.1.nP ∧ nestHoles v.1 = some v.2 ∧ v.1.nP = p.nP; ⊤⦄ := by
  -- `ematch`: one E-matching round per pure-side bind (`Runs.pure_bind_eq`), and the
  -- context's facts after the last one
  sym only [conleche_grind, blockNestCtx.eq_1, unwrapOr.eq_1, → blockNestCtx_ok henv hM hT,
      → holesOk_nestHoles, → allWS_hiAt] =>
    vcgen [blockNestCtx, unwrapOr] <;> finish (ematch := 8)

/-- Closed constructor types, as the root frame's precondition. -/
theorem ctorsClosed {memberCtors : List (List (ConstantVal × Nat))}
    (hct : ∀ ctorList ∈ memberCtors, ∀ c ∈ ctorList, WScoped 0 c.1.type) :
    ListAll (ListAll CtorClosed) memberCtors :=
  fun cs hcs c hc => not_hasFvar_of_fvarsBelow_zero (hct cs hcs c hc).fvarsBelow

/-- **The check's positivity stage at the shared operations**: every
successful cached run is a fueled one. -/
theorem checkBlockPositivityS_spec (henv : EnvWF env)
    (p : BlockShape)
    (hM : ∀ ms ∈ p.members, ms.cvT.type.hasFvar = false)
    (hT : ∀ cv ∈ p.formers, WScoped 0 cv.type)
    (hct : ∀ ctorList ∈ p.memberCtors, ∀ c ∈ ctorList, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄
      checkBlockPositivity (sharedOpsC .verified (mkFEnv env)) env env.find? p
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkBlockPositivity (fueledOpsM .verified) env env.find? p) v; ⊤⦄ := by
  sym only [conleche_grind, checkBlockPositivity.eq_1, nestHoles_length, ctorsClosed hct] =>
    vcgen [checkBlockPositivity, blockNestCtxS_spec (mode := .verified) henv p hM hT,
      nestUniformS_spec (mode := .verified) (env := env) p.memberCtors,
      nestRootS_spec henv, checkAbsCtorSortsAllS_spec henv] <;> finish

end Top

end ConLeche.Cached
