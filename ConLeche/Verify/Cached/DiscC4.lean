module

public import ConLeche.Verify.Cached.BinderLoopC
import ConLeche.Verify.BetaSpine

public section

/-!
# Cached body walks, part 4: head normalization and the whnf loop

Simulation walks (task #163) for the cached `reduceProjCoreI`,
`whnfAppI`/`betaPeelI`, `whnfCoreStepI`/`whnfCoreLoopI`/`whnfCoreBodyI`,
`whnfLoopI`/`whnfBodyI`, `inferSpineI`/`inferSpineIOI` and
`inferBodyI`/`inferBodyIOI` (`ConLeche/Cached/CoreC.lean`) against the
pure fueled comparands.  Every walk is a `Std.WP` triple proved by
`vcgen` and `grind` (`ConLeche/Verify/Cached/Grind.lean`); the bodies
are stated as `BodySpec`s, which the knot (`KnotC.lean`) consumes.

The loops are unfolded by their own `eq_def` in the `vcgen` list (the
generated per-arm equations of their inner `match` are conditional, which
`vcgen` skips); the pure mirrors' own equation lemmas go into the `sym`
list.  The bodies' `Expr` dispatch is one level deep, so the pure
bodies are unfolded as they are (one equation per constructor); where the
cached body walks a loop the chained specification does not
(`whnfCoreBody`'s head-normalization loop, `inferBody`'s spine), a
guarded `Runs` bridge (`Runs.whnfCoreBody_of_loop`, `Runs.inferBody_app`,
`Runs.inferBodyIO_app`) carries the loop's answer to the body's.

In `inferBodyI` the binder-telescope peel fuel is the constant
`peelFuelM`, opaque to the binder-loop tails, which quantify over the
fuel.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

section Walks

variable {env : Env} {f : Nat}

/-- The spine length the arity pre-check computes is the length of the
argument list the ι step builds. -/
private theorem iotaNumArgs_getAppArgsAcc (e : Expr) :
    ∀ acc : List Expr,
      iotaNumArgs e acc.length = (Expr.getAppArgsAccC e acc).length := by
  induction e with
  | app g a ihg _ =>
    intro acc
    rw [iotaNumArgs, Expr.getAppArgsAccC, ← ihg (a :: acc)]
    rfl
  | _ => intro acc; rfl

private theorem iotaNumArgs_zero (e : Expr) :
    iotaNumArgs e 0 = (Expr.getAppArgsC e).length :=
  iotaNumArgs_getAppArgsAcc e []

/-- Where the arity pre-check fails, the ι step has nothing to do: its
own guard returns `none` on exactly the same three grounds (the head is
not a constant, it is not a stored recursor, or the spine has the wrong
number of arguments or of levels). -/
private theorem iotaRecI_of_arityOk_false {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} (h : iotaArityOk fe e = false) :
    iotaRecI mi r fe d e = pure none := by
  unfold iotaArityOk at h
  unfold iotaRecI
  cases hg : Expr.getAppFn e with
  | const c us =>
    rw [hg] at h
    dsimp only at h
    simp only [pure_bind]
    cases hf : fe.find? c with
    | none => rfl
    | some ci =>
      rw [hf] at h
      cases ci with
      | recInfo cv mI rP rules =>
        dsimp only at h ⊢
        rw [ite_eq_right]
        rintro ⟨hlen, hlvl, -⟩
        rw [iotaNumArgs_zero, hlen, hlvl] at h
        simp at h
      | _ => rfl
  | _ => rfl

/-- The pre-check in the spine loop changes no verdict. -/
private theorem iotaArityOk_guard {mi : CheckMode} {r : CoreFnsI}
    {fe : FEnv} {d : Nat} {e : Expr} :
    (if iotaArityOk fe e then iotaRecI mi r fe d e else pure none)
      = iotaRecI mi r fe d e := by
  by_cases h : iotaArityOk fe e = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, iotaRecI_of_arityOk_false (Bool.not_eq_true _ |>.mp h)]

/-- The projection rule simulates its specification. -/
theorem reduceProjCoreC_spec (ih : SSimC mode env f) {d : Nat} {sn : Name} {ip : Nat}
    {i : Expr} {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      reduceProjCoreI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d sn ip i
    ⦃fun o s' => CSOK mode env s' ∧
      Runs (reduceProjCore mode (fueledFns mode env) env d sn ip i) o ∧ OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, reduceProjCore, mkFEnv_findProj?, projCertAtF_mkFEnv] =>
    vcgen [reduceProjCoreI, projLitToCtorC_spec ih] <;> finish

/-! ### The argument loop, by `vcgen` and `grind`

Each walk below is `sym only [conleche_grind, …] => vcgen […] <;> finish`
(`ConLeche/Verify/Cached/Grind.lean`).  The cached loops match their
head on `.lam`, and the equation compiler states their `a :: rest` step
as one equation per arm, the fall-through one conditional, which `vcgen`
skips; the unconditional `eq_def` unfolds them instead (`whnfAppI`'s by
`rw` before `sym`, so that `iotaArityOk_guard` can discharge the ι arity
guard: `vcgen` splits an `ite` before it tries an equation about it).
`vcgen` splits the `match`
and hands each arm its fall-through hypothesis; the pure mirrors'
own equation lemmas (`betaPeelW.eq_*`, `whnfAppW.eq_*`, the fall-through
one included) go into the `sym` list, and `grind` discharges the
fall-through premise from the arm's hypothesis. -/

/-- The peel step's scope: a binder peeled off a well-scoped
instantiated lambda, instantiated with one more well-scoped argument. -/
theorem wscoped_peel {d : Nat} {ty body a : Expr} {acc : List Expr}
    (hw : Expr.WScoped d ((Expr.lam ty body).instantiateList acc)) (ha : Expr.WScoped d a) :
    Expr.WScoped d (body.instantiateList (a :: acc)) := by
  rw [instList_lam, Expr.WScoped] at hw
  rw [Expr.instantiateList_cons]
  exact Expr.WScoped.instantiate1_gen ha 0 hw.2
grind_pattern [conleche_grind] wscoped_peel =>
  Expr.WScoped d ((Expr.lam ty body).instantiateList acc), body.instantiateList (a :: acc)

/-- The peel loop simulates its pure mirror. -/
theorem betaPeelC_spec (r : CoreFnsI) {d : Nat} :
    ∀ {args : List Expr} {t : Expr} {acc : List Expr} {s₀ : CState}, CSOK mode env s₀ →
      Expr.WScoped d (t.instantiateList acc) → AllWS d args →
      ⦃fun s => s = s₀⦄ betaPeelI r (mkFEnv env) d t acc args
      ⦃fun v s' => CSOK mode env s' ∧
          Runs (betaPeelW mode (fueledFns mode env) env d t acc args) v ∧ StepWS d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, betaPeelW.eq_1] =>
      vcgen [betaPeelI, instListM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, betaPeelW.eq_2, betaPeelW.eq_3] =>
      vcgen [betaPeelI.eq_def, mkAppNM, instListM_spec hs, ihr] <;> finish

/-- The bulk-beta argument loop simulates its pure mirror. -/
theorem whnfAppC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} :
    ∀ {args : List Expr} {v : Expr} {s₀ : CState}, CSOK mode env s₀ →
      Expr.WScoped d v → AllWS d args →
      ⦃fun s => s = s₀⦄ whnfAppI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d v args
      ⦃fun w s' => CSOK mode env s' ∧
          Runs (whnfAppW mode (fueledFns mode env) env d v args) w ∧ StepWS d w; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ _ _
    sym only [conleche_grind, whnfAppW.eq_1] =>
      vcgen [whnfAppI] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _
    rw [whnfAppI.eq_def]; simp only [iotaArityOk_guard]
    sym only [conleche_grind, whnfAppW.eq_2, whnfAppW.eq_3] =>
      vcgen [mkAppNM, iotaRecC_spec hμ ih henv,
        betaPeelC_spec (coreKnotI mode (mkFEnv env) f), ihr] <;> finish

/-- One head-normalization step simulates its pure mirror. -/
theorem whnfCoreStepC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} {i : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      whnfCoreStepI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c d i
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (whnfCoreStepW mode (fueledFns mode env) env c d i) v ∧ StepWS d v; ⊤⦄ := by
  sym only [conleche_grind, whnfCoreStepW] =>
    vcgen [whnfCoreStepI, inst1M_spec hs, ih.whnfCore_spec, ih.whnf_spec,
      reduceProjCoreC_spec ih, whnfAppC_spec hμ ih henv] <;> finish

/-- The mirror loop's answer is the chained body's
(`whnfCoreLoop_sound_body`). -/
theorem Runs.whnfCoreBody_of_loop {c : Bool} {d n : Nat} {e v : Expr}
    (h : Runs (whnfCoreLoopM mode (fueledFns mode env) env c d n e) v) :
    Runs (whnfCoreBody mode (fueledFns mode env) env c d e) v := by
  obtain ⟨F, hF⟩ := h
  exact whnfCoreLoop_sound_body d e v n F hF
grind_pattern [conleche_grind] Runs.whnfCoreBody_of_loop =>
  Runs (whnfCoreLoopM mode (fueledFns mode env) env c d n e) v,
  whnfCoreBody mode (fueledFns mode env) env c d e

/-- The head-normalization *loop* simulates its mirror, by induction on
the shared step budget (task #106); a step's outcome is the same on
both sides, and a continuation re-enters the loop (task #342 R2). -/
theorem whnfCoreLoopC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {c : Bool} {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : CState}, CSOK mode env s₀ → Expr.WScoped d i →
      ⦃fun s => s = s₀⦄
        whnfCoreLoopI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c d n i
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (whnfCoreLoopM mode (fueledFns mode env) env c d n i) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hw
    sym only [conleche_grind] => vcgen [whnfCoreLoopI] <;> finish
  | succ n ihn =>
    intro i s₀ hs hw
    sym only [conleche_grind, whnfCoreLoopM] =>
      vcgen [whnfCoreLoopI, whnfCoreStepC_spec hμ ih henv, ihn] <;> finish

/-- The cached head-normalization body simulates the chained
specification body: the loop run is reproduced by `whnfCoreBody` at
some knot fuel (`whnfCoreLoop_sound_body`). -/
theorem whnfCoreBodyC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) (c : Bool) :
    BodySpec mode env (whnfCoreBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) c)
      (whnfCoreBody mode (fueledFns mode env) env c) := by
  intro s₀ d i hs hw
  sym only [conleche_grind] =>
    vcgen [whnfCoreBodyI, whnfCoreLoopC_spec hμ ih henv] <;> finish

end Walks

section Walks2

variable {env : Env} {f : Nat}

/-- The reduction loop simulates its specification, by induction on the
shared step budget (task #106). -/
theorem whnfLoopC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} (n : Nat) :
    ∀ {i : Expr} {s₀ : CState}, CSOK mode env s₀ → Expr.WScoped d i →
      ⦃fun s => s = s₀⦄ whnfLoopI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d n i
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (whnfLoop (fueledFns mode env) env d n i) v ∧ Expr.WScoped d v; ⊤⦄ := by
  induction n with
  | zero =>
    intro i s₀ hs hw
    sym only [conleche_grind] => vcgen [whnfLoopI] <;> finish
  | succ n ihn =>
    intro i s₀ hs hw
    sym only [conleche_grind, whnfLoop, whnfStep, unfoldDefinition_WScoped henv] =>
      vcgen [whnfLoopI, whnfStepI, ih.whnfCore_spec, reduceNatC_spec ih,
        unfoldDefinitionC_spec (mode := mode) (env := env), ihn] <;> finish

theorem whnfBodyC_spec (ih : SSimC mode env f) (henv : EnvWF env) :
    BodySpec mode env (whnfBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env))
      (whnfBody (fueledFns mode env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, whnfBody] =>
    vcgen [whnfBodyI, whnfLoopC_spec ih henv] <;> finish

end Walks2

section Walks3

variable {env : Env} {f : Nat}

/-! ### The io view's entry points

The io-grade walks run on `CoreFnsI.ioView` of the knot; `vcgen` looks
specs up at the projection form, so the knot's specs are restated
there, and the pure views are read through `CoreFns.ioView_*`. -/

theorem SSimC.ioWhnf_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)).whnf d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).whnf d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  ih.whnf_spec hs hw

theorem SSimC.ioInfer_spec (ih : SSimC mode env f) {s₀ : CState} {d : Nat} {i : Expr}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)).infer d i
    ⦃fun r s' => CSOK mode env s' ∧ Runs ((fueledFns mode env).inferIO d i) r ∧
      Expr.WScoped d r; ⊤⦄ :=
  ih.inferIO_spec hs hw

theorem ensureSortIOC_spec (ih : SSimC mode env f) {d : Nat} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ ensureSortI (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) d i
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (ensureSort (CoreFns.ioView (fueledFns mode env)) env d i) v; ⊤⦄ :=
  ensureSortC_spec ih hs hw

theorem CoreFns.ioView_whnf {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).whnf d e = r.whnf d e := rfl

theorem CoreFns.ioView_infer {m : Type → Type} (r : CoreFns m) (d : Nat) (e : Expr) :
    (CoreFns.ioView r).infer d e = r.inferIO d e := rfl

/-! ### The inference spine loops

As for the argument loop: the cached loops by their `eq_def`, the pure
mirrors' own equation lemmas in the `sym` list. -/

/-- The application-inference spine loop simulates its pure mirror. -/
theorem inferSpineC_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄ inferSpineI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d ty acc args
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (inferSpine (fueledFns mode env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpine.eq_1] =>
      vcgen [inferSpineI, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpine.eq_2, inferSpine.eq_3, toListRev_singleton] =>
      vcgen [inferSpineI.eq_def, instListRevM_spec (mode := mode) (env := env), ih.infer_spec,
        ih.whnf_spec, defeqArgC_spec ih, ihr] <;> finish

/-- The io-grade spine loop simulates its pure mirror. -/
theorem inferSpineIOC_spec (ih : SSimC mode env f) {d : Nat} :
    ∀ {args : List Expr} {ty : Expr} {acc : Array Expr} {s₀ : CState}, CSOK mode env s₀ →
      Expr.WScoped d (ty.instantiateList acc.toList.reverse) → AllWS d args →
      ⦃fun s => s = s₀⦄
        inferSpineIOI (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env) d ty acc args
      ⦃fun v s' => CSOK mode env s' ∧
        Runs (inferSpineIO (fueledFns mode env) d ty acc.toList.reverse args) v ∧
        Expr.WScoped d v; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro _ _ _ hs _ _
    sym only [conleche_grind, inferSpineIO.eq_1] =>
      vcgen [inferSpineIOI, instListRevM_spec hs] <;> finish
  | cons _ rest ihr =>
    intro _ _ _ _ _ _
    sym only [conleche_grind, inferSpineIO.eq_2, inferSpineIO.eq_3, toListRev_singleton] =>
      vcgen [inferSpineIOI.eq_def, instListRevM_spec (mode := mode) (env := env),
        ih.ioWhnf_spec, ihr] <;> finish

/-! ### The inference bodies -/

/-- A free variable's type is scoped at the variable's depth, so at any
depth above it. -/
theorem wscoped_fvar_ty {d idx : Nat} {ty : Expr} (h : Expr.WScoped d (.fvar idx ty)) :
    Expr.WScoped d ty := by
  rw [Expr.WScoped] at h
  exact Expr.WScoped.mono (Nat.le_of_lt h.1) h.2
grind_pattern [conleche_grind] wscoped_fvar_ty => Expr.WScoped d (.fvar idx ty)

/-- A stored constant's type is closed. -/
theorem EnvWF.constTy_closed (henv : EnvWF env) {n : Name} {ci : ConstantInfo}
    (h : env.find? n = some ci) : ci.toConstantVal.type.hasFvar = false :=
  (henv.consts _ (Env.find?_mem h)).1

/-- A projection's type is well scoped at its subject's scope. -/
theorem wscoped_typeAt (henv : EnvWF env) {T : Name} {i : Nat} {entry : ProjEntry}
    (hf : env.findProj? T i = some entry) (us : List Level) {d : Nat} {targs : List Expr}
    (hlen : targs.length = entry.numParams) {pe : Expr} (hargs : AllWS d targs)
    (hpe : Expr.WScoped d pe) : Expr.WScoped d (entry.typeAt us targs pe) :=
  projEntry_typeAt_WScoped henv hf us hlen hargs hpe

/-- The cached spine walk's answer is the chained application clause's
(`inferSpine_sound_body`). -/
theorem Runs.inferBody_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode env).infer d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpine (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBody (fueledFns mode env) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpine (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpine_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBody_app =>
  Runs (inferSpine (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBody (fueledFns mode env) env d (.app g a)

/-- The pieces of a `U E C a rest` spine shape. -/
theorem bvUnsatSpine_args {h E C a : Expr} {args rest : List Expr}
    (hsp : bvUnsatSpine h args = some (E, C, a, rest)) : args = E :: C :: a :: rest := by
  unfold bvUnsatSpine at hsp
  split at hsp
  · split at hsp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hsp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hsp; rfl
    · exact nomatch hsp
  · exact nomatch hsp

/-- The skipped argument and the rest of the spine are scoped. -/
theorem wscoped_bvSpine {d : Nat} {i E C a cod : Expr} {rest : List Expr}
    (hsp : bvUnsatSpine i.getAppFn i.getAppArgs = some (E, C, a, rest)) (hw : Expr.WScoped d i)
    (hc : Expr.WScoped d cod) :
    Expr.WScoped d (cod.instantiate1 a) ∧ AllWS d rest ∧ AllWS d [E, C] := by
  have ha := allWS_getAppArgs hw
  rw [bvUnsatSpine_args hsp] at ha
  refine ⟨Expr.WScoped.instantiate1_gen (ha a (by simp)) 0 hc, fun x hx => ha x (by simp [hx]),
    fun x hx => ha x (by simp at hx; rcases hx with rfl | rfl <;> simp)⟩
grind_pattern [conleche_grind] wscoped_bvSpine =>
  bvUnsatSpine i.getAppFn i.getAppArgs, some (E, C, a, rest), Expr.WScoped d i, cod.instantiate1 a

theorem allWS_bvSpine {d : Nat} {i E C a : Expr} {rest : List Expr}
    (hsp : bvUnsatSpine i.getAppFn i.getAppArgs = some (E, C, a, rest)) (hw : Expr.WScoped d i) :
    AllWS d rest ∧ AllWS d [E, C] := by
  have ha := allWS_getAppArgs hw
  rw [bvUnsatSpine_args hsp] at ha
  exact ⟨fun x hx => ha x (by simp [hx]),
    fun x hx => ha x (by simp at hx; rcases hx with rfl | rfl <;> simp)⟩
grind_pattern [conleche_grind] allWS_bvSpine =>
  bvUnsatSpine i.getAppFn i.getAppArgs, some (E, C, a, rest), Expr.WScoped d i

/-- The cached walk's skipped `U E C a` spine (task #368)
is the chained application clause's (`inferBody_bvUnsat_sound`). -/
theorem Runs.inferBody_bvUnsat {d : Nat} {g x E C a tf t1 ty body v : Expr} {rest : List Expr}
    (hsp : bvUnsatSpine (Expr.app g x).getAppFn (Expr.app g x).getAppArgs = some (E, C, a, rest))
    (h1 : Runs ((fueledFns mode env).infer d (Expr.app g x).getAppFn) tf)
    (h2 : Runs (inferSpine (fueledFns mode env) d tf [] [E, C]) t1)
    (h3 : Runs ((fueledFns mode env).whnf d t1) (.forallE ty body))
    (hsk : bvUnsatSkip (mkFEnv env).find? (mkFEnv env).findProj?
      (.app (.app (Expr.app g x).getAppFn E) C) a body = true)
    (h4 : Runs (inferSpine (fueledFns mode env) d (body.instantiate1 a) [] rest) v) :
    Runs (inferBody (fueledFns mode env) env d (.app g x)) v := by
  have happ := Expr.mkAppN_getApp (Expr.app g x)
  unfold bvUnsatSpine at hsp
  split at hsp
  · rename_i c E' C' a' rest' hfn hargs
    by_cases hc : (c == unsatThmName) = true
    · rw [ite_eq_left hc] at hsp
      obtain ⟨rfl, rfl, rfl, rfl⟩ : E' = E ∧ C' = C ∧ a' = a ∧ rest' = rest := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp; exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2⟩
      simp only [beq_iff_eq] at hc
      subst hc
      rw [hfn] at h1 hsk
      rw [hfn, hargs] at happ
      rw [show (mkFEnv env).find? = env.find? from funext (mkFEnv_find? env),
        show (mkFEnv env).findProj? = env.findProj? from
          funext fun T => funext fun i => mkFEnv_findProj? env T i] at hsk
      obtain ⟨F1, h1⟩ := h1
      obtain ⟨F2, h2⟩ := h2
      obtain ⟨F3, h3⟩ := h3
      obtain ⟨F4, h4⟩ := h4
      rw [inferSpine_atF] at h2 h4
      obtain ⟨F', hF'⟩ := inferBody_bvUnsat_sound d h1 h2 h3 hsk h4
      rw [happ] at hF'
      cases F' with
      | zero => rw [inferTypeCore_zero] at hF'; exact nomatch hF'
      | succ G => exact ⟨G, by rw [inferBody_atF, ← inferTypeCore_succ]; exact hF'⟩
    · rw [ite_eq_right hc] at hsp; exact nomatch hsp
  · exact nomatch hsp
grind_pattern [conleche_grind] Runs.inferBody_bvUnsat =>
  bvUnsatSpine (Expr.app g x).getAppFn (Expr.app g x).getAppArgs,
  Runs (inferSpine (fueledFns mode env) d tf [] [E, C]) t1,
  Runs ((fueledFns mode env).whnf d t1) (.forallE ty body),
  Runs (inferSpine (fueledFns mode env) d (body.instantiate1 a) [] rest) v

/-- The ∀-telescope loop against `inferBody`'s ∀ tail, as a triple. -/
theorem inferPisC_tail_spec (ih : SSimC mode env f) {d fuel : Nat} {b ty : Expr} {u : Level}
    {s₀ : CState} (hs : CSOK mode env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferPisI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[.fvar d ty] [u]
    ⦃fun r s' => CSOK mode env s' ∧
      Runs (do
        let v ← ensureSort (fueledFns mode env) env (d + 1)
          (← (fueledFns mode env).infer (d + 1) (b.instantiate1 (.fvar d ty)))
        pure (Expr.sort (.imax u v))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferPisC_tail_sim ih hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The λ-telescope loop against `inferBody`'s λ tail, as a triple. -/
theorem inferLamsC_tail_spec (ih : SSimC mode env f) (henv : EnvWF env) {d fuel : Nat}
    {b ty : Expr} {s₀ : CState} (hs : CSOK mode env s₀) (hwty : Expr.WScoped d ty)
    (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ inferLamsI (coreKnotI mode (mkFEnv env) f) d fuel b 1 #[.fvar d ty] [ty]
    ⦃fun r s' => CSOK mode env s' ∧
      Runs (do
        let bt ← (fueledFns mode env).infer (d + 1) (b.instantiate1 (.fvar d ty))
        pure (Expr.forallE ty (bt.abstract1 d))) r ∧ Expr.WScoped d r; ⊤⦄ :=
  (inferLamsC_tail_sim ih henv hs rfl rfl rfl hwty hwb).triple relEC_inv

/-- The cached inference body simulates the specification body; the
application clause through the spine walk and `inferSpine_sound_body`. -/
theorem inferBodyC_spec (ih : SSimC mode env f) (henv : EnvWF env) :
    BodySpec mode env (inferBodyI (coreKnotI mode (mkFEnv env) f) (mkFEnv env))
      (inferBody (fueledFns mode env) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBody, natLitSupportedF_eq, strLitSupportedF_eq,
      mkFEnv_findProj?, constTyOf, ProjEntry.typeAtI_eq,
      toListRev_empty, Option.isSome_some, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyI, peelFuelM, inst1M_spec (mode := mode) (env := env), ih.infer_spec, ih.whnf_spec, ih.defeq_spec,
      ensureSortC_spec ih, constTyAtM_spec (mode := mode) (env := env),
      inferSpineC_spec ih, inferPisC_tail_spec ih, inferLamsC_tail_spec ih henv] <;> finish

/-- Abstracting away the top variable lowers the scope bound. -/
theorem wscoped_abstract1 {d : Nat} {e : Expr} (k : Nat) (h : Expr.WScoped (d + 1) e) :
    Expr.WScoped d (e.abstract1 d k) :=
  ConLeche.WScoped.abstract1 k h
grind_pattern [conleche_grind] wscoped_abstract1 => Expr.WScoped (d + 1) e, e.abstract1 d k

/-- The cached io spine walk's answer is the io application clause's
(`inferSpineIO_sound_body`). -/
theorem Runs.inferBodyIO_app {d : Nat} {g a tf v : Expr}
    (h₁ : Runs ((fueledFns mode env).inferIO d (Expr.app g a).getAppFn) tf)
    (h₂ : Runs (inferSpineIO (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) v) :
    Runs (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d (.app g a)) v := by
  obtain ⟨F, hF⟩ := Runs.bind (f := fun tf =>
    inferSpineIO (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) h₁ h₂
  exact inferSpineIO_sound_body d g a v F hF
grind_pattern [conleche_grind] Runs.inferBodyIO_app =>
  Runs (inferSpineIO (fueledFns mode env) d tf [] (Expr.app g a).getAppArgs) v,
  inferBodyIO (CoreFns.ioView (fueledFns mode env)) env d (.app g a)

/-- The io inference body's walk (task #172 B4).  The leaf and `proj`
arms are `inferBodyI`'s at the io view; the binder and `letE` arms are
the io lane's own chained clauses; the application arm is the io spine
walk (`inferSpineIOI`, no argument check) with
`inferSpineIO_sound_body`. -/
theorem inferBodyIOC_spec (ih : SSimC mode env f) (henv : EnvWF env) :
    BodySpec mode env
      (inferBodyIOI (CoreFnsI.ioView (coreKnotI mode (mkFEnv env) f)) (mkFEnv env))
      (inferBodyIO (CoreFns.ioView (fueledFns mode env)) env) := by
  intro s₀ d i hs hw
  sym only [conleche_grind, inferBodyIO, CoreFns.ioView_infer, CoreFns.ioView_whnf,
      natLitSupportedF_eq, strLitSupportedF_eq, mkFEnv_findProj?, constTyOf,
      ProjEntry.typeAtI_eq, toListRev_empty, Option.isSome_some,
      abstract1C_spec, EnvWF.constTy_closed henv, wscoped_typeAt henv] =>
    vcgen [inferBodyIOI, inferBodyI, abstract1M, ensureSortIOC_spec ih,
      inst1M_spec (mode := mode) (env := env), ih.ioInfer_spec, ih.ioWhnf_spec,
      constTyAtM_spec (mode := mode) (env := env), inferSpineIOC_spec ih] <;> finish

end Walks3

end ConLeche.Cached
