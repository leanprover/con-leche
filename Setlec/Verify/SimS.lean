import Setlec.Verify.BridgeDecl
import Setlec.Kernel.CheckerS

/-!
# Shared-state checker: the per-declaration faithfulness kit (task #51)

The interned-core simulation (`ISOK`/`SimAt`, `Setlec/Verify/SimI.lean`,
knotted in `Setlec/Verify/BridgeI.lean`) is stated for *arbitrary*
initial states, so extending the cache lifetime from one entry call to
one declaration needs no new state invariant: this file provides

* `mkFEnv_push` — the index of a cons-extended environment is one
  insert, so the incremental index the shared drivers maintain *is*
  `mkFEnv` of the current environment (definitional);
* `flushS_isok` — after a flush the state satisfies `ISOK` for *any*
  environment (the arena is environment-independent: `ISOK.fresh` needs
  only `EStore.WF`, which mentions no environment) — this is what makes
  the driver-directed flush at environment transitions sound;
* the shared entry-point simulation lemmas (`opE_*_sim`, `opB_sim`,
  `opS_sim`): a successful shared-state operation run from any `ISOK`
  state preserves the invariant and is reproduced by the pure fueled
  family — the per-declaration analog of `runEntry*_bridge`, keeping
  the final state facts instead of discarding them.

The driver-level walks composing these along `checkDeclSF` are in
`Setlec/Verify/BridgeS*.lean`.
-/

namespace Setlec

open EStore Expr

/-! ## The incremental index -/

/-- Pushing onto the index is `mkFEnv` of the cons-extended
environment (the `foldr` build peels its head). -/
theorem mkFEnv_push (env : Env) (ci : ConstantInfo) :
    (mkFEnv env).push ci = mkFEnv ⟨ci :: env.consts⟩ := rfl

/-! ## Flush -/

/-- `flushS` drops exactly the environment-dependent caches. -/
theorem flushS_run (s : IState) :
    flushS s = .ok ((), s.flushed) := rfl

/-- After a flush the invariant holds for *any* environment: the
surviving components are the environment-free residue (`ISOKF`), the
dropped caches' clauses are vacuous. -/
theorem flushS_isok {env' : Env} {s : IState} (hs : ISOKF s) :
    ISOK env' s.flushed := by
  refine ⟨hs.wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.lsimp, hs.lnz,
    hs.eqv, hs.ienv⟩ <;>
    (intros; simp_all [IState.flushed])

/-! ## Shared entry points simulate the fueled families -/

/-- The result relation for the shared expression-valued entry points:
equal values, well-scoped at the call depth (the scopedness of
intermediate results feeds the later call sites of a walk). -/
def RelW (d : Nat) (_s : IState) (v w : Expr) : Prop :=
  v = w ∧ WScoped d v

section Runners

variable {env : Env} {s₀ : IState}

private theorem fueledM_bind_pure {α : Type} (x : FueledM α) :
    x >>= pure = x := by
  refine Subtype.ext (funext fun F => ?_)
  show x.val F >>= pure = x.val F
  cases x.val F <;> rfl

/-- Generic unary shared-runner simulation: intern into the ambient
arena, run the simulated knot entry, read back. -/
theorem opE_sim {pick : CoreFnsI → Nat → EIdx → CheckIM EIdx}
    {pf : FueledM Expr} {d : Nat} {e : Expr}
    (hsim : ∀ {s₁ : IState} {i : EIdx}, ISOK env s₁ →
      s₁.store.denote i = some e →
      SimAt env s₁ (RelE d)
        (pick (coreKnotI (mkFEnv env) checkFuel) d i) pf)
    (hs : ISOK env s₀) :
    SimAt env s₀ (RelW d) (opE (mkFEnv env) pick d e) pf := by
  rw [← fueledM_bind_pure pf]
  show SimAt env s₀ (RelW d)
    (internExprM e >>= fun i =>
      pick (coreKnotI (mkFEnv env) checkFuel) d i >>= fun j =>
      withStore (fun st => st.readbackI j) >>= fun ro =>
      match ro with
      | some v => pure v
      | none => throw (.internal "interned readback failed"))
    (pf >>= pure)
  refine SimAt.bind_left (internExprM_eff hs e)
    (fun s₁ i hs₁ hext₁ hden => ?_)
  refine SimAt.bind (hsim hs₁ hden) (fun s₂ j w hs₂ hext₂ hP => ?_)
  refine SimAt.withStore ?_
  rw [readbackI_spec hs₂.wf hP.1]
  exact SimAt.pure hs₂ ⟨rfl, hP.2⟩

/-- Shared `annotate` simulates the fueled family, from any invariant
state. -/
theorem opE_annotate_sim (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : ISOK env s₀) (hw : WScoped d e) :
    SimAt env s₀ (RelW d) (opE (mkFEnv env) (·.annotate) d e)
      (fueledOpsM.annotate env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimI env henv checkFuel).annotate hs₁ hden hw) hs

/-- Shared `inferType` simulates the fueled family. -/
theorem opE_infer_sim (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : ISOK env s₀) (hw : WScoped d e) :
    SimAt env s₀ (RelW d) (opE (mkFEnv env) (·.infer) d e)
      (fueledOpsM.inferType env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimI env henv checkFuel).infer hs₁ hden hw) hs

/-- Shared `whnf` simulates the fueled family. -/
theorem opE_whnf_sim (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : ISOK env s₀) (hw : WScoped d e) :
    SimAt env s₀ (RelW d) (opE (mkFEnv env) (·.whnf) d e)
      (fueledOpsM.whnf env d e) :=
  opE_sim (fun hs₁ hden =>
    (ssimI env henv checkFuel).whnf hs₁ hden hw) hs

/-- Shared `isDefEq` simulates the fueled family. -/
theorem opB_sim (henv : EnvWF env) {d : Nat} {a b : Expr}
    (hs : ISOK env s₀) (hwa : WScoped d a) (hwb : WScoped d b) :
    SimAt env s₀ RelV (opB (mkFEnv env) d a b)
      (fueledOpsM.isDefEq env d a b) := by
  show SimAt env s₀ RelV
    (internExprM a >>= fun i => internExprM b >>= fun j =>
      (coreKnotI (mkFEnv env) checkFuel).defeq d i j)
    (fueledOpsM.isDefEq env d a b)
  refine SimAt.bind_left (internExprM_eff hs a)
    (fun s₁ i hs₁ hext₁ hdena => ?_)
  refine SimAt.bind_left (internExprM_eff hs₁ b)
    (fun s₂ j hs₂ hext₂ hdenb => ?_)
  exact (ssimI env henv checkFuel).defeq hs₂ (denote_mono hext₂ hdena)
    hdenb hwa hwb

/-- Shared `ensureSort` simulates the fueled family. -/
theorem opS_sim (henv : EnvWF env) {d : Nat} {e : Expr}
    (hs : ISOK env s₀) (hw : WScoped d e) :
    SimAt env s₀ RelV (opS (mkFEnv env) d e)
      (fueledOpsM.ensureSort env d e) := by
  have h1 : SimAt env s₀ RelV (opS (mkFEnv env) d e)
      (ensureSort (fueledFns env) env d e >>= pure) := by
    show SimAt env s₀ RelV
      (internExprM e >>= fun i =>
        ensureSortI (coreKnotI (mkFEnv env) checkFuel) d i >>= fun u =>
        readbackLevelM u)
      (ensureSort (fueledFns env) env d e >>= pure)
    refine SimAt.bind_left (internExprM_eff hs e)
      (fun s₁ i hs₁ hext₁ hden => ?_)
    refine SimAt.bind
      (ensureSortI_sim (ssimI env henv checkFuel) hs₁ hden hw)
      (fun s₂ u lu hs₂ hext₂ hPu => ?_)
    exact SimAt.of_eff (readbackLevelM_eff hs₂
      (hPu : s₂.store.denoteL u = some lu)) lu (fun s r hQ => hQ)
  refine SimAt.wr h1 (fun u F h => ⟨F, ?_⟩)
  rw [FueledM.atF_bind] at h
  simp only [Bind.bind] at h
  cases hx : (ensureSort (fueledFns env) env d e).val F with
  | error er =>
    rw [hx] at h
    exact nomatch h
  | ok v =>
    rw [hx] at h
    dsimp only [Except.bind] at h
    obtain rfl : v = u := by
      simpa [pure, Except.pure] using h
    rw [ensureSort_atF, ensureSort_def] at hx
    exact hx

end Runners

end Setlec
