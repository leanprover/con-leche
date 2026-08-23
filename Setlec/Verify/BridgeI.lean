import Setlec.Verify.DiscI6

/-!
# The interned knot induction

Ties the per-body walks (`Setlec/Verify/DiscI*.lean`) through the memo
wrappers (`Setlec/Verify/SimIKnot.lean`) into the interned conditional
simulation at every fuel: `ssimI` — every interned entry point
(`coreKnotI (mkFEnv env) f`) simulates the pure fueled families under
the denotation, on denoting well-scoped inputs over well-formed
environments.  The entry-point runners' bridges (consumed by
`Setlec/Verify/Bridge.lean` after the executable flip) are stated here
as well.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open EStore Expr

/-- The interned knot simulates the fueled families at every fuel. -/
theorem ssimI (env : Env) (henv : EnvWF env) : ∀ f, SSimI env f
  | 0 => ssimI_zero env
  | f + 1 =>
    { whnfCore := fun hs hden hw =>
        memoEI_whnfCore_sim henv
          (fun hs' hden' hw' =>
            whnfCoreBodyI_sim (ssimI env henv f) henv hs' hden' hw')
          hs hden hw
      whnf := fun hs hden hw =>
        memoEI_whnf_sim henv
          (fun hs' hden' hw' =>
            whnfBodyI_sim (ssimI env henv f) henv hs' hden' hw')
          hs hden hw
      infer := fun hs hden hw =>
        memoEI_infer_sim henv
          (fun hs' hden' hw' =>
            inferBodyI_sim (ssimI env henv f) henv hs' hden' hw')
          hs hden hw
      defeq := fun hs hdena hdenb hwa hwb =>
        memoBI_defeq_sim henv
          (fun hs' hdena' hdenb' hwa' hwb' =>
            defeqBodyI_sim (ssimI env henv f) henv hs' hdena' hdenb'
              hwa' hwb')
          hs hdena hdenb hwa hwb
      annotate := fun hs hden hw =>
        memoEI_annotate_sim henv
          (fun hs' hden' hw' =>
            annotateBodyI_sim (ssimI env henv f) henv hs' hden' hw')
          hs hden hw }

/-! ## Entry runners: from a successful interned run to a pure run

The runners intern the argument into a fresh arena, run the knot, and
read the result back; a successful run is reproduced by the pure
fueled entry point at some fuel. -/

section Runners

variable {env : Env}

private theorem run_inv {α : Type} {c : CheckIM α} {s₀ : IState}
    {v : α} {s' : IState} (h : c.run s₀ = .ok (v, s')) :
    c s₀ = .ok (v, s') := h

/-- Generic unary entry-runner bridge: a successful `runEntryE` is the
readback of a simulated interned run, hence reproduced by the fueled
comparand at some fuel. -/
theorem runEntryE_bridge {pick : CoreFnsI → Nat → EIdx → CheckIM EIdx}
    {pf : FueledM Expr} {d : Nat} {e v : Expr}
    (hsim : ∀ {s₀ : IState} {i : EIdx}, ISOK env s₀ →
      s₀.store.denote i = some e →
      SimAt env s₀ (RelE d)
        (pick (coreKnotI (mkFEnv env) checkFuel) d i) pf)
    (h : runEntryE env pick d e = .ok v) :
    ∃ F, pf.val F = .ok v := by
  unfold runEntryE at h
  rw [EStore.internExprFast_eq empty_wf] at h
  rcases hie : EStore.empty.internExpr e with ⟨i0, st0⟩
  rw [hie] at h
  obtain ⟨hwf0, -, hden0⟩ := internExpr_spec empty_wf e
  rw [hie] at hwf0 hden0
  simp only [Bind.bind, Except.bind] at h
  cases hrun : (pick (coreKnotI (mkFEnv env) checkFuel) d i0).run
      { store := st0 } with
  | error er => rw [hrun] at h; exact nomatch h
  | ok pr =>
    obtain ⟨j, s'⟩ := pr
    rw [hrun] at h
    dsimp only at h
    obtain ⟨hs', hext, vv, ⟨hjd, hwv⟩, F, hF⟩ :=
      hsim (ISOK.fresh env hwf0) hden0 j s' (run_inv hrun)
    rw [readbackI_spec hs'.wf hjd] at h
    obtain rfl : vv = v := by
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h
    exact ⟨F, hF⟩

/-- Binary entry-runner bridge (`isDefEq`). -/
theorem runEntryB_bridge {pf : FueledM Bool} {d : Nat} {a b : Expr}
    {v : Bool}
    (hsim : ∀ {s₀ : IState} {i j : EIdx}, ISOK env s₀ →
      s₀.store.denote i = some a → s₀.store.denote j = some b →
      SimAt env s₀ RelV
        ((coreKnotI (mkFEnv env) checkFuel).defeq d i j) pf)
    (h : runEntryB env d a b = .ok v) :
    ∃ F, pf.val F = .ok v := by
  unfold runEntryB at h
  rw [EStore.internExprFast_eq empty_wf] at h
  rcases hia : EStore.empty.internExpr a with ⟨i0, st1⟩
  rw [hia] at h
  dsimp only at h
  obtain ⟨hwf1, -, hdena⟩ := internExpr_spec empty_wf a
  rw [hia] at hwf1 hdena
  rw [EStore.internExprFast_eq hwf1] at h
  rcases hib : st1.internExpr b with ⟨j0, st2⟩
  rw [hib] at h
  obtain ⟨hwf2, hext2, hdenb⟩ := internExpr_spec hwf1 b
  rw [hib] at hwf2 hext2 hdenb
  simp only [StateT.run'] at h
  cases hrun : ((coreKnotI (mkFEnv env) checkFuel).defeq d i0 j0).run
      { store := st2 } with
  | error er =>
    rw [show ((coreKnotI (mkFEnv env) checkFuel).defeq d i0 j0).run
      { store := st2 } = (coreKnotI (mkFEnv env) checkFuel).defeq d i0 j0
      { store := st2 } from rfl] at hrun
    simp only [Functor.map, StateT.run, hrun, Except.map] at h
    exact nomatch h
  | ok pr =>
    obtain ⟨r, s'⟩ := pr
    obtain ⟨hs', hext, vv, hPv, F, hF⟩ :=
      hsim (ISOK.fresh env hwf2) (denote_mono hext2 hdena) hdenb
        r s' (run_inv hrun)
    obtain rfl : r = vv := hPv
    rw [show ((coreKnotI (mkFEnv env) checkFuel).defeq d i0 j0).run
      { store := st2 } = (coreKnotI (mkFEnv env) checkFuel).defeq d i0 j0
      { store := st2 } from rfl] at hrun
    simp only [Functor.map, StateT.run, hrun, Except.map,
      Except.ok.injEq] at h
    exact h ▸ ⟨F, hF⟩

/-- Sort-entry-runner bridge (`ensureSort`): the interned entry returns
a level index which the runner reads back. -/
theorem runEntryS_bridge {pf : FueledM Level} {d : Nat} {e : Expr}
    {u : Level}
    (hsim : ∀ {s₀ : IState} {i : EIdx}, ISOK env s₀ →
      s₀.store.denote i = some e →
      SimAt env s₀ RelL
        (ensureSortI (coreKnotI (mkFEnv env) checkFuel) d i) pf)
    (h : runEntryS env d e = .ok u) :
    ∃ F, pf.val F = .ok u := by
  unfold runEntryS at h
  rw [EStore.internExprFast_eq empty_wf] at h
  rcases hie : EStore.empty.internExpr e with ⟨i0, st0⟩
  rw [hie] at h
  obtain ⟨hwf0, -, hden0⟩ := internExpr_spec empty_wf e
  rw [hie] at hwf0 hden0
  simp only [Bind.bind, Except.bind] at h
  cases hrun : (ensureSortI (coreKnotI (mkFEnv env) checkFuel) d i0).run
      { store := st0 } with
  | error er =>
    rw [hrun] at h
    exact nomatch h
  | ok pr =>
    obtain ⟨r, s'⟩ := pr
    obtain ⟨hs', hext, vv, hPv, F, hF⟩ :=
      hsim (ISOK.fresh env hwf0) hden0 r s' (run_inv hrun)
    rw [hrun] at h
    dsimp only at h
    rw [readbackL_spec (hPv : s'.store.denoteL r = some vv)] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨F, hF⟩

end Runners

end Setlec
