import Setlec.Verify.InferLemmas

/-!
# Inversion lemmas for the io lane (task #161, stage 2)

`Setlec/Kernel/CoreIO.lean`'s `inferBodyIO` is `inferBody` with one
clause changed, so its inversions are the `InferLemmas` ones with the
recursive `infer` runs read at the io lane (`inferTypeCoreIO`) and the
`whnf`/`defeq`/`ensureSort` runs read at the **full** lane — the io
knot is a leaf lane, so its reduction fields *are* the full knot's
(`pureFnsIO_whnf` &c., `Verify/Knot.lean`).

Only the clauses the campaign's first worked example needs are here:
the ∀ binder rule.  The application rule's inversion — the one clause
whose *shape* differs, because the certificate is behind the gate — is
batch B2's, together with the mathematics it feeds.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

/-- Inversion for the ∀-rule of the io lane.  Compare
`inferTypeCore_forall_inv`: the clause is `inferBody`'s verbatim, so
the only deltas are the lane of the two recursive inferences and the
lane-folding rewrites.  The stored annotation is validated here exactly
as in the full lane — the io grade narrows the application clause and
nothing else. -/
theorem inferTypeCoreIO_forall_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.forallE n ty body m)
      = .ok t) :
    ∃ tty u bt v, inferTypeCoreIO mode env fuel d ty = .ok tty ∧
      whnf mode env fuel d tty = .ok (.sort u) ∧
      inferTypeCoreIO mode env fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      ensureSortCore mode env fuel (d + 1) bt = .ok v ∧
      (mode.verified = true → (Level.zeronessOf v).equiv m.pw = true) ∧
      t = .sort (.imax u v) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def] at h
  try dsimp only at h
  cases hty : inferTypeCoreIO mode env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnf mode env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  revert h
  match w with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ _ | .const _ _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCoreIO mode env fuel (d + 1)
      (body.instantiate1 (.fvar d n ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases hes : ensureSortCore mode env fuel (d + 1) bt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v =>
  rw [hes] at h
  dsimp only at h
  by_cases hv : mode.verified = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes,
      fun hv' => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  by_cases hz : (Level.zeronessOf v).equiv m.pw = true
  · rw [if_pos hz] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes, fun _ => hz, h.symm⟩
  · rw [if_neg hz] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

end Setlec
