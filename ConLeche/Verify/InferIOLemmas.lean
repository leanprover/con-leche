module

public import ConLeche.Verify.InferLemmas

public section

/-!
# Inversion lemmas for the io lane (task #161, stage 2)

`ConLeche/Kernel/CoreIO.lean`'s `inferBodyIO` is `inferBody` with one
clause changed, so its inversions are the `InferLemmas` ones with the
recursive `infer` runs read at the io lane (`inferTypeCoreIO`) and the
`whnf`/`defeq`/`ensureSort` runs read at the **full** lane — the io
knot is a leaf lane, so its reduction fields *are* the full knot's
(`pureFnsIO_whnf` &c., `Verify/Knot.lean`).

The rest of the file completes the set: the λ, application, `letE`
and projection inversions, the λ→∀ meta copy, and the literal-clause
run transfer.  The application rule's inversion is the one clause
whose *shape* differs: the io lane does not check the argument
(official `infer_app` at `infer_only`), so the inversion has no
certificate conjunct.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode} {eager : Bool}

/-- Inversion for the ∀-rule of the io lane.  Compare
`inferTypeCore_forall_inv`: the clause is `inferBody`'s verbatim, so
the only deltas are the lane of the two recursive inferences and the
lane-folding rewrites. -/
theorem inferTypeCoreIO_forall_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr}
    (h : inferTypeCoreIO mode eager env (fuel + 1) d (.forallE ty body)
      = .ok t) :
    ∃ tty u bt v, inferTypeCoreIO mode eager env fuel d ty = .ok tty ∧
      whnf mode eager env fuel d tty = .ok (.sort u) ∧
      inferTypeCoreIO mode eager env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      ensureSortCore mode eager env fuel (d + 1) bt = .ok v ∧
      t = .sort (.imax u v) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def] at h
  try dsimp only at h
  cases hty : inferTypeCoreIO mode eager env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hwt : whnf mode eager env fuel d tty with
  | error err => rw [hwt] at h; exact nomatch h
  | ok w =>
  rw [hwt] at h
  dsimp only at h
  revert h
  match w with
  | .sort u => ?_
  | .bvar _ | .fvar _ _ | .const _ _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCoreIO mode eager env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases hes : ensureSortCore mode eager env fuel (d + 1) bt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v =>
  rw [hes] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes, h.symm⟩

/-- Inversion for the λ-rule of the io lane: the body at the io lane,
and no domain-sort run (official `infer_lambda` at `infer_only`). -/
theorem inferTypeCoreIO_lam_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr}
    (h : inferTypeCoreIO mode eager env (fuel + 1) d (.lam ty body)
      = .ok t) :
    ∃ bt,
      inferTypeCoreIO mode eager env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      t = .forallE ty (bt.abstract1 d) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def] at h
  cases hbt : inferTypeCoreIO mode eager env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  simp only [Except.ok.injEq] at h
  exact ⟨bt, rfl, h.symm⟩

/-- **Inversion for the application rule of the io lane** (official
`infer_app` at `infer_only`, task #346): the function's type reduces to a
∀ and the result is its body at the argument; the argument is not
checked. -/
theorem inferTypeCoreIO_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCoreIO mode eager env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf ty' body', inferTypeCoreIO mode eager env fuel d f = .ok tf ∧
      whnf mode eager env fuel d tf = .ok (.forallE ty' body') ∧
      t = body'.instantiate1 a := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf] at h
  cases htf : inferTypeCoreIO mode eager env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnf mode eager env fuel d tf with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  match w, h with
  | .forallE ty' body', h =>
    simp only [Except.ok.injEq] at h
    exact ⟨tf, ty', body', rfl, hw, h.symm⟩
  | .sort u, h => exact nomatch h
  | .fvar i t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam t2 b2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h

/-- The let-rule of the io lane (official `infer_let` at `infer_only`,
task #342 R-C): the body's type at the value, neither the type nor the
value checked. -/
theorem inferTypeCoreIO_letE_inv {env : Env} {fuel d : Nat}
    {ty v b t : Expr}
    (h : inferTypeCoreIO mode eager env (fuel + 1) d (.letE ty v b)
      = .ok t) :
    inferTypeCoreIO mode eager env fuel d (b.instantiate1 v) = .ok t := by
  rw [inferTypeCoreIO_succ] at h
  simpa [inferBodyIO, inferIO_def] using h

/-- Inversion for the projection rule of the io lane
(`inferTypeCore_proj_inv`'s twin: the scrutinee's inference at the io
lane, the reduction at the full one). -/
theorem inferTypeCoreIO_proj_inv {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e t : Expr}
    (h : inferTypeCoreIO mode eager env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ tpe te T us entry,
      inferTypeCoreIO mode eager env fuel d e = .ok tpe ∧
      whnf mode eager env fuel d tpe = .ok te ∧
      te.getAppFn = .const T us ∧
      env.findProj? T i = some entry ∧
      te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length ∧
      -- the official `infer_proj` restriction (task #175 W4c/O4), as in
      -- `inferTypeCore_proj_inv`
      ((Level.isEquiv entry.structSort .zero == some true) = true →
        (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true) = true) ∧
      (t = entry.typeAt us te.getAppArgs e ∧
       -- task #175 wiring W5: the node's struct name is the head's
       T = sn) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf] at h
  cases hte : inferTypeCoreIO mode eager env fuel d e with
  | error err => rw [hte] at h; exact nomatch h
  | ok tpe =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode eager env fuel d tpe with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam t2 b2 => intro h; exact nomatch h
  | forallE t2 b2 => intro h; exact nomatch h
  | letE t2 v2 b2 => intro h; exact nomatch h
  | lit l2 => intro h; exact nomatch h
  | proj s2 i2 e2 => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  cases hfp : env.findProj? T i with
  | none => intro h; exact nomatch h
  | some entry => ?_
  intro h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hcond =>
    obtain ⟨hsn, hlen, hus⟩ := hcond
    -- the Prop guard (task #175 W4c/O4), then the residual walk's
    -- result
    have hg : (Level.isEquiv entry.structSort .zero == some true) = true →
        (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true) = true := by
      intro hp
      rw [ite_eq_left hp] at h
      by_cases hf : (Level.isEquiv
          (Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true) = true
      · exact hf
      · rw [ite_eq_right hf] at h
        exact absurd h (by
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
    have h' : (pure (entry.typeAt us te.getAppArgs e) : Except CheckError Expr) = .ok t := by
      by_cases hp : (Level.isEquiv entry.structSort .zero == some true) = true
      · rw [ite_eq_left hp, ite_eq_left (hg hp)] at h
        exact h
      · rw [ite_eq_right hp] at h
        exact h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hlen, hus,
      hg, h'.symm, hsn⟩

/-- **The literal clauses are lane-independent**: neither recurses, so
the io run *is* the full run — the io twins of the two literal claims
are the full claims applied across this equation. -/
theorem inferTypeCoreIO_lit_eq {env : Env} {fuel d : Nat} {l : Literal} :
    inferTypeCoreIO mode eager env (fuel + 1) d (.lit l) =
      inferTypeCore mode eager env (fuel + 1) d (.lit l) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  cases l <;> rfl

/-! ## The three remaining lane-independent shapes (task #172, B3)

`inferTypeCoreIO_lit_eq` is one instance of a small family, and the
io bridge (`ConLeche/Verify/Rules/InferBridge.lean`) wants the rest of it: a
clause that never touches `r` is the *same clause* in both bodies, so
the io statement about it is the full statement transported across an
equation rather than a re-proof.  Four of the eleven `inferBody`
shapes are of that kind — `.sort`, `.fvar`, `.const` and `.lit` — and
`.bvar` is a fifth that both lanes reject.  The equations below are
each `rfl` after one unfolding on each side, which is the mechanical
content of "the io grade narrows the application clause and nothing
else" at the leaves. -/

/-- `.sort` is lane-independent (no recursive run). -/
theorem inferTypeCoreIO_sort_eq {env : Env} {fuel d : Nat} {u : Level} :
    inferTypeCoreIO mode eager env (fuel + 1) d (.sort u) =
      inferTypeCore mode eager env (fuel + 1) d (.sort u) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.fvar` is lane-independent (the stored annotation, no run). -/
theorem inferTypeCoreIO_fvar_eq {env : Env} {fuel d idx : Nat}
    {ty : Expr} :
    inferTypeCoreIO mode eager env (fuel + 1) d (.fvar idx ty) =
      inferTypeCore mode eager env (fuel + 1) d (.fvar idx ty) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.const` is lane-independent (the stored type, no run). -/
theorem inferTypeCoreIO_const_eq {env : Env} {fuel d : Nat} {n : Name}
    {us : List Level} :
    inferTypeCoreIO mode eager env (fuel + 1) d (.const n us) =
      inferTypeCore mode eager env (fuel + 1) d (.const n us) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

end ConLeche
