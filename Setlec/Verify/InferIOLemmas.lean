import Setlec.Verify.InferLemmas

/-!
# Inversion lemmas for the io lane (task #161, stage 2)

`Setlec/Kernel/CoreIO.lean`'s `inferBodyIO` is `inferBody` with one
clause changed, so its inversions are the `InferLemmas` ones with the
recursive `infer` runs read at the io lane (`inferTypeCoreIO`) and the
`whnf`/`defeq`/`ensureSort` runs read at the **full** lane — the io
knot is a leaf lane, so its reduction fields *are* the full knot's
(`pureFnsIO_whnf` &c., `Verify/Knot.lean`).

The io-license batch completes the set: the λ, application, `letE`
and projection inversions, the λ→∀ meta copy, and the literal-clause
run transfer.  The application rule's inversion is the one clause
whose *shape* differs — the per-argument certificate sits behind the
gate, so its conjunct is a **disjunction**: either the mode's gate
fired at a `.never` binder, or the certificate ran and passed.  This
is `whnf_app_inv`'s β-gate pattern at the infer tier, and it is what
keeps the inversion mode-generic and true at every mode.
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

/-- Inversion for the λ-rule of the io lane — `inferTypeCore_lam_inv`
with the recursive inferences at the io lane and the codomain-sort
run packaged as its `ensureSortCore` spelling (consumers reach the
whnf form through `ensureSortCore_inv`, as the ∀ clause does).  The
validation block is verbatim: the io grade narrows the application
clause and nothing else. -/
theorem inferTypeCoreIO_lam_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.lam n ty body m)
      = .ok t) :
    ∃ tty u bt,
      inferTypeCoreIO mode env fuel d ty = .ok tty ∧
      whnf mode env fuel d tty = .ok (.sort u) ∧
      inferTypeCoreIO mode env fuel (d + 1)
        (body.instantiate1 (.fvar d n ty)) = .ok bt ∧
      (mode.verified = true → body.isLam = false → ∃ btt v,
        inferTypeCoreIO mode env fuel (d + 1) bt = .ok btt ∧
        ensureSortCore mode env fuel (d + 1) btt = .ok v ∧
        (Level.zeronessOf v).equiv m.pw = true) ∧
      (mode.verified = true → ∀ pwI, body.lamPw = some pwI →
        m.pw.equiv pwI = true) ∧
      t = .forallE n ty (bt.abstract1 d) m := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def] at h
  cases htty : inferTypeCoreIO mode env fuel d ty with
  | error err => rw [htty] at h; exact nomatch h
  | ok tty =>
  rw [htty] at h
  dsimp only at h
  cases hwtty : whnf mode env fuel d tty with
  | error err => rw [hwtty] at h; exact nomatch h
  | ok wtty =>
  rw [hwtty] at h
  dsimp only at h
  revert h
  match wtty with
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
  by_cases hv : mode.verified = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, rfl, hwtty, rfl,
      fun hv' _ => absurd hv' hv,
      fun hv' _ _ => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  revert h
  match body with
  | .lam nI tyI bI mbI =>
    intro h
    simp only [Expr.lamPw] at h
    by_cases hpw : m.pw.equiv mbI.pw = true
    · rw [if_pos hpw] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨tty, u, bt, rfl, hwtty, rfl, ?_, ?_, h.symm⟩
      · intro _ hlam; simp [Expr.isLam] at hlam
      · intro _ pwI heq
        try simp only [Expr.lamPw, Option.some.injEq] at heq
        first
          | (cases heq; exact hpw)
          | (rw [← heq]; exact hpw)
          | (injection heq with heq; rw [← heq]; exact hpw)
    · rw [if_neg hpw] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _ | .app _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h
    simp only [Expr.lamPw] at h
    revert h
    cases hbtt : inferTypeCoreIO mode env fuel (d + 1) bt with
    | error err => intro h; exact nomatch h
    | ok btt => ?_
    dsimp only
    cases hes : ensureSortCore mode env fuel (d + 1) btt with
    | error err => intro h; exact nomatch h
    | ok v => ?_
    intro h
    dsimp only at h
    by_cases hz : (Level.zeronessOf v).equiv m.pw = true
    · rw [if_pos hz] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨tty, u, bt, rfl, hwtty, rfl,
        fun _ _ => ⟨btt, v, hbtt, hes, hz⟩, ?_, h.symm⟩
      intro _ pwI heq
      first
        | exact nomatch heq
        | simp [Expr.lamPw] at heq
    · rw [if_neg hz] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The λ→∀ meta copy at the io lane (`infer_lam_meta_copy`'s twin):
the type the io lane returns for a λ is a `∀` carrying the λ's own
binder meta — annotation included. -/
theorem inferIO_lam_meta_copy {env : Env} {fuel d : Nat} {n : Name}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.lam n ty body m)
      = .ok t) :
    ∃ bt, t = .forallE n ty bt m := by
  obtain ⟨tty, u, bt, -, -, -, -, -, ht⟩ := inferTypeCoreIO_lam_inv h
  exact ⟨bt.abstract1 d, ht⟩

/-- **Inversion for the application rule of the io lane** — the frozen
statement (DESIGN.md, "THE IO LICENSE BATCH").  The certificate
conjunct is a disjunction: either the gate fired
(`mode.verified && m'.pw.isNever`), or the argument's io inference and
the conversion check ran and passed.  Consumers of the gated arm hold
the mode conjunct exactly where the licensing theorems
(`io_domain_transfer`, `SetP/IOLicenseP.lean`) need it. -/
theorem inferTypeCoreIO_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m', inferTypeCoreIO mode env fuel d f = .ok tf ∧
      whnf mode env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      t = body'.instantiate1 a ∧
      ((mode.verified && m'.pw.isNever) = true ∨
        ∃ ta, inferTypeCoreIO mode env fuel d a = .ok ta ∧
          isDefEqCore mode env fuel d ta ty' = .ok true) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, pureFnsIO_defeq] at h
  cases htf : inferTypeCoreIO mode env fuel d f with
  | error err => rw [htf] at h; exact nomatch h
  | ok tf =>
  rw [htf] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tf with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
  rw [hw] at h
  dsimp only at h
  match w, h with
  | .forallE n' ty' body' m', h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i n2 t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam n2 t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE n2 t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  by_cases hg : (mode.verified && m'.pw.isNever) = true
  · rw [if_pos hg] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, n', ty', body', m', rfl, hw, h.symm, Or.inl hg⟩
  · rw [if_neg hg] at h
    try simp only [Bind.bind, Except.bind] at h
    try dsimp only at h
    cases hta : inferTypeCoreIO mode env fuel d a with
    | error err => rw [hta] at h; exact nomatch h
    | ok ta =>
    rw [hta] at h
    dsimp only at h
    cases hde : isDefEqCore mode env fuel d ta ty' with
    | error err => rw [hde] at h; exact nomatch h
    | ok r =>
    rw [hde] at h
    cases r with
    | false => simp [throw, throwThe, MonadExceptOf.throw] at h
    | true =>
      simp only [if_true, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨tf, n', ty', body', m', rfl, hw, h.symm,
        Or.inr ⟨ta, rfl, hde⟩⟩

/-- Inversion for the let-rule of the io lane
(`inferTypeCore_letE_inv`'s twin: the three inferences at the io lane,
the sort/conversion runs at the full one). -/
theorem inferTypeCoreIO_letE_inv {env : Env} {fuel d : Nat} {n : Name}
    {ty v b t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.letE n ty v b)
      = .ok t) :
    ∃ tty s tv, inferTypeCoreIO mode env fuel d ty = .ok tty ∧
      ensureSortCore mode env fuel d tty = .ok s ∧
      inferTypeCoreIO mode env fuel d v = .ok tv ∧
      isDefEqCore mode env fuel d tv ty = .ok true ∧
      inferTypeCoreIO mode env fuel d (b.instantiate1 v) = .ok t := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, pureFnsIO_defeq,
    ensureSortIO_def] at h
  cases hty : inferTypeCoreIO mode env fuel d ty with
  | error err => rw [hty] at h; exact nomatch h
  | ok tty =>
  rw [hty] at h
  dsimp only at h
  cases hes : ensureSortCore mode env fuel d tty with
  | error err => rw [hes] at h; exact nomatch h
  | ok s =>
  rw [hes] at h
  dsimp only at h
  cases htv : inferTypeCoreIO mode env fuel d v with
  | error err => rw [htv] at h; exact nomatch h
  | ok tv =>
  rw [htv] at h
  dsimp only at h
  cases hde : isDefEqCore mode env fuel d tv ty with
  | error err => rw [hde] at h; exact nomatch h
  | ok r =>
  rw [hde] at h
  cases r with
  | false => simp [throw, throwThe, MonadExceptOf.throw] at h
  | true =>
    simp only [↓reduceIte] at h
    exact ⟨tty, s, tv, rfl, hes, rfl, hde, h⟩

/-- Inversion for the projection rule of the io lane
(`inferTypeCore_proj_inv`'s twin: the scrutinee's inference at the io
lane, the reduction at the full one). -/
theorem inferTypeCoreIO_proj_inv {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.proj sn i e) = .ok t) :
    ∃ tpe te T us entry,
      inferTypeCoreIO mode env fuel d e = .ok tpe ∧
      whnf mode env fuel d tpe = .ok te ∧
      te.getAppFn = .const T us ∧
      env.findProj? T i = some entry ∧ entry.native = true ∧
      te.getAppArgs.length = entry.numParams ∧
      us.length = entry.levelParams.length ∧
      (∃ A B, te.getAppArgs = [A, B] ∧
        ((i = 0 ∧ t = A) ∨ (i = 1 ∧ t = .app B (.proj T 0 e)))) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf] at h
  cases hte : inferTypeCoreIO mode env fuel d e with
  | error err => rw [hte] at h; exact nomatch h
  | ok tpe =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tpe with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 n2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam n2 t2 b2 m2 => intro h; exact nomatch h
  | forallE n2 t2 b2 m2 => intro h; exact nomatch h
  | letE n2 t2 v2 b2 => intro h; exact nomatch h
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
    obtain ⟨hnat, hlen, hus⟩ := hcond
    revert h
    match hargs : te.getAppArgs, i with
    | [A, B], 0 => ?_
    | [A, B], 1 => ?_
    | [], _ => intro h; exact nomatch h
    | [_], _ => intro h; exact nomatch h
    | _ :: _ :: _ :: _, _ => intro h; exact nomatch h
    | [_, _], _ + 2 => intro h; exact nomatch h
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
        A, B, hargs, Or.inl ⟨rfl, rfl⟩⟩
    · intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
        A, B, hargs, Or.inr ⟨rfl, rfl⟩⟩

/-- **The literal clauses are lane-independent**: neither recurses, so
the io run *is* the full run — the io twins of the two literal claims
are the full claims applied across this equation. -/
theorem inferTypeCoreIO_lit_eq {env : Env} {fuel d : Nat} {l : Literal} :
    inferTypeCoreIO mode env (fuel + 1) d (.lit l) =
      inferTypeCore mode env (fuel + 1) d (.lit l) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  cases l <;> rfl

/-! ## The three remaining lane-independent shapes (task #172, B3)

`inferTypeCoreIO_lit_eq` is one instance of a small family, and the
io reads walk (`SetP/Step2/ReadsIOP.lean`) wants the rest of it: a
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
    inferTypeCoreIO mode env (fuel + 1) d (.sort u) =
      inferTypeCore mode env (fuel + 1) d (.sort u) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.fvar` is lane-independent (the stored annotation, no run). -/
theorem inferTypeCoreIO_fvar_eq {env : Env} {fuel d idx : Nat}
    {n : Name} {ty : Expr} :
    inferTypeCoreIO mode env (fuel + 1) d (.fvar idx n ty) =
      inferTypeCore mode env (fuel + 1) d (.fvar idx n ty) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.const` is lane-independent (the stored type, no run). -/
theorem inferTypeCoreIO_const_eq {env : Env} {fuel d : Nat} {n : Name}
    {us : List Level} :
    inferTypeCoreIO mode env (fuel + 1) d (.const n us) =
      inferTypeCore mode env (fuel + 1) d (.const n us) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

end Setlec
