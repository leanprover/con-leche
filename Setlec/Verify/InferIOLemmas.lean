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

/-- **Fuel monotonicity for the io leaf lane** (task #172 B4): the
leaf knot's auxiliary slots are the full knot's (monotone by
`pureFns_mono`), and both infer slots are `inferBodyIO` over the
smaller leaf knot — `inferBodyIO_mono` closes the induction. -/
theorem pureFnsIO_mono (env : Env) : ∀ {f f' : Nat}, f ≤ f' →
    FnsRefines (pureFnsIO mode env f) (pureFnsIO mode env f')
  | 0, _, _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d e v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
    · intro d e v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
    · intro d e v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
    · intro d a b v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
    · intro d e v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
    · intro d e v hv
      simp [pureFnsIO, coreKnotIO, throw, throwThe,
        MonadExceptOf.throw] at hv
  | f + 1, f' + 1, hle => by
    have ih := pureFnsIO_mono env (Nat.le_of_succ_le_succ hle)
    have ihfull := pureFns_mono (mode := mode) env hle
    exact ⟨fun d e => ihfull.1 d e, fun d e => ihfull.2.1 d e,
      fun d e => inferBodyIO_mono ih d e,
      fun d a b => ihfull.2.2.2.1 d a b,
      fun d e => ihfull.2.2.2.2.1 d e,
      fun d e => inferBodyIO_mono ih d e⟩

theorem inferTypeCoreIO_mono {env : Env} {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {e r : Expr}
    (h : inferTypeCoreIO mode env f d e = .ok r) :
    inferTypeCoreIO mode env f' d e = .ok r :=
  (pureFnsIO_mono env hle).2.2.1 d e r h

/-- `inferTypeCoreIO_app_inv` with all runs re-levelled to the outer
fuel (`inferTypeCore_app_inv'`'s io twin). -/
theorem inferTypeCoreIO_app_inv' {env : Env} {fuel d : Nat}
    {f a t : Expr}
    (h : inferTypeCoreIO mode env fuel d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m', inferTypeCoreIO mode env fuel d f = .ok tf ∧
      whnf mode env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      t = body'.instantiate1 a ∧
      ((mode.verified && m'.pw.isNever) = true ∨
        ∃ ta, inferTypeCoreIO mode env fuel d a = .ok ta ∧
          isDefEqCore mode env fuel d ta ty' = .ok true) := by
  match fuel, h with
  | 0, h => rw [inferTypeCoreIO_zero] at h; exact nomatch h
  | fuel + 1, h =>
    obtain ⟨tf, n', ty', body', m', h1, h2, h3, hd⟩ :=
      inferTypeCoreIO_app_inv h
    refine ⟨tf, n', ty', body', m',
      inferTypeCoreIO_mono (Nat.le_succ _) h1,
      whnf_mono (Nat.le_succ _) h2, h3, ?_⟩
    rcases hd with hd | ⟨ta, h4, h5⟩
    · exact Or.inl hd
    · exact Or.inr ⟨ta, inferTypeCoreIO_mono (Nat.le_succ _) h4,
        isDefEqCore_mono (Nat.le_succ _) h5⟩

/-- Inversion for the constant rule of the io lane — the clause is the
full lane's verbatim. -/
theorem inferTypeCoreIO_const_inv {env : Env} {fuel d : Nat}
    {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCoreIO mode env fuel d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us := by
  match fuel, h with
  | 0, h => rw [inferTypeCoreIO_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [inferTypeCoreIO_succ] at h
    simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
      Bind.bind, Except.bind] at h
    revert h
    cases hf : env.find? n with
    | none =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    | some ci =>
      intro h
      dsimp only at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨ci, rfl, h.symm⟩
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h

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
      ((entry.tower = false →
        ∃ A B, te.getAppArgs = [A, B] ∧
          ((i = 0 ∧ t = A) ∨ (i = 1 ∧ t = .app B (.proj T 0 e)))) ∧
       (entry.tower = true →
        ∃ ds, Expr.instPisAt (te.getAppArgs ++ [e])
            (entry.ty.instantiateLevelParams entry.levelParams us)
          = some (ds, t))) := by
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
    by_cases htw : entry.tower = true
    · rw [if_pos htw] at h
      revert h
      cases hpi : Expr.instPisAt (te.getAppArgs ++ [e])
          (entry.ty.instantiateLevelParams entry.levelParams us) with
      | none => intro h; exact nomatch h
      | some q =>
        obtain ⟨ds, resid⟩ := q
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
          fun hf => absurd htw (by simp [hf]), fun _ => ⟨ds, hpi⟩⟩
    · rw [if_neg htw] at h
      have htw' : entry.tower = false := by
        cases hv : entry.tower
        · rfl
        · exact absurd hv htw
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
          fun _ => ⟨A, B, hargs, Or.inl ⟨rfl, rfl⟩⟩,
          fun ht => absurd ht (by simp [htw'])⟩
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hnat, hlen, hus,
          fun _ => ⟨A, B, hargs, Or.inr ⟨rfl, rfl⟩⟩,
          fun ht => absurd ht (by simp [htw'])⟩

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


/-! ## The full→io weakening (task #172 B4 — the interned short-bridge)

A successful full-grade inference is a successful io-grade inference
with the same value: the io lane runs a *subset* of the full lane's
checks and computes the same result at every clause.  This is the
mathematical core of the cross-memo "peek" future option (task #170's
memo ruling records it as an option, not a runtime device); here it
discharges the retiring interned core's io simulation clause — that
core's io slot deliberately stays at full grade (the interned
short-bridge, DESIGN.md B4 seal). -/

theorem inferTypeCoreIO_of_full {env : Env} :
    ∀ {fuel d : Nat} {e t : Expr},
      inferTypeCore mode env fuel d e = .ok t →
      inferTypeCoreIO mode env fuel d e = .ok t
  | 0, d, e, t, h => by
    rw [inferTypeCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, e, t, h => by
    match e with
    | .sort u => rw [inferTypeCoreIO_sort_eq]; exact h
    | .fvar idx n ty => rw [inferTypeCoreIO_fvar_eq]; exact h
    | .const n us => rw [inferTypeCoreIO_const_eq]; exact h
    | .lit l => rw [inferTypeCoreIO_lit_eq]; exact h
    | .bvar i =>
      rw [inferTypeCore_succ] at h
      simp [inferBody, viewM, Expr.view, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind, pure,
        Except.pure] at h
    | .forallE n ty body mb =>
      obtain ⟨tty, u, bt, v, hty, hwt, hbt, hes, hval, rfl⟩ :=
        inferTypeCore_forall_inv h
      rw [inferTypeCoreIO_succ]
      simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
        Bind.bind, Except.bind]
      simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def]
      rw [inferTypeCoreIO_of_full hty]
      dsimp only
      rw [hwt]
      dsimp only
      rw [inferTypeCoreIO_of_full hbt]
      dsimp only
      rw [hes]
      dsimp only
      cases hv : mode.verified with
      | false => simp [hv]
      | true => simp [hv, hval hv]
    | .lam n ty body mb =>
      obtain ⟨tty, u, bt, hty, hwt, hbt, hleaf, hchain, rfl⟩ :=
        inferTypeCore_lam_inv h
      rw [inferTypeCoreIO_succ]
      simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
        Bind.bind, Except.bind]
      simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def]
      rw [inferTypeCoreIO_of_full hty]
      dsimp only
      rw [hwt]
      dsimp only
      rw [inferTypeCoreIO_of_full hbt]
      dsimp only
      cases hv : mode.verified with
      | false => simp [hv]
      | true =>
        simp only [hv, if_true]
        cases hlp : body.lamPw with
        | some pwI =>
          simp [hchain hv pwI hlp]
        | none =>
          obtain ⟨btt, vb, hbtt, hesb, heqv⟩ :=
            hleaf hv (by
              cases hb : body.isLam
              · rfl
              · exact absurd hlp (by
                  cases body <;> simp_all [Expr.isLam, Expr.lamPw]))
          have hbtt' : inferTypeCoreIO mode env fuel (d + 1) bt
              = .ok btt := by
            cases hgb : mode.betaGate with
            | false =>
              rw [inferTypeIO_off hgb] at hbtt
              exact inferTypeCoreIO_of_full hbtt
            | true =>
              rw [inferTypeIO_on hgb] at hbtt
              exact hbtt
          rw [hbtt']
          dsimp only
          have hesb' : ensureSortCore mode env fuel (d + 1) btt
              = .ok vb := by
            show ((pureFns mode env fuel).whnf (d + 1) btt >>= fun w =>
              match w with
              | .sort u => pure u
              | _ => throw (.invalid "expected a sort")) = .ok vb
            rw [show (pureFns mode env fuel).whnf (d + 1) btt =
              whnf mode env fuel (d + 1) btt from rfl, hesb]
            rfl
          rw [hesb']
          dsimp only
          simp [heqv]
    | .app f a =>
      obtain ⟨tf, n', ty', body', m', htf, hw, rfl, ta, hta, hde⟩ :=
        inferTypeCore_app_inv h
      rw [inferTypeCoreIO_succ]
      simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
        Bind.bind, Except.bind]
      simp only [inferIO_def, pureFnsIO_whnf, pureFnsIO_defeq]
      rw [inferTypeCoreIO_of_full htf]
      dsimp only
      rw [hw]
      dsimp only
      by_cases hg2 : (mode.verified && m'.pw.isNever) = true
      · simp [hg2]
      · simp only [hg2, Bool.false_eq_true, if_false]
        rw [inferTypeCoreIO_of_full hta]
        dsimp only
        rw [hde]
        simp
    | .letE n ty v b =>
      obtain ⟨tty, sv, tv, hty, hes, htv, hde, htail⟩ :=
        inferTypeCore_letE_inv h
      rw [inferTypeCoreIO_succ]
      simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
        Bind.bind, Except.bind]
      simp only [inferIO_def, pureFnsIO_whnf, pureFnsIO_defeq,
        ensureSortIO_def]
      rw [inferTypeCoreIO_of_full hty]
      dsimp only
      rw [hes]
      dsimp only
      rw [inferTypeCoreIO_of_full htv]
      dsimp only
      rw [hde]
      simp only [if_true, ↓reduceIte]
      exact inferTypeCoreIO_of_full htail
    | .proj sn i pe =>
      obtain ⟨tpe, te, T, us, entry, htpe, hwte, hfn, hfe, hnat,
        hlenArgs, hlenUs, hpair, htow⟩ :=
        Setlec.inferTypeCore_proj_inv h
      rw [inferTypeCoreIO_succ]
      simp only [inferBodyIO, viewM, Expr.view, pure, Except.pure,
        Bind.bind, Except.bind]
      simp only [inferIO_def, pureFnsIO_whnf]
      rw [inferTypeCoreIO_of_full htpe]
      dsimp only
      rw [hwte]
      dsimp only
      rw [hfn]
      dsimp only
      rw [hfe]
      dsimp only
      rw [if_pos ⟨hnat, hlenArgs, hlenUs⟩]
      cases htw : entry.tower with
      | false =>
        obtain ⟨A, B, hAB, hcase⟩ := hpair htw
        rw [if_neg (by simp [htw]), hAB]
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
      | true =>
        obtain ⟨ds, hpi⟩ := htow htw
        rw [if_pos rfl, hpi]

/-- The weakening at the knot's io slot: at any mode, a full-grade
success is an io-slot success with the same value (gate-off: the slot
IS the full lane; gate-on: `inferTypeCoreIO_of_full`). -/
theorem inferTypeIO_of_full {env : Env} {fuel d : Nat} {e t : Expr}
    (h : inferTypeCore mode env fuel d e = .ok t) :
    inferTypeIO mode env fuel d e = .ok t := by
  cases hg : mode.betaGate with
  | false => rw [inferTypeIO_off hg]; exact h
  | true => rw [inferTypeIO_on hg]; exact inferTypeCoreIO_of_full h

/-- A slot success is a leaf-lane success: at the gated mode they are
the same lane; at a gate-off mode the slot is the full lane and the
weakening applies. -/
theorem inferTypeCoreIO_of_slot {env : Env} {fuel d : Nat} {e t : Expr}
    (h : inferTypeIO mode env fuel d e = .ok t) :
    inferTypeCoreIO mode env fuel d e = .ok t := by
  cases hg : mode.betaGate with
  | false =>
    rw [inferTypeIO_off hg] at h
    exact inferTypeCoreIO_of_full h
  | true =>
    rw [inferTypeIO_on hg] at h
    exact h


end Setlec
