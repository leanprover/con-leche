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

namespace ConLeche

variable {mode : CheckMode}

/-- Inversion for the ∀-rule of the io lane.  Compare
`inferTypeCore_forall_inv`: the clause is `inferBody`'s verbatim, so
the only deltas are the lane of the two recursive inferences and the
lane-folding rewrites.  The stored annotation is validated here exactly
as in the full lane — the io grade narrows the application clause and
nothing else. -/
theorem inferTypeCoreIO_forall_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.forallE ty body m)
      = .ok t) :
    ∃ tty u bt v, inferTypeCoreIO mode env fuel d ty = .ok tty ∧
      whnf mode env fuel d tty = .ok (.sort u) ∧
      inferTypeCoreIO mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      ensureSortCore mode env fuel (d + 1) bt = .ok v ∧
      (mode.verifiedChecks = true → Level.zeronessOf v = m.pw) ∧
      t = .sort (.imax u v) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
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
  | .bvar _ | .fvar _ _ | .const _ _ | .app _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  intro h
  dsimp only at h
  cases hbt : inferTypeCoreIO mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  cases hes : ensureSortCore mode env fuel (d + 1) bt with
  | error err => rw [hes] at h; exact nomatch h
  | ok v =>
  rw [hes] at h
  dsimp only at h
  by_cases hv : mode.verifiedChecks = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes,
      fun hv' => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  by_cases hz : (Level.zeronessOf v == m.pw) = true
  · rw [if_pos hz] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tty, u, bt, v, rfl, hwt, rfl, hes, fun _ => eq_of_beq hz, h.symm⟩
  · rw [if_neg hz] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Inversion for the λ-rule of the io lane — `inferTypeCore_lam_inv`
with the recursive inferences at the io lane and the codomain-sort
run packaged as its `ensureSortCore` spelling (consumers reach the
whnf form through `ensureSortCore_inv`, as the ∀ clause does).  The
validation block is verbatim: the io grade narrows the application
clause and nothing else. -/
theorem inferTypeCoreIO_lam_inv {env : Env} {fuel d : Nat}
    {ty body t : Expr} {m : BinderMeta}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.lam ty body m)
      = .ok t) :
    ∃ bt,
      inferTypeCoreIO mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) = .ok bt ∧
      (mode.verifiedChecks = true → body.isLam = false → ∃ btt v,
        inferTypeCoreIO mode env fuel (d + 1) bt = .ok btt ∧
        ensureSortCore mode env fuel (d + 1) btt = .ok v ∧
        Level.zeronessOf v = m.pw) ∧
      (mode.verifiedChecks = true → ∀ pwI, body.lamPw = some pwI →
        m.pw = pwI) ∧
      t = .forallE ty (bt.abstract1 d) m := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
    Except.bind] at h
  simp only [inferIO_def, pureFnsIO_whnf, ensureSortIO_def] at h
  cases hbt : inferTypeCoreIO mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty)) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok bt =>
  rw [hbt] at h
  dsimp only at h
  by_cases hv : mode.verifiedChecks = true
  case neg =>
    rw [if_neg hv] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨bt, rfl,
      fun hv' _ => absurd hv' hv,
      fun hv' _ _ => absurd hv' hv, h.symm⟩
  rw [if_pos hv] at h
  revert h
  match body with
  | .lam tyI bI mbI =>
    intro h
    simp only [Expr.lamPw] at h
    by_cases hpw : (m.pw == mbI.pw) = true
    · rw [if_pos hpw] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨bt, rfl, ?_, ?_, h.symm⟩
      · intro _ hlam; simp [Expr.isLam] at hlam
      · intro _ pwI heq
        try simp only [Expr.lamPw, Option.some.injEq] at heq
        first
          | (cases heq; exact eq_of_beq hpw)
          | (rw [← heq]; exact eq_of_beq hpw)
          | (injection heq with heq; rw [← heq]; exact eq_of_beq hpw)
    · rw [if_neg hpw] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .forallE _ _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ =>
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
    by_cases hz : (Level.zeronessOf v == m.pw) = true
    · rw [if_pos hz] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨bt, rfl,
        fun _ _ => ⟨btt, v, hbtt, hes, eq_of_beq hz⟩, ?_, h.symm⟩
      intro _ pwI heq
      first
        | exact nomatch heq
        | simp [Expr.lamPw] at heq
    · rw [if_neg hz] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **Inversion for the application rule of the io lane** — the frozen
statement (DESIGN.md, "THE IO LICENSE BATCH"), with the licence ruling
of 2026-09-06 applied.  The certificate conjunct is a disjunction:
either the licence fired (`m'.pw.isNever`), or the argument's io
inference and the conversion check ran and passed.

The gated arm used to carry a `mode.verifiedChecks` conjunct as well.
It went with the site's: the licensing theorem
(`io_domain_transfer`, `Model/IOLicense.lean`) spends only
`pwBit_ne_zero_of_isNever`, i.e. the **datum**, and never the mode —
so the conjunct was never a premise anything needed, and carrying it
made the trusted mode run a certificate the verified mode skips. -/
theorem inferTypeCoreIO_app_inv {env : Env} {fuel d : Nat} {f a t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.app f a) = .ok t) :
    ∃ tf ty' body' m', inferTypeCoreIO mode env fuel d f = .ok tf ∧
      whnf mode env fuel d tf = .ok (.forallE ty' body' m') ∧
      t = body'.instantiate1 a ∧
      (m'.pw.isNever = true ∨
        ∃ ta, inferTypeCoreIO mode env fuel d a = .ok ta ∧
          isDefEqCore mode env fuel d ta ty' = .ok true) := by
  rw [inferTypeCoreIO_succ] at h
  simp only [inferBodyIO, pure, Except.pure, Bind.bind,
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
  | .forallE ty' body' m', h => ?_
  | .sort u, h => exact nomatch h
  | .fvar i t2, h => exact nomatch h
  | .const n2 us, h => exact nomatch h
  | .lam t2 b2 m2, h => exact nomatch h
  | .bvar i, h => exact nomatch h
  | .app f2 a2, h => exact nomatch h
  | .letE t2 v2 b2, h => exact nomatch h
  | .lit l2, h => exact nomatch h
  | .proj s2 i2 e2, h => exact nomatch h
  dsimp only at h
  by_cases hg : m'.pw.isNever = true
  · rw [if_pos hg] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨tf, ty', body', m', rfl, hw, h.symm, Or.inl hg⟩
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
      exact ⟨tf, ty', body', m', rfl, hw, h.symm,
        Or.inr ⟨ta, rfl, hde⟩⟩

/-- The let-rule of the io lane is **unreachable** (task #241), like
`inferTypeCore_letE_inv`'s: the arm is a positive `.internal` error. -/
theorem inferTypeCoreIO_letE_inv {env : Env} {fuel d : Nat}
    {ty v b t : Expr}
    (h : inferTypeCoreIO mode env (fuel + 1) d (.letE ty v b)
      = .ok t) :
    False := by
  rw [inferTypeCoreIO_succ] at h
  simp [inferBodyIO, throw, throwThe, MonadExceptOf.throw] at h

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
  | fvar i2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam t2 b2 m2 => intro h; exact nomatch h
  | forallE t2 b2 m2 => intro h; exact nomatch h
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
      rw [if_pos hp] at h
      by_cases hf : (Level.isEquiv
          (Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true) = true
      · exact hf
      · rw [if_neg hf] at h
        exact absurd h (by
          simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind])
    have h' : (pure (entry.typeAt us te.getAppArgs e) : Except CheckError Expr) = .ok t := by
      by_cases hp : (Level.isEquiv entry.structSort .zero == some true) = true
      · rw [if_pos hp, if_pos (hg hp)] at h
        exact h
      · rw [if_neg hp] at h
        exact h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    exact ⟨tpe, te, T, us, entry, rfl, hw, hfn, hfp, hlen, hus,
      hg, h'.symm, hsn⟩

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
    inferTypeCoreIO mode env (fuel + 1) d (.sort u) =
      inferTypeCore mode env (fuel + 1) d (.sort u) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.fvar` is lane-independent (the stored annotation, no run). -/
theorem inferTypeCoreIO_fvar_eq {env : Env} {fuel d idx : Nat}
    {ty : Expr} :
    inferTypeCoreIO mode env (fuel + 1) d (.fvar idx ty) =
      inferTypeCore mode env (fuel + 1) d (.fvar idx ty) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

/-- `.const` is lane-independent (the stored type, no run). -/
theorem inferTypeCoreIO_const_eq {env : Env} {fuel d : Nat} {n : Name}
    {us : List Level} :
    inferTypeCoreIO mode env (fuel + 1) d (.const n us) =
      inferTypeCore mode env (fuel + 1) d (.const n us) := by
  rw [inferTypeCoreIO_succ, inferTypeCore_succ]
  rfl

end ConLeche
