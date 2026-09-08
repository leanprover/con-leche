import ConLeche.Kernel.CoreGated

/-!
# The gated knot's equations and its one changed clause (task #161, S12)

`Verify/Knot.lean` is the ungated knot's equation set; this module is
the **gated** knot's (`ConLeche/Kernel/CoreGated.lean`, the S9 subject).  It
carries exactly three kinds of fact, and the split is the whole point:

* **the shared four** — `whnf`, `infer`, `defeq` and `annotate` are
  *the same bodies* on both knots (`whnfBody`, `inferBody`,
  `defeqBody`, `annotateBody`), tied one fuel down.  Their unfolding
  equations are `rfl`, exactly as on the ungated side, and every
  inversion stated against a body with an abstract `CoreFns` record
  transfers to the gated knot with no new proof;
* **the collapse** (`whnfCoreBodyGated_eq`) — at every subject that is not
  an application, `whnfCoreBodyGated` *is* `whnfCoreBody`.  This is the S9
  seal's "both arms are `whnfCoreBody`'s verbatim" claim mechanized:
  ten constructors, nine of them `rfl`, so the gated lane owes new
  work at the `.app` clause and nowhere else;
* **the one changed clause** (`whnfCoreGated_app_inv`) — `whnf_app_inv`'s
  twin.  The β disjunct's certificate is replaced by a *disjunction*:
  either the gate fired (`mode.verifiedChecks && mb.pw.isNever`) or the
  certificate ran and passed.  Nothing else in the inversion moves;
  the ι and stuck disjuncts are character-for-character the ungated
  ones, because the gate wraps the **test** only.

**The asymmetry fence, at the statement level.**  The projection
clause is *not* gated (`Kernel/CoreGated.lean`'s docstring), so
`whnf_proj_inv`'s gated twin is `whnf_proj_inv` itself modulo the
knot: no certificate the gate skipped is ever reached for, because at
the zero-kind branch the gate does not fire — see
`Model/Steps/Gate.lean` for the P-tier reading of that condition
(`isNever_iff_forall_pwBit_ne_zero`).
-/

namespace ConLeche

variable {mode : CheckMode}

/-! ## The knot equations

`pureFnsGated mode env` is `coreKnotGated mode env`; its `whnf`/`infer`/
`defeq`/`annotate` fields are the shared bodies at the sub-knot, so
all four equations below are `rfl` — the gated lane inherits the
ungated lane's entire body-level inversion apparatus. -/

@[simp] theorem pureFnsGated_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env (f + 1)).whnfCore d e =
      whnfCoreBodyGated mode (pureFnsGated mode env f) env d e := rfl

@[simp] theorem pureFnsGated_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env (f + 1)).whnf d e =
      whnfBody (pureFnsGated mode env f) env d e := rfl

@[simp] theorem pureFnsGated_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env (f + 1)).infer d e =
      inferBody mode (pureFnsGated mode env f) env d e := rfl

@[simp] theorem pureFnsGated_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsGated mode env (f + 1)).defeq d a b =
      defeqBody mode (pureFnsGated mode env f) env d a b := rfl

@[simp] theorem pureFnsGated_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env (f + 1)).annotate d e =
      annotateBody (pureFnsGated mode env f) env d e := rfl

theorem whnfCoreGated_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfCoreGated mode env (f + 1) d e =
      whnfCoreBodyGated mode (pureFnsGated mode env f) env d e := rfl

theorem whnfGated_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfGated mode env (f + 1) d e = whnfBody (pureFnsGated mode env f) env d e := rfl

theorem inferTypeCoreGated_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCoreGated mode env (f + 1) d e =
      inferBody mode (pureFnsGated mode env f) env d e := rfl

theorem isDefEqCoreGated_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCoreGated mode env (f + 1) d a b =
      defeqBody mode (pureFnsGated mode env f) env d a b := rfl

theorem annotateCoreGated_succ (env : Env) (f d : Nat) (e : Expr) :
    annotateCoreGated mode env (f + 1) d e =
      annotateBody (pureFnsGated mode env f) env d e := rfl

theorem whnfCoreGated_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env f).whnfCore d e = whnfCoreGated mode env f d e := rfl

theorem whnfGated_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env f).whnf d e = whnfGated mode env f d e := rfl

theorem inferGated_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env f).infer d e = inferTypeCoreGated mode env f d e := rfl

theorem defeqGated_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsGated mode env f).defeq d a b = isDefEqCoreGated mode env f d a b := rfl

theorem annotateGated_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsGated mode env f).annotate d e = annotateCoreGated mode env f d e := rfl

theorem ensureSortGated_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFnsGated mode env f) env d e = ensureSortCoreGated mode env f d e :=
  rfl

/-- Fuel-zero spellings throw — the gate changes nothing at the base
of the knot, so the four claims' zero cases are the ungated ones. -/
theorem whnfCoreGated_zero (env : Env) (d : Nat) (e : Expr) :
    whnfCoreGated mode env 0 d e =
      throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnfGated_zero (env : Env) (d : Nat) (e : Expr) :
    whnfGated mode env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCoreGated_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCoreGated mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCoreGated_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCoreGated mode env 0 d a b =
      throw (.internal "fuel exhausted: defeq") := rfl

theorem annotateCoreGated_zero (env : Env) (d : Nat) (e : Expr) :
    annotateCoreGated mode env 0 d e =
      throw (.internal "fuel exhausted: annotate") := rfl

/-! ## The collapse: the gate touches one constructor -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **THE COLLAPSE.**  At every subject that is not an application the
gated body *is* the ungated body — the same term, not merely the same
verdict.  Nine of `whnfCoreBodyGated`'s ten clauses were copied verbatim
from `whnfCoreBody` (including the ungated **projection** clause: the
establishment/consumption asymmetry fence), and this is that copy,
checked by the kernel rather than asserted in a docstring. -/
theorem whnfCoreBodyGated_eq (r : CoreFns m) (env : Env) (d : Nat) (e : Expr)
    (hne : ∀ f a, e ≠ .app f a) :
    whnfCoreBodyGated mode r env d e = whnfCoreBody mode r env d e := by
  cases e with
  | app f a => exact absurd rfl (hne f a)
  | sort u => rfl
  | fvar idx ty => rfl
  | forallE ty body bi => rfl
  | lam ty body mb => rfl
  | const n us => rfl
  | lit l => rfl
  | proj sn i pe => rfl
  | letE t v b => rfl
  | bvar i => rfl

/-! ## The one changed clause -/

set_option linter.unusedSimpArgs false in
/-- **`whnf_app_inv`'s gated twin.**  The shape is the ungated one with
a single edit: the β disjunct's certificate premise becomes

    (mode.verifiedChecks && mb.pw.isNever) = true ∨
      ∃ ta, infer a = .ok ta ∧ defeq ta ty = .ok true

— "either the gate fired, or the certificate ran and passed".  The
head reduction, the ι disjunct and the stuck disjunct are the ungated
statement's, verbatim, because the gate wraps the **test** only and
both of its arms are `whnfCoreBody`'s.

The gated disjunct is what a transposed β clause consumes in place of
the certificate: at a fired gate the λ's datum is `.never`, hence
positive at *every* valuation, hence the zero-kind arm — the one that
consumes a certificate — is unreachable (`gate_pwBit_ne_zero`,
`Model/Steps/Gate.lean`).  No obligation reaches for a certificate the
gate skipped; that is the asymmetry fence, discharged.

(The linter option is `Verify/InferLemmas.lean`'s, for the same
reason: the ten-constructor `all_goals` block applies one `simp only`
list to branches that need different subsets of it.) -/
theorem whnfCoreGated_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : whnfCoreGated mode env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f', whnfCoreGated mode env fuel d f = .ok f' ∧
      ((∃ ty body mb, f' = .lam ty body mb ∧
          whnfCoreGated mode env fuel d (body.instantiate1 a) = .ok e' ∧
          ((mode.verifiedChecks && mb.pw.isNever) = true ∨
            ∃ ta, inferTypeCoreGated mode env fuel d a = .ok ta ∧
              isDefEqCoreGated mode env fuel d ta ty = .ok true)) ∨
        (∃ e'', iotaRec mode (pureFnsGated mode env fuel) env d (.app f' a)
            = .ok (some e'') ∧
          whnfCoreGated mode env fuel d e'' = .ok e') ∨
        e' = .app f' a) := by
  rw [whnfCoreGated_succ] at h
  simp only [whnfCoreBodyGated, Bind.bind, Except.bind] at h
  simp only [whnfCoreGated_def, inferGated_def, defeqGated_def] at h
  cases hwf : whnfCoreGated mode env fuel d f with
  | error err => rw [hwf] at h; exact nomatch h
  | ok f' =>
  rw [hwf] at h
  dsimp only at h
  refine ⟨f', rfl, ?_⟩
  match f', h with
  | .lam ty body mb, h => ?_
  | .sort u, h => ?_
  | .fvar i t', h => ?_
  | .const n' us, h => ?_
  | .forallE t' b' m', h => ?_
  | .bvar i, h => ?_
  | .app f'' a'', h => ?_
  | .letE t' v' b', h => ?_
  | .lit l', h => ?_
  | .proj s' i' e'', h => ?_
  case _ =>
    dsimp only at h
    by_cases hg : (mode.verifiedChecks && mb.pw.isNever) = true
    · rw [if_pos hg] at h
      exact Or.inl ⟨ty, body, mb, rfl, h, Or.inl hg⟩
    · rw [if_neg hg] at h
      cases hta : inferTypeCoreGated mode env fuel d a with
      | error err => rw [hta] at h; exact nomatch h
      | ok ta =>
      rw [hta] at h
      dsimp only at h
      cases hde : isDefEqCoreGated mode env fuel d ta ty with
      | error err => rw [hde] at h; exact nomatch h
      | ok bb =>
      rw [hde] at h
      cases bb with
      | true =>
        simp only [if_true] at h
        exact Or.inl ⟨ty, body, mb, rfl, h, Or.inr ⟨ta, rfl, hde⟩⟩
      | false =>
        simp only [Bool.false_eq_true, if_false, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    cases hio : iotaRec mode (pureFnsGated mode env fuel) env d (.app _ a) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
      rw [hio] at h
      dsimp only at h
      cases o with
      | some e'' => exact Or.inr (Or.inl ⟨e'', rfl, h⟩)
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)

end ConLeche
