import Lech.Verify.InferLemmas
import Lech.Kernel.CoreP

/-!
# The gated knot's equations and its one changed clause (task #161, S12)

`Verify/Knot.lean` is the ungated knot's equation set; this module is
the **gated** knot's (`Lech/Kernel/CoreP.lean`, the S9 subject).  It
carries exactly three kinds of fact, and the split is the whole point:

* **the shared four** — `whnf`, `infer`, `defeq` and `annotate` are
  *the same bodies* on both knots (`whnfBody`, `inferBody`,
  `defeqBody`, `annotateBody`), tied one fuel down.  Their unfolding
  equations are `rfl`, exactly as on the ungated side, and every
  inversion stated against a body with an abstract `CoreFns` record
  transfers to the gated knot with no new proof;
* **the collapse** (`whnfCoreBodyP_eq`) — at every subject that is not
  an application, `whnfCoreBodyP` *is* `whnfCoreBody`.  This is the S9
  seal's "both arms are `whnfCoreBody`'s verbatim" claim mechanized:
  ten constructors, nine of them `rfl`, so the gated lane owes new
  work at the `.app` clause and nowhere else;
* **the one changed clause** (`whnfCoreP_app_inv`) — `whnf_app_inv`'s
  twin.  The β disjunct's certificate is replaced by a *disjunction*:
  either the gate fired (`mode.verifiedChecks && mb.pw.isNever`) or the
  certificate ran and passed.  Nothing else in the inversion moves;
  the ι and stuck disjuncts are character-for-character the ungated
  ones, because the gate wraps the **test** only.

**The asymmetry fence, at the statement level.**  The projection
clause is *not* gated (`Kernel/CoreP.lean`'s docstring), so
`whnf_proj_inv`'s gated twin is `whnf_proj_inv` itself modulo the
knot: no certificate the gate skipped is ever reached for, because at
the zero-kind branch the gate does not fire — see
`SetP/Step2/GateP.lean` for the P-tier reading of that condition
(`isNever_iff_forall_pwBit_ne_zero`).
-/

namespace Lech

variable {mode : CheckMode}

/-! ## The knot equations

`pureFnsP mode env` is `coreKnotP mode env`; its `whnf`/`infer`/
`defeq`/`annotate` fields are the shared bodies at the sub-knot, so
all four equations below are `rfl` — the gated lane inherits the
ungated lane's entire body-level inversion apparatus. -/

@[simp] theorem pureFnsP_whnfCore (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env (f + 1)).whnfCore d e =
      whnfCoreBodyP mode (pureFnsP mode env f) env d e := rfl

@[simp] theorem pureFnsP_whnf (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env (f + 1)).whnf d e =
      whnfBody (pureFnsP mode env f) env d e := rfl

@[simp] theorem pureFnsP_infer (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env (f + 1)).infer d e =
      inferBody mode (pureFnsP mode env f) env d e := rfl

@[simp] theorem pureFnsP_defeq (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsP mode env (f + 1)).defeq d a b =
      defeqBody mode (pureFnsP mode env f) env d a b := rfl

@[simp] theorem pureFnsP_annotate (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env (f + 1)).annotate d e =
      annotateBody (pureFnsP mode env f) env d e := rfl

theorem whnfCoreP_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfCoreP mode env (f + 1) d e =
      whnfCoreBodyP mode (pureFnsP mode env f) env d e := rfl

theorem whnfP_succ (env : Env) (f d : Nat) (e : Expr) :
    whnfP mode env (f + 1) d e = whnfBody (pureFnsP mode env f) env d e := rfl

theorem inferTypeCoreP_succ (env : Env) (f d : Nat) (e : Expr) :
    inferTypeCoreP mode env (f + 1) d e =
      inferBody mode (pureFnsP mode env f) env d e := rfl

theorem isDefEqCoreP_succ (env : Env) (f d : Nat) (a b : Expr) :
    isDefEqCoreP mode env (f + 1) d a b =
      defeqBody mode (pureFnsP mode env f) env d a b := rfl

theorem annotateCoreP_succ (env : Env) (f d : Nat) (e : Expr) :
    annotateCoreP mode env (f + 1) d e =
      annotateBody (pureFnsP mode env f) env d e := rfl

theorem whnfCoreP_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env f).whnfCore d e = whnfCoreP mode env f d e := rfl

theorem whnfP_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env f).whnf d e = whnfP mode env f d e := rfl

theorem inferP_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env f).infer d e = inferTypeCoreP mode env f d e := rfl

theorem defeqP_def (env : Env) (f d : Nat) (a b : Expr) :
    (pureFnsP mode env f).defeq d a b = isDefEqCoreP mode env f d a b := rfl

theorem annotateP_def (env : Env) (f d : Nat) (e : Expr) :
    (pureFnsP mode env f).annotate d e = annotateCoreP mode env f d e := rfl

theorem ensureSortP_def (env : Env) (f d : Nat) (e : Expr) :
    ensureSort (pureFnsP mode env f) env d e = ensureSortCoreP mode env f d e :=
  rfl

/-- Fuel-zero spellings throw — the gate changes nothing at the base
of the knot, so the four claims' zero cases are the ungated ones. -/
theorem whnfCoreP_zero (env : Env) (d : Nat) (e : Expr) :
    whnfCoreP mode env 0 d e =
      throw (.internal "fuel exhausted: whnfCore") := rfl

theorem whnfP_zero (env : Env) (d : Nat) (e : Expr) :
    whnfP mode env 0 d e = throw (.internal "fuel exhausted: whnf") := rfl

theorem inferTypeCoreP_zero (env : Env) (d : Nat) (e : Expr) :
    inferTypeCoreP mode env 0 d e =
      throw (.internal "fuel exhausted: infer") := rfl

theorem isDefEqCoreP_zero (env : Env) (d : Nat) (a b : Expr) :
    isDefEqCoreP mode env 0 d a b =
      throw (.internal "fuel exhausted: defeq") := rfl

theorem annotateCoreP_zero (env : Env) (d : Nat) (e : Expr) :
    annotateCoreP mode env 0 d e =
      throw (.internal "fuel exhausted: annotate") := rfl

/-! ## The collapse: the gate touches one constructor -/

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- **THE COLLAPSE.**  At every subject that is not an application the
gated body *is* the ungated body — the same term, not merely the same
verdict.  Nine of `whnfCoreBodyP`'s ten clauses were copied verbatim
from `whnfCoreBody` (including the ungated **projection** clause: the
establishment/consumption asymmetry fence), and this is that copy,
checked by the kernel rather than asserted in a docstring. -/
theorem whnfCoreBodyP_eq (r : CoreFns m) (env : Env) (d : Nat) (e : Expr)
    (hne : ∀ f a, e ≠ .app f a) :
    whnfCoreBodyP mode r env d e = whnfCoreBody mode r env d e := by
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
`SetP/Step2/GateP.lean`).  No obligation reaches for a certificate the
gate skipped; that is the asymmetry fence, discharged.

(The linter option is `Verify/InferLemmas.lean`'s, for the same
reason: the ten-constructor `all_goals` block applies one `simp only`
list to branches that need different subsets of it.) -/
theorem whnfCoreP_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : whnfCoreP mode env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f', whnfCoreP mode env fuel d f = .ok f' ∧
      ((∃ n ty body mb, f' = .lam ty body mb ∧
          whnfCoreP mode env fuel d (body.instantiate1 a) = .ok e' ∧
          ((mode.verifiedChecks && mb.pw.isNever) = true ∨
            ∃ ta, inferTypeCoreP mode env fuel d a = .ok ta ∧
              isDefEqCoreP mode env fuel d ta ty = .ok true)) ∨
        (∃ e'', iotaRec mode (pureFnsP mode env fuel) env d (.app f' a)
            = .ok (some e'') ∧
          whnfCoreP mode env fuel d e'' = .ok e') ∨
        e' = .app f' a) := by
  rw [whnfCoreP_succ] at h
  simp only [whnfCoreBodyP, Bind.bind, Except.bind] at h
  simp only [whnfCoreP_def, inferP_def, defeqP_def] at h
  cases hwf : whnfCoreP mode env fuel d f with
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
      exact Or.inl ⟨n, ty, body, mb, rfl, h, Or.inl hg⟩
    · rw [if_neg hg] at h
      cases hta : inferTypeCoreP mode env fuel d a with
      | error err => rw [hta] at h; exact nomatch h
      | ok ta =>
      rw [hta] at h
      dsimp only at h
      cases hde : isDefEqCoreP mode env fuel d ta ty with
      | error err => rw [hde] at h; exact nomatch h
      | ok bb =>
      rw [hde] at h
      cases bb with
      | true =>
        simp only [if_true] at h
        exact Or.inl ⟨n, ty, body, mb, rfl, h, Or.inr ⟨ta, rfl, hde⟩⟩
      | false =>
        simp only [Bool.false_eq_true, if_false, pure, Except.pure,
          Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)
  all_goals
    try simp only [Bind.bind, Except.bind] at h
    cases hio : iotaRec mode (pureFnsP mode env fuel) env d (.app _ a) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
      rw [hio] at h
      dsimp only at h
      cases o with
      | some e'' => exact Or.inr (Or.inl ⟨e'', rfl, h⟩)
      | none =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inr (Or.inr h.symm)

end Lech
