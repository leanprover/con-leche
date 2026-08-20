import Setlec.Model.Core.Infer

/-!
# Soundness of the type checker functions

All statements are relative to a model `m : EnvModel V env` of the current
environment and interpret with `m.val`.  Reduction, definitional equality
and inference are mutually recursive on a shared fuel (the beta rule
certifies possibly-Prop redexes by inference + defeq), so their soundness
is one mutual fuel induction, `check_sound`:

* whnf claims: reduction preserves the interpretation and annotation
  truthfulness (delta via `m.defn_eq`; beta via the substitution lemma,
  `SetTheory.app_lam`, and — for the guarded path — the proof-point
  axioms; the certified path gets `⟦a⟧ ∈ ⟦ty⟧` from the runtime check).
* defeq claims: a positive verdict means the interpretations agree
  whenever both are defined.
* infer claims: a successful inference means expression and type are
  interpreted and `⟦e⟧ ∈ ⟦t⟧`, and the inferred type carries truthful
  annotations.

The `*_sound` wrappers at the end instantiate the fuel.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-- The mutual soundness induction; see the module docstring. -/
theorem check_sound (m : EnvModel V env) :
    ∀ (fuel : Nat), WhnfCoreClaims m φ fuel ∧ WhnfClaims m φ fuel ∧
      DefEqClaims m φ fuel ∧ InferClaims m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d e e' ρ h
      rw [whnfCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e e' ρ h
      rw [whnf_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d a b ρ h
      rw [isDefEqCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    · intro d e t ρ h
      rw [inferTypeCore_zero] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi⟩ := ih
    exact ⟨whnfCore_claims m ihwc ihw ihd ihi,
      whnfLoop_claims m ihwc ihw,
      defeq_claims m ihw ihd ihi,
      infer_claims m ihw ihd ihi⟩

/-! ## Fuel-generic soundness lemmas -/

/-- Head normalization (no delta) preserves the interpretation and
annotation truthfulness. -/
theorem whnfCore_facts (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e e' : Expr} {ρ : Nat → V}
    (h : whnfCore env fuel d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m fuel).1 h hw hb hLb hok ha

/-- The reduction loop preserves the interpretation and annotation
truthfulness. -/
theorem whnf_facts (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e e' : Expr} {ρ : Nat → V}
    (h : whnf env fuel d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m fuel).2.1 h hw hb hLb hok ha

/-- Definitional equality identifies interpretations. -/
theorem isDefEqCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {a b : Expr} {ρ : Nat → V}
    (h : isDefEqCore env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  (check_sound m fuel).2.2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab
    hva hvb

/-- Successful inference is sound (bundled with syntactic
well-scopedness of the output). -/
theorem inferTypeCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e t : Expr} {ρ : Nat → V}
    (h : inferTypeCore env fuel d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m fuel).2.2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf fuel h hw, this.2⟩

/-- A successful `ensureSortCore` identifies the interpretation of the
type with a universe. -/
theorem ensureSortCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {t : Expr} {u : Level}
    (h : ensureSortCore env fuel d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSortCore ensureSort at h
  simp only [whnf_def, Bind.bind, Except.bind] at h
  cases hwh : whnf env fuel d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnf_facts m fuel hwh hw hb hLb hok ha
    cases w <;> simp_all [pure, Except.pure, interpExpr, throw, throwThe,
      MonadExceptOf.throw]

end Setlec
