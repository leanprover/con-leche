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
    ∀ (fuel : Nat), WhnfClaims m φ fuel ∧ DefEqClaims m φ fuel ∧ InferClaims m φ fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ihAll =>
    match fuel with
    | 0 =>
      refine ⟨?_, ?_, ?_⟩
      · intro d e e' ρ h
        exact nomatch h
      · intro d a b ρ h
        exact nomatch h
      · intro d e t ρ h
        exact nomatch h
    | fuel + 1 =>
      obtain ⟨ihw, ihd, ihi⟩ := ihAll fuel (by omega)
      exact ⟨whnf_claims m ihw ihd ihi (fun f hf => ihAll f (by omega)),
        defeq_claims m ihw ihd ihi (fun f hf => ihAll f (by omega)),
        infer_claims m ihw ihd ihi⟩

/-! ## Fuel-generic core soundness lemmas -/

/-- Reduction preserves the interpretation and annotation truthfulness
(explicit fuel). -/
theorem whnfCore_facts (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e e' : Expr} {ρ : Nat → V}
    (h : whnfCore env fuel d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m fuel).1 h hw hb hLb hok ha

/-- Definitional equality identifies interpretations (explicit fuel). -/
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
  (check_sound m fuel).2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab
    hva hvb

/-- Successful inference is sound (explicit fuel). -/
theorem inferTypeCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {e t : Expr} {ρ : Nat → V}
    (h : inferTypeCore env fuel d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m fuel).2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf fuel h hw, this.2⟩

/-- A successful `ensureSortCore` identifies the interpretation of the
type with a universe (explicit fuel). -/
theorem ensureSortCore_sound (m : EnvModel V env) (fuel : Nat) {d : Nat}
    {t : Expr} {u : Level}
    (h : ensureSortCore env fuel d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSortCore at h
  cases hwh : whnfCore env fuel d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnfCore_facts m fuel hwh hw hb hLb hok ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure,
      interpExpr]

/-! ## Fuel-instantiated wrappers -/

/-- Reduction preserves the interpretation and annotation truthfulness. -/
theorem whnf_facts (m : EnvModel V env) {d : Nat} {e e' : Expr} {ρ : Nat → V}
    (h : whnf env d e = .ok e')
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e' :=
  (check_sound m checkFuel).1 h hw hb hLb hok ha

/-- A positive definitional-equality verdict means the interpretations
agree, whenever both are defined. -/
theorem isDefEq_sound (m : EnvModel V env) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : isDefEq env d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb :=
  (check_sound m checkFuel).2.1 h hwa hwb hba hbb hLba hLbb hoka hokb haa hab hva hvb

/-- Successful inference is sound (bundled with syntactic
well-scopedness of the output). -/
theorem inferType_sound (m : EnvModel V env) {d : Nat} {e t : Expr} {ρ : Nat → V}
    (h : inferType env d e = .ok t)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e)
    (hok : FvarsOk V m.val env φ d ρ e) (ha : AnnotOk V m.val env φ d ρ e) :
    (∃ v tv, interpExpr V m.val env φ d ρ e = some v ∧
      interpExpr V m.val env φ d ρ t = some tv ∧ v ∈ˢ tv) ∧
    WScoped d t ∧ AnnotOk V m.val env φ d ρ t :=
  have := (check_sound m checkFuel).2.2 h hw hb hLb hok ha
  ⟨this.1, inferTypeCore_WScoped m.wf checkFuel h hw, this.2⟩

/-- A successful `ensureSort` identifies the interpretation of the type
with a universe. -/
theorem ensureSort_sound (m : EnvModel V env) {d : Nat} {t : Expr} {u : Level}
    (h : ensureSort env d t = .ok u) {ρ : Nat → V}
    (hw : WScoped d t) (hb : t.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded t)
    (hok : FvarsOk V m.val env φ d ρ t) (ha : AnnotOk V m.val env φ d ρ t) :
    interpExpr V m.val env φ d ρ t = some (univ (u.eval φ)) := by
  unfold ensureSort at h
  cases hwh : whnf env d t with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
    rw [hwh] at h
    obtain ⟨hi, -⟩ := whnf_facts m hwh hw hb hLb hok ha
    cases w <;> simp_all [Bind.bind, Except.bind, pure, Except.pure, interpExpr]

end Setlec
