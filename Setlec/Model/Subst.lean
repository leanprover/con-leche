import Setlec.Model.AnnotOkLemmas
import Setlec.Verify.Subst

/-!
# The substitution lemma

Substituting a term `a` for the top free variable corresponds to
contracting the valuation (`delV`) at the variable's index — the
model-side of beta reduction.  With the structural (annotation-reading)
interpretation this is a mechanical induction; no typing metatheory is
involved (see DESIGN.md).

`interp_beta`/`AnnotOk_beta` package the equation in the form the
`whnf`-beta soundness case consumes: opening a binder with the argument
directly equals opening with a fresh variable valued at `⟦a⟧`.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory Expr

/-- Remove index `p` from a valuation (inverse of `insV`). -/
def delV (ρ : Nat → V) (p : Nat) : Nat → V := fun i => if i < p then ρ i else ρ (i + 1)

omit [SetTheory V] in
theorem delV_updV {ρ : Nat → V} {p D : Nat} {x : V} (hpd : p ≤ D) :
    updV V (delV ρ p) D x = delV (updV V ρ (D + 1) x) p := by
  funext i
  simp only [delV, updV]
  grind

/-- Depth-lifting: a `p`-scoped term interprets the same at any depth
`≥ p`, under any valuation agreeing below `p`. -/
theorem interp_lift {p : Nat} {e : Expr} (hw : WScoped p e) :
    ∀ (D : Nat), p ≤ D → ∀ (ρ ρ' : Nat → V), (∀ i, i < p → ρ' i = ρ i) →
      interpExpr V cval env φ D ρ' e = interpExpr V cval env φ p ρ e := by
  intro D
  induction D with
  | zero =>
    intro hpD ρ ρ' hag
    have hp : p = 0 := by omega
    subst hp
    exact interp_ext e hag hw.fvarsBelow
  | succ D ih =>
    intro hpD ρ ρ' hag
    by_cases hpD' : p = D + 1
    · subst hpD'
      exact interp_ext e hag hw.fvarsBelow
    · have hpD2 : p ≤ D := by omega
      have hupd : updV V ρ' D (ρ' D) = ρ' := by
        funext i
        simp only [updV]
        split <;> simp_all
      rw [← hupd, interp_weaken_top (hw.mono hpD2)]
      exact ih hpD2 ρ ρ' hag

/-- Depth-lifting for annotation truthfulness. -/
theorem AnnotOk.lift {p : Nat} {e : Expr} (hw : WScoped p e) :
    ∀ (D : Nat), p ≤ D → ∀ (ρ ρ' : Nat → V), (∀ i, i < p → ρ' i = ρ i) →
      AnnotOk V cval env φ p ρ e → AnnotOk V cval env φ D ρ' e := by
  intro D
  induction D with
  | zero =>
    intro hpD ρ ρ' hag hA
    have hp : p = 0 := by omega
    subst hp
    exact AnnotOk.ext e (fun i hi => (hag i hi).symm) hw.fvarsBelow hA
  | succ D ih =>
    intro hpD ρ ρ' hag hA
    by_cases hpD' : p = D + 1
    · subst hpD'
      exact AnnotOk.ext e (fun i hi => (hag i hi).symm) hw.fvarsBelow hA
    · have hpD2 : p ≤ D := by omega
      have hupd : updV V ρ' D (ρ' D) = ρ' := by
        funext i
        simp only [updV]
        split <;> simp_all
      rw [← hupd]
      exact AnnotOk.weaken_top (hw.mono hpD2) (ih hpD2 ρ ρ' hag hA)

/-- The substitution lemma: substituting `a` for `fvar p` corresponds to
contracting the valuation at `p`, provided `ρ'` values `p` at `⟦a⟧`. -/
theorem interp_substFvarAt {p : Nat} {a : Expr} {va : V}
    (hwa : WScoped p a) (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (D : Nat), p ≤ D → ∀ (ρ' : Nat → V), ρ' p = va →
      interpExpr V cval env φ p ρ' a = some va →
      interpExpr V cval env φ D (delV ρ' p) (substFvarAt p a e) =
        interpExpr V cval env φ (D + 1) ρ' e
  | .bvar i, D, hpD, ρ', hva, ha => by simp [substFvarAt, interpExpr]
  | .sort u, D, hpD, ρ', hva, ha => by simp [substFvarAt, interpExpr]
  | .const n us, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
  | .fvar idx n ty, D, hpD, ρ', hva, ha => by
    by_cases h1 : idx = p
    · simp only [substFvarAt, if_pos h1]
      rw [interp_lift hwa D hpD ρ' (delV ρ' p) (fun i hi => by simp [delV, hi]), ha]
      simp [interpExpr, h1, hva]
    · by_cases h2 : idx > p
      · simp only [substFvarAt, if_neg h1, if_pos h2]
        simp only [interpExpr, delV]
        have h3 : ¬ (idx - 1 < p) := by omega
        have h4 : idx - 1 + 1 = idx := by omega
        rw [if_neg h3, h4]
      · simp only [substFvarAt, if_neg h1, if_neg h2]
        simp only [interpExpr, delV]
        have h3 : idx < p := by omega
        rw [if_pos h3]
  | .forallE n ty body m, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
    rw [interp_substFvarAt hwa hba ty D hpD ρ' hva ha]
    cases hty : interpExpr V cval env φ (D + 1) ρ' ty with
    | none => rfl
    | some A =>
      simp only [Option.some.injEq]
      congr 1
      funext x
      rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
      rw [interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) x)
        (show updV V ρ' (D + 1) x p = va by
          simp only [updV]; rw [if_neg (by omega)]; exact hva)
        (show interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va by
          rw [interp_ext a (fun i hi => by
            simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
          exact ha)]
  | .lam n ty body m, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
    rw [interp_substFvarAt hwa hba ty D hpD ρ' hva ha]
    cases hty : interpExpr V cval env φ (D + 1) ρ' ty with
    | none => rfl
    | some A =>
      simp only [Option.some.injEq]
      congr 1
      funext x
      rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
      rw [interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) x)
        (show updV V ρ' (D + 1) x p = va by
          simp only [updV]; rw [if_neg (by omega)]; exact hva)
        (show interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va by
          rw [interp_ext a (fun i hi => by
            simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
          exact ha)]
  | .app f b, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
    rw [interp_substFvarAt hwa hba f D hpD ρ' hva ha,
      interp_substFvarAt hwa hba b D hpD ρ' hva ha]
  | .letE n ty val body, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
    rw [interp_substFvarAt hwa hba val D hpD ρ' hva ha]
    cases hval : interpExpr V cval env φ (D + 1) ρ' val with
    | none => rfl
    | some xv =>
      simp only []
      rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
      rw [interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty))
        (D + 1) (by omega) (updV V ρ' (D + 1) xv)
        (show updV V ρ' (D + 1) xv p = va by
          simp only [updV]; rw [if_neg (by omega)]; exact hva)
        (show interpExpr V cval env φ p (updV V ρ' (D + 1) xv) a = some va by
          rw [interp_ext a (fun i hi => by
            simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
          exact ha)]
  | .lit l, D, hpD, ρ', hva, ha => by cases l <;> simp [substFvarAt, interpExpr]
  | .proj s i e, D, hpD, ρ', hva, ha => by
    simp only [substFvarAt, interpExpr]
    rw [interp_substFvarAt hwa hba e D hpD ρ' hva ha]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Beta, interpretation side: opening a binder body with the argument
directly equals opening with a fresh variable valued at `⟦a⟧`. -/
theorem interp_beta {d : Nat} {n : Name} {ty body a : Expr} {ρ : Nat → V} {va : V}
    (hfb : fvarsBelow d body) (hwa : WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (ha : interpExpr V cval env φ d ρ a = some va) (k : Nat) :
    interpExpr V cval env φ d ρ (body.instantiate1 a k) =
      interpExpr V cval env φ (d + 1) (updV V ρ d va)
        (body.instantiate1 (.fvar d n ty) k) := by
  have hva : updV V ρ d va d = va := by simp [updV]
  have ha' : interpExpr V cval env φ d (updV V ρ d va) a = some va := by
    rw [interp_ext a (fun i hi => by
      simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
    exact ha
  have h := interp_substFvarAt (p := d) hwa hba
    (body.instantiate1 (.fvar d n ty) k) d (Nat.le_refl d)
    (updV V ρ d va) hva ha'
  rw [substFvarAt_instantiate1_self body k hfb] at h
  rw [← h]
  exact interp_ext _ (fun i hi => by
      simp only [delV, updV]
      rw [if_pos hi, if_neg (by omega)])
    (fvarsBelow_instantiate1_gen hwa.fvarsBelow k hfb)

/-- The substitution lemma for annotation truthfulness. -/
theorem AnnotOk.substFvarAt {p : Nat} {a : Expr} {va : V}
    (hwa : WScoped p a) (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (D : Nat), p ≤ D → ∀ (ρ' : Nat → V), ρ' p = va →
      interpExpr V cval env φ p ρ' a = some va →
      AnnotOk V cval env φ p ρ' a →
      AnnotOk V cval env φ (D + 1) ρ' e →
      AnnotOk V cval env φ D (delV ρ' p) (Expr.substFvarAt p a e)
  | .bvar i, D, hpD, ρ', hva, ha, hAa, hA => by simp [Expr.substFvarAt, AnnotOk]
  | .sort u, D, hpD, ρ', hva, ha, hAa, hA => by simp [Expr.substFvarAt, AnnotOk]
  | .const n us, D, hpD, ρ', hva, ha, hAa, hA => by simp [Expr.substFvarAt, AnnotOk]
  | .lit l, D, hpD, ρ', hva, ha, hAa, hA => by simp [Expr.substFvarAt, AnnotOk]
  | .letE n ty val body, D, hpD, ρ', hva, ha, hAa, hA => by
    simp only [AnnotOk] at hA
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := hA
    simp only [Expr.substFvarAt, AnnotOk]
    refine ⟨AnnotOk.substFvarAt hwa hba ty D hpD ρ' hva ha hAa haty,
      AnnotOk.substFvarAt hwa hba val D hpD ρ' hva ha hAa hav, xv, ?_, ?_⟩
    · rw [interp_substFvarAt hwa hba val D hpD ρ' hva ha]
      exact hxv
    · have hva' : updV V ρ' (D + 1) xv p = va := by
        simp only [updV]; rw [if_neg (by omega)]; exact hva
      have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) xv) a = some va := by
        rw [interp_ext a (fun i hi => by
          simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
        exact ha
      have hAa' : AnnotOk V cval env φ p (updV V ρ' (D + 1) xv) a := by
        refine AnnotOk.ext a (fun i hi => by
          simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow hAa
      rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
      exact AnnotOk.substFvarAt hwa hba
        (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) xv) hva' ha' hAa' hopen
  | .proj s i e, D, hpD, ρ', hva, ha, hAa, hA => by
    simp only [AnnotOk] at hA
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := hA
    simp only [Expr.substFvarAt, AnnotOk]
    refine ⟨AnnotOk.substFvarAt hwa hba e D hpD ρ' hva ha hAa hae, hi2,
      ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [interp_substFvarAt hwa hba e D hpD ρ' hva ha]
    exact hvei
  | .fvar idx n ty, D, hpD, ρ', hva, ha, hAa, hA => by
    by_cases h1 : idx = p
    · simp only [Expr.substFvarAt, if_pos h1]
      exact AnnotOk.lift hwa D hpD ρ' (delV ρ' p) (fun i hi => by simp [delV, hi]) hAa
    · by_cases h2 : idx > p
      · simp only [Expr.substFvarAt, if_neg h1, if_pos h2]
        simp [AnnotOk]
      · simp only [Expr.substFvarAt, if_neg h1, if_neg h2]
        simp [AnnotOk]
  | .forallE n ty body m, D, hpD, ρ', hva, ha, hAa, hA => by
    simp only [AnnotOk] at hA
    obtain ⟨haty, hcond⟩ := hA
    simp only [Expr.substFvarAt, AnnotOk]
    refine ⟨AnnotOk.substFvarAt hwa hba ty D hpD ρ' hva ha hAa haty, ?_⟩
    intro x A hA' hx
    rw [interp_substFvarAt hwa hba ty D hpD ρ' hva ha] at hA'
    obtain ⟨hbody, hwfact⟩ := hcond x A hA' hx
    have hva' : updV V ρ' (D + 1) x p = va := by
      simp only [updV]; rw [if_neg (by omega)]; exact hva
    have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va := by
      rw [interp_ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
      exact ha
    have hAa' : AnnotOk V cval env φ p (updV V ρ' (D + 1) x) a := by
      refine AnnotOk.ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow hAa
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
    refine ⟨AnnotOk.substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha' hAa' hbody, ?_⟩
    obtain ⟨w, hwi⟩ := hwfact
    refine ⟨w, ?_⟩
    rw [interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha']
    exact hwi
  | .lam n ty body m, D, hpD, ρ', hva, ha, hAa, hA => by
    simp only [AnnotOk] at hA
    obtain ⟨haty, hcond⟩ := hA
    simp only [Expr.substFvarAt, AnnotOk]
    refine ⟨AnnotOk.substFvarAt hwa hba ty D hpD ρ' hva ha hAa haty, ?_⟩
    intro x A hA' hx
    rw [interp_substFvarAt hwa hba ty D hpD ρ' hva ha] at hA'
    obtain ⟨hbody, hwfact⟩ := hcond x A hA' hx
    have hva' : updV V ρ' (D + 1) x p = va := by
      simp only [updV]; rw [if_neg (by omega)]; exact hva
    have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va := by
      rw [interp_ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
      exact ha
    have hAa' : AnnotOk V cval env φ p (updV V ρ' (D + 1) x) a := by
      refine AnnotOk.ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow hAa
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD]
    refine ⟨AnnotOk.substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha' hAa' hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB⟩ := hwfact
    refine ⟨w, B, ?_, hwB⟩
    rw [interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha']
    exact hwi
  | .app f b, D, hpD, ρ', hva, ha, hAa, hA => by
    simp only [AnnotOk] at hA
    obtain ⟨haf, hab, vf, vb, A, B, hfi, hbi, hpi, hvb⟩ := hA
    simp only [Expr.substFvarAt, AnnotOk]
    refine ⟨AnnotOk.substFvarAt hwa hba f D hpD ρ' hva ha hAa haf,
      AnnotOk.substFvarAt hwa hba b D hpD ρ' hva ha hAa hab,
      vf, vb, A, B, ?_, ?_, hpi, hvb⟩
    · rw [interp_substFvarAt hwa hba f D hpD ρ' hva ha]; exact hfi
    · rw [interp_substFvarAt hwa hba b D hpD ρ' hva ha]; exact hbi
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The *inverse* substitution lemma for annotation truthfulness
(task #100 stage 6): truthfulness of the substituted term transports
back onto the `fvar`-opened term — every clause's interpretation facts
transfer along the (reversible) `interp_substFvarAt` equation, and the
`fvar`-hit positions have the trivial clause.  This is what lets the
restructured inference soundness conclude the letE clause's opened-body
truthfulness from the run on the zeta reduct. -/
theorem AnnotOk.substFvarAt_inv {p : Nat} {a : Expr} {va : V}
    (hwa : WScoped p a) (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (D : Nat), p ≤ D → ∀ (ρ' : Nat → V), ρ' p = va →
      interpExpr V cval env φ p ρ' a = some va →
      AnnotOk V cval env φ D (delV ρ' p) (Expr.substFvarAt p a e) →
      AnnotOk V cval env φ (D + 1) ρ' e
  | .bvar i, D, hpD, ρ', hva, ha, hA => by simp [AnnotOk]
  | .sort u, D, hpD, ρ', hva, ha, hA => by simp [AnnotOk]
  | .const n us, D, hpD, ρ', hva, ha, hA => by simp [AnnotOk]
  | .lit l, D, hpD, ρ', hva, ha, hA => by simp [AnnotOk]
  | .fvar idx n ty, D, hpD, ρ', hva, ha, hA => by simp [AnnotOk]
  | .letE n ty val body, D, hpD, ρ', hva, ha, hA => by
    simp only [Expr.substFvarAt, AnnotOk] at hA
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := hA
    simp only [AnnotOk]
    refine ⟨AnnotOk.substFvarAt_inv hwa hba ty D hpD ρ' hva ha haty,
      AnnotOk.substFvarAt_inv hwa hba val D hpD ρ' hva ha hav, xv, ?_, ?_⟩
    · rw [← interp_substFvarAt hwa hba val D hpD ρ' hva ha]
      exact hxv
    · have hva' : updV V ρ' (D + 1) xv p = va := by
        simp only [updV]; rw [if_neg (by omega)]; exact hva
      have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) xv) a = some va := by
        rw [interp_ext a (fun i hi => by
          simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
        exact ha
      rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD] at hopen
      exact AnnotOk.substFvarAt_inv hwa hba
        (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) xv) hva' ha' hopen
  | .proj s i e, D, hpD, ρ', hva, ha, hA => by
    simp only [Expr.substFvarAt, AnnotOk] at hA
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := hA
    simp only [AnnotOk]
    refine ⟨AnnotOk.substFvarAt_inv hwa hba e D hpD ρ' hva ha hae, hi2,
      ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [← interp_substFvarAt hwa hba e D hpD ρ' hva ha]
    exact hvei
  | .forallE n ty body m, D, hpD, ρ', hva, ha, hA => by
    simp only [Expr.substFvarAt, AnnotOk] at hA
    obtain ⟨haty, hcond⟩ := hA
    simp only [AnnotOk]
    refine ⟨AnnotOk.substFvarAt_inv hwa hba ty D hpD ρ' hva ha haty, ?_⟩
    intro x A hA' hx
    rw [← interp_substFvarAt hwa hba ty D hpD ρ' hva ha] at hA'
    obtain ⟨hbody, hwfact⟩ := hcond x A hA' hx
    have hva' : updV V ρ' (D + 1) x p = va := by
      simp only [updV]; rw [if_neg (by omega)]; exact hva
    have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va := by
      rw [interp_ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
      exact ha
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD] at hbody
    refine ⟨AnnotOk.substFvarAt_inv hwa hba
      (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha' hbody, ?_⟩
    obtain ⟨w, hwi⟩ := hwfact
    refine ⟨w, ?_⟩
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD,
      interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) x) hva' ha'] at hwi
    exact hwi
  | .lam n ty body m, D, hpD, ρ', hva, ha, hA => by
    simp only [Expr.substFvarAt, AnnotOk] at hA
    obtain ⟨haty, hcond⟩ := hA
    simp only [AnnotOk]
    refine ⟨AnnotOk.substFvarAt_inv hwa hba ty D hpD ρ' hva ha haty, ?_⟩
    intro x A hA' hx
    rw [← interp_substFvarAt hwa hba ty D hpD ρ' hva ha] at hA'
    obtain ⟨hbody, hwfact⟩ := hcond x A hA' hx
    have hva' : updV V ρ' (D + 1) x p = va := by
      simp only [updV]; rw [if_neg (by omega)]; exact hva
    have ha' : interpExpr V cval env φ p (updV V ρ' (D + 1) x) a = some va := by
      rw [interp_ext a (fun i hi => by
        simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
      exact ha
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD] at hbody
    refine ⟨AnnotOk.substFvarAt_inv hwa hba
      (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
      (by omega) (updV V ρ' (D + 1) x) hva' ha' hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB⟩ := hwfact
    refine ⟨w, B, ?_, hwB⟩
    rw [← substFvarAt_instantiate1 hpD hba body 0, delV_updV hpD,
      interp_substFvarAt hwa hba (body.instantiate1 (.fvar (D + 1) n ty)) (D + 1)
        (by omega) (updV V ρ' (D + 1) x) hva' ha'] at hwi
    exact hwi
  | .app f b, D, hpD, ρ', hva, ha, hA => by
    simp only [Expr.substFvarAt, AnnotOk] at hA
    obtain ⟨haf, hab, vf, vb, A, B, hfi, hbi, hpi, hvb⟩ := hA
    simp only [AnnotOk]
    refine ⟨AnnotOk.substFvarAt_inv hwa hba f D hpD ρ' hva ha haf,
      AnnotOk.substFvarAt_inv hwa hba b D hpD ρ' hva ha hab,
      vf, vb, A, B, ?_, ?_, hpi, hvb⟩
    · rw [← interp_substFvarAt hwa hba f D hpD ρ' hva ha]; exact hfi
    · rw [← interp_substFvarAt hwa hba b D hpD ρ' hva ha]; exact hbi
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Beta, annotation-truthfulness side. -/
theorem AnnotOk_beta {d : Nat} {n : Name} {ty body a : Expr} {ρ : Nat → V} {va : V}
    (hfb : fvarsBelow d body) (hwa : WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (ha : interpExpr V cval env φ d ρ a = some va)
    (hAa : AnnotOk V cval env φ d ρ a) (k : Nat)
    (hAopened : AnnotOk V cval env φ (d + 1) (updV V ρ d va)
      (body.instantiate1 (.fvar d n ty) k)) :
    AnnotOk V cval env φ d ρ (body.instantiate1 a k) := by
  have hva : updV V ρ d va d = va := by simp [updV]
  have hag : ∀ i, i < d → updV V ρ d va i = ρ i := fun i hi => by
    simp only [updV]; rw [if_neg (by omega)]
  have ha' : interpExpr V cval env φ d (updV V ρ d va) a = some va := by
    rw [interp_ext a hag hwa.fvarsBelow]
    exact ha
  have hAa' : AnnotOk V cval env φ d (updV V ρ d va) a :=
    AnnotOk.ext a (fun i hi => (hag i hi).symm) hwa.fvarsBelow hAa
  have h := AnnotOk.substFvarAt (p := d) hwa hba
    (body.instantiate1 (.fvar d n ty) k) d (Nat.le_refl d)
    (updV V ρ d va) hva ha' hAa' hAopened
  rw [substFvarAt_instantiate1_self body k hfb] at h
  exact AnnotOk.ext _ (fun i hi => by
      simp only [delV, updV]
      rw [if_pos hi, if_neg (by omega)])
    (fvarsBelow_instantiate1_gen hwa.fvarsBelow k hfb) h

/-- Beta, annotation-truthfulness side, *inverse* direction (task #100
stage 6): truthfulness of the reduct transports back onto the opened
body at the argument's value.  This is what the restructured inference
soundness uses at the letE clause — the kernel checks the zeta reduct,
and the letE `AnnotOk` clause speaks about the opened body. -/
theorem AnnotOk_beta_inv {d : Nat} {n : Name} {ty body a : Expr} {ρ : Nat → V} {va : V}
    (hfb : fvarsBelow d body) (hwa : WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (ha : interpExpr V cval env φ d ρ a = some va) (k : Nat)
    (hAred : AnnotOk V cval env φ d ρ (body.instantiate1 a k)) :
    AnnotOk V cval env φ (d + 1) (updV V ρ d va)
      (body.instantiate1 (.fvar d n ty) k) := by
  have hva : updV V ρ d va d = va := by simp [updV]
  have ha' : interpExpr V cval env φ d (updV V ρ d va) a = some va := by
    rw [interp_ext a (fun i hi => by
      simp only [updV]; rw [if_neg (by omega)]) hwa.fvarsBelow]
    exact ha
  have h0 : AnnotOk V cval env φ d (delV (updV V ρ d va) d)
      (body.instantiate1 a k) := by
    refine AnnotOk.ext _ (fun i hi => ?_)
      (fvarsBelow_instantiate1_gen hwa.fvarsBelow k hfb) hAred
    simp only [delV, updV]
    rw [if_pos hi, if_neg (by omega)]
  rw [← substFvarAt_instantiate1_self body k hfb] at h0
  exact AnnotOk.substFvarAt_inv hwa hba _ d (Nat.le_refl d)
    (updV V ρ d va) hva ha' h0

/-- Functionalize per-point fibre witnesses (for `lamC_mem`; task #100
stage 6: level-free — no fibre-universe component). -/
theorem choose_fibres {A : V} {F : V → V}
    (h : ∀ x, x ∈ˢ A → ∃ B, F x ∈ˢ B) :
    ∃ B : V → V, ∀ x, x ∈ˢ A → F x ∈ˢ B x := by
  classical
  refine ⟨fun x => if hx : x ∈ˢ A then (h x hx).choose else SetTheory.empty, ?_⟩
  intro x hx
  simp only [dif_pos hx]
  exact (h x hx).choose_spec

end Setlec
