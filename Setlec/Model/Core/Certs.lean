import Setlec.Model.Core.Spine

/-!
# Checker-core soundness: Certs

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

section Claims

variable {m : EnvModel V env} {fuel : Nat}
variable (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
  (ihi : InferClaims m φ fuel)

/-- A successful pairwise definitional-equality check relates spines of
equal length. -/
theorem defEqList_length {fuel : Nat} :
    ∀ {d : Nat} (as bs : List Expr),
      defEqListP env fuel d as bs = .ok true → as.length = bs.length := by
  intro d as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => rfl
    | _ :: _, h => exact nomatch h
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, h =>
      obtain ⟨-, hrest⟩ := defEqList_step_inv h
      simpa using ih bs hrest

/-- Pairwise definitional equality of two interpreted spines yields
pointwise equal values. -/
theorem defEqList_values {m : EnvModel V env} {fuel : Nat}
    (ihd : DefEqClaims m φ fuel) :
    ∀ {d : Nat} {ρ : Nat → V}
      (as bs : List Expr) (vs us : List V),
      defEqListP env fuel d as bs = .ok true →
      (∀ x ∈ as, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      (∀ x ∈ bs, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      InterpSpine m.val env φ d ρ as vs →
      InterpSpine m.val env φ d ρ bs us →
      vs = us := by
  intro d ρ as
  induction as with
  | nil =>
    intro bs vs us h _ _ hs1 hs2
    match bs, h with
    | [], h =>
      match vs, hs1, us, hs2 with
      | [], _, [], _ => rfl
    | _ :: _, h => exact nomatch h
  | cons a as ih =>
    intro bs vs us h ha hb hs1 hs2
    match bs, h with
    | b :: bs, h =>
      obtain ⟨hde, hrest⟩ := defEqList_step_inv h
      match vs, hs1, us, hs2 with
      | v :: vs, ⟨hiv, hs1'⟩, u :: us, ⟨hiu, hs2'⟩ =>
        obtain ⟨haw, hab, haL, haF, haA⟩ := ha a List.mem_cons_self
        obtain ⟨hbw, hbb, hbL, hbF, hbA⟩ := hb b List.mem_cons_self
        have hvu : v = u := ihd hde haw hbw hab hbb
          haL hbL haF hbF haA hbA hiv hiu
        rw [hvu, ih bs vs us hrest
          (fun x hx => ha x (List.mem_cons_of_mem _ hx))
          (fun x hx => hb x (List.mem_cons_of_mem _ hx)) hs1' hs2']

/-- The iota certificates build an expression-spine telescope fit:
each certified argument's inferred type is definitionally equal to the
corresponding (progressively instantiated) domain, so its interpreted
value is a member of the interpreted domain. -/
theorem certs_fit {m : EnvModel V env} {fuel : Nat}
    (ihd : DefEqClaims m φ fuel) (ihi : InferClaims m φ fuel) :
    ∀ {d : Nat} {ρ : Nat → V}
      (ty : Expr) (args : List Expr) (vs : List V) (T : V),
      iotaCertsP env fuel d ty args = .ok true →
      WScoped d ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → FvarsOk V m.val env φ d ρ ty →
      AnnotOk V m.val env φ d ρ ty →
      interpExpr V m.val env φ d ρ ty = some T →
      (∀ x ∈ args, WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ FvarsOk V m.val env φ d ρ x ∧
        AnnotOk V m.val env φ d ρ x) →
      InterpSpine m.val env φ d ρ args vs →
      ∃ rest, TeleFitI V m.val env φ d ρ ty args vs rest := by
  intro d ρ ty args
  induction args generalizing ty with
  | nil =>
    intro vs T hc hwty hbty hLty hFty hAty hity hargs hsp
    match vs, hsp with
    | [], _ => exact ⟨ty, TeleFitI.nil⟩
  | cons a as ih =>
    intro vs T hc hwty hbty hLty hFty hAty hity hargs hsp
    match vs, hsp with
    | v :: vs, ⟨hia, hsp'⟩ =>
    match ty, hc with
    | .bvar _, hc => exact nomatch hc
    | .fvar _ _ _, hc => exact nomatch hc
    | .sort _, hc => exact nomatch hc
    | .const _ _, hc => exact nomatch hc
    | .app _ _, hc => exact nomatch hc
    | .lam _ _ _ _, hc => exact nomatch hc
    | .letE _ _ _ _, hc => exact nomatch hc
    | .lit _, hc => exact nomatch hc
    | .proj _ _ _, hc => exact nomatch hc
    | .forallE n dom body mt, hc =>
    obtain ⟨ta, hta, hde, hrest⟩ := iotaCerts_step_inv hc
    obtain ⟨haw, hab, haL, haF, haA⟩ := hargs a List.mem_cons_self
    -- the domain interprets (the ∀-tower interp forces it)
    simp only [AnnotOk] at hAty
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hAty
    rw [interpExpr, hcod] at hity
    obtain ⟨A, hidom, hpieq⟩ : ∃ A,
        interpExpr V m.val env φ d ρ dom = some A ∧
        T = pi (cod.eval φ) A fun x =>
          (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n dom))).getD SetTheory.empty := by
      revert hity
      cases hd : interpExpr V m.val env φ d ρ dom with
      | none => intro hity; exact nomatch hity
      | some A =>
        intro hity
        dsimp only at hity
        exact ⟨A, rfl, (Option.some.inj hity).symm⟩
    -- the inferred type's value equals the domain's
    obtain ⟨⟨va, tva, hiva, hita, hmemta⟩, hAta⟩ :=
      ihi hta haw hab haL haF haA
    obtain rfl : va = v := by rw [hiva] at hia; exact Option.some.inj hia
    have htaw : WScoped d ta := inferTypeCore_WScoped m.wf fuel hta haw
    have htab : ta.looseBVarsBounded 0 = true :=
      inferTypeCore_looseBVars m.wf fuel hta haw hab haL
    have htaL : Expr.LeavesBounded ta := fun l hl =>
      haL l (inferTypeCore_fvarLeaves m.wf fuel hta haw l hl)
    have htaF : FvarsOk V m.val env φ d ρ ta :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta haw) haF
    have hwty' : WScoped d dom ∧ WScoped d body := by
      simpa [WScoped] using hwty
    have hdomw : WScoped d dom := hwty'.1
    have hdomb : dom.looseBVarsBounded 0 = true := by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbty
      exact hbty.1
    have hdomL : Expr.LeavesBounded dom := fun l hl =>
      hLty l (by simp [Expr.fvarLeaves, hl])
    have hdomF : FvarsOk V m.val env φ d ρ dom :=
      FvarsOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hFty
    have hveq : tva = A := ihd hde htaw hdomw htab hdomb
      htaL hdomL htaF hdomF hAta hAdom hita hidom
    have hvA : va ∈ˢ A := hveq ▸ hmemta
    -- the instantiated body interprets and stays truthful
    obtain ⟨hbodyA, hwfact⟩ := hcond va A hidom hvA
    obtain ⟨w, hwi, -⟩ := hwfact cod hcod
    have hfb : Expr.fvarsBelow d body := hwty'.2.fvarsBelow
    have hibody : interpExpr V m.val env φ d ρ (body.instantiate1 a) =
        some w := by
      rw [interp_beta (n := n) (ty := dom) hfb haw hab hia 0]
      exact hwi
    have hAbody : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
      AnnotOk_beta hfb haw hab hia haA 0 hbodyA
    have hwbody : WScoped d (body.instantiate1 a) :=
      WScoped.instantiate1_gen haw 0 hwty'.2
    have hbbody : (body.instantiate1 a).looseBVarsBounded 0 = true := by
      refine looseBVarsBounded_instantiate1_gen hab ?_
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbty
      exact hbty.2
    have hLbody : Expr.LeavesBounded (body.instantiate1 a) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hLty l (by simp [Expr.fvarLeaves, hl'])
      · exact haL l hl'
    have hFbody : FvarsOk V m.val env φ d ρ (body.instantiate1 a) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
      · exact hFty l (by simp [Expr.fvarLeaves, hl'])
      · exact haF l hl'
    obtain ⟨rest, hfit⟩ := ih (body.instantiate1 a) vs w hrest
      hwbody hbbody hLbody hFbody hAbody hibody
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx)) hsp'
    exact ⟨rest, TeleFitI.cons hidom hia hvA hfb haw hab haA hfit⟩

end Claims

end Setlec
