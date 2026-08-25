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

/-- Soundness of the lazy delta same-head spine congruence: a positive
`defeqSpine` verdict identifies the two interpretations.  Both sides
are applications of the *same* constant at pointwise-equal level
values (so the head values coincide), and the argument values agree
pairwise (`defEqList_values`), so the interpretations — the
set-application folds over the head value (`annotOk_spine_inv`) —
coincide.  The reducibility hints that *scheduled* this comparison
never enter: the fact is unconditional in them. -/
theorem defeqSpine_values {m : EnvModel V env} {fuel : Nat}
    (ihd : DefEqClaims m φ fuel) {d : Nat} {a b : Expr} {ρ : Nat → V}
    (h : defeqSpineP env fuel d a b = .ok true)
    (hwa : WScoped d a) (hwb : WScoped d b)
    (hba : a.looseBVarsBounded 0 = true) (hbb : b.looseBVarsBounded 0 = true)
    (hLba : Expr.LeavesBounded a) (hLbb : Expr.LeavesBounded b)
    (hoka : FvarsOk V m.val env φ d ρ a) (hokb : FvarsOk V m.val env φ d ρ b)
    (haa : AnnotOk V m.val env φ d ρ a) (hab : AnnotOk V m.val env φ d ρ b)
    {va vb : V} (hva : interpExpr V m.val env φ d ρ a = some va)
    (hvb : interpExpr V m.val env φ d ρ b = some vb) : va = vb := by
  obtain ⟨n, us, us', hfa, hfb, hlen, hlev, hlist⟩ := defeqSpine_inv h
  have hspa : a = Expr.mkAppN (.const n us) a.getAppArgs := by
    have := (Expr.mkAppN_getApp a).symm
    rw [hfa] at this
    exact this
  have hspb : b = Expr.mkAppN (.const n us') b.getAppArgs := by
    have := (Expr.mkAppN_getApp b).symm
    rw [hfb] at this
    exact this
  -- same head constant at equivalent levels: equal head values
  have hconst : ∀ {w w' : V},
      interpExpr V m.val env φ d ρ (.const n us) = some w →
      interpExpr V m.val env φ d ρ (.const n us') = some w' → w = w' := by
    intro w w' hw hw'
    simp only [interpExpr] at hw hw'
    cases hf : env.find? n with
    | none => rw [hf] at hw; exact nomatch hw
    | some ci =>
    rw [hf] at hw hw'
    dsimp only at hw hw'
    by_cases hal : us.length = ci.toConstantVal.levelParams.length
    · rw [if_pos hal] at hw
      have hal' : us'.length = ci.toConstantVal.levelParams.length := by
        have := Level.isEquivList_length hlev
        omega
      rw [if_pos hal'] at hw'
      obtain rfl := Option.some.inj hw
      obtain rfl := Option.some.inj hw'
      rw [Level.substFn_congr (Level.isEquivList_sound hlev φ)]
    · rw [if_neg hal] at hw
      exact nomatch hw
  by_cases hane : a.getAppArgs = []
  case pos =>
    have hbn : b.getAppArgs = [] := by
      rw [hane] at hlen
      exact List.eq_nil_of_length_eq_zero hlen.symm
    rw [hspa, hane] at hva
    rw [hspb, hbn] at hvb
    rw [show Expr.mkAppN (.const n us) [] = (.const n us : Expr) from rfl]
      at hva
    rw [show Expr.mkAppN (.const n us') [] = (.const n us' : Expr) from rfl]
      at hvb
    exact hconst hva hvb
  case neg =>
    have hbne : b.getAppArgs ≠ [] := by
      intro hnil
      rw [hnil] at hlen
      exact hane (List.eq_nil_of_length_eq_zero hlen)
    have haa' : AnnotOk V m.val env φ d ρ
        (Expr.mkAppN (.const n us) a.getAppArgs) := hspa ▸ haa
    have hab' : AnnotOk V m.val env φ d ρ
        (Expr.mkAppN (.const n us') b.getAppArgs) := hspb ▸ hab
    obtain ⟨-, hxsA, vf, vs, hif, hisp, -, hifold⟩ :=
      annotOk_spine_inv _ _ hane haa'
    obtain ⟨-, hxsB, vg, ws, hig, hispb, -, higold⟩ :=
      annotOk_spine_inv _ _ hbne hab'
    have hva' : va = SpineFold V vf vs := by
      rw [hspa, hifold] at hva
      exact (Option.some.inj hva).symm
    have hvb' : vb = SpineFold V vg ws := by
      rw [hspb, higold] at hvb
      exact (Option.some.inj hvb).symm
    have hfacts_a : ∀ x ∈ a.getAppArgs, WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x :=
      fun x hx =>
        ⟨hwa.getAppArgs x hx, looseBVarsBounded_getAppArgs hba x hx,
         (fun l hl => hLba l (fvarLeaves_getAppArgs hx l hl)),
         FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hoka,
         hxsA x hx⟩
    have hfacts_b : ∀ x ∈ b.getAppArgs, WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        FvarsOk V m.val env φ d ρ x ∧ AnnotOk V m.val env φ d ρ x :=
      fun x hx =>
        ⟨hwb.getAppArgs x hx, looseBVarsBounded_getAppArgs hbb x hx,
         (fun l hl => hLbb l (fvarLeaves_getAppArgs hx l hl)),
         FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hx l hl) hokb,
         hxsB x hx⟩
    have hvs : vs = ws :=
      defEqList_values ihd _ _ _ _ hlist hfacts_a hfacts_b hisp hispb
    have hfg : vf = vg := hconst hif hig
    rw [hva', hvb', hvs, hfg]

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
    obtain ⟨hAdom, vE, hcond⟩ := hAty
    rw [interpExpr] at hity
    obtain ⟨A, hidom, hpieq⟩ : ∃ A,
        interpExpr V m.val env φ d ρ dom = some A ∧
        T = piC A fun x =>
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
    obtain ⟨w, hwi, -⟩ := hwfact
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

