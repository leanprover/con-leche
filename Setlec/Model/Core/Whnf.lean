import Setlec.Model.Core.Iota

/-!
# Checker-core soundness: Whnf

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

theorem whnf_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel)
    (ihAll : ∀ f, f ≤ fuel →
      WhnfClaims m φ f ∧ DefEqClaims m φ f ∧ InferClaims m φ f) :
    WhnfClaims m φ (fuel + 1) := by
  intro d e e' ρ h hw hb hLb hok ha
  match e, h with
  | .sort u, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .fvar idx n ty, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .forallE n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .lam n ty body bi, h =>
      simp only [whnfCore, pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ ⟨rfl, ha⟩
  | .const n ws, h =>
    simp only [whnfCore] at h
    cases hf : env.find? n with
    | none => rw [hf] at h; exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv value =>
        dsimp only at h
        split at h
        next hal =>
          obtain ⟨-, -, -, -, hval, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
          obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
          have hcl : (value.instantiateLevelParams cv.levelParams ws).hasFvar = false := by
            rw [hasFvar_instantiateLevelParams]; exact hvc
          have hstored := (m.annot_ok _ (List.mem_of_find?_eq_some hf)
            (Level.substFn φ cv.levelParams ws)).2 cv value rfl
          have hinst := AnnotOk.instLevels m.val_params value 0 (rho0 V) hstored
          obtain ⟨hi, ha'⟩ := ihw h
            (WScoped.of_not_hasFvar hcl)
            (by rw [looseBVarsBounded_instantiateLevelParams]; exact hvb)
            (Expr.LeavesBounded.of_not_hasFvar hcl)
            (FvarsOk.of_not_hasFvar hcl)
            (AnnotOk.closed_invariant hcl d ρ hinst)
          refine ⟨?_, ha'⟩
          rw [hi]
          rw [interp_closed_invariant hcl]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          have hmem : ConstantInfo.defnInfo cv value ∈ env.consts :=
            List.mem_of_find?_eq_some hf
          have hde := m.defn_eq cv value hmem (Level.substFn φ cv.levelParams ws)
          unfold interpClosed at hde
          rw [hde]
          have hname : cv.name = n := by
            have := find?_name hf
            simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
          rw [interp_const hf hal, hname]
          rfl
        next hal => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | axiomInfo cv => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | thmInfo cv value => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | indInfo cv _ => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | ctorInfo cv nP nF => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
      | recInfo cv nP nM nm ni rules => exact (Except.ok.inj h) ▸ ⟨rfl, ha⟩
  | .app f a, h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hvA, hfib⟩ := ha
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨hif, haf'⟩ := ihw hwf hw.1 hb.1 hLbf hokf haf
    rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, hcert⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- beta (guarded or certified)
      have hwlam := whnf_WScoped m.wf fuel hwf hw.1
      have hblam := whnf_looseBVars m.wf fuel hwf hb.1
      have hLblam : Expr.LeavesBounded (Expr.lam n ty body mm) := fun l hl =>
        hLbf l (whnf_fvarLeaves m.wf fuel hwf l hl)
      have hoklam : FvarsOk V m.val env φ d ρ (.lam n ty body mm) :=
        whnf_FvarsOk m.wf fuel hwf hokf
      simp only [WScoped] at hwlam
      simp only [looseBVarsBounded, Bool.and_eq_true] at hblam
      have hfi' : interpExpr V m.val env φ d ρ (.lam n ty body mm) = some vf := by
        rw [hif]; exact hfi
      rw [interpExpr, hc] at hfi'
      dsimp only at hfi'
      cases hty : interpExpr V m.val env φ d ρ ty with
      | none => rw [hty] at hfi'; exact nomatch hfi'
      | some Aty =>
      rw [hty] at hfi'
      simp only [Option.some.injEq] at hfi'
      simp only [AnnotOk] at haf'
      obtain ⟨haty, -, hcond⟩ := haf'
      -- the argument is in the λ's domain
      have hdom : va ∈ˢ Aty := by
        rcases hcert with hnz | ⟨ta, hta, hde⟩
        · -- guarded: certainly non-Prop, so the graph determines its domain
          have hnz' : Level.eval φ v ≠ 0 := Level.isNonZero_sound hnz φ
          by_cases hvE : vE = 0
          · subst hvE
            exact absurd (hfi'.trans (mem_pi_zero hpi)) (lam_ne_pt hnz')
          · have hpil : SetTheory.lam (v.eval φ) Aty
                (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
                  (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ
                pi vE A B := by
              rw [hfi']; exact hpi
            exact lam_dom hpil hvE hnz' va hvA
        · -- certified: the runtime check hands the fact directly
          obtain ⟨⟨va₂, vta, hai₂, htai, hmema⟩, hAta⟩ :=
            ihi hta hw.2 hb.2 hLba hoka haa
          have hva₂ : va₂ = va := by
            rw [hai] at hai₂
            exact (Option.some.inj hai₂).symm
          subst hva₂
          have hLbta : Expr.LeavesBounded ta := fun l hl =>
            hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
          have hLbty : Expr.LeavesBounded ty := fun l hl =>
            hLblam l (by simp [fvarLeaves, hl])
          have heqA : vta = Aty :=
            ihd hde
              (inferTypeCore_WScoped m.wf fuel hta hw.2) hwlam.1
              (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba) hblam.1
              hLbta hLbty
              (FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
              ((FvarsOk.of_lam hoklam).1)
              hAta haty htai hty
          exact heqA ▸ hmema
      obtain ⟨hbodyA, hwfact⟩ := hcond va Aty hty hdom
      obtain ⟨w, Bl, hwi, hwB, hBu⟩ := hwfact v hc
      have hfb : fvarsBelow d body := hwlam.2.fvarsBelow
      have hred_w : WScoped d (body.instantiate1 a) :=
        WScoped.instantiate1_gen hw.2 0 hwlam.2
      have hred_b : (body.instantiate1 a).looseBVarsBounded 0 = true :=
        looseBVarsBounded_instantiate1_gen hb.2 hblam.2
      have hred_Lb : Expr.LeavesBounded (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hLblam l (by simp [fvarLeaves, hl'])
        · exact hLba l hl'
      have hred_ok : FvarsOk V m.val env φ d ρ (body.instantiate1 a) := by
        intro l hl
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact (FvarsOk.of_lam hoklam).2 l hl'
        · exact hoka l hl'
      have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
        (n := n) (ty := ty) hfb hw.2 hb.2 hai 0
      have hred_A : AnnotOk V m.val env φ d ρ (body.instantiate1 a) :=
        AnnotOk_beta hfb hw.2 hb.2 hai haa 0 hbodyA
      obtain ⟨hi2, ha2⟩ := ihw hbeta hred_w hred_b hred_Lb hred_ok hred_A
      refine ⟨?_, ha2⟩
      have hfibres : ∀ x, x ∈ˢ Aty →
          ∃ B', ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty) ∈ˢ B' ∧
            B' ∈ˢ univ (v.eval φ) := by
        intro x hx
        obtain ⟨-, hwfact_x⟩ := hcond x Aty hty hx
        obtain ⟨w_x, B_x, hwi_x, hwB_x, hBu_x⟩ := hwfact_x v hc
        exact ⟨B_x, by rw [hwi_x]; exact hwB_x, hBu_x⟩
      obtain ⟨Bf, hBf1, hBf2⟩ := choose_fibres (V := V) hfibres
      have happi : interpExpr V m.val env φ d ρ (.app f a) =
          some (SetTheory.app vf va) := by
        rw [interpExpr, hfi, hai]
      rw [hi2, hbeta_eq, hwi, happi]
      simp only [Option.some.injEq]
      rw [← hfi', app_lam hdom hBf1 hBf2]
      simp [hwi]
    · -- iota step
      have hw' : WScoped d (Expr.app f' a) := by
        simp only [WScoped]
        exact ⟨whnf_WScoped m.wf fuel hwf hw.1, hw.2⟩
      have hb' : (Expr.app f' a).looseBVarsBounded 0 = true := by
        simp only [looseBVarsBounded, Bool.and_eq_true]
        exact ⟨whnf_looseBVars m.wf fuel hwf hb.1, hb.2⟩
      have hLb' : Expr.LeavesBounded (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLbf l (whnf_fvarLeaves m.wf fuel hwf l hl)
        · exact hLba l hl
      have hok' : FvarsOk V m.val env φ d ρ (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact whnf_FvarsOk m.wf fuel hwf hokf l hl
        · exact hoka l hl
      have ha' : AnnotOk V m.val env φ d ρ (Expr.app f' a) := by
        simp only [AnnotOk]
        exact ⟨haf', haa, vf, va, vE, A, B, hif.trans hfi, hai, hpi, hvA,
          hfib⟩
      obtain ⟨⟨hie, hae''⟩, hwE, hbE, hLbE, hokE⟩ :=
        iota_sound ihAll hio hw' hb' hLb' hok' ha'
      obtain ⟨hi2, ha2⟩ := ihw hwe'' hwE hbE hLbE hokE hae''
      refine ⟨?_, ha2⟩
      rw [hi2, hie]
      simp only [interpExpr]
      rw [hif]
    · -- stuck application
      refine ⟨?_, ?_⟩
      · simp only [interpExpr]
        rw [hif]
      · simp only [AnnotOk]
        refine ⟨haf', haa, vf, va, vE, A, B, ?_, hai, hpi, hvA, hfib⟩
        rw [hif]; exact hfi
  | .proj sn i e, h =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded] at hb
    have hLbe : Expr.LeavesBounded e := fun l hl => hLb l (by
      simp only [fvarLeaves]; exact hl)
    have hoke : FvarsOk V m.val env φ d ρ e := fun l hl => hok l (by
      simp only [fvarLeaves]; exact hl)
    simp only [AnnotOk] at ha
    obtain ⟨hae, hilt, veC, uC, vC, AC, BfC, hveiC, hsigC, hAuC, hBfC⟩ := ha
    obtain ⟨e₂, he, hcase⟩ := whnf_proj_inv h
    obtain ⟨hie, hae₂⟩ := ihw he hw hb hLbe hoke hae
    rcases hcase with rfl | ⟨us, cv, nP, nF, hfn, hf, hi2, hlen, hus, hred, hcert⟩
    · -- stuck projection
      refine ⟨?_, ?_⟩
      · simp only [interpExpr]
        rw [hie]
      · simp only [AnnotOk]
        refine ⟨hae₂, hilt, veC, uC, vC, AC, BfC, ?_, hsigC, hAuC, hBfC⟩
        rw [hie]; exact hveiC
    · -- projection of the pair constructor
      obtain ⟨hnP, hnF, hlp, hmkfacts⟩ := m.ind_ok.right.left cv nP nF hf
      subst hnP; subst hnF
      obtain ⟨l0, l1, rfl⟩ := List.length_two hus
      obtain ⟨α, β, a, b, hargs⟩ := List.length_four hlen
      have he₂ : e₂ = .app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b := by
        have h0 := Expr.mkAppN_getApp e₂
        rw [hfn, hargs] at h0
        exact h0.symm
      have hargd : e₂.getAppArgs.getD (2 + i) (.bvar 0) = if i = 0 then a else b := by
        rw [hargs]
        match i, hi2 with
        | 0, _ => rfl
        | 1, _ => rfl
      -- pristine invariants of the whnf'd struct (for the certificates)
      have hwC := whnf_WScoped m.wf fuel he hw
      have hbC := whnf_looseBVars m.wf fuel he hb
      have hLbC : Expr.LeavesBounded e₂ := fun l hl =>
        hLbe l (whnf_fvarLeaves m.wf fuel he l hl)
      have hokC := whnf_FvarsOk m.wf fuel he hoke
      have haC := hae₂
      -- decomposed (substituted) forms
      have hwe₂ := hwC
      have hbe₂ := hbC
      have hLbe₂ := hLbC
      have hoke₂ := hokC
      rw [he₂] at hwe₂ hbe₂ hLbe₂ hoke₂ hae₂
      have hien : interpExpr V m.val env φ d ρ
          (.app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b) =
          interpExpr V m.val env φ d ρ e := by
        rw [← he₂]; exact hie
      simp only [WScoped] at hwe₂
      obtain ⟨⟨⟨⟨-, hwα⟩, hwβ⟩, hwa⟩, hwb⟩ := hwe₂
      simp only [looseBVarsBounded, Bool.and_eq_true] at hbe₂
      obtain ⟨⟨⟨⟨-, hbα⟩, hbβ⟩, hba⟩, hbb⟩ := hbe₂
      have hLba : Expr.LeavesBounded a := fun l hl => hLbe₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inl (Or.inr hl))
      have hLbb : Expr.LeavesBounded b := fun l hl => hLbe₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inr hl)
      have hoka : FvarsOk V m.val env φ d ρ a := fun l hl => hoke₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inl (Or.inr hl))
      have hokb : FvarsOk V m.val env φ d ρ b := fun l hl => hoke₂ l (by
        simp only [fvarLeaves, List.mem_append]
        exact Or.inr hl)
      -- decompose the spine's clauses
      try simp only [AnnotOk] at hae₂
      obtain ⟨ha3, hab, vf₃, vb, vE₃, A₃, B₃, hf₃i, hbi, hpi₃, hvb₃, hfib₃⟩ := hae₂
      try simp only [AnnotOk] at ha3
      obtain ⟨ha2, haa, vf₂, va, vE₂, A₂, B₂, hf₂i, hai, hpi₂, hva₂, hfib₂⟩ := ha3
      try simp only [AnnotOk] at ha2
      obtain ⟨ha1, haβ, vf₁, vβ, vE₁, A₁, B₁, hf₁i, hβi, hpi₁, hvβ₁, hfib₁⟩ := ha2
      try simp only [AnnotOk] at ha1
      obtain ⟨hac, haα, vf₀, vα, vE₀, A₀, B₀, hci, hαi, hpi₀, hvα₀, hfib₀⟩ := ha1
      -- the head constant's value
      rw [interpExpr, hf] at hci
      dsimp only [ConstantInfo.toConstantVal] at hci
      obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cv.levelParams [l0, l1] := ⟨_, rfl⟩
      rw [← hψ'] at hci
      by_cases hal : ([l0, l1] : List Level).length = cv.levelParams.length
      case neg => simp only [hal, if_false] at hci; exact nomatch hci
      simp only [hal, if_true] at hci
      have hval : interpExpr V m.val env φ d ρ (.const psigmaMkName [l0, l1]) =
          some (m.val psigmaMkName ψ') := by
        rw [interpExpr, hf]
        dsimp only [ConstantInfo.toConstantVal]
        rw [← hψ']
        simp only [hal, if_true]
      have hvf₀ : vf₀ = m.val psigmaMkName ψ' := (Option.some.inj hci).symm
      -- level bookkeeping
      have hne : uN ≠ vN := by decide
      have hψu : ψ' uN = Level.eval φ l0 := by
        rw [hψ', hlp]
        simp [Level.substFn]
      have hψv : ψ' vN = Level.eval φ l1 := by
        rw [hψ', hlp]
        simp [Level.substFn, hne]
      -- partial-fold equations
      have hf₁ : vf₁ = app (m.val psigmaMkName ψ') vα := by
        rw [interpExpr, hval, hαi] at hf₁i
        dsimp only at hf₁i
        exact (Option.some.inj hf₁i).symm
      have hf₂ : vf₂ = app vf₁ vβ := by
        rw [interpExpr, hf₁i, hβi] at hf₂i
        dsimp only at hf₂i
        exact (Option.some.inj hf₂i).symm
      have hf₃ : vf₃ = app vf₂ va := by
        rw [interpExpr, hf₂i, hai] at hf₃i
        dsimp only at hf₃i
        exact (Option.some.inj hf₃i).symm
      have hnesti : interpExpr V m.val env φ d ρ
          (.app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b) =
          some (app vf₃ vb) := by
        rw [interpExpr, hf₃i, hbi]
      have hveC' : veC = app vf₃ vb := by
        have : some veC = some (app vf₃ vb) := by
          rw [← hveiC, ← hien, hnesti]
        exact Option.some.inj this
      by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
      · -- collapse: everything is the proof point (certified)
        have hnz : ¬ (Level.max l0 l1).isNonZero = true := by
          intro hnz'
          have := Level.isNonZero_sound hnz' φ
          simp only [Level.eval] at this
          rw [← hψu, ← hψv] at this
          exact this hw0
        rcases hcert with hcert | hcert
        case inl => exact absurd hcert hnz
        cases fuel with
        | zero => simp [projCert] at hcert
        | succ f =>
        obtain ⟨ihwL, ihdL, ihiL⟩ := ihAll f (by omega)
        obtain ⟨ta, sta, uT, te, ste, wT, hta, hsta, hwta, heq1, hte, hste, hwte, heq2⟩ :=
          projCert_inv hcert
        have hwT0 : Level.eval φ wT = 0 := by
          rw [Level.isEquiv_sound heq2 φ]
          simp only [Level.eval, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [← hψu, ← hψv]
          exact hw0
        have hept : interpExpr V m.val env φ d ρ e₂ = some pt :=
          sortCert_pt ihwL ihiL hte hste hwte hwT0 hwC hbC hLbC hokC haC
        have hveCpt : veC = pt := by
          have : some veC = some pt := by
            rw [← hveiC, ← hie, hept]
          exact Option.some.inj this
        -- the projected argument is a proof point too
        rw [hargd] at hta
        have huT0 : Level.eval φ uT = 0 := by
          rw [Level.isEquiv_sound heq1 φ]
          have hu0 : ψ' uN = 0 :=
            Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw0))
          have hv0 : ψ' vN = 0 :=
            Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw0))
          match i, hi2 with
          | 0, _ =>
            simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
            rw [← hψu]
            exact hu0
          | 1, _ =>
            simp only [List.getD, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some]
            rw [← hψv]
            exact hv0
        match i, hi2, hred, hargd, hta with
        | 0, _, hred, hargd, hta =>
          rw [if_pos rfl] at hargd
          rw [hargd] at hred
          have hapt : interpExpr V m.val env φ d ρ a = some pt :=
            sortCert_pt ihwL ihiL hta hsta hwta huT0 hwa hba hLba hoka haa
          obtain ⟨hired, hared⟩ := ihw hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hapt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, sfst_pt]
          simp
        | 1, _, hred, hargd, hta =>
          rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          have hbpt : interpExpr V m.val env φ d ρ b = some pt :=
            sortCert_pt ihwL ihiL hta hsta hwta huT0 hwb hbb hLbb hokb hab
          obtain ⟨hired, hared⟩ := ihw hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbpt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, ssnd_pt]
          simp
      · -- no collapse: the fold is a genuine pair
        have hfacts := hmkfacts ψ'
        have hαmem : vα ∈ˢ univ (ψ' uN) := hfacts.dom₀ hw0 (hvf₀ ▸ hpi₀) hvα₀
        have hpi₁' : app (m.val psigmaMkName ψ') vα ∈ˢ pi vE₁ A₁ B₁ := by
          rw [← hf₁]; exact hpi₁
        have hβmem : vβ ∈ˢ pi (ψ' vN + 1) vα (fun _ => univ (ψ' vN)) :=
          hfacts.dom₁ hw0 hαmem hpi₁' hvβ₁
        have hpi₂' : app (app (m.val psigmaMkName ψ') vα) vβ ∈ˢ pi vE₂ A₂ B₂ := by
          rw [← hf₁, ← hf₂]; exact hpi₂
        have hamem : va ∈ˢ vα := hfacts.dom₂ hw0 hαmem hβmem hpi₂' hva₂
        have hpi₃' : app (app (app (m.val psigmaMkName ψ') vα) vβ) va ∈ˢ pi vE₃ A₃ B₃ := by
          rw [← hf₁, ← hf₂, ← hf₃]; exact hpi₃
        have hbmem : vb ∈ˢ app vβ va := hfacts.dom₃ hw0 hαmem hβmem hamem hpi₃' hvb₃
        have hfold : app vf₃ vb = spair va vb := by
          rw [hf₃, hf₂, hf₁]
          rw [hfacts.fold hαmem hβmem hamem hbmem]
          simp [hw0]
        match i, hi2, hred, hargd with
        | 0, _, hred, hargd =>
          rw [if_pos rfl] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihw hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hai]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, sfst_spair]
          simp
        | 1, _, hred, hargd =>
          rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihw hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbi]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, ssnd_spair]
          simp


end Claims

end Setlec
