import Setlec.Model.Core.Iota
import Setlec.Model.NatOps

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

set_option maxHeartbeats 1600000 in
/-- Head normalization (no delta) preserves the interpretation and
annotation truthfulness. -/
theorem whnfCore_claims (m : EnvModel V env)
    (ihwc : WhnfCoreClaims m φ fuel) (ihw : WhnfClaims m φ fuel)
    (ihd : DefEqClaims m φ fuel) (ihi : InferClaims m φ fuel) :
    WhnfCoreClaims m φ (fuel + 1) := by
  intro d e e' ρ h hw hb hLb hok ha
  cases e with
  | sort u =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | fvar idx n ty =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | forallE n ty body bi =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | lam n ty body bi =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | lit l0 =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | bvar i =>
    rw [whnfCore_succ] at h
    simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
  | letE nn tt vv bb =>
    rw [whnfCore_succ] at h
    simp [whnfCoreBody, throw, throwThe, MonadExceptOf.throw] at h
  | const n ws =>
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨rfl, ha⟩
  | app f a =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hvA, hfib⟩ := ha
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨hif, haf'⟩ := ihwc hwf hw.1 hb.1 hLbf hokf haf
    rcases hcase with ⟨n, ty, body, mm, v, rfl, hc, hbeta, hcert⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- beta (guarded or certified)
      have hwlam := whnfCore_WScoped m.wf fuel hwf hw.1
      have hblam := whnfCore_looseBVars m.wf fuel hwf hb.1
      have hLblam : Expr.LeavesBounded (Expr.lam n ty body mm) := fun l hl =>
        hLbf l (whnfCore_fvarLeaves m.wf fuel hwf l hl)
      have hoklam : FvarsOk V m.val env φ d ρ (.lam n ty body mm) :=
        whnfCore_FvarsOk m.wf fuel hwf hokf
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
      obtain ⟨hi2, ha2⟩ := ihwc hbeta hred_w hred_b hred_Lb hred_ok hred_A
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
        exact ⟨whnfCore_WScoped m.wf fuel hwf hw.1, hw.2⟩
      have hb' : (Expr.app f' a).looseBVarsBounded 0 = true := by
        simp only [looseBVarsBounded, Bool.and_eq_true]
        exact ⟨whnfCore_looseBVars m.wf fuel hwf hb.1, hb.2⟩
      have hLb' : Expr.LeavesBounded (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLbf l (whnfCore_fvarLeaves m.wf fuel hwf l hl)
        · exact hLba l hl
      have hok' : FvarsOk V m.val env φ d ρ (Expr.app f' a) := by
        intro l hl
        simp only [fvarLeaves, List.mem_append] at hl
        rcases hl with hl | hl
        · exact whnfCore_FvarsOk m.wf fuel hwf hokf l hl
        · exact hoka l hl
      have ha' : AnnotOk V m.val env φ d ρ (Expr.app f' a) := by
        simp only [AnnotOk]
        exact ⟨haf', haa, vf, va, vE, A, B, hif.trans hfi, hai, hpi, hvA,
          hfib⟩
      obtain ⟨⟨hie, hae''⟩, hwE, hbE, hLbE, hokE⟩ :=
        iota_sound ihw ihd ihi hio hw' hb' hLb' hok' ha'
      obtain ⟨hi2, ha2⟩ := ihwc hwe'' hwE hbE hLbE hokE hae''
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
  | proj sn i e =>
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
      have hi2' : i = 0 ∨ i = 1 := by omega
      have hargd : e₂.getAppArgs.getD (2 + i) (.bvar 0) = if i = 0 then a else b := by
        rw [hargs]
        rcases hi2' with rfl | rfl
        · rfl
        · rfl
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
        obtain ⟨ta, sta, uT, te, ste, wT, hta, hsta, hwta, heq1, hte, hste, hwte, heq2⟩ :=
          projCert_inv hcert
        have hwT0 : Level.eval φ wT = 0 := by
          rw [Level.isEquiv_sound heq2 φ]
          simp only [Level.eval, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [← hψu, ← hψv]
          exact hw0
        have hept : interpExpr V m.val env φ d ρ e₂ = some pt :=
          sortCert_pt ihw ihi hte hste hwte hwT0 hwC hbC hLbC hokC haC
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
          rcases hi2' with rfl | rfl
          · simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
            rw [← hψu]
            exact hu0
          · simp only [List.getD, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some]
            rw [← hψv]
            exact hv0
        rcases hi2' with rfl | rfl
        · rw [if_pos rfl] at hargd
          rw [hargd] at hred
          have hapt : interpExpr V m.val env φ d ρ a = some pt :=
            sortCert_pt ihw ihi hta hsta hwta huT0 hwa hba hLba hoka haa
          obtain ⟨hired, hared⟩ := ihwc hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hapt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, sfst_pt]
          simp
        · rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          have hbpt : interpExpr V m.val env φ d ρ b = some pt :=
            sortCert_pt ihw ihi hta hsta hwta huT0 hwb hbb hLbb hokb hab
          obtain ⟨hired, hared⟩ := ihwc hred hwb hbb hLbb hokb hab
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
        rcases hi2' with rfl | rfl
        · rw [if_pos rfl] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihwc hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hai]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, sfst_spair]
          simp
        · rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          obtain ⟨hired, hared⟩ := ihwc hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbi]
          simp only [interpExpr, hveiC]
          rw [hveC', hfold, ssnd_spair]
          simp


/-- Full inversion of a successful literal-acceleration step:
`Nat.succ` folding, the unary `pred` fast path, or a binary fast
path. -/
theorem reduceNat_full_inv {env : Env} {fuel d : Nat} {e e₂ : Expr}
    (h : reduceNatP env fuel d e = .ok (some e₂)) :
    (∃ a n, e = .app (.const natSuccName []) a ∧
      natLitSupported env = true ∧ rawNatLit? a = some n ∧
      e₂ = .lit (.natVal (n + 1))) ∨
    (∃ a a' n, e = .app (.const natPredName []) a ∧
      natOpGuard env natPredName = true ∧
      whnf env fuel d a = .ok a' ∧ rawNatLit? a' = some n ∧
      e₂ = .lit (.natVal (n - 1))) ∨
    (∃ c a b a' b' n₁ n₂, e = .app (.app (.const c []) a) b ∧
      (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
       c = natPowName ∨ c = natBeqName ∨ c = natBleName) ∧
      natOpGuard env c = true ∧
      whnf env fuel d a = .ok a' ∧ rawNatLit? a' = some n₁ ∧
      whnf env fuel d b = .ok b' ∧ rawNatLit? b' = some n₂ ∧
      natOpResult c n₁ n₂ = some e₂) := by
  dsimp only [reduceNatP] at h
  revert h
  match e with
  | .app (.const c []) a => ?_
  | .app (.app (.const c []) a) b => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .lam _ _ _ _ | .forallE _ _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ | .const _ _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.bvar _) _ | .app (.fvar _ _ _) _ | .app (.sort _) _
  | .app (.lam _ _ _ _) _ | .app (.forallE _ _ _ _) _
  | .app (.letE _ _ _ _) _ | .app (.lit _) _ | .app (.proj _ _ _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.const c (_ :: _)) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.bvar _) _) _ | .app (.app (.fvar _ _ _) _) _
  | .app (.app (.sort _) _) _ | .app (.app (.app _ _) _) _
  | .app (.app (.lam _ _ _ _) _) _ | .app (.app (.forallE _ _ _ _) _) _
  | .app (.app (.letE _ _ _ _) _) _ | .app (.app (.lit _) _) _
  | .app (.app (.proj _ _ _) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  | .app (.app (.const c (_ :: _)) _) _ =>
    intro h; simp [reduceNat, pure, Except.pure] at h
  · -- unary heads: `succ` folding or the `pred` fast path
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    case isTrue hg =>
      obtain ⟨rfl, hs⟩ := hg
      cases hraw : rawNatLit? a with
      | none => intro h; simp [hraw, pure, Except.pure] at h
      | some n =>
        intro h
        simp only [hraw, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        exact Or.inl ⟨a, n, rfl, hs, hraw, h.symm⟩
    case isFalse =>
      split
      case isTrue hg =>
        obtain ⟨rfl, hguard⟩ := hg
        cases hwa : whnf env fuel d a with
        | error err => intro h; exact nomatch h
        | ok a' =>
        intro h
        dsimp only at h
        revert h
        match hraw : rawNatLit? a' with
        | some n => ?_
        | none => intro h; simp [pure, Except.pure] at h
        intro h
        dsimp only at h
        have hres : natOpResult natPredName n 0 =
            some (.lit (.natVal (n - 1))) := by
          simp [natOpResult]
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        exact Or.inr (Or.inl ⟨a, a', n, rfl, hguard, hwa, hraw, h.symm⟩)
      case isFalse => intro h; simp [pure, Except.pure] at h
  · -- binary fast paths
    intro h
    simp only [reduceNat, Bind.bind, Except.bind, whnf_def] at h
    revert h
    split
    case isTrue hg =>
      obtain ⟨hor, hguard⟩ := hg
      cases hwa : whnf env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a' =>
      intro h
      dsimp only at h
      revert h
      cases hwb : whnf env fuel d b with
      | error err => intro h; exact nomatch h
      | ok b' =>
      intro h
      dsimp only at h
      revert h
      match hraw1 : rawNatLit? a', hraw2 : rawNatLit? b' with
      | some n₁, some n₂ => ?_
      | some _, none => intro h; simp [pure, Except.pure] at h
      | none, some _ => intro h; simp [pure, Except.pure] at h
      | none, none => intro h; simp [pure, Except.pure] at h
      intro h
      dsimp only at h
      cases hres : natOpResult c n₁ n₂ with
      | none => rw [hres] at h; simp [pure, Except.pure] at h
      | some r =>
        rw [hres] at h
        simp only [pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        exact Or.inr (Or.inr ⟨c, a, b, a', b', n₁, n₂, rfl, hor, hguard,
          hwa, hraw1, hwb, hraw2, h ▸ hres⟩)
    case isFalse => intro h; simp [pure, Except.pure] at h

/-- Soundness of a literal-acceleration step: the reduct (a literal or
a `Bool`-constant) interprets to the redex's value — via the whnf
claims on the arguments and the meta-level literal inductions over the
stored recurrences (`EnvModel.nat_ops`) — and every invariant is
trivially re-established (the result is a closed atom). -/
theorem reduceNat_sound (m : EnvModel V env) {fuel d : Nat} {e e₂ : Expr}
    {ρ : Nat → V} (ihw : WhnfClaims m φ fuel)
    (h : reduceNatP env fuel d e = .ok (some e₂))
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hok : FvarsOk V m.val env φ d ρ e)
    (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e₂ = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e₂ ∧ WScoped d e₂ ∧
    e₂.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e₂ ∧
    FvarsOk V m.val env φ d ρ e₂ := by
  rcases reduceNat_full_inv h with
    ⟨a, n, rfl, hs, hraw, rfl⟩ |
    ⟨a, a', n, rfl, hguard, hwa, hraw, rfl⟩ |
    ⟨c, a, b, a', b', n₁, n₂, rfl, hor, hguard, hwa, hraw1, hwb, hraw2,
      hres⟩
  · -- `succ` folding
    refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
      by simp [Expr.looseBVarsBounded],
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
    rw [interpExpr_lit hs]
    obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, hl1, hl2, hl3,
      -⟩ := natLitSupported_inv hs
    simp [interpExpr, hss, ConstantInfo.toConstantVal, hl3, Level.substFn_nil,
      interpExpr_rawNatLit hs hraw, natLitVal]
  · -- `pred`
    have hs := (natOpGuard_inv hguard).1
    obtain ⟨cvp, vp, hfp, hlpp⟩ := natOpGuard_self_defn (by decide) hguard
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLba : Expr.LeavesBounded a := fun l hl =>
      hLb l (by simp [fvarLeaves, hl])
    have hoka := (FvarsOk.of_app hok).2
    simp only [AnnotOk] at ha
    obtain ⟨-, haa, -⟩ := ha
    obtain ⟨hia', -⟩ := ihw hwa hw.2 hb.2 hLba hoka haa
    have hia : interpExpr V m.val env φ d ρ a =
        some (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n) :=
      hia'.symm.trans (interpExpr_rawNatLit hs hraw)
    refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
      by simp [Expr.looseBVarsBounded],
      (fun l hl => by simp [Expr.fvarLeaves] at hl),
      (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
    rw [interpExpr_lit hs,
      interp_app1 (interp_const_mono hfp
        (show (ConstantInfo.defnInfo cvp vp).toConstantVal.levelParams = []
          from hlpp)) hia,
      natOpVal_pred m hfp φ n]
  · -- binary operations
    have hc : c ∈ natOpNames := by
      rcases hor with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hs := (natOpGuard_inv hguard).1
    obtain ⟨cvc, vc, hfc, hlpc⟩ := natOpGuard_self_defn hc hguard
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    have hLba : Expr.LeavesBounded a := fun l hl =>
      hLb l (by simp [fvarLeaves, hl])
    have hLbb : Expr.LeavesBounded b := fun l hl =>
      hLb l (by simp [fvarLeaves, hl])
    obtain ⟨hokf, hokb⟩ := FvarsOk.of_app hok
    have hoka := (FvarsOk.of_app hokf).2
    simp only [AnnotOk] at ha
    obtain ⟨ha1, hab, -⟩ := ha
    obtain ⟨-, haa, -⟩ := ha1
    obtain ⟨hia', -⟩ := ihw hwa hw.1.2 hb.1.2 hLba hoka haa
    obtain ⟨hib', -⟩ := ihw hwb hw.2 hb.2 hLbb hokb hab
    have hia : interpExpr V m.val env φ d ρ a =
        some (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n₁) :=
      hia'.symm.trans (interpExpr_rawNatLit hs hraw1)
    have hib : interpExpr V m.val env φ d ρ b =
        some (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n₂) :=
      hib'.symm.trans (interpExpr_rawNatLit hs hraw2)
    have hie : interpExpr V m.val env φ d ρ (.app (.app (.const c []) a) b) =
        some (app (app (m.val c φ)
          (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n₁))
          (natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n₂)) :=
      interp_app1 (interp_app1 (interp_const_mono hfc
        (show (ConstantInfo.defnInfo cvc vc).toConstantVal.levelParams = []
          from hlpc)) hia) hib
    rcases hor with rfl | rfl | rfl | rfl | rfl | rfl
    · -- add
      have he₂ : e₂ = .lit (.natVal (n₁ + n₂)) := by
        rw [show natOpResult natAddName n₁ n₂ =
            some (.lit (.natVal (n₁ + n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_add m hfc φ n₁ n₂]
    · -- sub
      have he₂ : e₂ = .lit (.natVal (n₁ - n₂)) := by
        rw [show natOpResult natSubName n₁ n₂ =
            some (.lit (.natVal (n₁ - n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_sub m hfc φ n₁ n₂]
    · -- mul
      have he₂ : e₂ = .lit (.natVal (n₁ * n₂)) := by
        rw [show natOpResult natMulName n₁ n₂ =
            some (.lit (.natVal (n₁ * n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_mul m hfc φ n₁ n₂]
    · -- pow
      have he₂ : e₂ = .lit (.natVal (n₁ ^ n₂)) := by
        rw [show natOpResult natPowName n₁ n₂ =
            some (.lit (.natVal (n₁ ^ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_pow m hfc φ n₁ n₂]
    · -- beq
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ :=
        (natOpGuard_inv hguard).2.2 (Or.inl rfl)
      have he₂ : e₂ = .const (if n₁ = n₂ then boolTrueName else boolFalseName)
          [] := by
        rw [show natOpResult natBeqName n₁ n₂ =
            some (.const (if n₁ = n₂ then boolTrueName else boolFalseName) [])
          by simp +decide [natOpResult]] at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by split <;> simp [AnnotOk], by split <;> simp [WScoped],
        by split <;> simp [Expr.looseBVarsBounded],
        (fun l hl => by split at hl <;> simp [Expr.fvarLeaves] at hl),
        (fun l hl => by split at hl <;> simp [Expr.fvarLeaves] at hl)⟩
      rw [hie, natOpVal_beq m hfc φ n₁ n₂]
      by_cases hn : n₁ = n₂
      · rw [if_pos hn, if_pos hn, interp_const_mono hT hlpT]
      · rw [if_neg hn, if_neg hn, interp_const_mono hF hlpF]
    · -- ble
      obtain ⟨⟨ciT, hT, hlpT⟩, ⟨ciF, hF, hlpF⟩⟩ :=
        (natOpGuard_inv hguard).2.2 (Or.inr rfl)
      have he₂ : e₂ = .const (if n₁ ≤ n₂ then boolTrueName else boolFalseName)
          [] := by
        rw [show natOpResult natBleName n₁ n₂ =
            some (.const (if n₁ ≤ n₂ then boolTrueName else boolFalseName) [])
          by simp +decide [natOpResult]] at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by split <;> simp [AnnotOk], by split <;> simp [WScoped],
        by split <;> simp [Expr.looseBVarsBounded],
        (fun l hl => by split at hl <;> simp [Expr.fvarLeaves] at hl),
        (fun l hl => by split at hl <;> simp [Expr.fvarLeaves] at hl)⟩
      rw [hie, natOpVal_ble m hfc φ n₁ n₂]
      by_cases hn : n₁ ≤ n₂
      · rw [if_pos hn, if_pos hn, interp_const_mono hT hlpT]
      · rw [if_neg hn, if_neg hn, interp_const_mono hF hlpF]

/-- Inversion of a one-step delta unfolding. -/
theorem unfoldDefinition_inv {env : Env} {e e₂ : Expr}
    (h : unfoldDefinition env e = some e₂) :
    ∃ n us cv value, e.getAppFn = .const n us ∧
      env.find? n = some (.defnInfo cv value) ∧
      us.length = cv.levelParams.length ∧
      e₂ = Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
        e.getAppArgs := by
  unfold unfoldDefinition at h
  revert h
  match hfn : e.getAppFn with
  | .const n us => ?_
  | .bvar _ | .fvar _ _ _ | .sort _ | .app _ _ | .lam _ _ _ _
  | .forallE _ _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ =>
    intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  match hf : env.find? n with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value) => ?_
  intro h
  dsimp only at h
  revert h
  split
  case isTrue hal =>
    intro h
    simp only [Option.some.injEq] at h
    exact ⟨n, us, cv, value, rfl, hf, hal, h.symm⟩
  case isFalse =>
    intro h; exact nomatch h

/-- Soundness of a one-step delta unfolding: the definition's stored
value interprets to the constant's value (`defn_eq`), so replacing the
head preserves the spine's interpretation, and the stored annotation
truthfulness transfers along the spine. -/
theorem unfoldDefinition_sound (m : EnvModel V env) {d : Nat}
    {e e₂ : Expr} {ρ : Nat → V}
    (hu : unfoldDefinition env e = some e₂)
    (hw : WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hok : FvarsOk V m.val env φ d ρ e)
    (ha : AnnotOk V m.val env φ d ρ e) :
    interpExpr V m.val env φ d ρ e₂ = interpExpr V m.val env φ d ρ e ∧
    AnnotOk V m.val env φ d ρ e₂ ∧ WScoped d e₂ ∧
    e₂.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e₂ ∧
    FvarsOk V m.val env φ d ρ e₂ := by
  have hsynW := unfoldDefinition_WScoped m.wf hu hw
  have hsynB := unfoldDefinition_looseBVars m.wf hu hb
  have hsynL : Expr.LeavesBounded e₂ := fun l hl =>
    hLb l (unfoldDefinition_fvarLeaves m.wf hu l hl)
  have hsynO : FvarsOk V m.val env φ d ρ e₂ :=
    FvarsOk.of_subset (unfoldDefinition_fvarLeaves m.wf hu) hok
  obtain ⟨n, us, cv, value, hfn, hf, hal, rfl⟩ := unfoldDefinition_inv hu
  -- head facts
  obtain ⟨-, -, -, -, hval, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
  obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
  have hcl : (value.instantiateLevelParams cv.levelParams us).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hvc
  have hstored := (m.annot_ok _ (List.mem_of_find?_eq_some hf)
    (Level.substFn φ cv.levelParams us)).2 cv value rfl
  have hinst := AnnotOk.instLevels m.val_params value 0 (rho0 V) hstored
  have hA₂ : AnnotOk V m.val env φ d ρ
      (value.instantiateLevelParams cv.levelParams us) :=
    AnnotOk.closed_invariant hcl d ρ hinst
  have hname : cv.name = n := by
    have := find?_name hf
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
  have hi₂ : interpExpr V m.val env φ d ρ
      (value.instantiateLevelParams cv.levelParams us) =
      some (m.val n (Level.substFn φ cv.levelParams us)) := by
    rw [interp_closed_invariant hcl]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    have hde := m.defn_eq cv value (List.mem_of_find?_eq_some hf)
      (Level.substFn φ cv.levelParams us)
    unfold interpClosed at hde
    rw [hde, hname]
  have hi₁ : interpExpr V m.val env φ d ρ (.const n us) =
      some (m.val n (Level.substFn φ cv.levelParams us)) := by
    rw [interp_const hf hal]
    rfl
  have hspine : e = Expr.mkAppN (.const n us) e.getAppArgs := by
    have := (Expr.mkAppN_getApp e).symm
    rw [hfn] at this
    exact this
  cases hargs : e.getAppArgs with
  | nil =>
    rw [hargs] at hsynW hsynB hsynL hsynO hspine
    refine ⟨?_, hA₂, hsynW, hsynB, hsynL, hsynO⟩
    rw [show Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
        [] = value.instantiateLevelParams cv.levelParams us from rfl,
      hi₂, hspine]
    rw [show Expr.mkAppN (.const n us) [] = (.const n us : Expr) from rfl,
      hi₁]
  | cons x xs =>
    rw [hargs] at hsynW hsynB hsynL hsynO hspine
    have ha' : AnnotOk V m.val env φ d ρ
        (Expr.mkAppN (.const n us) (x :: xs)) := hspine ▸ ha
    obtain ⟨-, hxsA, vf, vs, hif, hsp, hchain, hifold⟩ :=
      annotOk_spine_inv _ _ (by simp) ha'
    have hvf : vf = m.val n (Level.substFn φ cv.levelParams us) := by
      rw [hi₁] at hif
      exact (Option.some.inj hif).symm
    obtain ⟨hA₂', hi₂'⟩ := annotOk_spine (x :: xs)
      (value.instantiateLevelParams cv.levelParams us) hA₂
      (hvf ▸ hi₂) hxsA hsp hchain
    refine ⟨?_, hA₂', hsynW, hsynB, hsynL, hsynO⟩
    rw [hi₂', hspine]
    exact hifold.symm

/-- The reduction loop preserves the interpretation and annotation
truthfulness: a `whnfCore` step, then literal acceleration or one
delta unfolding, then the loop again. -/
theorem whnfLoop_claims (m : EnvModel V env)
    (ihwc : WhnfCoreClaims m φ fuel) (ihw : WhnfClaims m φ fuel) :
    WhnfClaims m φ (fuel + 1) := by
  intro d e e' ρ h hw hb hLb hok ha
  obtain ⟨e₁, hwc, hcase⟩ := whnf_loop_inv h
  obtain ⟨hi1, ha1⟩ := ihwc hwc hw hb hLb hok ha
  have hw1 := whnfCore_WScoped m.wf fuel hwc hw
  have hb1 := whnfCore_looseBVars m.wf fuel hwc hb
  have hLb1 : Expr.LeavesBounded e₁ := fun l hl =>
    hLb l (whnfCore_fvarLeaves m.wf fuel hwc l hl)
  have hok1 := whnfCore_FvarsOk m.wf fuel hwc hok
  rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
  · obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      reduceNat_sound m ihw hrn hw1 hb1 hLb1 hok1 ha1
    obtain ⟨hi3, ha3⟩ := ihw hcont hw2 hb2 hLb2 hok2 ha2
    exact ⟨by rw [hi3, hi2, hi1], ha3⟩
  · obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      unfoldDefinition_sound m hu hw1 hb1 hLb1 hok1 ha1
    obtain ⟨hi3, ha3⟩ := ihw hcont hw2 hb2 hLb2 hok2 ha2
    exact ⟨by rw [hi3, hi2, hi1], ha3⟩
  · exact ⟨hi1, ha1⟩

end Claims

end Setlec
