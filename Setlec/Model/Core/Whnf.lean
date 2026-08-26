import Setlec.Model.Core.Iota
import Setlec.Model.NatOps
import Setlec.Verify.Mono

/-!
# Checker-core soundness: Whnf

Part of the mutual soundness claims layer (split from
`Setlec/Model/TypeChecker.lean`; see that module's docstring).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-! Fuel-lifted inversions for the certificate walk of the native pair
projection (task #100: the walk replaces the collapse-refuted
`PairMkFacts` domain clauses; `Verify/Mono.lean` lifts the one-level
inner facts back to the claims' fuel). -/

private theorem whnf_forallE_eq {env : Env} {fuel d : Nat} {n : Name}
    {t b e' : Expr} {mb : BinderMeta}
    (h : whnf env fuel d (.forallE n t b mb) = .ok e') :
    e' = .forallE n t b mb := by
  have h1 := whnf_mono (Nat.le_add_right fuel 2) h
  have h2 : whnf env (fuel + 2) d (.forallE n t b mb) =
      .ok (.forallE n t b mb) := by
    -- one iteration of the reduction loop suffices (task #106: the
    -- budget is `irreducible`, so peel it with its positivity witness)
    obtain ⟨k, hk⟩ := whnfLoopFuel_succ
    rw [whnf_succ]
    show whnfLoop (pureFns env (fuel + 1)) env d whnfLoopFuel _ = _
    rw [hk]
    rfl
  rw [h1] at h2
  exact Except.ok.inj h2

private theorem inferTypeCore_app_inv' {env : Env} {fuel d : Nat}
    {f a t : Expr} (h : inferTypeCore env fuel d (.app f a) = .ok t) :
    ∃ tf n' ty' body' m', inferTypeCore env fuel d f = .ok tf ∧
      whnf env fuel d tf = .ok (.forallE n' ty' body' m') ∧
      t = body'.instantiate1 a ∧
      ∃ ta, inferTypeCore env fuel d a = .ok ta ∧
        isDefEqCore env fuel d ta ty' = .ok true := by
  match fuel, h with
  | 0, h => rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    obtain ⟨tf, n', ty', body', m', h1, h2, h3, ta, h4, h5⟩ :=
      inferTypeCore_app_inv h
    exact ⟨tf, n', ty', body', m', inferTypeCore_mono (Nat.le_succ _) h1,
      whnf_mono (Nat.le_succ _) h2, h3, ta,
      inferTypeCore_mono (Nat.le_succ _) h4,
      isDefEqCore_mono (Nat.le_succ _) h5⟩

private theorem inferTypeCore_const_inv {env : Env} {fuel d : Nat}
    {n : Name} {us : List Level} {t : Expr}
    (h : inferTypeCore env fuel d (.const n us) = .ok t) :
    ∃ ci, env.find? n = some ci ∧
      t = ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us := by
  match fuel, h with
  | 0, h => rw [inferTypeCore_zero] at h; exact nomatch h
  | fuel + 1, h =>
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, pure, Except.pure, Bind.bind,
      Except.bind] at h
    revert h
    cases hf : env.find? n with
    | none =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    | some ci =>
      intro h
      dsimp only at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact ⟨ci, rfl, h.symm⟩
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h

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
    -- zeta: the reduct is the body instantiated with the value; its
    -- interpretation and truthfulness come from the letE `AnnotOk`
    -- clause through the substitution lemmas (`interp_beta`,
    -- `AnnotOk_beta`), exactly as in the beta case
    rw [whnfCore_succ] at h
    simp only [whnfCoreBody, whnfCore_def] at h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, haopen⟩ := ha
    have hfb : fvarsBelow d bb := hw.2.2.fvarsBelow
    have hwred : WScoped d (bb.instantiate1 vv) :=
      WScoped.instantiate1_gen hw.2.1 0 hw.2.2
    have hbred : (bb.instantiate1 vv).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
    have hLbred : Expr.LeavesBounded (bb.instantiate1 vv) := fun l hl => by
      rcases fvarLeaves_instantiate1 bb 0 hl with h2 | h2
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inr h2)
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr h2))
    have hokred : FvarsOk V m.val env φ d ρ (bb.instantiate1 vv) :=
      fun l hl => by
        rcases fvarLeaves_instantiate1 bb 0 hl with h2 | h2
        · exact hok l (by
            simp only [fvarLeaves, List.mem_append]; exact Or.inr h2)
        · exact hok l (by
            simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr h2))
    have hared : AnnotOk V m.val env φ d ρ (bb.instantiate1 vv) :=
      AnnotOk_beta hfb hw.2.1 hb.1.2 hxv hav 0 haopen
    obtain ⟨hie, hae⟩ := ihwc h hwred hbred hLbred hokred hared
    refine ⟨?_, hae⟩
    rw [hie]
    rw [interp_beta (n := nn) (ty := tt) hfb hw.2.1 hb.1.2 hxv 0]
    simp only [interpExpr, hxv]
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
    obtain ⟨haf, haa, vf, va, A, B, hfi, hai, hpi, hvA⟩ := ha
    obtain ⟨f', hwf, hcase⟩ := whnf_app_inv h
    obtain ⟨hif, haf'⟩ := ihwc hwf hw.1 hb.1 hLbf hokf haf
    rcases hcase with ⟨n, ty, body, mm, rfl, hbeta, ta, hta, hde⟩ |
      ⟨e'', hio, hwe''⟩ | rfl
    · -- beta (always certified; task #100 de-gating)
      have hwlam := whnfCore_WScoped m.wf fuel hwf hw.1
      have hblam := whnfCore_looseBVars m.wf fuel hwf hb.1
      have hLblam : Expr.LeavesBounded (Expr.lam n ty body mm) := fun l hl =>
        hLbf l (whnfCore_fvarLeaves m.wf fuel hwf l hl)
      have hoklam : FvarsOk V m.val env φ d ρ (.lam n ty body mm) :=
        whnfCore_FvarsOk m.wf fuel hwf hokf
      simp only [WScoped] at hwlam
      simp only [looseBVarsBounded, Bool.and_eq_true] at hblam
      simp only [AnnotOk] at haf'
      obtain ⟨haty, hcond⟩ := haf'
      have hfi' : interpExpr V m.val env φ d ρ (.lam n ty body mm) = some vf := by
        rw [hif]; exact hfi
      rw [interpExpr] at hfi'
      cases hty : interpExpr V m.val env φ d ρ ty with
      | none => rw [hty] at hfi'; exact nomatch hfi'
      | some Aty =>
      rw [hty] at hfi'
      simp only [Option.some.injEq] at hfi'
      -- the argument is in the λ's domain: the (unconditional)
      -- certificate hands the fact directly
      have hdom : va ∈ˢ Aty := by
        obtain ⟨-, ⟨va₂, vta, hai₂, htai, hmema⟩, hAta⟩ :=
          ihi hta hw.2 hb.2 hLba hoka
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
      obtain ⟨w, Bl, hwi, hwB⟩ := hwfact
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
      have happi : interpExpr V m.val env φ d ρ (.app f a) =
          some (SetTheory.app vf va) := by
        rw [interpExpr, hfi, hai]
      rw [hi2, hbeta_eq, hwi, happi]
      simp only [Option.some.injEq]
      rw [← hfi', app_lamC hdom]
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
        exact ⟨haf', haa, vf, va, A, B, hif.trans hfi, hai, hpi, hvA⟩
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
        refine ⟨haf', haa, vf, va, A, B, ?_, hai, hpi, hvA⟩
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
    obtain ⟨e₁', e₂, he, hlit, hcase⟩ := whnf_proj_inv h
    obtain ⟨hie₁, hae₁⟩ := ihw he hw hb hLbe hoke hae
    -- the string-literal expansion step's claims package (identity
    -- except on a supported string literal)
    have hw₁ := whnf_WScoped m.wf fuel he hw
    have hb₁ := whnf_looseBVars m.wf fuel he hb
    have hLb₁ : Expr.LeavesBounded e₁' := fun l hl =>
      hLbe l (whnf_fvarLeaves m.wf fuel he l hl)
    have hok₁ := whnf_FvarsOk m.wf fuel he hoke
    obtain ⟨hie₂, hae₂, hwC, hbC, hLbC, hokC⟩ :=
      projLitToCtor_claims ihw hlit hw₁ hb₁ hLb₁ hok₁ hae₁
    have hie : interpExpr V m.val env φ d ρ e₂ =
        interpExpr V m.val env φ d ρ e := hie₂.trans hie₁
    rcases hcase with rfl |
      ⟨us, entry, hfn, hf, hnat, hi2, hlen, hus, hred, hcert⟩
    · -- stuck projection
      refine ⟨?_, ?_⟩
      · simp only [interpExpr]
        rw [hie]
      · simp only [AnnotOk]
        refine ⟨hae₂, hilt, veC, uC, vC, AC, BfC, ?_, hsigC, hAuC, hBfC⟩
        rw [hie]; exact hveiC
    · -- projection through a native table entry: the model identifies
      -- the pinned pair through `ProjOk`, never by name
      obtain ⟨hpin, hpsig, hpsigMk⟩ :=
        m.proj_ok _ _ (Env.findProj?_some hf) hnat
      have hidx : entry.idx = i := by
        have h1 := List.find?_some (Env.findProj?_some hf)
        have h2 : (ConstantInfo.projInfo entry).name = projFnName sn i :=
          eq_of_beq (by simpa using h1)
        simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
        exact (projFnName_inj h2).2
      -- concrete fields of the pinned entries
      have hctor : entry.ctor = psigmaMkName := by
        rcases hpin with rfl | rfl <;> rfl
      have hnPe : entry.numParams = 2 := by
        rcases hpin with rfl | rfl <;> rfl
      have hnFe : entry.numFields = 2 := by
        rcases hpin with rfl | rfl <;> rfl
      have hus2 : us.length = 2 := by
        rw [hus]
        rcases hpin with rfl | rfl <;> rfl
      rw [hctor] at hfn
      rw [hnPe] at hred
      rw [hnPe, hnFe] at hlen
      -- the pinned constructor's stored facts
      obtain ⟨cvMk, hfMk⟩ : ∃ cvMk, env.find? psigmaMkName =
          some (.ctorInfo cvMk 2 2) := ⟨_, by rw [hpsigMk]; rfl⟩
      obtain ⟨-, -, hlp, hmkfacts⟩ := m.ind_ok.right.left cvMk 2 2 hfMk
      obtain ⟨l0, l1, rfl⟩ := List.length_two hus2
      -- the level guards, in the pinned entries' concrete shape
      have hstructS : Level.subst entry.levelParams [l0, l1]
          entry.structSort = .max l0 l1 := by
        rcases hpin with rfl | rfl <;>
          simp [pairFstEntry, pairSndEntry, Level.subst, Level.subst.go,
            uN, vN]
      have hfieldS : Level.subst entry.levelParams [l0, l1]
          entry.fieldSort = ([l0, l1].getD i .zero) := by
        rcases hpin with rfl | rfl <;>
          (rw [← hidx];
           simp [pairFstEntry, pairSndEntry, Level.subst, Level.subst.go,
             uN, vN])
      rw [hstructS, hfieldS] at hcert
      obtain ⟨α, β, a, b, hargs⟩ := List.length_four hlen
      have he₂ : e₂ = .app (.app (.app (.app (.const psigmaMkName [l0, l1]) α) β) a) b := by
        have h0 := Expr.mkAppN_getApp e₂
        rw [hfn, hargs] at h0
        exact h0.symm
      have hi2' : i = 0 ∨ i = 1 := by
        rw [hnFe] at hi2
        omega
      have hargd : e₂.getAppArgs.getD (2 + i) (.bvar 0) = if i = 0 then a else b := by
        rw [hargs]
        rcases hi2' with rfl | rfl
        · rfl
        · rfl
      -- pristine invariants of the converted struct (for the
      -- certificates; already assembled by `projLitToCtor_claims`)
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
      obtain ⟨ha3, hab, vf₃, vb, A₃, B₃, hf₃i, hbi, hpi₃, hvb₃⟩ := hae₂
      try simp only [AnnotOk] at ha3
      obtain ⟨ha2, haa, vf₂, va, A₂, B₂, hf₂i, hai, hpi₂, hva₂⟩ := ha3
      try simp only [AnnotOk] at ha2
      obtain ⟨ha1, haβ, vf₁, vβ, A₁, B₁, hf₁i, hβi, hpi₁, hvβ₁⟩ := ha2
      try simp only [AnnotOk] at ha1
      obtain ⟨hac, haα, vf₀, vα, A₀, B₀, hci, hαi, hpi₀, hvα₀⟩ := ha1
      -- the head constant's value
      rw [interpExpr, hfMk] at hci
      dsimp only [ConstantInfo.toConstantVal] at hci
      obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cvMk.levelParams [l0, l1] := ⟨_, rfl⟩
      rw [← hψ'] at hci
      by_cases hal : ([l0, l1] : List Level).length = cvMk.levelParams.length
      case neg => simp only [hal, if_false] at hci; exact nomatch hci
      simp only [hal, if_true] at hci
      have hval : interpExpr V m.val env φ d ρ (.const psigmaMkName [l0, l1]) =
          some (m.val psigmaMkName ψ') := by
        rw [interpExpr, hfMk]
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
        obtain ⟨ta, sta, uT, te, ste, wT, hta, hsta, hwta, heq1, hte, hste, hwte, heq2⟩ :=
          projCert_inv hcert
        have hwT0 : Level.eval φ wT = 0 := by
          rw [Level.isEquiv_sound heq2 φ]
          simp only [Level.eval, List.getD, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some]
          rw [← hψu, ← hψv]
          exact hw0
        have hept : interpExpr V m.val env φ d ρ e₂ = some pt :=
          sortCert_pt ihw ihi hte hste hwte hwT0 hwC hbC hLbC hokC
        have hveCpt : veC = pt := by
          have : some veC = some pt := by
            rw [← hveiC, ← hie, hept]
          exact Option.some.inj this
        -- the projected argument is a proof point too
        rw [hnPe] at hta
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
            sortCert_pt ihw ihi hta hsta hwta huT0 hwa hba hLba hoka
          obtain ⟨hired, hared⟩ := ihwc hred hwa hba hLba hoka haa
          refine ⟨?_, hared⟩
          rw [hired, hapt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, sfst_pt]
          simp
        · rw [if_neg (by omega)] at hargd
          rw [hargd] at hred
          have hbpt : interpExpr V m.val env φ d ρ b = some pt :=
            sortCert_pt ihw ihi hta hsta hwta huT0 hwb hbb hLbb hokb
          obtain ⟨hired, hared⟩ := ihwc hred hwb hbb hLbb hokb hab
          refine ⟨?_, hared⟩
          rw [hired, hbpt]
          simp only [interpExpr, hveiC]
          rw [hveCpt, ssnd_pt]
          simp
      · -- no collapse: the certificate's inference walk on the pinned
        -- constructor type pins the canonical argument memberships
        -- (task #100: the old value-side domain clauses are false
        -- under the collapse), then the stored fold computes the pair
        have hfacts := hmkfacts ψ'
        -- α/β invariant bundles
        have hLbα : Expr.LeavesBounded α := fun l hl => hLbe₂ l (by
          simp only [fvarLeaves, List.mem_append]
          exact Or.inl (Or.inl (Or.inl (Or.inr hl))))
        have hLbβ : Expr.LeavesBounded β := fun l hl => hLbe₂ l (by
          simp only [fvarLeaves, List.mem_append]
          exact Or.inl (Or.inl (Or.inr hl)))
        have hokα : FvarsOk V m.val env φ d ρ α := fun l hl => hoke₂ l (by
          simp only [fvarLeaves, List.mem_append]
          exact Or.inl (Or.inl (Or.inl (Or.inr hl))))
        have hokβ : FvarsOk V m.val env φ d ρ β := fun l hl => hoke₂ l (by
          simp only [fvarLeaves, List.mem_append]
          exact Or.inl (Or.inl (Or.inr hl)))
        -- the pinned block fixes the stored constructor type
        obtain ⟨hpinned, -⟩ := m.ind_ok.2.2.2.1 psigmaMkName _ hfMk rfl
          (by rfl)
        rw [show pinnedInfo psigmaMkName = psigmaMkA from rfl] at hpinned
        rw [show psigmaMkA =
          ConstantInfo.ctorInfo psigmaMkA.toConstantVal 2 2 from rfl]
          at hpinned
        injection hpinned with hcv
        -- the certificate's inference chain on the constructor spine
        obtain ⟨tc, stc, uT', te, ste, wT', -, -, -, -, hte, -, -, -⟩ :=
          projCert_inv hcert
        rw [he₂] at hte
        obtain ⟨tf₃, n₃, ty₃, body₃, m₃, hitf₃, hwtf₃, -, tb', hitb, hdeb⟩ :=
          inferTypeCore_app_inv' hte
        obtain ⟨tf₂, n₂', ty₂', body₂', m₂', hitf₂, hwtf₂, htf₃eq, ta',
          hita, hdea⟩ := inferTypeCore_app_inv' hitf₃
        obtain ⟨tf₁, n₁', ty₁', body₁', m₁', hitf₁, hwtf₁, htf₂eq, tβ,
          hitβ, hdeβ⟩ := inferTypeCore_app_inv' hitf₂
        obtain ⟨tf₀, n₀', ty₀', body₀', m₀', hitf₀, hwtf₀, htf₁eq, tα,
          hitα, hdeα⟩ := inferTypeCore_app_inv' hitf₁
        obtain ⟨ciMk, hfMk', htf₀eq⟩ := inferTypeCore_const_inv hitf₀
        obtain rfl : ciMk = ConstantInfo.ctorInfo cvMk 2 2 := by
          rw [hfMk'] at hfMk
          exact (Option.some.inj hfMk)
        rw [show (ConstantInfo.ctorInfo cvMk 2 2).toConstantVal = cvMk
          from rfl, hcv] at htf₀eq
        -- the instantiated pinned telescope, walked level by level
        have htf₀c : tf₀ =
            Expr.forallE (Name.anonymous.str "α") (.sort l0)
              (Expr.forallE (Name.anonymous.str "β")
                (Expr.forallE (Name.anonymous.str "x") (.bvar 0) (.sort l1)
                  ⟨.default⟩)
                (Expr.forallE (Name.anonymous.str "fst") (.bvar 1)
                  (Expr.forallE (Name.anonymous.str "snd")
                    (.app (.bvar 1) (.bvar 0))
                    (.app (.app (.const psigmaName [l0, l1]) (.bvar 3))
                      (.bvar 2))
                    ⟨.default⟩)
                  ⟨.default⟩)
                ⟨.implicit⟩)
              ⟨.implicit⟩ := by
          rw [htf₀eq]
          rfl
        obtain ⟨hn₀, hty₀, hbody₀, -⟩ :=
          Expr.forallE.inj (whnf_forallE_eq (htf₀c ▸ hwtf₀))
        have htf₁c : tf₁ =
            Expr.forallE (Name.anonymous.str "β")
              (Expr.forallE (Name.anonymous.str "x") α (.sort l1)
                ⟨.default⟩)
              (Expr.forallE (Name.anonymous.str "fst") α
                (Expr.forallE (Name.anonymous.str "snd")
                  (.app (.bvar 1) (.bvar 0))
                  (.app (.app (.const psigmaName [l0, l1]) α) (.bvar 2))
                  ⟨.default⟩)
                ⟨.default⟩)
              ⟨.implicit⟩ := by
          rw [htf₁eq, hbody₀]
          simp [Expr.instantiate1]
        obtain ⟨hn₁, hty₁, hbody₁, -⟩ :=
          Expr.forallE.inj (whnf_forallE_eq (htf₁c ▸ hwtf₁))
        have htf₂c : tf₂ =
            Expr.forallE (Name.anonymous.str "fst") α
              (Expr.forallE (Name.anonymous.str "snd")
                (.app β (.bvar 0))
                (.app (.app (.const psigmaName [l0, l1]) α) β)
                ⟨.default⟩)
              ⟨.default⟩ := by
          rw [htf₂eq, hbody₁]
          simp [Expr.instantiate1, instantiate1_eq_self hbα,
            instantiate1_eq_self
              (looseBVarsBounded_mono (Nat.zero_le _) hbα)]
        obtain ⟨hn₂, hty₂, hbody₂, -⟩ :=
          Expr.forallE.inj (whnf_forallE_eq (htf₂c ▸ hwtf₂))
        have htf₃c : tf₃ =
            Expr.forallE (Name.anonymous.str "snd") (.app β a)
              (.app (.app (.const psigmaName [l0, l1]) α) β)
              ⟨.default⟩ := by
          rw [htf₃eq, hbody₂]
          simp [Expr.instantiate1, instantiate1_eq_self hbα,
            instantiate1_eq_self hbβ,
            instantiate1_eq_self
              (looseBVarsBounded_mono (Nat.zero_le _) hbα),
            instantiate1_eq_self
              (looseBVarsBounded_mono (Nat.zero_le _) hbβ)]
        obtain ⟨hn₃, hty₃, hbody₃, -⟩ :=
          Expr.forallE.inj (whnf_forallE_eq (htf₃c ▸ hwtf₃))
        -- interpretations of the walked domains
        have hity₀ : interpExpr V m.val env φ d ρ ty₀' =
            some (univ (ψ' uN)) := by
          rw [hty₀]
          simp only [interpExpr, Option.some.injEq]
          rw [hψu]
        have hity₁ : interpExpr V m.val env φ d ρ ty₁' =
            some (pi (ψ' vN + 1) vα (fun _ => univ (ψ' vN))) := by
          rw [hty₁]
          rw [interpExpr, hαi]
          refine congrArg some (congrArg (piC vα) (funext fun x => ?_))
          rw [show (Expr.sort l1).instantiate1
            (.fvar d (Name.anonymous.str "x") α) = Expr.sort l1 from rfl]
          simp only [interpExpr, Option.getD_some]
          rw [hψv]
        have hity₂ : interpExpr V m.val env φ d ρ ty₂' = some vα := by
          rw [hty₂]
          exact hαi
        have hity₃ : interpExpr V m.val env φ d ρ ty₃ =
            some (app vβ va) := by
          rw [hty₃]
          rw [interpExpr, hβi, hai]
        -- the arguments' membership in the walked domains, through
        -- the certified defeqs
        have hwty₀ : WScoped d ty₀' := by rw [hty₀]; simp [WScoped]
        have hbty₀ : ty₀'.looseBVarsBounded 0 = true := by rw [hty₀]; rfl
        have hLbty₀ : Expr.LeavesBounded ty₀' := by
          rw [hty₀]
          intro l hl
          simp [fvarLeaves] at hl
        have hokty₀ : FvarsOk V m.val env φ d ρ ty₀' := by
          rw [hty₀]
          intro l hl
          simp [fvarLeaves] at hl
        have haty₀ : AnnotOk V m.val env φ d ρ ty₀' := by
          rw [hty₀]
          simp [AnnotOk]
        have hwtα := inferTypeCore_WScoped m.wf fuel hitα hwα
        have hbtα := inferTypeCore_looseBVars m.wf fuel hitα hwα hbα hLbα
        have hLbtα : Expr.LeavesBounded tα := fun l hl =>
          hLbα l (inferTypeCore_fvarLeaves m.wf fuel hitα hwα l hl)
        have hoktα : FvarsOk V m.val env φ d ρ tα :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hitα hwα)
            hokα
        obtain ⟨-, ⟨vα', vtα, hiα', htαi, hmemα⟩, hAtα⟩ :=
          ihi hitα hwα hbα hLbα hokα
        have hvαeq : vα' = vα := by
          rw [hαi] at hiα'
          exact (Option.some.inj hiα').symm
        rw [hvαeq] at hmemα
        have hαmem : vα ∈ˢ univ (ψ' uN) := by
          have hveq := ihd hdeα hwtα hwty₀ hbtα hbty₀ hLbtα hLbty₀
            hoktα hokty₀ hAtα haty₀ htαi hity₀
          rw [← hveq]
          exact hmemα
        have hwty₁ : WScoped d ty₁' := by
          rw [hty₁]
          simp only [WScoped]
          exact ⟨hwα, trivial⟩
        have hbty₁ : ty₁'.looseBVarsBounded 0 = true := by
          rw [hty₁]
          simp [looseBVarsBounded, hbα]
        have hLbty₁ : Expr.LeavesBounded ty₁' := by
          rw [hty₁]
          intro l hl
          refine hLbα l ?_
          simpa [fvarLeaves] using hl
        have hokty₁ : FvarsOk V m.val env φ d ρ ty₁' := by
          rw [hty₁]
          intro l hl
          refine hokα l ?_
          simpa [fvarLeaves] using hl
        have haty₁ : AnnotOk V m.val env φ d ρ ty₁' := by
          rw [hty₁]
          simp only [AnnotOk]
          refine ⟨haα, ?_⟩
          intro x Ax hAx hx
          refine ⟨by simp [Expr.instantiate1, AnnotOk], ?_⟩
          refine ⟨univ (ψ' vN), ?_⟩
          simp only [Expr.instantiate1, interpExpr, Option.some.injEq]
          rw [hψv]
        have hwtβ := inferTypeCore_WScoped m.wf fuel hitβ hwβ
        have hbtβ := inferTypeCore_looseBVars m.wf fuel hitβ hwβ hbβ hLbβ
        have hLbtβ : Expr.LeavesBounded tβ := fun l hl =>
          hLbβ l (inferTypeCore_fvarLeaves m.wf fuel hitβ hwβ l hl)
        have hoktβ : FvarsOk V m.val env φ d ρ tβ :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hitβ hwβ)
            hokβ
        obtain ⟨-, ⟨vβ', vtβ, hiβ', htβi, hmemβ⟩, hAtβ⟩ :=
          ihi hitβ hwβ hbβ hLbβ hokβ
        have hvβeq : vβ' = vβ := by
          rw [hβi] at hiβ'
          exact (Option.some.inj hiβ').symm
        rw [hvβeq] at hmemβ
        have hβmem : vβ ∈ˢ pi (ψ' vN + 1) vα (fun _ => univ (ψ' vN)) := by
          have hveq := ihd hdeβ hwtβ hwty₁ hbtβ hbty₁ hLbtβ hLbty₁
            hoktβ hokty₁ hAtβ haty₁ htβi hity₁
          rw [← hveq]
          exact hmemβ
        have hwta' := inferTypeCore_WScoped m.wf fuel hita hwa
        have hbta' := inferTypeCore_looseBVars m.wf fuel hita hwa hba hLba
        have hLbta' : Expr.LeavesBounded ta' := fun l hl =>
          hLba l (inferTypeCore_fvarLeaves m.wf fuel hita hwa l hl)
        have hokta' : FvarsOk V m.val env φ d ρ ta' :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hita hwa)
            hoka
        obtain ⟨-, ⟨va', vta, hia', htai', hmema⟩, hAta'⟩ :=
          ihi hita hwa hba hLba hoka
        have hvaeq' : va' = va := by
          rw [hai] at hia'
          exact (Option.some.inj hia').symm
        rw [hvaeq'] at hmema
        have hwty₂ : WScoped d ty₂' := by rw [hty₂]; exact hwα
        have hbty₂ : ty₂'.looseBVarsBounded 0 = true := by
          rw [hty₂]; exact hbα
        have hLbty₂ : Expr.LeavesBounded ty₂' := by rw [hty₂]; exact hLbα
        have hokty₂ : FvarsOk V m.val env φ d ρ ty₂' := by
          rw [hty₂]; exact hokα
        have haty₂ : AnnotOk V m.val env φ d ρ ty₂' := by
          rw [hty₂]; exact haα
        have hamem : va ∈ˢ vα := by
          have hveq := ihd hdea hwta' hwty₂ hbta' hbty₂ hLbta' hLbty₂
            hokta' hokty₂ hAta' haty₂ htai' hity₂
          rw [← hveq]
          exact hmema
        have hwtb' := inferTypeCore_WScoped m.wf fuel hitb hwb
        have hbtb' := inferTypeCore_looseBVars m.wf fuel hitb hwb hbb hLbb
        have hLbtb' : Expr.LeavesBounded tb' := fun l hl =>
          hLbb l (inferTypeCore_fvarLeaves m.wf fuel hitb hwb l hl)
        have hoktb' : FvarsOk V m.val env φ d ρ tb' :=
          FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hitb hwb)
            hokb
        obtain ⟨-, ⟨vb', vtb, hib', htbi', hmemb⟩, hAtb'⟩ :=
          ihi hitb hwb hbb hLbb hokb
        have hvbeq' : vb' = vb := by
          rw [hbi] at hib'
          exact (Option.some.inj hib').symm
        rw [hvbeq'] at hmemb
        have hwty₃ : WScoped d ty₃ := by
          rw [hty₃]
          simp only [WScoped]
          exact ⟨hwβ, hwa⟩
        have hbty₃ : ty₃.looseBVarsBounded 0 = true := by
          rw [hty₃]
          simp [looseBVarsBounded, hbβ, hba]
        have hLbty₃ : Expr.LeavesBounded ty₃ := by
          rw [hty₃]
          intro l hl
          simp only [fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hLbβ l hl
          · exact hLba l hl
        have hokty₃ : FvarsOk V m.val env φ d ρ ty₃ := by
          rw [hty₃]
          intro l hl
          simp only [fvarLeaves, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hokβ l hl
          · exact hoka l hl
        have haty₃ : AnnotOk V m.val env φ d ρ ty₃ := by
          rw [hty₃]
          simp only [AnnotOk]
          exact ⟨haβ, haa, vβ, va, vα, (fun _ => univ (ψ' vN)),
            hβi, hai, hβmem, hamem⟩
        have hbmem : vb ∈ˢ app vβ va := by
          have hveq := ihd hdeb hwtb' hwty₃ hbtb' hbty₃ hLbtb' hLbty₃
            hoktb' hokty₃ hAtb' haty₃ htbi' hity₃
          rw [← hveq]
          exact hmemb
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
    (∃ a a' n, e = .app (.const natSuccName []) a ∧
      natLitSupported env = true ∧
      whnf env fuel d a = .ok a' ∧ rawNatLit? a' = some n ∧
      e₂ = .lit (.natVal (n + 1))) ∨
    (∃ c a a' n, e = .app (.const c []) a ∧
      (c = natPredName ∨ c = natLog2Name) ∧
      natOpGuard env c = true ∧
      whnf env fuel d a = .ok a' ∧ rawNatLit? a' = some n ∧
      natOpResult c n 0 = some e₂) ∨
    (∃ c a b a' b' n₁ n₂, e = .app (.app (.const c []) a) b ∧
      (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
       c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
       c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
       c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
       c = natShiftLeftName ∨ c = natShiftRightName) ∧
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
      cases hwa : whnf env fuel d a with
      | error err => intro h; exact nomatch h
      | ok a' =>
      intro h
      dsimp only at h
      revert h
      cases hraw : rawNatLit? a' with
      | none => intro h; simp [hraw, pure, Except.pure] at h
      | some n =>
        intro h
        simp only [hraw, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h
        exact Or.inl ⟨a, a', n, rfl, hs, hwa, hraw, h.symm⟩
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
        exact Or.inr (Or.inl ⟨natPredName, a, a', n, rfl, Or.inl rfl,
          hguard, hwa, hraw, h ▸ hres⟩)
      case isFalse =>
        split
        case isTrue hg =>
          -- the certified `log2` branch
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
          cases hres : natOpResult natLog2Name n 0 with
          | none => rw [hres] at h; simp [pure, Except.pure] at h
          | some r =>
            rw [hres] at h
            simp only [pure, Except.pure, Except.ok.injEq,
              Option.some.injEq] at h
            exact Or.inr (Or.inl ⟨natLog2Name, a, a', n, rfl, Or.inr rfl,
              hguard, hwa, hraw, h ▸ hres⟩)
        case isFalse =>
          -- the capless `log2` decline branch never returns a reduct
          split
          · intro h
            revert h
            cases hw : whnf env fuel d a with
            | error err => intro h; exact nomatch h
            | ok a' =>
            intro h
            dsimp only at h
            revert h
            match rawNatLit? a' with
            | some _ => intro h; exact nomatch h
            | none => intro h; simp [pure, Except.pure] at h
          · intro h; simp [pure, Except.pure] at h
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
    case isFalse =>
      -- the WF-op decline branch never returns a reduct
      split
      · intro h
        revert h
        cases hw1 : whnf env fuel d a with
        | error err => intro h; exact nomatch h
        | ok a' =>
        intro h
        dsimp only at h
        revert h
        cases hw2 : whnf env fuel d b with
        | error err => intro h; exact nomatch h
        | ok b' =>
        intro h
        dsimp only at h
        revert h
        match rawNatLit? a', rawNatLit? b' with
        | some _, some _ => intro h; exact nomatch h
        | some _, none => intro h; simp [pure, Except.pure] at h
        | none, some _ => intro h; simp [pure, Except.pure] at h
        | none, none => intro h; simp [pure, Except.pure] at h
      · intro h; simp [pure, Except.pure] at h

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
    ⟨a, a', n, rfl, hs, hwa, hraw, rfl⟩ |
    ⟨c, a, a', n, rfl, hunary, hguard, hwa, hraw, hres⟩ |
    ⟨c, a, b, a', b', n₁, n₂, rfl, hor, hguard, hwa, hraw1, hwb, hraw2,
      hres⟩
  · -- `succ` folding (through the argument's reduction)
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
    rw [interpExpr_lit hs]
    obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hnn, hzz, hss, hl1, hl2, hl3,
      -⟩ := natLitSupported_inv hs
    simp [interpExpr, hss, ConstantInfo.toConstantVal, hl3, Level.substFn_nil,
      hia, natLitVal]
  · -- the unary fast paths (`pred`, and the pin-certified `log2`)
    have hs := (natOpGuard_inv hguard).1
    obtain ⟨cvp, vp, hntp, hfp, hlpp⟩ :
        ∃ cv v h, env.find? c = some (.defnInfo cv v h) ∧
          cv.levelParams = [] := by
      rcases hunary with rfl | rfl
      · exact natOpGuard_self_defn (by decide) hguard
      · exact natDivModGuard_self_defn (by decide) hguard
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
    rcases hunary with rfl | rfl
    · -- pred
      have he₂ : e₂ = .lit (.natVal (n - 1)) := by
        rw [show natOpResult natPredName n 0 =
            some (.lit (.natVal (n - 1))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs,
        interp_app1 (interp_const_mono hfp
          (show (ConstantInfo.defnInfo cvp vp hntp).toConstantVal.levelParams
            = [] from hlpp)) hia,
        natOpVal_pred m hfp φ n]
    · -- log2 (pin-certified: `EnvModel.div_mod` via `natOpVal_log2`)
      have he₂ : e₂ = .lit (.natVal (Nat.log2 n)) := by
        rw [show natOpResult natLog2Name n 0 =
            some (.lit (.natVal (Nat.log2 n))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs,
        interp_app1 (interp_const_mono hfp
          (show (ConstantInfo.defnInfo cvp vp hntp).toConstantVal.levelParams
            = [] from hlpp)) hia,
        natOpVal_log2 m hfp φ n]
  · -- binary operations
    have hcd : c ∈ natOpNames ∨ c ∈ natDivModNames := by
      rcases hor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Or.inl (by decide)
        | exact Or.inr (by decide)
    have hs := (natOpGuard_inv hguard).1
    obtain ⟨cvc, vc, hntc, hfc, hlpc⟩ :=
      hcd.elim (fun hc => natOpGuard_self_defn hc hguard)
        (fun hc => natDivModGuard_self_defn hc hguard)
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
        (show (ConstantInfo.defnInfo cvc vc hntc).toConstantVal.levelParams = []
          from hlpc)) hia) hib
    rcases hor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
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
        (natOpGuard_inv hguard).2.2 (Or.inr (Or.inl rfl))
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
    · -- div (pin-certified: `EnvModel.div_mod` via `natOpVal_div`)
      have he₂ : e₂ = .lit (.natVal (n₁ / n₂)) := by
        rw [show natOpResult natDivName n₁ n₂ =
            some (.lit (.natVal (n₁ / n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_div m hfc φ n₁ n₂]
    · -- mod (pin-certified: `EnvModel.div_mod` via `natOpVal_mod`)
      have he₂ : e₂ = .lit (.natVal (n₁ % n₂)) := by
        rw [show natOpResult natModName n₁ n₂ =
            some (.lit (.natVal (n₁ % n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_mod m hfc φ n₁ n₂]
    · -- gcd (pin-certified: `EnvModel.div_mod` via `natOpVal_gcd`)
      have he₂ : e₂ = .lit (.natVal (Nat.gcd n₁ n₂)) := by
        rw [show natOpResult natGcdName n₁ n₂ =
            some (.lit (.natVal (Nat.gcd n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_gcd m hfc φ n₁ n₂]
    · -- land (pin-certified: `EnvModel.div_mod` via `natOpVal_land`)
      have he₂ : e₂ = .lit (.natVal (Nat.land n₁ n₂)) := by
        rw [show natOpResult natLandName n₁ n₂ =
            some (.lit (.natVal (Nat.land n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_land m hfc φ n₁ n₂]
    · -- lor (pin-certified: `EnvModel.div_mod` via `natOpVal_lor`)
      have he₂ : e₂ = .lit (.natVal (Nat.lor n₁ n₂)) := by
        rw [show natOpResult natLorName n₁ n₂ =
            some (.lit (.natVal (Nat.lor n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_lor m hfc φ n₁ n₂]
    · -- xor (pin-certified: `EnvModel.div_mod` via `natOpVal_xor`)
      have he₂ : e₂ = .lit (.natVal (Nat.xor n₁ n₂)) := by
        rw [show natOpResult natXorName n₁ n₂ =
            some (.lit (.natVal (Nat.xor n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_xor m hfc φ n₁ n₂]
    · -- shiftLeft (pin-certified: `EnvModel.div_mod` via `natOpVal_shiftLeft`)
      have he₂ : e₂ = .lit (.natVal (Nat.shiftLeft n₁ n₂)) := by
        rw [show natOpResult natShiftLeftName n₁ n₂ =
            some (.lit (.natVal (Nat.shiftLeft n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_shiftLeft m hfc φ n₁ n₂]
    · -- shiftRight (pin-certified: `EnvModel.div_mod` via `natOpVal_shiftRight`)
      have he₂ : e₂ = .lit (.natVal (Nat.shiftRight n₁ n₂)) := by
        rw [show natOpResult natShiftRightName n₁ n₂ =
            some (.lit (.natVal (Nat.shiftRight n₁ n₂))) by simp +decide [natOpResult]]
          at hres
        exact (Option.some.inj hres).symm
      subst he₂
      refine ⟨?_, by simp [AnnotOk], by simp [WScoped],
        by simp [Expr.looseBVarsBounded],
        (fun l hl => by simp [Expr.fvarLeaves] at hl),
        (fun l hl => by simp [Expr.fvarLeaves] at hl)⟩
      rw [interpExpr_lit hs, hie, natOpVal_shiftRight m hfc φ n₁ n₂]

/-- Inversion of a one-step delta unfolding: the head is a stored
definition or theorem with a matching level-list length, and the
result is the (instantiated) value re-applied to the spine. -/
theorem unfoldDefinition_inv {env : Env} {e e₂ : Expr}
    (h : unfoldDefinition env e = some e₂) :
    ∃ n us cv value, e.getAppFn = .const n us ∧
      ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
        env.find? n = some (.thmInfo cv value)) ∧
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
  | some (.projInfo _) => intro h; exact nomatch h
  | some (.thmInfo cv value) =>
    intro h
    dsimp only at h
    revert h
    split
    case isTrue hal =>
      intro h
      simp only [Option.some.injEq] at h
      exact ⟨n, us, cv, value, rfl, Or.inr hf, hal, h.symm⟩
    case isFalse =>
      intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo _ _ _ _) => intro h; exact nomatch h
  | some (.defnInfo cv value hint) => ?_
  intro h
  dsimp only at h
  revert h
  split
  case isTrue hal =>
    intro h
    simp only [Option.some.injEq] at h
    exact ⟨n, us, cv, value, rfl, Or.inl ⟨hint, hf⟩, hal, h.symm⟩
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
  obtain ⟨n, us, cv, value, hfn, hfd, hal, rfl⟩ := unfoldDefinition_inv hu
  -- head facts, uniform over the definition/theorem cases: the stored
  -- value is closed, carries truthful annotations, interprets to the
  -- constant's value, and the head constant interprets accordingly
  obtain ⟨hvc, hvb, hstored, hde, hi₁⟩ :
      value.hasFvar = false ∧ value.looseBVarsBounded 0 = true ∧
      AnnotOk V m.val env (Level.substFn φ cv.levelParams us) 0 (rho0 V)
        value ∧
      interpClosed V m.val env (Level.substFn φ cv.levelParams us) value =
        some (m.val n (Level.substFn φ cv.levelParams us)) ∧
      interpExpr V m.val env φ d ρ (.const n us) =
        some (m.val n (Level.substFn φ cv.levelParams us)) := by
    rcases hfd with ⟨hint, hf⟩ | hf
    · obtain ⟨-, -, -, -, hval, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value hint rfl
      have hname : cv.name = n := by
        have := find?_name hf
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
      refine ⟨hvc, hvb,
        (m.annot_ok _ (List.mem_of_find?_eq_some hf)
          (Level.substFn φ cv.levelParams us)).2 cv value hint rfl,
        hname ▸ m.defn_eq cv value hint (List.mem_of_find?_eq_some hf)
          (Level.substFn φ cv.levelParams us), ?_⟩
      rw [interp_const hf hal]
      rfl
    · obtain ⟨-, -, -, -, -, -, hval⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
      obtain ⟨hvc, -, -, hvb⟩ := hval cv value rfl
      have hname : cv.name = n := by
        have := find?_name hf
        simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
      obtain ⟨hde, hAv⟩ := m.thm_ok cv value (List.mem_of_find?_eq_some hf)
        (Level.substFn φ cv.levelParams us)
      refine ⟨hvc, hvb, hAv, hname ▸ hde, ?_⟩
      rw [interp_const hf hal]
      rfl
  have hcl : (value.instantiateLevelParams cv.levelParams us).hasFvar
      = false := by
    rw [hasFvar_instantiateLevelParams]; exact hvc
  have hinst := AnnotOk.instLevels m.val_params value 0 (rho0 V) hstored
  have hA₂ : AnnotOk V m.val env φ d ρ
      (value.instantiateLevelParams cv.levelParams us) :=
    AnnotOk.closed_invariant hcl d ρ hinst
  have hi₂ : interpExpr V m.val env φ d ρ
      (value.instantiateLevelParams cv.levelParams us) =
      some (m.val n (Level.substFn φ cv.levelParams us)) := by
    rw [interp_closed_invariant hcl]
    unfold interpClosed
    rw [interp_instLevels m.val_params]
    unfold interpClosed at hde
    rw [hde]
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
  -- Task #106: the delta/literal chain is iteration on the loop's own
  -- step budget, so the claim is an induction on that budget at the
  -- *same* knot fuel; `ihwc` covers each step's head normalization and
  -- `ihw` the `whnf` calls inside `reduceNat`.
  suffices hloop : ∀ (n : Nat) {d : Nat} {e e' : Expr} {ρ : Nat → V},
      whnfLoop (pureFns env fuel) env d n e = .ok e' →
      WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
      FvarsOk V m.val env φ d ρ e → AnnotOk V m.val env φ d ρ e →
      interpExpr V m.val env φ d ρ e' = interpExpr V m.val env φ d ρ e ∧
      AnnotOk V m.val env φ d ρ e' by
    intro d e e' ρ h hw hb hLb hok ha
    exact hloop whnfLoopFuel h hw hb hLb hok ha
  intro n
  induction n with
  | zero => intro _ _ _ _ h _ _ _ _ _; exact nomatch h
  | succ n ihN =>
  intro d e e' ρ h hw hb hLb hok ha
  obtain ⟨e₁, hwc, hcase⟩ := whnfStep_inv h
  obtain ⟨hi1, ha1⟩ := ihwc hwc hw hb hLb hok ha
  have hw1 := whnfCore_WScoped m.wf fuel hwc hw
  have hb1 := whnfCore_looseBVars m.wf fuel hwc hb
  have hLb1 : Expr.LeavesBounded e₁ := fun l hl =>
    hLb l (whnfCore_fvarLeaves m.wf fuel hwc l hl)
  have hok1 := whnfCore_FvarsOk m.wf fuel hwc hok
  rcases hcase with ⟨e₂, hrn, hcont⟩ | ⟨-, e₂, hu, hcont⟩ | ⟨-, -, rfl⟩
  · obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      reduceNat_sound m ihw hrn hw1 hb1 hLb1 hok1 ha1
    obtain ⟨hi3, ha3⟩ := ihN hcont hw2 hb2 hLb2 hok2 ha2
    exact ⟨by rw [hi3, hi2, hi1], ha3⟩
  · obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      unfoldDefinition_sound m hu hw1 hb1 hLb1 hok1 ha1
    obtain ⟨hi3, ha3⟩ := ihN hcont hw2 hb2 hLb2 hok2 ha2
    exact ⟨by rw [hi3, hi2, hi1], ha3⟩
  · exact ⟨hi1, ha1⟩

end Claims

end Setlec
