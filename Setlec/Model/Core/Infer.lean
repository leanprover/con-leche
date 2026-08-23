import Setlec.Model.Core.DefEq

/-!
# Checker-core soundness: Infer

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
theorem infer_claims (m : EnvModel V env)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    InferClaims m φ (fuel + 1) := by
  intro d e t ρ h hw hb hLb hok ha
  cases e with
  | sort u =>
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨⟨univ (u.eval φ), univ (u.eval φ + 1), ?_, ?_, univ_mem_univ _⟩, ?_⟩ <;>
      simp [interpExpr, Level.eval, AnnotOk]
  | fvar idx n ty =>
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure,
      Except.pure] at h
    revert h
    split
    case isFalse =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    case isTrue =>
      intro h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨⟨hidx, hAty, T, hT, hmem⟩, hFty⟩ := FvarsOk.of_fvar hok
      exact ⟨⟨ρ idx, T, by simp [interpExpr], hT, hmem⟩, hAty⟩
  | lit l0 =>
    rw [inferTypeCore_succ] at h
    match l0, h with
    | .natVal n, h => ?_
    | .strVal sv, h => ?strCase
    case strCase =>
      dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure,
        Except.pure] at h
      revert h
      split
      case isFalse =>
        intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
      case isTrue hs =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨⟨strLitVal V m.val env φ sv, m.val stringName φ,
          interpExpr_strLit (V := V) hs, interpExpr_const_string hs,
          strLitVal_mem_string m hs φ sv⟩, by simp [AnnotOk]⟩
    dsimp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
    revert h
    split
    case isFalse =>
      intro h
      simp [throw, throwThe, MonadExceptOf.throw] at h
    case isTrue hs =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨⟨natLitVal V (m.val natZeroName φ) (m.val natSuccName φ) n,
        m.val natName φ, interpExpr_lit hs, interpExpr_const_nat hs,
        natLitVal_mem_nat m hs φ n⟩, by simp [AnnotOk]⟩
  | const n ws =>
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure] at h
    revert h
    cases hf : env.find? n with
    | none => intro h; exact nomatch h
    | some ci =>
      intro h
      dsimp only at h
      revert h
      split
      case isFalse => intro h; exact nomatch h
      case isTrue hal =>
        intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨htc, -, -, -, -, -⟩ := m.wf _ (List.mem_of_find?_eq_some hf)
        have hcl : (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ws).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]; exact htc
        obtain ⟨T, hT, hmem⟩ :=
          m.mem_type ci (List.mem_of_find?_eq_some hf)
            (Level.substFn φ ci.toConstantVal.levelParams ws)
        have hAstored := (m.annot_ok ci (List.mem_of_find?_eq_some hf)
          (Level.substFn φ ci.toConstantVal.levelParams ws)).1
        refine ⟨⟨m.val n (Level.substFn φ ci.toConstantVal.levelParams ws), T, ?_, ?_, ?_⟩, ?_⟩
        · simp only [interpExpr, hf]
          rw [if_pos hal]
        · rw [interp_closed_invariant hcl]
          unfold interpClosed
          rw [interp_instLevels m.val_params]
          exact hT
        · have hname : ci.name = n := find?_name hf
          simp only [ConstantInfo.name] at hname
          rw [← hname]
          exact hmem
        · exact AnnotOk.closed_invariant hcl d ρ
            (AnnotOk.instLevels m.val_params _ 0 (rho0 V) hAstored)
  | forallE n ty body m' =>
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_forallE hok
    simp only [AnnotOk] at ha
    obtain ⟨haty, ⟨v₀, hv₀⟩, hcond⟩ := ha
    obtain ⟨tty, u, hty, hwt, rfl⟩ := inferTypeCore_forall_inv hv₀ h
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    obtain ⟨⟨A, tA, hA, htA, hmemA⟩, hAtA⟩ :=
      ihi hty hw.1 hb.1 hLbty hokty haty
    have hwtty := inferTypeCore_WScoped m.wf fuel hty hw.1
    have hbtty := inferTypeCore_looseBVars m.wf fuel hty hw.1 hb.1 hLbty
    have hLbtty : Expr.LeavesBounded tty := fun l hl =>
      hLbty l (inferTypeCore_fvarLeaves m.wf fuel hty hw.1 l hl)
    have hoktty : FvarsOk V m.val env φ d ρ tty :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hty hw.1) hokty
    rw [sort_result ihw hwt hwtty hbtty hLbtty hoktty hAtA] at htA
    obtain rfl := Option.some.inj htA
    refine ⟨⟨pi (v₀.eval φ) A (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      univ ((Level.imax u v₀).eval φ), ?_, ?_, ?_⟩, by simp [AnnotOk]⟩
    · simp only [interpExpr, hv₀, hA]
    · simp only [interpExpr]
    · have hpi := pi_mem_univ (V := V) (v := v₀.eval φ)
        (B := fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
        hmemA
        (fun x hx => by
          obtain ⟨-, hwfact⟩ := hcond x A hA hx
          obtain ⟨w, hwi, hmem⟩ := hwfact v₀ hv₀
          simpa [hwi] using hmem)
      have heq : Level.eval φ (.imax u v₀) =
          if v₀.eval φ = 0 then 0 else Nat.max (u.eval φ) (v₀.eval φ) := rfl
      rw [heq]
      exact hpi
  | lam n ty body m' =>
    obtain ⟨v, tty, u, bt, tbt, v', hc, htyi, hu, hbt, htbt, hwv, heqv, rfl⟩ :=
      inferTypeCore_lam_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokty, hokbody⟩ := FvarsOk.of_lam hok
    simp only [AnnotOk] at ha
    obtain ⟨haty, -, hcond⟩ := ha
    have hLbty : Expr.LeavesBounded ty := fun l hl => hLb l (by simp [fvarLeaves, hl])
    -- the domain interprets (via its own inference)
    obtain ⟨⟨A, tA, hA, -, -⟩, -⟩ :=
      ihi htyi hw.1 hb.1 hLbty hokty haty
    -- facts about the opened body
    have hwo : WScoped (d + 1) (body.instantiate1 (.fvar d n ty)) :=
      hw.1.instantiate1 0 hw.2
    have hbo : (body.instantiate1 (.fvar d n ty)).looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1 body 0 hb.2
    have hLbo : Expr.LeavesBounded (body.instantiate1 (.fvar d n ty)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body 0 hl with hb' | hb'
      · exact hLb l (by simp [fvarLeaves, hb'])
      · simp only [fvarLeaves, List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · exact hb.1
        · exact hLbty l hb'
    -- the abstraction roundtrip
    have hwbt := inferTypeCore_WScoped m.wf fuel hbt hwo
    have hrt : (bt.abstract1 d).instantiate1 (.fvar d n ty) = bt :=
      abstract1_instantiate1 bt 0
        (Expr.fvarConsistent_of_leafCond bt (fun l hl hld =>
          Expr.LeafCond_opened hw.1 hw.2 0 l
            (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl) hld))
        (inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo)
    -- per-member facts about the body and its type
    have hfacts : ∀ x, x ∈ˢ A →
        (∃ w tw, interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          interpExpr V m.val env φ (d + 1) (updV V ρ d x) bt = some tw ∧
          w ∈ˢ tw ∧ tw ∈ˢ univ (v.eval φ)) ∧
        AnnotOk V m.val env φ (d + 1) (updV V ρ d x) bt := by
      intro x hx
      obtain ⟨hbodyA⟩ := hcond x A hA hx
      have hoko : FvarsOk V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty)) :=
        FvarsOk.instantiate1 hw.1 hokty haty hA hx body 0 hw.2 hokbody
      obtain ⟨⟨w, tw, hwi, hbti, hmem⟩, hAbt⟩ :=
        ihi hbt hwo hbo hLbo hoko hbodyA
      -- the re-check gives the fibre's universe
      have hokbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) bt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hbt hwo) hoko
      have hbbt : bt.looseBVarsBounded 0 = true :=
        inferTypeCore_looseBVars m.wf fuel hbt hwo hbo hLbo
      have hLbbt : Expr.LeavesBounded bt := fun l hl =>
        hLbo l (inferTypeCore_fvarLeaves m.wf fuel hbt hwo l hl)
      obtain ⟨⟨vbt, tvbt, hbti2, htbti, hmem2⟩, hAtbt⟩ :=
        ihi htbt hwbt hbbt hLbbt hokbt hAbt
      have hwtbt := inferTypeCore_WScoped m.wf fuel htbt hwbt
      have hbtbt := inferTypeCore_looseBVars m.wf fuel htbt hwbt hbbt hLbbt
      have hLbtbt : Expr.LeavesBounded tbt := fun l hl =>
        hLbbt l (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt l hl)
      have hoktbt : FvarsOk V m.val env φ (d + 1) (updV V ρ d x) tbt :=
        FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htbt hwbt) hokbt
      rw [sort_result ihw hwv hwtbt hbtbt hLbtbt hoktbt hAtbt] at htbti
      obtain rfl := Option.some.inj htbti
      rw [hbti] at hbti2
      have hvbt : tw = vbt := Option.some.inj hbti2
      refine ⟨⟨w, tw, hwi, hbti, hmem, ?_⟩, hAbt⟩
      rw [Level.isEquiv_sound heqv φ, hvbt]
      exact hmem2
    -- assemble
    refine ⟨⟨SetTheory.lam (v.eval φ) A (fun x =>
        (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      pi (v.eval φ) A (fun x =>
        (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
          ((bt.abstract1 d).instantiate1 (.fvar d n ty))).getD SetTheory.empty),
      ?_, ?_, ?_⟩, ?_⟩
    · simp only [interpExpr, hc, hA]
    · simp only [interpExpr, hc, hA]
    · refine lam_mem fun x hx => ?_
      obtain ⟨⟨w, tw, hwi, hbti, hmem, -⟩, -⟩ := hfacts x hx
      rw [hrt, hwi, hbti]
      simpa using hmem
    · -- annotation truthfulness of the inferred Π-type
      simp only [AnnotOk]
      refine ⟨haty, ⟨v, hc⟩, ?_⟩
      intro x A' hA' hx
      rw [hA] at hA'
      obtain rfl := Option.some.inj hA'
      obtain ⟨⟨w, tw, hwi, hbti, hmem, htwu⟩, hAbt⟩ := hfacts x hx
      rw [hrt]
      refine ⟨hAbt, ?_⟩
      intro v'' hv''
      obtain rfl : v = v'' := by rw [hc] at hv''; injection hv''
      exact ⟨tw, hbti, htwu⟩
  | app f a =>
    obtain ⟨tf, n', ty', body', mPi, htf, hwh, rfl, hgate⟩ :=
      inferTypeCore_app_inv h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨hokf, hoka⟩ := FvarsOk.of_app hok
    simp only [AnnotOk] at ha
    obtain ⟨haf, haa, vfA, vaA, vEc, Ac, Bc, hifA, hiaA, hpiA, hmemA, -⟩ :=
      ha
    have hLbf : Expr.LeavesBounded f := fun l hl => hLb l (by simp [fvarLeaves, hl])
    have hLba : Expr.LeavesBounded a := fun l hl => hLb l (by simp [fvarLeaves, hl])
    -- infer f, reduce its type to a Π
    obtain ⟨⟨vf, vtf, hfi, htfi, hmemf⟩, hAtf⟩ :=
      ihi htf hw.1 hb.1 hLbf hokf haf
    have hwtf := inferTypeCore_WScoped m.wf fuel htf hw.1
    have hbtf := inferTypeCore_looseBVars m.wf fuel htf hw.1 hb.1 hLbf
    have hLbtf : Expr.LeavesBounded tf := fun l hl =>
      hLbf l (inferTypeCore_fvarLeaves m.wf fuel htf hw.1 l hl)
    have hoktf : FvarsOk V m.val env φ d ρ tf :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel htf hw.1) hokf
    obtain ⟨hiw, haPi⟩ := ihw hwh hwtf hbtf hLbtf hoktf hAtf
    have hwPi := whnf_WScoped m.wf fuel hwh hwtf
    have hbPi := whnf_looseBVars m.wf fuel hwh hbtf
    have hLbPi : Expr.LeavesBounded (Expr.forallE n' ty' body' mPi) := fun l hl =>
      hLbtf l (whnf_fvarLeaves m.wf fuel hwh l hl)
    have hokPi : FvarsOk V m.val env φ d ρ (.forallE n' ty' body' mPi) :=
      whnf_FvarsOk m.wf fuel hwh hoktf
    simp only [WScoped] at hwPi
    simp only [looseBVarsBounded, Bool.and_eq_true] at hbPi
    -- interpret the Π
    have hPii : interpExpr V m.val env φ d ρ (.forallE n' ty' body' mPi) = some vtf := by
      rw [hiw]; exact htfi
    rw [interpExpr] at hPii
    cases hcPi : mPi.cod with
    | none => rw [hcPi] at hPii; exact nomatch hPii
    | some vPi =>
    rw [hcPi] at hPii
    dsimp only at hPii
    cases htyPi : interpExpr V m.val env φ d ρ ty' with
    | none => rw [htyPi] at hPii; exact nomatch hPii
    | some A' =>
    rw [htyPi] at hPii
    simp only [Option.some.injEq] at hPii
    simp only [AnnotOk] at haPi
    obtain ⟨haty', -, hcond'⟩ := haPi
    have hLbty' : Expr.LeavesBounded ty' := fun l hl =>
      hLbPi l (by simp [fvarLeaves, hl])
    -- the argument is in the Π's domain: at a provably nonzero
    -- codomain sort by domain determination (the function value is a
    -- graph over the domain, and graphs determine their domains, so
    -- the app node's own `AnnotOk` slot supplies the membership); on
    -- the possibly-Prop residue from the runtime re-check (task #49)
    obtain ⟨va, hai, hva⟩ : ∃ va,
        interpExpr V m.val env φ d ρ a = some va ∧ va ∈ˢ A' := by
      rcases hgate with hnz | ⟨ta, hta, hde⟩
      · obtain ⟨v0, hcod0, hnz0⟩ := codNonZero_eq_true hnz
        have hveq : v0 = vPi := by
          rw [hcod0] at hcPi
          exact Option.some.inj hcPi
        rw [hveq] at hnz0
        have hcne : vPi.eval φ ≠ 0 := Level.isNonZero_sound hnz0 φ
        refine ⟨vaA, hiaA, ?_⟩
        have hfeq : vfA = vf := by
          rw [hifA] at hfi
          exact Option.some.inj hfi
        rw [hfeq] at hpiA
        have hpiM : vf ∈ˢ pi (vPi.eval φ) A'
            (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
              (body'.instantiate1 (.fvar d n' ty'))).getD
                SetTheory.empty) := by
          rw [hPii]; exact hmemf
        rw [pi_pos hcne] at hpiM
        have hgr := eq_graph_app_of_mem_piSet hpiM
        by_cases hvE : vEc = 0
        · subst hvE
          exact absurd (mem_pi_zero hpiA)
            (by rw [← hgr]; exact graph_ne_pt)
        · rw [← hgr, pi_pos hvE] at hpiA
          exact graph_dom_of_mem_piSet hpiA vaA hmemA
      · obtain ⟨⟨va, vta, hai, htai, hmema⟩, hAta⟩ :=
          ihi hta hw.2 hb.2 hLba hoka haa
        have hLbta : Expr.LeavesBounded ta := fun l hl =>
          hLba l (inferTypeCore_fvarLeaves m.wf fuel hta hw.2 l hl)
        have hAeq : vta = A' :=
          ihd hde
            (inferTypeCore_WScoped m.wf fuel hta hw.2) hwPi.1
            (inferTypeCore_looseBVars m.wf fuel hta hw.2 hb.2 hLba)
            hbPi.1 hLbta hLbty'
            (FvarsOk.of_subset
              (inferTypeCore_fvarLeaves m.wf fuel hta hw.2) hoka)
            ((FvarsOk.of_forallE hokPi).1)
            hAta haty' htai htyPi
        exact ⟨va, hai, hAeq ▸ hmema⟩
    obtain ⟨hAopened, hwfact'⟩ := hcond' va A' htyPi hva
    obtain ⟨w', hwi', hmem'⟩ := hwfact' vPi hcPi
    have hfb' : fvarsBelow d body' := hwPi.2.fvarsBelow
    have hbeta_eq := interp_beta (V := V) (cval := m.val) (env := env) (φ := φ)
      (n := n') (ty := ty') hfb' hw.2 hb.2 hai 0
    refine ⟨⟨SetTheory.app vf va, w', ?_, ?_, ?_⟩, ?_⟩
    · simp only [interpExpr]
      rw [hfi, hai]
    · rw [hbeta_eq]
      exact hwi'
    · have hpiM : vf ∈ˢ pi (vPi.eval φ) A'
          (fun x => (interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) := by
        rw [hPii]; exact hmemf
      have hfib : ∀ x, x ∈ˢ A' →
          ((interpExpr V m.val env φ (d + 1) (updV V ρ d x)
            (body'.instantiate1 (.fvar d n' ty'))).getD SetTheory.empty) ∈ˢ
            univ (vPi.eval φ) := by
        intro x hx
        obtain ⟨-, hwf_x⟩ := hcond' x A' htyPi hx
        obtain ⟨w_x, hwi_x, hm_x⟩ := hwf_x vPi hcPi
        rw [hwi_x]
        simpa using hm_x
      have happ := app_mem hpiM hva hfib
      rw [hwi'] at happ
      simpa using happ
    · exact AnnotOk_beta hfb' hw.2 hb.2 hai haa 0 hAopened
  | proj sn i e =>
    obtain ⟨tpe, te, T, us, entry, hte, hwt, hfn, hf, hnat, hlen, husl,
      hres⟩ := inferTypeCore_proj_inv h
    obtain ⟨hpin, hpsig, hpsigMk⟩ :=
      m.proj_ok _ _ (Env.findProj?_some hf) hnat
    -- the entry's stored name pins the head and the index
    have hidx : entry.idx = i ∧ entry.structName = T := by
      have h1 := List.find?_some (Env.findProj?_some hf)
      have h2 : (ConstantInfo.projInfo entry).name = projFnName T i :=
        eq_of_beq (by simpa using h1)
      simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at h2
      exact ⟨(projFnName_inj h2).2, (projFnName_inj h2).1⟩
    have hT : T = psigmaName := by
      rw [← hidx.2]
      rcases hpin with rfl | rfl <;> rfl
    subst hT
    have hlen2 : te.getAppArgs.length = 2 := by
      rw [hlen]
      rcases hpin with rfl | rfl <;> rfl
    obtain ⟨A, B, hargs2⟩ := List.length_two hlen2
    have hteEq : te = .app (.app (.const psigmaName us) A) B := by
      have h0 := Expr.mkAppN_getApp te
      rw [hfn, hargs2] at h0
      exact h0.symm
    subst hteEq
    obtain ⟨cvP, capsP, hfind⟩ : ∃ cvP capsP, env.find? psigmaName =
        some (.indInfo cvP capsP) := ⟨_, _, by rw [hpsig]; rfl⟩
    simp only [WScoped] at hw
    simp only [looseBVarsBounded] at hb
    have hLbe : Expr.LeavesBounded e := fun l hl => hLb l (by
      simp only [fvarLeaves]; exact hl)
    have hoke : FvarsOk V m.val env φ d ρ e := fun l hl => hok l (by
      simp only [fvarLeaves]; exact hl)
    simp only [AnnotOk] at ha
    obtain ⟨hae, -⟩ := ha
    obtain ⟨⟨ve, vte, hei, htei, hmem⟩, hAte⟩ := ihi hte hw hb hLbe hoke hae
    -- reduce the type to the pair form and transfer facts
    have hwte := inferTypeCore_WScoped m.wf fuel hte hw
    have hbte := inferTypeCore_looseBVars m.wf fuel hte hw hb hLbe
    have hLbte : Expr.LeavesBounded tpe := fun l hl =>
      hLbe l (inferTypeCore_fvarLeaves m.wf fuel hte hw l hl)
    have hokte : FvarsOk V m.val env φ d ρ tpe :=
      FvarsOk.of_subset (inferTypeCore_fvarLeaves m.wf fuel hte hw) hoke
    obtain ⟨hiw, haPi⟩ := ihw hwt hwte hbte hLbte hokte hAte
    have hPii : interpExpr V m.val env φ d ρ
        (.app (.app (.const psigmaName us) A) B) = some vte := by
      rw [hiw]; exact htei
    try simp only [AnnotOk] at haPi
    obtain ⟨haCA, haB, vf₁, vB, vE₁, A₁, B₁, hf₁i, hBi, hpi₁, hvB₁, hfib₁⟩ := haPi
    try simp only [AnnotOk] at haCA
    obtain ⟨hac, haA, vf₀, vA, vE₀, A₀, B₀, hci, hAi, hpi₀, hvA₀, hfib₀⟩ := haCA
    -- the head is the pair former's value
    rw [interpExpr, hfind] at hci
    dsimp only [ConstantInfo.toConstantVal] at hci
    obtain ⟨ψ', hψ'⟩ : ∃ ψ', ψ' = Level.substFn φ cvP.levelParams us := ⟨_, rfl⟩
    rw [← hψ'] at hci
    by_cases hal : us.length = cvP.levelParams.length
    case neg => simp only [hal, if_false] at hci; exact nomatch hci
    simp only [hal, if_true] at hci
    have hval : interpExpr V m.val env φ d ρ (.const psigmaName us) =
        some (m.val psigmaName ψ') := by
      rw [interpExpr, hfind]
      dsimp only [ConstantInfo.toConstantVal]
      rw [← hψ']
      simp only [hal, if_true]
    have hvf₀ : vf₀ = m.val psigmaName ψ' := (Option.some.inj hci).symm
    have hfacts := ((m.ind_ok.1 cvP capsP hfind).2 ψ')
    have hAmem : vA ∈ˢ univ (ψ' uN) := hfacts.dom₀ (hvf₀ ▸ hpi₀) hvA₀
    -- the partial application and its second argument
    have hf₁ : vf₁ = app (m.val psigmaName ψ') vA := by
      rw [interpExpr, hval, hAi] at hf₁i
      dsimp only at hf₁i
      exact (Option.some.inj hf₁i).symm
    have hBmem : vB ∈ˢ pi (ψ' vN + 1) vA (fun _ => univ (ψ' vN)) :=
      hfacts.dom₁ hAmem (hf₁ ▸ hpi₁) hvB₁
    -- the type's interpretation is the sigma set
    have hfold : vte = sigmaSet (Nat.max (ψ' uN) (ψ' vN)) vA (fun x => app vB x) := by
      rw [interpExpr, hf₁i, hBi] at hPii
      dsimp only at hPii
      have := Option.some.inj hPii
      rw [← this, hf₁, hfacts.fold hAmem hBmem]
    have hvemem : ve ∈ˢ sigmaSet (Nat.max (ψ' uN) (ψ' vN)) vA (fun x => app vB x) := by
      rw [← hfold]; exact hmem
    obtain ⟨a', b', ha', hb', hpt0, hpair⟩ := mem_sigma_elim hvemem
    have hu0 : Nat.max (ψ' uN) (ψ' vN) = 0 → ψ' uN = 0 := fun hw0 =>
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_of_eq hw0))
    have hv0 : Nat.max (ψ' uN) (ψ' vN) = 0 → ψ' vN = 0 := fun hw0 =>
      Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq hw0))
    have hsfst : sfst ve ∈ˢ vA := by
      by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
      · rw [hpt0 hw0, sfst_pt]
        have hA0 : vA ∈ˢ univ 0 := (hu0 hw0) ▸ hAmem
        have := mem_univ_zero hA0 ha'
        rwa [← this]
      · rw [hpair hw0, sfst_spair]
        exact ha'
    -- compute the pinned entry type's residual (the inferred type);
    -- the no-op instantiations on the (bvar-closed) components vanish
    have hbPair := whnf_looseBVars m.wf fuel hwt hbte
    simp only [looseBVarsBounded, Bool.and_eq_true] at hbPair
    obtain ⟨⟨-, hbA⟩, hbB⟩ := hbPair
    have hcase : (i = 0 ∧ t = A) ∨
        (i = 1 ∧ t = .app B (.proj psigmaName 0 e)) := by
      rcases hpin with rfl | rfl
      · refine Or.inl ⟨hidx.1.symm, ?_⟩
        rw [hargs2] at hres
        simp [pairFstEntry, pairFstTyA, piResidual,
          Expr.instantiateLevelParams, Expr.instantiate1, Level.subst,
          Level.subst.go,
          instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le _) hbA),
          instantiate1_eq_self hbA] at hres
        exact hres.symm
      · refine Or.inr ⟨hidx.1.symm, ?_⟩
        rw [hargs2] at hres
        simp [pairSndEntry, pairSndTyA, piResidual,
          Expr.instantiateLevelParams, Expr.instantiate1, Level.subst,
          Level.subst.go,
          instantiate1_eq_self (looseBVarsBounded_mono (Nat.zero_le _) hbB),
          instantiate1_eq_self hbB] at hres
        exact hres.symm
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- i = 0 : the first component
      refine ⟨⟨sfst ve, vA, ?_, hAi, hsfst⟩, haA⟩
      simp only [interpExpr, hei]
      rfl
    · -- i = 1 : the second component
      have hproj0 : interpExpr V m.val env φ d ρ (.proj psigmaName 0 e) = some (sfst ve) := by
        simp only [interpExpr, hei]
        rfl
      have hfib : ∀ x, x ∈ˢ vA → app vB x ∈ˢ univ (ψ' vN) := fun x hx =>
        app_mem hBmem hx fun _ _ => univ_mem_univ _
      have hssnd : ssnd ve ∈ˢ app vB (sfst ve) := by
        by_cases hw0 : Nat.max (ψ' uN) (ψ' vN) = 0
        · rw [hpt0 hw0, ssnd_pt, sfst_pt]
          have hA0 : vA ∈ˢ univ 0 := (hu0 hw0) ▸ hAmem
          have hapt : a' = pt := mem_univ_zero hA0 ha'
          have hb'' : b' ∈ˢ app vB pt := hapt ▸ hb'
          have hB0 : app vB pt ∈ˢ univ 0 := (hv0 hw0) ▸ hfib pt (hapt ▸ ha')
          have hbpt : b' = pt := mem_univ_zero hB0 hb''
          exact hbpt ▸ hb''
        · rw [hpair hw0, ssnd_spair, sfst_spair]
          exact hb'
      refine ⟨⟨ssnd ve, app vB (sfst ve), ?_, ?_, hssnd⟩, ?_⟩
      · simp only [interpExpr, hei]
        rfl
      · simp only [interpExpr, hBi, hproj0]
      · -- AnnotOk of `app B (proj sn 0 e)`
        simp only [AnnotOk]
        refine ⟨haB, ?_, vB, sfst ve, ψ' vN + 1, vA, (fun _ => univ (ψ' vN)),
          hBi, hproj0, hBmem, hsfst, fun _ _ => univ_mem_univ _⟩
        exact ⟨hae, by omega, ve, ψ' uN, ψ' vN, vA, (fun x => app vB x),
          hei, hvemem, hAmem, hfib⟩
  | bvar i =>
    rw [inferTypeCore_succ] at h
    simp [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  | letE n' t' v' b' =>
    -- infer of the instantiated body; the letE node's interpretation is
    -- the reduct's by `interp_beta`, and the reduct's truthfulness is
    -- `AnnotOk_beta` on the letE clause
    rw [inferTypeCore_succ] at h
    simp only [inferBody, viewM, Expr.view, Bind.bind, Except.bind, pure,
      Except.pure, infer_def] at h
    simp only [WScoped] at hw
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, haopen⟩ := ha
    have hfb : fvarsBelow d b' := hw.2.2.fvarsBelow
    have hwred : WScoped d (b'.instantiate1 v') :=
      WScoped.instantiate1_gen hw.2.1 0 hw.2.2
    have hbred : (b'.instantiate1 v').looseBVarsBounded 0 = true :=
      looseBVarsBounded_instantiate1_gen hb.1.2 hb.2
    have hLbred : Expr.LeavesBounded (b'.instantiate1 v') := fun l hl => by
      rcases fvarLeaves_instantiate1 b' 0 hl with h2 | h2
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inr h2)
      · exact hLb l (by
          simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr h2))
    have hokred : FvarsOk V m.val env φ d ρ (b'.instantiate1 v') :=
      fun l hl => by
        rcases fvarLeaves_instantiate1 b' 0 hl with h2 | h2
        · exact hok l (by
            simp only [fvarLeaves, List.mem_append]; exact Or.inr h2)
        · exact hok l (by
            simp only [fvarLeaves, List.mem_append]; exact Or.inl (Or.inr h2))
    have hared : AnnotOk V m.val env φ d ρ (b'.instantiate1 v') :=
      AnnotOk_beta hfb hw.2.1 hb.1.2 hxv hav 0 haopen
    obtain ⟨⟨w, tw, hwi, htwi, hmem⟩, hAt⟩ :=
      ihi h hwred hbred hLbred hokred hared
    refine ⟨⟨w, tw, ?_, htwi, hmem⟩, hAt⟩
    rw [← hwi, interp_beta (n := n') (ty := t') hfb hw.2.1 hb.1.2 hxv 0]
    simp only [interpExpr, hxv]

end Claims

end Setlec
