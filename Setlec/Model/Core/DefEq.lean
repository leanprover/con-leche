import Setlec.Model.Core.Whnf

/-!
# Checker-core soundness: DefEq

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

set_option maxHeartbeats 3200000 in
theorem defeq_claims (m : EnvModel V env)
    (ihwc : WhnfCoreClaims m φ fuel)
    (ihw : WhnfClaims m φ fuel) (ihd : DefEqClaims m φ fuel)
    (ihi : InferClaims m φ fuel) :
    DefEqClaims m φ (fuel + 1) := by
  intro d a b ρ h hwa hwb hba hbb hLba hLbb hoka hokb haa hab va vb hva hvb
  rw [isDefEqCore_succ] at h
  simp only [defeqBody, Bind.bind, Except.bind] at h
  simp only [whnfCore_def, whnf_def, defeq_def, infer_def, stuckIrrel_fold,
    etaCert_fold, reduceNat_fold, defeqSpine_fold, proofIrrel_fold] at h
  by_cases heqab : (a == b) = true
  · obtain rfl : a = b := eq_of_beq heqab
    rw [hva] at hvb
    exact Option.some.inj hvb
  rw [if_neg heqab] at h
  cases hwha : whnfCore env fuel d a with
  | error e => rw [hwha] at h; exact nomatch h
  | ok a' =>
  rw [hwha] at h
  dsimp only at h
  cases hwhb : whnfCore env fuel d b with
  | error e => rw [hwhb] at h; exact nomatch h
  | ok b' =>
  rw [hwhb] at h
  dsimp only at h
  -- transfer facts through head normalization (no delta)
  obtain ⟨hia, haa'⟩ := ihwc hwha hwa hba hLba hoka haa
  obtain ⟨hib, hab'⟩ := ihwc hwhb hwb hbb hLbb hokb hab
  rw [← hia] at hva
  rw [← hib] at hvb
  have hwa' := whnfCore_WScoped m.wf fuel hwha hwa
  have hwb' := whnfCore_WScoped m.wf fuel hwhb hwb
  have hba' := whnfCore_looseBVars m.wf fuel hwha hba
  have hbb' := whnfCore_looseBVars m.wf fuel hwhb hbb
  have hLba' : Expr.LeavesBounded a' := fun l hl =>
    hLba l (whnfCore_fvarLeaves m.wf fuel hwha l hl)
  have hLbb' : Expr.LeavesBounded b' := fun l hl =>
    hLbb l (whnfCore_fvarLeaves m.wf fuel hwhb l hl)
  have hoka' := whnfCore_FvarsOk m.wf fuel hwha hoka
  have hokb' := whnfCore_FvarsOk m.wf fuel hwhb hokb
  clear hwha hwhb hwa hwb haa hab hia hib hba hbb hLba hLbb hoka hokb
  have hPI : stuckIrrelP env fuel d a' b' = .ok true → va = vb := fun hp =>
    stuckIrrel_sound ihw ihd ihi hp hwa' hwb' hba' hbb' hLba' hLbb'
      hoka' hokb' haa' hab' hva hvb
  by_cases heqab' : (a' == b') = true
  · obtain rfl : a' = b' := eq_of_beq heqab'
    rw [hva] at hvb
    exact Option.some.inj hvb
  rw [if_neg heqab'] at h
  -- proof irrelevance, hoisted before lazy delta (official kernel
  -- order): a positive certification collapses both sides to `pt`
  cases hpi : proofIrrelP env fuel d a' b' with
  | error e => rw [hpi] at h; exact nomatch h
  | ok rpi =>
  rw [hpi] at h
  dsimp only at h
  cases rpi with
  | true =>
    obtain ⟨hpa, hpb⟩ := proofIrrel_pt ihw ihi hpi hwa' hwb' hba' hbb'
      hLba' hLbb' hoka' hokb' haa' hab'
    rw [hva] at hpa
    rw [hvb] at hpb
    exact (Option.some.inj hpa).trans (Option.some.inj hpb).symm
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- literal acceleration before delta (mirrors the whnf loop order),
  -- guarded on both sides being fvar-free (the official kernel's
  -- `lazy_delta_reduction` guard); the guard only prunes, so a `some`
  -- result always comes from `reduceNatP` and `reduceNat_sound`
  -- applies unchanged
  cases hrna : (if !a'.hasFvar && !b'.hasFvar then
      reduceNatP env fuel d a' else pure none) with
  | error e => rw [hrna] at h; exact nomatch h
  | ok oa =>
  rw [hrna] at h
  dsimp only at h
  cases oa with
  | some a₂ =>
    have hrna' : reduceNatP env fuel d a' = .ok (some a₂) := by
      by_cases hg : (!a'.hasFvar && !b'.hasFvar) = true
      · rwa [if_pos hg] at hrna
      · rw [if_neg hg] at hrna
        exact absurd hrna (by simp [pure, Except.pure])
    obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      reduceNat_sound m ihw hrna' hwa' hba' hLba' hoka' haa'
    exact ihd h hw2 hwb' hb2 hbb' hLb2 hLbb' hok2 hokb' ha2 hab'
      (by rw [hi2]; exact hva) hvb
  | none =>
  dsimp only at h
  cases hrnb : (if !a'.hasFvar && !b'.hasFvar then
      reduceNatP env fuel d b' else pure none) with
  | error e => rw [hrnb] at h; exact nomatch h
  | ok ob =>
  rw [hrnb] at h
  dsimp only at h
  cases ob with
  | some b₂ =>
    have hrnb' : reduceNatP env fuel d b' = .ok (some b₂) := by
      by_cases hg : (!a'.hasFvar && !b'.hasFvar) = true
      · rwa [if_pos hg] at hrnb
      · rw [if_neg hg] at hrnb
        exact absurd hrnb (by simp [pure, Except.pure])
    obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      reduceNat_sound m ihw hrnb' hwb' hbb' hLbb' hokb' hab'
    exact ihd h hwa' hw2 hba' hb2 hLba' hLb2 hoka' hok2 haa' ha2
      hva (by rw [hi2]; exact hvb)
  | none =>
  dsimp only at h
  -- the lazy delta unfolding decision: every branch is an
  -- independently sound reduction or comparison, so the reducibility
  -- hints (which only schedule) never enter the argument
  cases hua : unfoldDefinition env a' with
  | some a₂ =>
    obtain ⟨hi2, ha2, hw2, hb2, hLb2, hok2⟩ :=
      unfoldDefinition_sound m hua hwa' hba' hLba' hoka' haa'
    cases hub : unfoldDefinition env b' with
    | none =>
      rw [hua, hub] at h
      dsimp only at h
      exact ihd h hw2 hwb' hb2 hbb' hLb2 hLbb' hok2 hokb' ha2 hab'
        (by rw [hi2]; exact hva) hvb
    | some b₂ =>
      rw [hua, hub] at h
      dsimp only at h
      obtain ⟨hi3, ha3, hw3, hb3, hLb3, hok3⟩ :=
        unfoldDefinition_sound m hub hwb' hbb' hLbb' hokb' hab'
      split at h
      case isTrue =>
        exact ihd h hw2 hwb' hb2 hbb' hLb2 hLbb' hok2 hokb' ha2 hab'
          (by rw [hi2]; exact hva) hvb
      case isFalse =>
      split at h
      case isTrue =>
        exact ihd h hwa' hw3 hba' hb3 hLba' hLb3 hoka' hok3 haa' ha3
          hva (by rw [hi3]; exact hvb)
      case isFalse =>
      split at h
      case isFalse =>
        exact ihd h hw2 hw3 hb2 hb3 hLb2 hLb3 hok2 hok3 ha2 ha3
          (by rw [hi2]; exact hva) (by rw [hi3]; exact hvb)
      case isTrue =>
        -- same-head short-circuit; a negative verdict falls back to
        -- unfolding both sides
        cases hsp : defeqSpineP env fuel d a' b' with
        | error e => rw [hsp] at h; exact nomatch h
        | ok r =>
        rw [hsp] at h
        dsimp only at h
        cases r with
        | true =>
          exact defeqSpine_values ihd hsp hwa' hwb' hba' hbb' hLba' hLbb'
            hoka' hokb' haa' hab' hva hvb
        | false =>
          exact ihd h hw2 hw3 hb2 hb3 hLb2 hLb3 hok2 hok3 ha2 ha3
            (by rw [hi2]; exact hva) (by rw [hi3]; exact hvb)
  | none =>
  cases hub : unfoldDefinition env b' with
  | some b₂ =>
    rw [hua, hub] at h
    dsimp only at h
    obtain ⟨hi3, ha3, hw3, hb3, hLb3, hok3⟩ :=
      unfoldDefinition_sound m hub hwb' hbb' hLbb' hokb' hab'
    exact ihd h hwa' hw3 hba' hb3 hLba' hLb3 hoka' hok3 haa' ha3
      hva (by rw [hi3]; exact hvb)
  | none =>
  rw [hua, hub] at h
  dsimp only at h
  match a', b', h with
  | Expr.sort u, Expr.sort v, h =>
    dsimp only at h
    simp only [interpExpr, Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have : Level.isEquiv u v = some true := by
      revert h
      cases hEq : Level.isEquiv u v with
      | none => simp [liftFueled]
      | some x => cases x <;> simp [liftFueled, pure, Except.pure]
    rw [Level.isEquiv_sound this φ]
  | Expr.fvar i ni tyi, Expr.fvar j nj tyj, h =>
    dsimp only at h
    split at h
    next hij =>
      have hij' : i = j := by simpa using hij
      subst hij'
      simp only [interpExpr, Option.some.injEq] at hva hvb
      subst hva; subst hvb
      rfl
    next _ => exact hPI h
  | Expr.const n us, Expr.const n' us', h =>
    dsimp only at h
    split at h
    case _ hnn =>
      subst hnn
      try simp only [Bind.bind, Except.bind] at h
      cases hEq : Level.isEquivList us us' with
      | none => rw [hEq] at h; simp [liftFueled] at h
      | some r =>
      rw [hEq] at h
      dsimp only [liftFueled] at h
      try simp only [pure, Except.pure] at h
      try dsimp only at h
      cases r with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact hPI h
      | true =>
      have hlev : Level.isEquivList us us' = some true := hEq
      simp only [interpExpr] at hva hvb
      cases hf : env.find? n with
      | none => rw [hf] at hva; exact nomatch hva
      | some ci =>
      rw [hf] at hva hvb
      dsimp only at hva hvb
      by_cases hal : us.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal] at hva
        have hal' : us'.length = ci.toConstantVal.levelParams.length := by
          have := Level.isEquivList_length hlev
          omega
        rw [if_pos hal'] at hvb
        simp only [Option.some.injEq] at hva hvb
        subst hva; subst hvb
        rw [Level.substFn_congr (Level.isEquivList_sound hlev φ)]
      · rw [if_neg hal] at hva
        exact nomatch hva
    case _ hnn => exact hPI h
  | Expr.forallE n₁ ty₁ body₁ m₁, Expr.forallE n₂ ty₂ body₂ m₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_forallE hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_forallE hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haty₁, hcond₁⟩ := haa'
    obtain ⟨haty₂, hcond₂⟩ := hab'
    cases hd1 : isDefEqCore env fuel d ty₁ ty₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    cases hd2 : isDefEqCore env fuel (d + 1)
        (body₁.instantiate1 (.fvar d n₁ ty₁)) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    try dsimp only at h
    cases r₂ with
    | false => simp [pure, Except.pure] at h
    | true =>
    -- The binder annotations are not compared and not interpreted
    -- (task #100 stage 3): `piC_congr` needs only domain and fibre
    -- agreement.
    simp only [interpExpr] at hva hvb
    cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
    | none => rw [hA1] at hva; exact nomatch hva
    | some A₁ =>
    rw [hA1] at hva
    cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
    | none => rw [hA2] at hvb; exact nomatch hvb
    | some A₂ =>
    rw [hA2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hAeq : A₁ = A₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    refine piC_congr fun x hx => ?_
    obtain ⟨habody₁, w₁, hw₁⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, w₂, hw₂⟩ := hcond₂ x A₁ hA2 hx
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbty₁ : Expr.LeavesBounded ty₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbty₂ : Expr.LeavesBounded ty₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokty₁, hokbody₁⟩ := FvarsOk.of_lam hoka'
    obtain ⟨hokty₂, hokbody₂⟩ := FvarsOk.of_lam hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haty₁, hcond₁⟩ := haa'
    obtain ⟨haty₂, hcond₂⟩ := hab'
    cases hd1 : isDefEqCore env fuel d ty₁ ty₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false => simp [pure, Except.pure] at h
    | true =>
    simp only [] at h
    cases hd2 : isDefEqCore env fuel (d + 1)
        (body₁.instantiate1 (.fvar d n₁ ty₁)) (body₂.instantiate1 (.fvar d n₂ ty₂)) with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    try dsimp only at h
    cases r₂ with
    | false => simp [pure, Except.pure] at h
    | true =>
    -- no annotation comparison; `lamC_congr` (task #100 stage 3)
    simp only [interpExpr] at hva hvb
    cases hA1 : interpExpr V m.val env φ d ρ ty₁ with
    | none => rw [hA1] at hva; exact nomatch hva
    | some A₁ =>
    rw [hA1] at hva
    cases hA2 : interpExpr V m.val env φ d ρ ty₂ with
    | none => rw [hA2] at hvb; exact nomatch hvb
    | some A₂ =>
    rw [hA2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hAeq : A₁ = A₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbty₁ hLbty₂ hokty₁ hokty₂
        haty₁ haty₂ hA1 hA2
    subst hAeq
    refine lamC_congr fun x hx => ?_
    obtain ⟨habody₁, w₁, B₁, hw₁, -⟩ := hcond₁ x A₁ hA1 hx
    obtain ⟨habody₂, w₂, B₂, hw₂, -⟩ := hcond₂ x A₁ hA2 hx
    rw [hw₁, hw₂]
    have hLbo₁ : Expr.LeavesBounded (body₁.instantiate1 (.fvar d n₁ ty₁)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₁ 0 hl with hl' | hl'
      · exact hLba' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hba'.1
        · exact hLbty₁ l hl'
    have hLbo₂ : Expr.LeavesBounded (body₂.instantiate1 (.fvar d n₂ ty₂)) := by
      intro l hl
      rcases fvarLeaves_instantiate1 body₂ 0 hl with hl' | hl'
      · exact hLbb' l (by simp [fvarLeaves, hl'])
      · simp only [fvarLeaves, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact hbb'.1
        · exact hLbty₂ l hl'
    simpa using ihd hd2
      (hwa'.1.instantiate1 0 hwa'.2) (hwb'.1.instantiate1 0 hwb'.2)
      (looseBVarsBounded_instantiate1 body₁ 0 hba'.2)
      (looseBVarsBounded_instantiate1 body₂ 0 hbb'.2)
      hLbo₁ hLbo₂
      (FvarsOk.instantiate1 hwa'.1 hokty₁ haty₁ hA1 hx body₁ 0 hwa'.2 hokbody₁)
      (FvarsOk.instantiate1 hwb'.1 hokty₂ haty₂ hA2 hx body₂ 0 hwb'.2 hokbody₂)
      habody₁ habody₂ hw₁ hw₂
  | Expr.app f₁ a₁, Expr.app f₂ a₂, h =>
    dsimp only at h
    simp only [WScoped] at hwa' hwb'
    simp only [looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
    have hLbf₁ : Expr.LeavesBounded f₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLbf₂ : Expr.LeavesBounded f₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    have hLba₁ : Expr.LeavesBounded a₁ := fun l hl => hLba' l (by simp [fvarLeaves, hl])
    have hLba₂ : Expr.LeavesBounded a₂ := fun l hl => hLbb' l (by simp [fvarLeaves, hl])
    obtain ⟨hokf₁, hoka₁⟩ := FvarsOk.of_app hoka'
    obtain ⟨hokf₂, hoka₂⟩ := FvarsOk.of_app hokb'
    simp only [AnnotOk] at haa' hab'
    obtain ⟨haf₁, haa₁, -⟩ := haa'
    obtain ⟨haf₂, haa₂, -⟩ := hab'
    try simp only [Bind.bind, Except.bind] at h
    cases hd1 : isDefEqCore env fuel d f₁ f₂ with
    | error e => rw [hd1] at h; exact nomatch h
    | ok r₁ =>
    rw [hd1] at h
    dsimp only at h
    cases r₁ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact hPI h
    | true =>
    simp only [↓reduceIte] at h
    cases hd2 : isDefEqCore env fuel d a₁ a₂ with
    | error e => rw [hd2] at h; exact nomatch h
    | ok r₂ =>
    rw [hd2] at h
    dsimp only at h
    cases r₂ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact hPI h
    | true =>
    simp only [interpExpr] at hva hvb
    cases hf1 : interpExpr V m.val env φ d ρ f₁ with
    | none => rw [hf1] at hva; exact nomatch hva
    | some vf₁ =>
    rw [hf1] at hva
    cases ha1 : interpExpr V m.val env φ d ρ a₁ with
    | none => rw [ha1] at hva; exact nomatch hva
    | some va₁ =>
    rw [ha1] at hva
    cases hf2 : interpExpr V m.val env φ d ρ f₂ with
    | none => rw [hf2] at hvb; exact nomatch hvb
    | some vf₂ =>
    rw [hf2] at hvb
    cases ha2 : interpExpr V m.val env φ d ρ a₂ with
    | none => rw [ha2] at hvb; exact nomatch hvb
    | some va₂ =>
    rw [ha2] at hvb
    simp only [Option.some.injEq] at hva hvb
    subst hva; subst hvb
    have hfe : vf₁ = vf₂ :=
      ihd hd1 hwa'.1 hwb'.1 hba'.1 hbb'.1 hLbf₁ hLbf₂ hokf₁ hokf₂ haf₁ haf₂ hf1 hf2
    have hae : va₁ = va₂ :=
      ihd hd2 hwa'.2 hwb'.2 hba'.2 hbb'.2 hLba₁ hLba₂ hoka₁ hoka₂ haa₁ haa₂ ha1 ha2
    rw [hfe, hae]
  | Expr.sort _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.sort _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.sort _, Expr.const _ _, h => exact hPI h
  | Expr.sort u, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.sort _, Expr.app _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.sort _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.fvar i ni tyi, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.fvar _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.sort _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.forallE n₁ ty₁ body₁ m₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.forallE _ _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.const _ _, Expr.sort _, h => exact hPI h
  | Expr.const _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.const n us, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.const _ _, Expr.app _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.sort u, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.fvar j nj tyj, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.forallE n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.const n' us', h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.app f₂ a₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.sort _, h => exact hPI h
  | Expr.app _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.app _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.app _ _, Expr.const _ _, h => exact hPI h
  | Expr.app f₁ a₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.bvar i₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.bvar _, Expr.sort _, h => exact hPI h
  | Expr.bvar _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.const _ _, h => exact hPI h
  | Expr.bvar _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.app _ _, h => exact hPI h
  | Expr.bvar _, Expr.bvar _, h => exact hPI h
  | Expr.bvar _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.bvar _, Expr.lit _, h => exact hPI h
  | Expr.bvar _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.bvar _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.const _ _, Expr.bvar _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.bvar i₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.bvar _, h => exact hPI h
  | Expr.letE n₁ ty₁ v₁ body₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.letE _ _ _ _, Expr.sort _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.lit _, h => exact hPI h
  | Expr.letE _ _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.letE n₂ ty₂ v₂ body₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lit l₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.lit _, Expr.sort _, h => exact hPI h
  | Expr.lit _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.lit (.natVal n), Expr.const c us, h =>
    dsimp only at h
    split at h
    case isTrue hc =>
      obtain ⟨rfl, rfl⟩ := hc
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      have hs : natLitSupported env = true := by
        cases hns : natLitSupported env
        · simp [interpExpr, hns] at hva
        · rfl
      rw [interpExpr_lit hs] at hva
      rw [interpExpr_const_natZero hs] at hvb
      rw [← Option.some.inj hva, ← Option.some.inj hvb]
      rfl
    case isFalse => exact hPI h
  | Expr.lit (.strVal _), Expr.const _ _, h => exact hPI h
  | Expr.lit _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.lit (.natVal nn), Expr.app f x, h =>
    dsimp only at h
    match nn, f, h with
    | 0, f, h => exact hPI h
    | k + 1, .const c [], h =>
      dsimp only at h
      split at h
      case isTrue hc =>
        subst hc
        have hs : natLitSupported env = true := by
          cases hns : natLitSupported env
          · simp [interpExpr, hns] at hva
          · rfl
        rw [interpExpr_lit hs] at hva
        rw [interpExpr_app_succ hs] at hvb
        revert hvb
        cases hx : interpExpr V m.val env φ d ρ x with
        | none => intro hvb; exact nomatch hvb
        | some vx =>
        intro hvb
        dsimp only at hvb
        simp only [WScoped] at hwb'
        simp only [looseBVarsBounded, Bool.and_eq_true] at hbb'
        have hLbx : Expr.LeavesBounded x := fun l hl =>
          hLbb' l (by simp [fvarLeaves, hl])
        have hokx : FvarsOk V m.val env φ d ρ x :=
          (FvarsOk.of_app hokb').2
        simp only [AnnotOk] at hab'
        obtain ⟨-, hax, -⟩ := hab'
        have hveq : natLitVal V (m.val natZeroName φ)
            (m.val natSuccName φ) k = vx :=
          ihd h (by simp [WScoped]) hwb'.2
            (by simp [looseBVarsBounded]) hbb'.2
            (fun l hl => by simp [fvarLeaves] at hl) hLbx
            (fun l hl => by simp [fvarLeaves] at hl) hokx
            (by simp [AnnotOk]) hax (interpExpr_lit hs) hx
        rw [← Option.some.inj hva, ← Option.some.inj hvb, ← hveq]
        rfl
      case isFalse => exact hPI h
    | k + 1, .bvar _, h => exact hPI h
    | k + 1, .fvar _ _ _, h => exact hPI h
    | k + 1, .sort _, h => exact hPI h
    | k + 1, .const _ (_ :: _), h => exact hPI h
    | k + 1, .app _ _, h => exact hPI h
    | k + 1, .lam _ _ _ _, h => exact hPI h
    | k + 1, .forallE _ _ _ _, h => exact hPI h
    | k + 1, .letE _ _ _ _, h => exact hPI h
    | k + 1, .lit _, h => exact hPI h
    | k + 1, .proj _ _ _, h => exact hPI h
  | Expr.lit (.strVal st), Expr.app f x, h =>
    match f, h with
    | .const cO usO, h =>
      dsimp only at h
      split at h
      case isTrue hc =>
        obtain ⟨rfl, rfl, hs⟩ := hc
        have hLbS : Expr.LeavesBounded (strLitToConstructor st) :=
          fun l hl => by
            rw [strLitToConstructor_fvarLeaves] at hl
            cases hl
        refine ihd h (strLitToConstructor_WScoped st d) hwb'
          (strLitToConstructor_looseBVars st 0) hbb' hLbS hLbb'
          (FvarsOk.of_not_hasFvar (strLitToConstructor_hasFvar st)) hokb'
          (annotOk_strLitToConstructor m hs) hab' ?_ hvb
        rw [interpExpr_strLitToConstructor hs]
        exact hva
      case isFalse => exact hPI h
    | .bvar _, h => exact hPI h
    | .fvar _ _ _, h => exact hPI h
    | .sort _, h => exact hPI h
    | .app _ _, h => exact hPI h
    | .lam _ _ _ _, h => exact hPI h
    | .forallE _ _ _ _, h => exact hPI h
    | .letE _ _ _ _, h => exact hPI h
    | .lit _, h => exact hPI h
    | .proj _ _ _, h => exact hPI h
  | Expr.lit _, Expr.bvar _, h => exact hPI h
  | Expr.lit _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.lit l₁, Expr.lit l₂, h =>
    dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    rw [hva] at hvb
    exact Option.some.inj hvb
  | Expr.lit _, Expr.proj _ _ _, h => exact hPI h
  | Expr.sort _, Expr.lit _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.lit _, h => exact hPI h
  | Expr.const c us, Expr.lit (.natVal n), h =>
    dsimp only at h
    split at h
    case isTrue hc =>
      obtain ⟨rfl, rfl⟩ := hc
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h.symm
      have hs : natLitSupported env = true := by
        cases hns : natLitSupported env
        · simp [interpExpr, hns] at hvb
        · rfl
      rw [interpExpr_lit hs] at hvb
      rw [interpExpr_const_natZero hs] at hva
      rw [← Option.some.inj hva, ← Option.some.inj hvb]
      rfl
    case isFalse => exact hPI h
  | Expr.const _ _, Expr.lit (.strVal _), h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.lit _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.lit l₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app f x, Expr.lit (.natVal nn), h =>
    dsimp only at h
    match nn, f, h with
    | 0, f, h => exact hPI h
    | k + 1, .const c [], h =>
      dsimp only at h
      split at h
      case isTrue hc =>
        subst hc
        have hs : natLitSupported env = true := by
          cases hns : natLitSupported env
          · simp [interpExpr, hns] at hvb
          · rfl
        rw [interpExpr_lit hs] at hvb
        rw [interpExpr_app_succ hs] at hva
        revert hva
        cases hx : interpExpr V m.val env φ d ρ x with
        | none => intro hva; exact nomatch hva
        | some vx =>
        intro hva
        dsimp only at hva
        simp only [WScoped] at hwa'
        simp only [looseBVarsBounded, Bool.and_eq_true] at hba'
        have hLbx : Expr.LeavesBounded x := fun l hl =>
          hLba' l (by simp [fvarLeaves, hl])
        have hokx : FvarsOk V m.val env φ d ρ x :=
          (FvarsOk.of_app hoka').2
        simp only [AnnotOk] at haa'
        obtain ⟨-, hax, -⟩ := haa'
        have hveq : vx = natLitVal V (m.val natZeroName φ)
            (m.val natSuccName φ) k :=
          ihd h hwa'.2 (by simp [WScoped]) hba'.2
            (by simp [looseBVarsBounded]) hLbx
            (fun l hl => by simp [fvarLeaves] at hl) hokx
            (fun l hl => by simp [fvarLeaves] at hl) hax
            (by simp [AnnotOk]) hx (interpExpr_lit hs)
        rw [← Option.some.inj hva, ← Option.some.inj hvb, hveq]
        rfl
      case isFalse => exact hPI h
    | k + 1, .bvar _, h => exact hPI h
    | k + 1, .fvar _ _ _, h => exact hPI h
    | k + 1, .sort _, h => exact hPI h
    | k + 1, .const _ (_ :: _), h => exact hPI h
    | k + 1, .app _ _, h => exact hPI h
    | k + 1, .lam _ _ _ _, h => exact hPI h
    | k + 1, .forallE _ _ _ _, h => exact hPI h
    | k + 1, .letE _ _ _ _, h => exact hPI h
    | k + 1, .lit _, h => exact hPI h
    | k + 1, .proj _ _ _, h => exact hPI h
  | Expr.app f x, Expr.lit (.strVal st), h =>
    match f, h with
    | .const cO usO, h =>
      dsimp only at h
      split at h
      case isTrue hc =>
        obtain ⟨rfl, rfl, hs⟩ := hc
        have hLbS : Expr.LeavesBounded (strLitToConstructor st) :=
          fun l hl => by
            rw [strLitToConstructor_fvarLeaves] at hl
            cases hl
        refine ihd h hwa' (strLitToConstructor_WScoped st d)
          hba' (strLitToConstructor_looseBVars st 0) hLba' hLbS hoka'
          (FvarsOk.of_not_hasFvar (strLitToConstructor_hasFvar st))
          haa' (annotOk_strLitToConstructor m hs) hva ?_
        rw [interpExpr_strLitToConstructor hs]
        exact hvb
      case isFalse => exact hPI h
    | .bvar _, h => exact hPI h
    | .fvar _ _ _, h => exact hPI h
    | .sort _, h => exact hPI h
    | .app _ _, h => exact hPI h
    | .lam _ _ _ _, h => exact hPI h
    | .forallE _ _ _ _, h => exact hPI h
    | .letE _ _ _ _, h => exact hPI h
    | .lit _, h => exact hPI h
    | .proj _ _ _, h => exact hPI h
  | Expr.proj s₁ i₁ e₁, Expr.lam n₂ ty₂ body₂ m₂, h =>
    exact etaBranch_sound' ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.proj _ _ _, Expr.sort _, h => exact hPI h
  | Expr.proj _ _ _, Expr.fvar _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.const _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.forallE _ _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.app _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.bvar _, h => exact hPI h
  | Expr.proj _ _ _, Expr.letE _ _ _ _, h => exact hPI h
  | Expr.proj _ _ _, Expr.lit _, h => exact hPI h
  | Expr.proj s₁ i₁ e₁, Expr.proj s₂ i₂ e₂, h =>
    dsimp only at h
    split at h
    case _ hi =>
      try simp only [Bind.bind, Except.bind] at h
      cases hd : isDefEqCore env fuel d e₁ e₂ with
      | error e => rw [hd] at h; exact nomatch h
      | ok r =>
      rw [hd] at h
      dsimp only at h
      cases r with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact hPI h
      | true =>
      have hieq : i₁ = i₂ := by simpa using hi
      subst hieq
      simp only [WScoped] at hwa' hwb'
      simp only [looseBVarsBounded] at hba' hbb'
      have hLbe₁ : Expr.LeavesBounded e₁ := fun l hl =>
        hLba' l (by simp [fvarLeaves, hl])
      have hLbe₂ : Expr.LeavesBounded e₂ := fun l hl =>
        hLbb' l (by simp [fvarLeaves, hl])
      have hoke₁ : FvarsOk V m.val env φ d ρ e₁ :=
        FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hoka'
      have hoke₂ : FvarsOk V m.val env φ d ρ e₂ :=
        FvarsOk.of_subset (fun l hl => by simpa [fvarLeaves] using hl) hokb'
      simp only [AnnotOk] at haa' hab'
      simp only [interpExpr] at hva hvb
      cases he₁ : interpExpr V m.val env φ d ρ e₁ with
      | none => rw [he₁] at hva; exact nomatch hva
      | some ve₁ =>
      rw [he₁] at hva
      dsimp only at hva
      cases he₂ : interpExpr V m.val env φ d ρ e₂ with
      | none => rw [he₂] at hvb; exact nomatch hvb
      | some ve₂ =>
      rw [he₂] at hvb
      dsimp only at hvb
      have hee : ve₁ = ve₂ :=
        ihd hd hwa' hwb' hba' hbb' hLbe₁ hLbe₂ hoke₁ hoke₂
          haa'.1 hab'.1 he₁ he₂
      subst hee
      exact Option.some.inj (hva.symm.trans hvb)
    case _ _ => exact hPI h
  | Expr.sort _, Expr.proj _ _ _, h => exact hPI h
  | Expr.fvar _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.const _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.forallE _ _ _ _, Expr.proj _ _ _, h => exact hPI h
  | Expr.lam n₁ ty₁ body₁ m₁, Expr.proj s₂ i₂ e₂, h =>
    exact etaBranch_sound ihw ihd ihi h hwa' hwb' hba' hbb' hLba' hLbb' hoka' hokb' haa' hab' hva hvb
  | Expr.app _ _, Expr.proj _ _ _, h => exact hPI h

end Claims

end Setlec
