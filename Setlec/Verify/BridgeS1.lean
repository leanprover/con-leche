import Setlec.Verify.SimS
import Setlec.Verify.BridgeWfImp

/-!
# Shared-state walks, part 1: the single-environment checker functions

Each lemma relates a generic declaration-checker function instantiated
at the shared operations (`sharedOps mode (mkFEnv env)`, state shared across
all operation calls) to the same function at the fueled families
(`(fueledOpsM mode)`), as a `SimAt` — the invariant `ISOK mode env` is threaded
through every call, so cache entries created by one call are consumed
by later ones soundly.  The per-site well-scopedness facts mirror the
`_wfimp` walks (`Setlec/Verify/BridgeWfImp.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {mode : CheckMode}

open Expr

section Walks1

variable {env : Env} {s₀ : IState}

/-- `checkConstantVal` at the shared operations simulates the fueled
instantiation; the returned constant's type is well-scoped. -/
theorem checkConstantValS_sim (henv : EnvWF env) {cv : ConstantVal}
    (hs : ISOK mode env s₀) :
    SimAt mode env s₀ (fun _ v w => v = w ∧ WScoped 0 v.type)
      (checkConstantVal (sharedOps mode (mkFEnv env)) env cv)
      (checkConstantVal (fueledOpsM mode) env cv) := by
  unfold checkConstantVal
  dsimp only [sharedOps]
  by_cases h1 : (env.find? cv.name).isSome = true
  · simp only [if_pos h1]
    exact SimAt.throw_bind
  simp only [if_neg h1]
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · simp only [if_pos h2]
    exact SimAt.throw_bind
  simp only [if_neg h2]
  by_cases h3 : cv.name.isProjFnShape = true
  · simp only [if_pos h3]
    exact SimAt.throw_bind
  simp only [if_neg h3]
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg =>
    simp only [if_neg h4]
    exact SimAt.throw_bind
  simp only [if_pos h4]
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg =>
    simp only [if_neg h5]
    exact SimAt.throw_bind
  simp only [if_pos h5]
  by_cases h6 : cv.type.hasFvar = true
  · simp only [if_pos h6]
    exact SimAt.throw_bind
  simp only [if_neg h6]
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)))
    (fun s₁ ty ty' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwty⟩ := hP
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams ty = true
  case neg =>
    simp only [if_neg h7]
    exact SimAt.throw_bind
  simp only [if_pos h7]
  by_cases h8 : Expr.constsResolve env ty = true
  case neg =>
    simp only [if_neg h8]
    exact SimAt.throw_bind
  simp only [if_pos h8]
  refine SimAt.bind (opE_infer_sim henv hs₁ hwty)
    (fun s₂ sty sty' hs₂ hext₂ hP₂ => ?_)
  obtain ⟨rfl, hwsty⟩ := hP₂
  refine SimAt.bind (opS_sim henv hs₂ hwsty)
    (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
  exact SimAt.pure hs₃ ⟨rfl, hwty⟩

/-- `checkDefnVal` at the shared operations; the returned environment
stores the annotated (fvar-free) value under `cv.name`. -/
theorem checkDefnValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint} (htf : WScoped 0 cv.type)
    (hs : ISOK mode env s₀) :
    SimAt mode env s₀ (fun _ v w => v = w ∧ ∀ cv' v' h',
        v.find? cv.name = some (.defnInfo cv' v' h') → v'.hasFvar = false)
      (checkDefnVal (sharedOps mode (mkFEnv env)) env cv value hint)
      (checkDefnVal (fueledOpsM mode) env cv value hint) := by
  unfold checkDefnVal
  dsimp only [sharedOps]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ val val' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind (opE_infer_sim henv hs₁ hwval)
    (fun s₂ vt vt' hs₂ hext₂ hP₂ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₂
  refine SimAt.bind (opB_sim henv hs₂ hwvt htf)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    refine SimAt.pure hs₃ ⟨rfl, ?_⟩
    intro cv' v' h' hf
    rw [Env.find?_cons, if_pos (show (ConstantInfo.defnInfo cv val
      hint).name = cv.name from rfl)] at hf
    simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
    obtain ⟨-, rfl, -⟩ := hf
    exact not_hasFvar_of_fvarsBelow_zero hwval.fvarsBelow

/-- `checkThmVal` at the shared operations. -/
theorem checkThmValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} (htf : WScoped 0 cv.type) (hs : ISOK mode env s₀) :
    SimAt mode env s₀ RelV
      (checkThmVal (sharedOps mode (mkFEnv env)) env cv value)
      (checkThmVal (fueledOpsM mode) env cv value) := by
  unfold checkThmVal
  dsimp only [sharedOps]
  refine SimAt.bind (opE_infer_sim henv hs htf)
    (fun s₁ sty sty' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwsty⟩ := hP
  refine SimAt.bind (opS_sim henv hs₁ hwsty)
    (fun s₂ u u' hs₂ hext₂ hP₂ => ?_)
  obtain rfl : u = u' := hP₂
  refine SimAt.bind (SimAt.liftFueled _ _ hs₂)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind (opE_annotate_sim henv hs₃
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₄ val val' hs₄ hext₄ hP₄ => ?_)
  obtain ⟨rfl, hwval⟩ := hP₄
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind (opE_infer_sim henv hs₄ hwval)
    (fun s₅ vt vt' hs₅ hext₅ hP₅ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₅
  refine SimAt.bind (opB_sim henv hs₅ hwvt htf)
    (fun s₆ b b' hs₆ hext₆ hP₆ => ?_)
  obtain rfl : b = b' := hP₆
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs₆ rfl

/-- `checkOpaqueVal` at the shared operations (the postcondition
carries the raw value's `hasFvar` fact for the compiler-trust install
gate's re-annotation). -/
theorem checkOpaqueValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} (htf : WScoped 0 cv.type) (hs : ISOK mode env s₀) :
    SimAt mode env s₀ (fun _ v w => v = w ∧ value.hasFvar = false)
      (checkOpaqueVal (sharedOps mode (mkFEnv env)) env cv value)
      (checkOpaqueVal (fueledOpsM mode) env cv value) := by
  unfold checkOpaqueVal
  dsimp only [sharedOps]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimAt.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimAt.throw_bind
  simp only [if_neg h2]
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ val val' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimAt.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimAt.throw_bind
  simp only [if_pos h4]
  refine SimAt.bind (opE_infer_sim henv hs₁ hwval)
    (fun s₂ vt vt' hs₂ hext₂ hP₂ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₂
  refine SimAt.bind (opB_sim henv hs₂ hwvt htf)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimAt.pure hs₃ ⟨rfl, Bool.not_eq_true _ ▸ h2⟩

/-- `checkReducePin` at the shared operations. -/
theorem checkReducePinS_sim (henv : EnvWF env) {env2 : Env} {c : Name}
    {value : Expr} (hvf : value.hasFvar = false)
    (hs : ISOK mode env s₀) :
    SimAt mode env s₀ RelV
      (checkReducePin (sharedOps mode (mkFEnv env)) env env2 c value)
      (checkReducePin (fueledOpsM mode) env env2 c value) := by
  unfold checkReducePin
  dsimp only [sharedOps]
  by_cases h1 : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg => simp only [if_neg h1]; exact SimAt.throw
  simp only [if_pos h1]
  by_cases h2 : reducePinGuard env c = true
  case neg => simp only [if_neg h2]; exact SimAt.throw
  simp only [if_pos h2]
  refine SimAt.bind (opE_annotate_sim henv hs
      (WScoped.of_not_hasFvar hvf))
    (fun s₁ valA valA' hs₁ hext₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  have h2' := h2
  unfold reducePinGuard at h2'
  simp only [Bool.and_eq_true] at h2'
  have hpinF : (reduceDeclPin c).hasFvar = false := by
    simpa using h2'.1.1.2
  refine SimAt.bind (opE_annotate_sim henv hs₁
      (WScoped.of_not_hasFvar hpinF))
    (fun s₂ pinA pinA' hs₂ hext₂ hP₂ => ?_)
  obtain ⟨rfl, hwpin⟩ := hP₂
  refine SimAt.bind (opB_sim henv hs₂ hwval hwpin)
    (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimAt.throw
  | true =>
    simp only [↓reduceIte]
    have hxW : WScoped 1 (reduceCertVar c) := by
      unfold reduceCertVar
      simp only [WScoped]
      refine ⟨Nat.zero_lt_one, ?_⟩
      unfold reduceElemTy
      split <;> simp only [WScoped]
    have happW : WScoped 1 (Expr.app valA (reduceCertVar c)) := by
      simp only [WScoped]
      exact ⟨WScoped.mono (Nat.zero_le 1) hwval, hxW⟩
    refine SimAt.bind (opB_sim henv hs₃ happW hxW)
      (fun s₄ b2 b2' hs₄ hext₄ hP₄ => ?_)
    obtain rfl : b2 = b2' := hP₄
    cases b2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.throw
    | true =>
      simp only [↓reduceIte]
      exact SimAt.pure hs₄ rfl

/-- `certifyNatEqs` at the shared operations. -/
theorem certifyNatEqsS_sim (henv : EnvWF env) :
    ∀ {eqs : List (Expr × Expr)},
      (∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true)) →
      ∀ {s₀ : IState}, ISOK mode env s₀ →
      SimAt mode env s₀ RelV
        (certifyNatEqs (sharedOps mode (mkFEnv env)) env eqs)
        (certifyNatEqs (fueledOpsM mode) env eqs)
  | [], _, s₀, hs => SimAt.pure hs rfl
  | eq :: rest, hsc, s₀, hs => by
    unfold certifyNatEqs
    dsimp only [sharedOps]
    have hh := hsc eq (List.mem_cons_self ..)
    refine SimAt.bind (opB_sim henv hs (WScoped.of_wscopedB hh.1)
        (WScoped.of_wscopedB hh.2))
      (fun s₁ b b' hs₁ hext₁ hP => ?_)
    obtain rfl : b = b' := hP
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact certifyNatEqsS_sim henv
        (fun e he => hsc e (List.mem_cons_of_mem _ he)) hs₁
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.pure hs₁ rfl

/-- `checkDivModCerts` at the shared operations. -/
theorem checkDivModCertsS_sim (henv : EnvWF env) {c : Name}
    {annVal : Expr} (hvf : annVal.hasFvar = false) :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      (∀ st ∈ stmts, (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧
        st.2.wscopedB 4 = true) →
      ∀ {s₀ : IState}, ISOK mode env s₀ →
      SimAt mode env s₀ RelV
        (checkDivModCerts (sharedOps mode (mkFEnv env)) env c annVal
          stmts proofs)
        (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs)
  | [], [], _, s₀, hs => SimAt.pure hs rfl
  | [], _ :: _, _, s₀, hs => SimAt.pure hs rfl
  | _ :: _, [], _, s₀, hs => SimAt.pure hs rfl
  | (hyps, eqE) :: srest, proof :: prest, hsc, s₀, hs => by
    unfold checkDivModCerts
    dsimp only [sharedOps]
    obtain ⟨hhyps, heqw⟩ := hsc (hyps, eqE) (List.mem_cons_self ..)
    have hhypsS : ∀ hyp ∈ hyps.map (Expr.substConst0 c annVal),
        hyp.wscopedB 2 = true := by
      intro hyp hh
      obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
      exact wscopedB_substConst0 hvf _ (hhyps h₀ hh₀)
    have heqS : (Expr.substConst0 c annVal eqE).wscopedB 4 = true :=
      wscopedB_substConst0 hvf _ heqw
    by_cases hguards : divModCertGuard env c annVal hyps eqE proof = true
    case neg =>
      simp only [if_neg hguards]
      exact SimAt.pure hs rfl
    simp only [if_pos hguards]
    have hguards' := hguards
    unfold divModCertGuard at hguards'
    simp only [Bool.and_eq_true] at hguards'
    have hpf : (Expr.substConstAll c annVal proof).hasFvar = false := by
      simpa using hguards'.1.1.1.1.2
    have happW : (divModCertApplied (Expr.substConstAll c annVal proof)
        (hyps.map (Expr.substConst0 c annVal))).wscopedB 4 = true :=
      divModCertApplied_wscopedB hpf hhypsS
    refine SimAt.bind (opE_annotate_sim henv hs
        (WScoped.of_wscopedB happW))
      (fun s₁ appliedA appliedA' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hwapp⟩ := hP
    refine SimAt.bind (opE_infer_sim henv hs₁ hwapp)
      (fun s₂ tp tp' hs₂ hext₂ hP₂ => ?_)
    obtain ⟨rfl, hwtp⟩ := hP₂
    refine SimAt.bind (opB_sim henv hs₂ hwtp (WScoped.of_wscopedB heqS))
      (fun s₃ b b' hs₃ hext₃ hP₃ => ?_)
    obtain rfl : b = b' := hP₃
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact checkDivModCertsS_sim henv hvf
        (fun st hst => hsc st (List.mem_cons_of_mem _ hst)) hs₃
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimAt.pure hs₃ rfl

/-- `checkDivModPin` at the shared operations. -/
theorem checkDivModPinS_sim (henv : EnvWF env) {env2 : Env} {c : Name}
    (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    (hs : ISOK mode env s₀) :
    SimAt mode env s₀ RelV
      (checkDivModPin (sharedOps mode (mkFEnv env)) env env2 c)
      (checkDivModPin (fueledOpsM mode) env env2 c) := by
  unfold checkDivModPin
  dsimp only [sharedOps]
  by_cases h1 : divModEnvGuard env2 c = true
  case neg => simp only [if_neg h1]; exact SimAt.throw
  simp only [if_pos h1]
  cases hfind : env2.find? c with
  | none => exact SimAt.throw
  | some ci =>
    cases ci with
    | axiomInfo cv' => exact SimAt.throw
    | thmInfo cv' v' => exact SimAt.throw
    | indInfo cv' caps => exact SimAt.throw
    | ctorInfo cv' nP nF => exact SimAt.throw
    | recInfo cv' mI rP rules => exact SimAt.throw
    | projInfo _ => exact SimAt.throw
    | defnInfo cv' value' hint' =>
      dsimp only
      by_cases hping : (divModPinGuard env c &&
          divModCertsGuard env c value') = true
      case neg => simp only [if_neg hping]; exact SimAt.throw
      simp only [if_pos hping]
      have hping' := hping
      simp only [Bool.and_eq_true] at hping'
      have hping'' := hping'.1
      unfold divModPinGuard at hping''
      simp only [Bool.and_eq_true] at hping''
      have hpinF : (divModDeclPin c).hasFvar = false := by
        simpa using hping''.1.1.2
      refine SimAt.bind (opE_annotate_sim henv hs
          (WScoped.of_not_hasFvar hpinF))
        (fun s₁ pinA pinA' hs₁ hext₁ hP => ?_)
      obtain ⟨rfl, hwpin⟩ := hP
      have hvf : value'.hasFvar = false := hv'f _ _ _ hfind
      refine SimAt.bind (opB_sim henv hs₁
          (WScoped.of_not_hasFvar hvf) hwpin)
        (fun s₂ b b' hs₂ hext₂ hP₂ => ?_)
      obtain rfl : b = b' := hP₂
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimAt.throw
      | true =>
        simp only [↓reduceIte]
        refine SimAt.bind (checkDivModCertsS_sim henv hvf
            (divModCertStmts_wscopedB hc) hs₂)
          (fun s₃ ok ok' hs₃ hext₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.throw
        | true =>
          simp only [↓reduceIte]
          exact SimAt.pure hs₃ rfl

/-- `installBasisDecl` (operation-free) as a `SimAt`. -/
theorem installBasisDeclS_sim {env' : Env} {ci : ConstantInfo}
    (hs : ISOK mode env s₀) :
    SimAt mode env s₀ RelV (installBasisDecl env' ci : CheckIM Env)
      (installBasisDecl env' ci : FueledM Env) := by
  unfold installBasisDecl
  by_cases h1 : (env'.find? ci.name).isNone = true
  · simp only [if_pos h1]
    exact SimAt.pure hs rfl
  · simp only [if_neg h1]
    exact SimAt.throw_bind

/-- The basis-install fold as a `SimAt`. -/
theorem installBasisFoldS_sim :
    ∀ (cis : List ConstantInfo) (env' : Env) {s₀ : IState},
      ISOK mode env s₀ →
      SimAt mode env s₀ RelV
        (cis.foldlM installBasisDecl env' : CheckIM Env)
        (cis.foldlM installBasisDecl env' : FueledM Env)
  | [], env', s₀, hs => SimAt.pure hs rfl
  | ci :: cis, env', s₀, hs => by
    simp only [List.foldlM]
    refine SimAt.bind (installBasisDeclS_sim hs)
      (fun s₁ e e' hs₁ hext₁ hP => ?_)
    obtain rfl : e = e' := hP
    exact installBasisFoldS_sim cis e hs₁

/-- The non-inductive branches of `checkDecl` at the shared
operations: the whole declaration runs at the input environment, all
operation calls sharing one state. -/
theorem checkDeclS_nonind_sim (henv : EnvWF env) (hs : ISOK mode env s₀)
    {d : Declaration} (hnotind : ∀ block, d ≠ .indDecl block) :
    SimAt mode env s₀ RelV (checkDecl mode (sharedOps mode (mkFEnv env)) env d)
      (checkDecl mode (fueledOpsM mode) env d) := by
  cases d with
  | indDecl block => exact absurd rfl (hnotind block)
  | defnDecl cv value hint =>
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    refine SimAt.bind (checkDefnValS_sim henv hwty hs₁)
      (fun s₂ env2 env2' hs₂ hext₂ hP₂ => ?_)
    obtain ⟨rfl, hv'fD⟩ := hP₂
    by_cases h1 : natOpNames.contains cvA.name = true
    case neg =>
      simp only [if_neg h1]
      by_cases h4 : natDivModNames.contains cvA.name = true
      case neg =>
        simp only [if_neg h4]
        exact SimAt.pure hs₂ rfl
      simp only [if_pos h4]
      refine SimAt.bind (checkDivModPinS_sim henv
          (List.contains_iff_mem.mp h4) hv'fD hs₂)
        (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
      exact SimAt.pure hs₃ rfl
    simp only [if_pos h1]
    by_cases h2 : (natOpGuard env2 cvA.name &&
        (natOpDeps cvA.name).all (natOpStoredOk env2)) = true
    case neg => simp only [if_neg h2]; exact SimAt.throw_bind
    simp only [if_pos h2]
    cases hfind : env2.find? cvA.name with
    | none => exact SimAt.throw_bind
    | some ci =>
      cases ci with
      | defnInfo cvS value' hintS =>
        dsimp only
        have hvf : value'.hasFvar = false := hv'fD _ _ _ hfind
        have hsc : ∀ eq ∈ (natOpEquations 0 cvA.name).map
            (fun eq => (Expr.substConst0 cvA.name value' eq.1,
              Expr.substConst0 cvA.name value' eq.2)),
            (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true) := by
          intro eq heq
          obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
          obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB
            (by simpa using h1) eq₀ heq₀
          exact ⟨wscopedB_substConst0 hvf _ hs1,
            wscopedB_substConst0 hvf _ hs2⟩
        refine SimAt.bind (certifyNatEqsS_sim henv hsc hs₂)
          (fun s₃ ok ok' hs₃ hext₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimAt.throw_bind
        | true =>
          simp only [↓reduceIte]
          by_cases h4 : natDivModNames.contains cvA.name = true
          case neg =>
            simp only [if_neg h4]
            exact SimAt.pure hs₃ rfl
          simp only [if_pos h4]
          refine SimAt.bind (checkDivModPinS_sim henv
              (List.contains_iff_mem.mp h4) hv'fD hs₃)
            (fun s₄ u u' hs₄ hext₄ hP₄ => ?_)
          exact SimAt.pure hs₄ rfl
      | axiomInfo cv' => exact SimAt.throw_bind
      | thmInfo cv' v' => exact SimAt.throw_bind
      | indInfo cv' caps => exact SimAt.throw_bind
      | ctorInfo cv' nP nF => exact SimAt.throw_bind
      | recInfo cv' mI rP rules => exact SimAt.throw_bind
      | projInfo _ => exact SimAt.throw_bind
  | thmDecl cv value =>
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    exact checkThmValS_sim henv hwty hs₁
  | opaqueDecl cv value =>
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    refine SimAt.bind (checkOpaqueValS_sim henv hwty hs₁)
      (fun s₂ env2 env2' hs₂ hext₂ hP₂ => ?_)
    obtain ⟨rfl, hvf⟩ := hP₂
    by_cases h1 : reduceOpNames.contains cvA.name = true
    case neg =>
      simp only [if_neg h1]
      exact SimAt.pure hs₂ rfl
    simp only [if_pos h1]
    refine SimAt.bind (checkReducePinS_sim henv hvf hs₂)
      (fun s₃ u u' hs₃ hext₃ hP₃ => ?_)
    exact SimAt.pure hs₃ rfl
  | axiomDecl cv =>
    unfold checkDecl
    dsimp only
    refine SimAt.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hext₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    by_cases h1 : stdAxiomOk env cvA = true
    · simp only [if_pos h1]
      exact SimAt.pure hs₁ rfl
    · simp only [if_neg h1]
      by_cases htc : cvA.name = trustCompilerName
      · simp only [if_pos htc]
        by_cases htc2 : trustCompilerOk env cvA = true
        · simp only [if_pos htc2]
          exact SimAt.pure hs₁ rfl
        · simp only [if_neg htc2]
          exact SimAt.throw
      · simp only [if_neg htc]
        by_cases hor : cvA.name = ofReduceNatName ∨
            cvA.name = ofReduceBoolName
        · simp only [if_pos hor]
          by_cases hor2 : ofReduceAxOk env cvA = true
          · simp only [if_pos hor2]
            exact SimAt.pure hs₁ rfl
          · simp only [if_neg hor2]
            exact SimAt.throw
        · simp only [if_neg hor]
          by_cases h2 : cvA.name = propextName ∨ cvA.name = choiceName
          · simp only [if_pos h2]
            exact SimAt.throw
          · simp only [if_neg h2]
            by_cases h3 : toleratedAxiomNames.contains cvA.name = true
            · simp only [if_pos h3]
              exact SimAt.pure hs₁ rfl
            · simp only [if_neg h3]
              exact SimAt.throw
  | basisDecl kind =>
    unfold checkDecl
    dsimp only
    by_cases hq : kind = .quotK
    · simp only [if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · simp only [if_pos he]
        exact installBasisFoldS_sim _ env hs
      · simp only [if_neg he]
        exact SimAt.throw_bind
    · simp only [if_neg hq]
      exact installBasisFoldS_sim _ env hs

end Walks1

end Setlec
